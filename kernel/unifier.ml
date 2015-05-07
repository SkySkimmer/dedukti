open Basics
open Term

type refine_error =
  | UnknownMeta of int

exception RefineError of refine_error

module S = Msubst.S

type metainfo =
  | MetaDecl of context*int*term (* ctx |- ?j : ty *)
  | MetaType of context*int      (* either ctx |- ?j : s or ?j = Kind *)
  | MetaSort of context*int      (* ?j = Type or Kind *)

let pp_metainfo out = function
  | MetaDecl (ctx,n,ty) -> Printf.fprintf out "%a |- ?_%i : %a" pp_context ctx n pp_term ty
  | MetaType (ctx,n)    -> Printf.fprintf out "%a |- ?_%i : *" pp_context ctx n
  | MetaSort (ctx,n)    -> Printf.fprintf out "%a |- ?_%i sort" pp_context ctx n

type disagreement = context*term*term

type problem = { cpt:int; decls: metainfo list; defs: S.t; pairs: disagreement list; }

let empty = { cpt=0; decls=[]; defs=S.identity; pairs=[]; }

let pp_problem out pb = Printf.fprintf out "cpt=%i;\n%a\n%a\n" pb.cpt (pp_list "\n" pp_metainfo) pb.decls S.pp pb.defs

(** Monad *)
type 'a t = problem -> 'a*problem

let return (x:'a) : 'a t = fun pb -> x,pb

let (>>=) (x:'a t) (f:'a -> 'b t) : 'b t = fun pb -> let (x,pb) = x pb in f x pb

let extract f = f empty

let apply pb t = S.apply pb.defs t

let simpl t pb = apply pb t,pb

(** Methods *)

let new_meta ctx l s c pb =
  let substj = List.mapi (fun i (_,x,_) -> x,mk_DB dloc x i) ctx in
  let mj = mk_Meta l s pb.cpt substj in
  match c with
    | MTyped ty -> 
          (mj,{cpt=pb.cpt+1; decls=(MetaDecl (ctx,pb.cpt,ty))::pb.decls; defs=pb.defs; pairs=pb.pairs;})
    | MType -> (mj,{cpt=pb.cpt+1; decls=(MetaType (ctx,pb.cpt))::pb.decls; defs=pb.defs; pairs=pb.pairs;})
    | MSort -> (mj,{cpt=pb.cpt+1; decls=(MetaSort (ctx,pb.cpt))::pb.decls; defs=pb.defs; pairs=pb.pairs;})

let rec accessible n pb = function
  | Kind | Type _ | DB _ | Const _ | Hole _ -> false
  | App (f,a,args) -> List.exists (accessible n pb) (f::a::args)
  | Lam (_,_,None,u) -> accessible n pb u
  | Lam (_,_,Some a,u) -> accessible n pb a || accessible n pb u
  | Pi (_,_,a,b) -> accessible n pb a || accessible n pb b
  | Meta (_,_,m,ts) -> (n==m) || List.exists (fun (_,x) -> accessible n pb x) ts || ( match S.meta_raw pb.defs m with
      | Some t -> accessible n pb t
      | None -> false)

let set_meta n t pb = if accessible n pb t
  then false,pb
  else true,{cpt=pb.cpt; decls=pb.decls; defs=S.add pb.defs n t; pairs=pb.pairs;}

let set_decl d pb = let n = match d with | MetaDecl (_,n,_) | MetaType (_,n) | MetaSort (_,n) -> n in
  let rec aux s = function
    | MetaDecl (_,m,_) :: tl | MetaType (_,m) :: tl | MetaSort (_,m) :: tl when n=m -> List.rev_append s (d::tl)
    | d' :: tl -> aux (d'::s) tl
    | [] -> assert false
  in (),{cpt=pb.cpt; decls=aux [] pb.decls; defs=pb.defs; pairs=pb.pairs;}

(* We need to infer a type for gamma |- ?j[sigma].
   If delta |- ?j : t in the context we check gamma |- sigma : delta then return sigma(t)
   If delta |- ?j : * then we know that ?j <> Kind, then ?j : ?k with ?k = * and we are in the standard case
   If delta |- ?j = * then ?j = Type : Kind
*)
let meta_constraint = function
  | Meta (l,s,n,_) -> begin fun pb ->
    try (List.find (function
      | MetaDecl (_,m,_) | MetaType (_,m) | MetaSort (_,m) -> n=m) pb.decls),pb
    with | Not_found -> raise (RefineError (UnknownMeta n))
    end >>= begin function
      | MetaDecl (ctx,_,ty) -> return (ctx,ty)
      | MetaType (ctx,_) -> new_meta ctx l s MSort >>= fun mk ->
          set_decl (MetaDecl (ctx,n,mk)) >>= fun () -> return (ctx,mk)
      | MetaSort (ctx,_) -> set_decl (MetaDecl (ctx,n,mk_Kind)) >>= fun () ->
          set_meta n (mk_Type l) >>= fun _ -> return (ctx,mk_Kind)
      end
  | _ -> assert false

(** Unification *)

let whnf sg t pb = (S.whnf sg pb.defs t,pb)

let rec gen_pair sg ctx t1 t2 : disagreement list option t = whnf sg t1 >>= fun t1' -> whnf sg t2 >>= fun t2' ->
  match t1', t2' with
    | Kind, Kind | Type _, Type _ -> return (Some [])
    | DB (_,n,_), DB (_,m,_) when (n=m) -> return (Some [])
    | Const (_,m,v), Const (_,m',v') when (ident_eq v v' && ident_eq m m') -> return (Some [])
    | Pi (_,_,a,b), Pi (_,_,a',b') -> gen_pair sg ctx a a' >>= begin function
        | Some l -> gen_pair sg ctx b b' >>= begin function
            | Some l' -> return (Some (List.append l l'))
            | None -> return None
            end
        | None -> return None
        end
    | Lam (l,x,Some a,b), Lam (_,_,_,b') | Lam (_,_,_,b), Lam (l,x,Some a,b') -> gen_pair sg ((l,x,a)::ctx) b b'
    | Meta (_,_,n,_), Meta (_,_,m,_) -> set_meta n t2' >>= (function | true -> return true | false -> set_meta m t1') >>= (function
        | true -> return (Some []) | false -> return None)
    | Meta (_,_,n,_), t | t, Meta (_,_,n,_) -> set_meta n t >>= (function | true -> return (Some []) | false -> return None)
(*
    | App
*)
    | _, _ -> if Reduction.are_convertible sg t1' t2'
      then return (Some [])
      else return None

let add_pairs l pb = (),{pb with pairs=List.append pb.pairs l}

let unify sg ctx t c =
  let aux t1 t2 = gen_pair sg ctx t1 t2 >>= function
    | Some [] -> return true
    | Some l -> add_pairs l >>= fun () -> return true
    | None -> return false
  in
  match c with
    | MTyped u -> aux t u
    | MType -> failwith "Refine mode: cannot unify with type"
    | MSort -> begin match t with
        | Kind | Type _ -> return true
        | _ -> aux t (mk_Type dloc) (* bad *)
        end

