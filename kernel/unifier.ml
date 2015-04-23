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

type problem = { cpt:int; decls: metainfo list; defs: S.t; }

let empty = { cpt=0; decls=[]; defs=S.identity; }

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
    | CTerm ty -> 
          (mj,{cpt=pb.cpt+1; decls=(MetaDecl (ctx,pb.cpt,ty))::pb.decls; defs=pb.defs;})
    | CType -> (mj,{cpt=pb.cpt+1; decls=(MetaType (ctx,pb.cpt))::pb.decls; defs=pb.defs;})
    | CSort -> (mj,{cpt=pb.cpt+1; decls=(MetaSort (ctx,pb.cpt))::pb.decls; defs=pb.defs;})

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
  else true,{cpt=pb.cpt; decls=pb.decls; defs=S.add pb.defs n t}

let set_decl d pb = let n = match d with | MetaDecl (_,n,_) | MetaType (_,n) | MetaSort (_,n) -> n in
  let rec aux s = function
    | MetaDecl (_,m,_) :: tl | MetaType (_,m) :: tl | MetaSort (_,m) :: tl when n=m -> List.rev_append s (d::tl)
    | d' :: tl -> aux (d'::s) tl
    | [] -> assert false
  in (),{cpt=pb.cpt; decls=aux [] pb.decls; defs=pb.defs;}

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
      | MetaType (ctx,_) -> new_meta ctx l s CSort >>= fun mk ->
          set_decl (MetaDecl (ctx,n,mk)) >>= fun () -> return (ctx,mk)
      | MetaSort (ctx,_) -> set_decl (MetaDecl (ctx,n,mk_Kind)) >>= fun () ->
          set_meta n (mk_Type l) >>= fun _ -> return (ctx,mk_Kind)
      end
  | _ -> assert false

(** Unification *)

let whnf sg t pb = (S.whnf sg pb.defs t,pb)

let unify sg ctx t c =
  let rec aux ctx t1 t2 = whnf sg t1 >>= fun t1' -> whnf sg t2 >>= fun t2' ->
    if Reduction.are_convertible sg t1' t2'
      then return true
      else begin (*(fun pb -> Printf.eprintf "Unification: %a === %a\nunder %a\nwith %a.\n" pp_term t1 pp_term t2 pp_context (Context.to_context ctx) pp_problem pb; (),pb) >>= fun () ->*)
      match t1', t2' with
        | Meta (_,_,n,_), Meta (_,_,m,_) -> set_meta n t2' >>= (function | true -> return true | false -> set_meta m t1')
        | Meta (_,_,n,_), _ -> set_meta n t2'
        | _, Meta (_,_,n,_) -> set_meta n t1'
        | Pi (l,x,a1,b1), Pi(_,_,a2,b2) -> aux ctx a1 a2 >>= fun b -> if b
          then aux ((l,x,a1)::ctx) b1 b2
          else return false
        | _, _ -> (fun pb -> Printf.eprintf "Failed to unify %a === %a\nunder %a\nwith %a.\n" pp_term t1' pp_term t2' pp_context ctx pp_problem pb; (),pb) >>= fun () ->
            return false
    end in
  match c with
    | CTerm u -> aux ctx t u
    | CType -> failwith "Refine mode: cannot unify with type"
    | CSort -> begin match t with
        | Kind | Type _ -> return true
        | _ -> aux ctx t (mk_Type dloc) (* bad *)
        end

