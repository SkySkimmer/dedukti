open Basics
open Term
open Monads
open Typing

module S = Msubst

let subst_l l n t = Subst.psubst_l (LList.of_list (List.map Lazy.from_val l)) n t

let mk_Appl t = function
  | a::args -> mk_App t a args
  | [] -> t

let mkind_map f = function
  | MTyped ty -> MTyped (f ty)
  | MType | MSort as m -> m

type mdecl = context*mkind

type pair = context*term*term

type problem = { cpt:int; decls:mdecl IntMap.t; sigma:S.t; pairs: pair list; }

let fresh = {cpt=0; decls=IntMap.empty; sigma=S.identity; pairs=[]; }

(* A monad with effects, backtracking and restricted state operations *)
module Types = struct
  type err = typing_error
  type state = problem
end
module M0 = BacktrackF(IO)(Types)
module M = StateF(M0)(Types)
include M

include MonadF(M)

include M.EffectT(struct
  type 'a t = 'a M0.t
  include M0.EffectT(IO)
end)

include M.BacktrackT(M0)

let run m = match IO.run (M0.run (M.run m fresh)) () with
  | Nil e -> raise (TypingError e)
  | Cons (r,_) -> r

let raise e = effectful (fun () -> raise e)

(* monad basic operations end here *)

let pp_mkind out = function
  | MTyped ty -> Printf.fprintf out ": %a" pp_term ty
  | MType -> Printf.fprintf out ": *"
  | MSort -> Printf.fprintf out "= *"

let pp_mdecl out n (ctx,mk) = Printf.fprintf out "%a |- %i %a\n" pp_context ctx n pp_mkind mk

let pp_decls out m = IntMap.iter (fun i d -> pp_mdecl out i d) m

let pp_pair out (ctx,t1,t2) = Printf.fprintf out "%a |- %a == %a\n" pp_context ctx pp_term t1 pp_term t2

let pp_problem out pb = Printf.fprintf out "{ cpt=%i;\n%a\n%a\n%a\n }\n" pb.cpt pp_decls pb.decls S.pp pb.sigma  (pp_list "" pp_pair) pb.pairs

let pp_state = get >>= fun pb -> effectful (fun () ->
  Printf.printf "%a\n" pp_problem pb
  )

let apply pb t = S.apply pb.sigma t

let add_pair sg p = (*effectful (fun () -> Printf.printf "Adding pair %a in\n" pp_pair p) >>= fun () -> pp_state >>= fun () ->*)
  modify (fun pb -> {pb with pairs=p::pb.pairs})

let new_meta ctx lc s k = get >>= fun pb -> match k with
  | MSort -> let mj = mk_Meta lc s pb.cpt [] in
      set { pb with cpt=pb.cpt+1; decls=IntMap.add pb.cpt ([],MSort) pb.decls } >>= fun () ->
      return mj
  | _ -> let substj = List.mapi (fun i (_,x,_) -> x,mk_DB dloc x i) ctx in
      let mj = mk_Meta lc s pb.cpt substj in
      set { pb with cpt=pb.cpt+1; decls=IntMap.add pb.cpt (ctx,k) pb.decls } >>= fun () ->
      return mj

let meta_decl lc s n = get >>= fun pb ->
  try return (IntMap.find n pb.decls)
  with | Not_found -> raise (TypingError (UnknownMeta (lc,s,n)))

let add_sort_pair sg ctx = function
  | Meta (lc,s,x,ts) as t -> meta_decl lc s x >>= begin function
      | (_,MSort) -> return ()
      | _ -> new_meta ctx lc (hstring "Sort") MSort >>= fun ms -> add_pair sg (ctx,t,ms)
      end
  | t -> new_meta ctx dloc (hstring "Sort") MSort >>= fun ms -> add_pair sg (ctx,t,ms)

let set_decl n d = modify (fun pb -> { pb with decls=IntMap.add n d pb.decls })

let set_meta n t = get >>= fun pb ->
  if S.mem pb.sigma n then zero Not_Applicable
  else set { pb with sigma=S.add pb.sigma n t }

let meta_constraint lc s n = meta_decl lc s n >>= function
  | (ctx,MTyped ty) -> return (ctx,ty)
  | (ctx,MType) -> new_meta ctx lc s MSort >>= fun mk ->
      set_decl n (ctx,MTyped mk) >>= fun () -> return (ctx,mk)
  | (ctx,MSort) -> set_decl n (ctx,MTyped mk_Kind) >>= fun () ->
      set_meta n (mk_Type dloc) >>= fun () -> return (ctx,mk_Kind)


let whnf sg t = get >>= fun pb -> return (S.whnf sg pb.sigma t)

(*
This is only used in the pseudo-unification step of pattern checking.
TODO(future work): If possible we would like to use unification instead.
*)
let simpl t = get >>= fun pb -> return (apply pb t)

let normalize = modify (fun pb -> let s = S.normalize pb.sigma in
  let d = IntMap.map (fun (ctx,ty) -> (List.map (fun (lc,x,t) -> (lc,x,S.apply s t)) ctx, mkind_map (S.apply s) ty)) pb.decls in
  let p = List.map (fun (ctx,t1,t2) -> (List.map (fun (lc,x,t) -> (lc,x,S.apply s t)) ctx, S.apply s t1, S.apply s t2)) pb.pairs in
  {cpt=pb.cpt; decls=d; sigma=s; pairs=p; })

let var_get_type ctx lc x n = try let (_,_,ty) = List.nth ctx n in return (Subst.shift (n+1) ty)
  with | Failure _ -> raise (TypingError (VariableNotFound (lc,x,n,ctx)))

let rec pi_app sg ty = function
  | a::args -> whnf sg ty >>= begin function
      | Pi (_,_,_,b) -> pi_app sg (Subst.subst b a) args
      | _ -> zero Not_Applicable (* Not necessarily the right error but w/e *)
      end
  | [] -> return ty

let rec expected_type sg ctx = function
  | Kind -> raise (TypingError KindIsNotTypable)
  | Type _ -> return mk_Kind
  | DB (lc,x,n) -> var_get_type ctx lc x n
  | Const (l,md,id) -> return (Signature.get_type sg l md id)
  | App (f,a,args) -> expected_type sg ctx f >>= fun ty -> pi_app sg ty (a::args)
  | Lam (lc,x,Some a,b) -> expected_type sg ((lc,x,a)::ctx) b >>= fun ty ->
      return (mk_Pi lc x a ty)
  | Lam (lc,_,None,_) -> raise (TypingError (DomainFreeLambda lc))
  | Pi (lc,x,a,b) -> expected_type sg ((lc,x,a)::ctx) b
  | Hole _ -> assert false
  | Meta (lc,s,x,ts) -> meta_constraint lc s x >>= fun (_,ty0) ->
      return (subst_l (List.map snd ts) 0 ty0)

(* returns None if there are no (unsolved) disagreement pairs *)
let inspect = get >>= function
  | { pairs = p::_ } -> return (Some p)
  | _ -> return None

(* the first pair is popped and used for f's argument *)
let pair_modify f = get >>= fun pb -> match pb.pairs with
  | p::rem -> set { pb with pairs=rem } >>= fun () -> f p >>= fun l -> modify (fun pb -> { pb with pairs=List.append l pb.pairs })
  | _ -> zero Not_Applicable

type side = LEFT | RIGHT

let pp_side out = function
  | LEFT -> Printf.fprintf out "LEFT"
  | RIGHT -> Printf.fprintf out "RIGHT"

let pair_modify_side side f = pair_modify (fun (ctx,lop,rop) -> match side with
  | LEFT -> f lop >>= fun lop -> return [ctx,lop,rop]
  | RIGHT -> f rop >>= fun rop -> return [ctx,lop,rop])

let pair_symmetric side f = pair_modify (fun (ctx,lop,rop) -> match side with
  | LEFT -> f ctx lop rop
  | RIGHT -> f ctx rop lop)


(*
pair-convertible and helpers
*)

let rec add_to_list2 l1 l2 lst =
  match l1, l2 with
    | [], [] -> Some lst
    | s1::l1, s2::l2 -> add_to_list2 l1 l2 ((s1,s2)::lst)
    | _,_ -> None

let rec are_convertible_lst sg : (term*term) list -> bool t = function
  | [] -> return true
  | (t1,t2)::lst ->
    begin
      ( if term_eq t1 t2 then return (Some lst)
        else
          whnf sg t1 >>= fun t1 -> whnf sg t2 >>= fun t2 -> match t1,t2 with
          | Kind, Kind | Type _, Type _ | Hole _, Hole _ -> return (Some lst)
          | Const (_,m,v), Const (_,m',v') when ( ident_eq v v' && ident_eq m m' ) -> return (Some lst)
          | DB (_,_,n), DB (_,_,n') when ( n==n' ) -> return (Some lst)
          | App (f,a,args), App (f',a',args') ->
            return (add_to_list2 args args' ((f,f')::(a,a')::lst))
          | Lam (_,_,_,b), Lam (_,_,_,b') -> return (Some ((b,b')::lst))
          | Pi (_,_,a,b), Pi (_,_,a',b') -> return (Some ((a,a')::(b,b')::lst))
          | Meta (_,_,n,ts), Meta (_,_,n',ts') when ( n==n' ) -> return (add_to_list2 (List.map snd ts) (List.map snd ts') lst)
          | t1, t2 -> return None
      ) >>= function
      | None -> return false
      | Some lst2 -> are_convertible_lst sg lst2
    end

let are_convertible sg t1 t2 = are_convertible_lst sg [(t1,t2)]

let pair_convertible sg = pair_modify (fun (ctx,lop,rop) ->
  are_convertible sg lop rop >>= function
  | true -> return []
  | false -> zero Not_Applicable)

(* Tries to unfold the meta at the head of the left (resp right) term *)
let meta_delta side = pair_modify_side side (fun t -> get >>= fun pb -> match t with
  | Meta _ as m -> begin match S.meta_val pb.sigma m with
      | Some m' -> return m'
      | None -> zero Not_Applicable
      end
  | App (Meta _ as m,a,args) -> begin match S.meta_val pb.sigma m with
      | Some m' -> return (mk_App m' a args)
      | None -> zero Not_Applicable
      end
  | _ -> zero Not_Applicable
  )

let step_reduce sg side = pair_modify_side side (fun t -> match Reduction.one_step sg t with
  | Some t' -> return t'
  | None -> zero Not_Applicable
  )

(*
Decompose the pair according to the common constructor of the terms:
- Psi, App c ts, App c' ts' -> Psi,c,c' and Psi,ts,ts' (fails if |ts| <> |ts'|)
- Psi,Pi a b, Pi a' b' -> Psi,a,a' and a::Psi,b,b'
- Psi,Type,Type -> []
- etc
*)

let decompose = let pair_decompose (ctx,t1,t2) = match t1,t2 with
  | Kind, Kind | Type _, Type _ -> return []
  | Const (_,m,v), Const (_,m',v') when ( ident_eq v v' && ident_eq m m' ) -> return []
  | DB (_,_,n), DB (_,_,n') when (n=n') -> return []
  | App (f,a,args), App (f',a',args') ->
    begin match try Some (List.map2 (fun t1 t2 -> (ctx,t1,t2)) (f::a::args) (f'::a'::args')) with | Invalid_argument _ -> None with
        | Some l -> return l
        | None -> zero Not_Applicable
        end
  | Lam (_,x,Some a,b), Lam (_,_,Some a',b') -> return [(ctx,a,a');((dloc,x,a)::ctx,b,b')]
  | Lam (_,x,Some a,b), Lam (_,_,None,b') -> return [(dloc,x,a)::ctx,b,b']
  | Lam (_,_,None,b), Lam (_,y,Some a',b') -> return [((dloc,y,a')::ctx,b,b')]
  | Lam _, Lam _ -> zero DecomposeDomainFreeLambdas
  | Pi (_,x,a,b), Pi (_,_,a',b') -> return [(ctx,a,a');((dloc,x,a)::ctx,b,b')]
  | Meta (_,_,n,ts), Meta (_,_,n',ts') when ( n==n' ) -> return (List.map2 (fun (_,t1) (_,t2) -> (ctx,t1,t2)) ts ts')
  | App _, _ | _, App _ | Meta _, _ | _, Meta _ -> zero Not_Applicable
  | Const _, _ | _, Const _ -> zero Not_Applicable
  | _, _ -> zero Not_Unifiable
  in pair_modify pair_decompose

let meta_same_same = pair_modify (fun (ctx,lop,rop) -> match lop,rop with
  | Meta (_,_,n,ts), Meta (_,_,n',ts') when (n=n') ->
    let b = try List.for_all2 (fun (_,t1) (_,t2) -> term_eq t1 t2) ts ts' with | Invalid_argument _ -> false in
      if b then return [] else zero Not_Applicable
  | App (Meta (_,_,n,ts),a,args), App (Meta (_,_,n',ts'),a',args') when (n=n') ->
    let b = try List.for_all2 (fun (_,t1) (_,t2) -> term_eq t1 t2) ts ts' with | Invalid_argument _ -> false in
      if b then match try Some (List.map2 (fun t1 t2 -> ctx,t1,t2) (a::args) (a'::args')) with | Invalid_argument _ -> None with
          | Some l -> return l
          | None -> zero Not_Applicable
          else zero Not_Applicable
  | _,_ -> zero Not_Applicable)

(* Count occurences of true before index n, returning None if nth l n = false *)
let sanitize_index l n = let rec aux n c = function
  | [] -> None
  | b::l -> if n=0 then if b then Some c else None
            else aux (n-1) (if b then c+1 else c) l
  in aux n 0 l

(* if t lives in context ctx, sanitize_term l t lives in ctx filtered by l *)
let rec sanitize_term sigma l = function
  | Kind | Type _ | Const _ as t -> Some t
  | DB (lc,x,n) -> map_opt (fun n -> mk_DB lc x n) (sanitize_index l n)
  | App (f,a,args) -> Opt.(Opt.fold (fun args t -> map_opt (fun t -> t::args) (sanitize_term sigma l t))
                                    [] (List.rev_append args [a;f]) >>= function
      | f::a::args -> Some (mk_App f a args)
      | _ -> assert false)
  | Lam (lc,x,Some a,b) -> Opt.(sanitize_term sigma l a >>= fun a -> Opt.(sanitize_term sigma (true::l) b >>= fun b -> Some (mk_Lam lc x (Some a) b)))
  | Lam (lc,x,None,b) -> Opt.(sanitize_term sigma (true::l) b >>= fun b -> Some (mk_Lam lc x None b))
  | Pi (lc,x,a,b) -> Opt.(sanitize_term sigma l a >>= fun a -> Opt.(sanitize_term sigma (true::l) b >>= fun b -> Some (mk_Pi lc x a b)))
  | Hole _ -> assert false
  | Meta (lc,s,n,ts) as m -> begin match S.meta_val sigma m with
      | Some m' -> sanitize_term sigma l m'
      | None -> Opt.(Opt.fold (fun ts (x,t) -> map_opt (fun t -> (x,t)::ts) (sanitize_term sigma l t))
                              [] (List.rev ts) >>= fun ts ->
          Some (mk_Meta lc s n ts))
      end

let rec sanitize_context s l ctx = match l,ctx with
  | b::l, (lc,x,ty)::ctx -> let (l,ctx) = sanitize_context s l ctx in
      if b then begin match sanitize_term s l ty with
        | Some ty -> true::l,(lc,x,ty)::ctx
        | None -> false::l,ctx
        end
      else false::l,ctx
  | [],[] -> [],[]
  | _,_ -> assert false

let subst_intersection ts ts' = List.map2 (fun (_,t1) (_,t2) -> term_eq t1 t2) ts ts'

let context_project l ctx = let rec aux n acc = function
  | true::l,(lc,x,_)::ctx -> aux (n+1) ((x,mk_DB lc x n)::acc) (l,ctx)
  | false::l,(lc,x,_)::ctx -> aux (n+1) acc (l,ctx)
  | [],[] -> List.rev acc
  | _ -> assert false
  in aux 0 [] (l,ctx)

let narrow_meta lc s n filter = meta_decl lc s n >>= fun (mctx,mty) ->
  get >>= fun pb ->
  let (filter,mctx') = sanitize_context pb.sigma filter mctx in
  begin match mty with
    | MTyped ty -> begin match sanitize_term pb.sigma filter ty with
        | Some ty' -> return (MTyped ty')
        | None -> zero Not_Applicable
        end
    | MType | MSort -> return mty
    end >>= fun mty' ->
  new_meta mctx' lc s mty' >>= function
    | Meta (lc,s,k,_) -> let mk = mk_Meta lc s k (context_project filter mctx) in
        set_meta n mk
    | _ -> assert false

let meta_same = pair_modify (fun (ctx,lop,rop) -> begin match lop,rop with
  | Meta (lc,s,n,ts), Meta (_,_,n',ts') when (n=n') -> return (lc,s,n,ts,ts',[],[])
  | App (Meta (lc,s,n,ts),a,args), App (Meta (_,_,n',ts'),a',args') when (n=n') -> return (lc,s,n,ts,ts',a::args,a'::args')
  | _,_ -> zero Not_Applicable
  end >>= fun (lc,s,n,ts,ts',args,args') -> 
  let inter = subst_intersection ts ts' in
  narrow_meta lc s n inter >>
  match try Some (List.map2 (fun a b -> ctx,a,b) args args') with | Invalid_argument _ -> None with
    | Some l -> return l
    | None -> zero Not_Applicable)


(** META-INST and helpers *)

let find_unique p l = let rec aux i = function
  | x::l -> if p x then if List.exists p l then None else Some i
            else aux (i+1) l
  | [] -> None
  in aux 0 l


let opt_filter filter l = let rec aux acc filter l = match filter,l with
  | true::filter,(Some x)::l -> aux (x::acc) filter l
  | false::filter,_::l -> aux acc filter l
  | [],[] -> List.rev acc
  | _ -> assert false
  in aux [] filter l

(*
y a metavariable, ts : (ident*term) option list
Indices which are None in ts should be irrelevant for y
*)
let prune lc s y ts = meta_decl lc s y >>= fun (mctx,mty) ->
  let filter = List.map (function | Some _ -> true | None -> false) ts in
  get >>= fun pb ->
  let filter,mctx' = sanitize_context pb.sigma filter mctx in
  begin match mty with
    | MTyped ty -> begin match sanitize_term pb.sigma filter ty with
        | Some ty' -> return (MTyped ty')
        | None -> zero Not_Applicable
        end
    | MType | MSort -> return mty
    end >>= fun mty' ->
  new_meta mctx' lc s mty' >>= function
    | Meta (lc,s,z,_) -> let mz = mk_Meta lc s z (context_project filter mctx) in
        set_meta y mz >>
        return (mk_Meta lc s z (opt_filter filter ts)) (* not sure about this *)
    | _ -> assert false


(*
We try to invert the term, and fail with Not_Applicable if an unknown variable or the forbidden metavariable appear.
If we fail for a term in a metavariable's substitution it should be pruned.
*)
let rec invert_term x vars q = function
  | Kind | Type _ | Const _ as t -> return t
  | DB (_,_,n) as t when (n<q) -> return t
  | DB (lc,x,n) -> begin match find_unique (fun m -> (n-q)=m) vars with
      | Some m -> return (mk_DB lc x (m+q))
      | None -> zero Not_Applicable
      end
  | App (f,a,args) -> fold (fun l t -> invert_term x vars q t >>= fun t' -> return (t'::l)) [] (f::a::args) >>= fun l ->
      begin match List.rev l with
        | f::a::args -> return (mk_App f a args)
        | _ -> assert false
        end
  | Lam (lc,y,Some a,b) -> invert_term x vars q a >>= fun a -> invert_term x vars (q+1) b >>= fun b -> return (mk_Lam lc y (Some a) b)
  | Lam (lc,y,None  ,b) -> invert_term x vars (q+1) b >>= fun b -> return (mk_Lam lc y None b)
  | Pi (lc,y,a,b) -> invert_term x vars q a >>= fun a -> invert_term x vars (q+1) b >>= fun b -> return (mk_Pi lc y a b)
  | Hole _ -> assert false
  | Meta (lc,s,y,ts) as mt -> get >>= fun pb -> begin match S.meta_val pb.sigma mt with
    | Some mt' -> invert_term x vars q mt'
    | None -> if x=y then zero Not_Applicable
      else fold (fun (l,clean) (y,t) -> once (plus
          (invert_term x vars q t >>= fun t -> return ((Some (y,t))::l,clean))
          (function | Not_Applicable -> return (None::l,false) | e -> zero e)
        )) ([],true) ts >>= fun (ts',clean) ->
        if clean then return (mk_Meta lc s y (List.rev_map (function | Some x -> x | None -> assert false) ts'))
        else prune lc s y (List.rev ts')
    end

let rec invert_add_lambdas ctx x argn varl t = if argn = 0 then return t
  else match varl with
  | v::varl -> var_get_type ctx dloc empty v >>= fun ty ->
    invert_term x varl 0 ty >>= fun ty ->
    invert_add_lambdas ctx x (argn-1) varl (mk_Lam dloc empty (Some ty) t)
  | [] -> assert false

let invert ctx x ts_var args_var t =
  let argn,varl = List.fold_left (fun (n,l) v -> (n+1,v::l)) (0,List.rev ts_var) args_var in
  invert_term x varl 0 t >>= fun t' ->
  invert_add_lambdas ctx x argn varl t'

let rec meta_occurs x = function
  | Kind | Type _ | DB _ | Const _ -> false
  | App (f,a,args) -> List.exists (meta_occurs x) (f::a::args)
  | Lam (_,_,Some a,b) | Pi (_,_,a,b) -> meta_occurs x a || meta_occurs x b
  | Lam (_,_,None,b) -> meta_occurs x b
  | Hole _ -> assert false
  | Meta (_,_,y,ts) -> (x=y) || List.exists (fun (_,t) -> meta_occurs x t) ts

(* m is a meta whose type or kind must be the same as that of t *)
let meta_set_ensure_type sg lc s n t =
  meta_decl lc s n >>= fun (mctx,mty) ->
  begin match mty with
    | MTyped ty -> expected_type sg mctx t >>= fun ty' ->
        return [mctx,ty,ty']
    | MType -> begin match t with
        | Kind -> return []
        | Meta (lc',s',x,_) -> meta_decl lc' s' x >>= begin function
            | (_,MType) -> return []
            | (_,MSort) -> set_decl n (mctx,MSort) >>= fun () -> return []
            | (_,MTyped _) -> expected_type sg mctx t >>= fun ty' ->
                new_meta mctx lc s MSort >>= fun ty ->
                set_decl n (mctx,MTyped ty) >>= fun () ->
                return [mctx,ty,ty']
            end
        | _ -> expected_type sg mctx t >>= fun ty' ->
            new_meta mctx lc s MSort >>= fun ty ->
            set_decl n (mctx,MTyped ty) >>= fun () ->
            return [mctx,ty,ty']
        end
    | MSort -> begin match t with
        | Kind -> return []
        | Meta (lc',s',x,_) -> meta_decl lc' s' x >>= begin function
            | (mctx',MType) -> set_decl x (mctx',MSort) >>= fun () -> return []
            | (_,MSort) -> return []
            | (mctx',MTyped _) -> expected_type sg mctx t >>= fun ty' ->
                set_decl n (mctx,MTyped mk_Kind) >>= fun () ->
                return [(mctx,t,mk_Type dloc);(mctx,ty',mk_Kind)]
            end
        | _ -> expected_type sg mctx t >>= fun ty' ->
            set_decl n (mctx,MTyped mk_Kind) >>= fun () ->
            return [(mctx,t,mk_Type dloc);(mctx,ty',mk_Kind)]
        end
    end >>= fun l -> set_meta n t >>= fun () -> return l

let meta_inst sg side = pair_symmetric side (fun ctx active passive -> begin match active with
  | Meta _ -> return (active,[])
  | App (Meta _ as m,a,args) -> return (m,a::args)
  | _ -> zero Not_Applicable
  end >>= fun (m,args) -> match m with
  | Meta (lc,s,n,ts) -> begin match Opt.fold (fun vl -> function | (_,DB (_,_,n)) -> Some (n::vl) | _ -> None) [] ts with
    | Some ts_var -> begin match Opt.fold (fun vl -> function | DB (_,_,n) -> Some (n::vl) | _ -> None) [] args with
      | Some args_var -> return (lc,s,n,ts_var,args_var)
      | None -> zero Not_Applicable
      end
    | None -> zero Not_Applicable
    end >>= fun (lc,s,n,ts_var,args_var) ->
    let passive = Reduction.whnf sg passive in
    invert ctx n ts_var args_var passive >>= fun inst ->
    if meta_occurs n inst then zero Not_Applicable
    else meta_set_ensure_type sg lc s n inst
  | _ -> assert false
  )

(*
split_app and helpers
*)

(*
[split_at n l] returns Some(l1,l2) such that |l1|=n and l=l1++l2 if possible
(TODO: remove duplication with list_slice)
*)
let list_slice n l = let rec aux n acc = fun l -> if n=0 then Some (List.rev acc,l) else match l with
  | x::l -> aux (n-1) (x::acc) l
  | [] -> None
  in aux n [] l

let split_app n = pair_modify (fun (ctx,lop,rop) -> match lop,rop with
  | App (f,a,args), App (f',a',args') -> begin match list_slice n (List.rev (a::args)), list_slice n (List.rev (a'::args')) with
      | Some (a1,a2), Some (a1',a2') ->
          return ((ctx,mk_Appl f (List.rev a2),mk_Appl f' (List.rev a2'))::(List.map2 (fun t1 t2 -> (ctx,t1,t2)) a1 a1'))
      | _,_ -> zero Not_Applicable
      end
  | _,_ -> zero Not_Applicable
  )

