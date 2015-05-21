open Basics
open Term
open Monads

module S = Msubst

let subst_l l n t = Subst.psubst_l (LList.of_list (List.map Lazy.from_val l)) n t

let mk_Appl t = function
  | a::args -> mk_App t a args
  | [] -> t

type typing_error =
  | KindIsNotTypable
  | ConvertibilityError of term*context*term*term
  | VariableNotFound of loc*ident*int*context
  | SortExpected of term*context*term
  | ProductExpected of term*context*term
  | InexpectedKind of term*context
  | DomainFreeLambda of loc
  | MetaInKernel of loc*ident
  | InferSortMeta of loc*ident
  | UnknownMeta of loc*ident*int
  | ConvRule_Bad of term*term
  | DecomposeDomainFreeLambdas
  | CannotSolveDeferred
  | Not_Unifiable
  | Not_Applicable

exception TypingError of typing_error

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

let apply pb t = S.apply pb.sigma t

let add_pair sg p = modify (fun pb -> {pb with pairs=p::pb.pairs})

let new_meta ctx lc s k = get >>= fun pb ->
  let substj = List.mapi (fun i (_,x,_) -> x,mk_DB dloc x i) ctx in
  let mj = mk_Meta lc s pb.cpt substj in
  set { pb with cpt=pb.cpt+1; decls=IntMap.add pb.cpt (ctx,k) pb.decls } >>= fun () ->
  return mj

let get_decl decls n = try Some (IntMap.find n decls) with | Not_found -> None

let set_decl n d = modify (fun pb -> { pb with decls=IntMap.add n d pb.decls })

let set_meta n t = modify (fun pb -> { pb with sigma=S.add pb.sigma n t })

let meta_constraint = function
  | Meta (lc,s,n,_) -> get >>= fun pb -> begin match get_decl pb.decls n with
      | Some (ctx,MTyped ty) -> return (ctx,ty)
      | Some (ctx,MType) -> new_meta ctx lc s MSort >>= fun mk ->
          set_decl n (ctx,MTyped mk) >>= fun () -> return (ctx,mk)
      | Some (ctx,MSort) -> set_decl n (ctx,MTyped mk_Kind) >>= fun () ->
          set_meta n (mk_Type dloc) >>= fun () -> return (ctx,mk_Kind)
      | None -> raise (TypingError (UnknownMeta (lc,s,n)))
      end
  | _ -> assert false


let whnf sg t = get >>= fun pb -> return (S.whnf sg pb.sigma t)

(*
This is only used in the pseudo-unification step of pattern checking.
TODO(future work): If possible we would like to use unification instead.
*)
let simpl t = get >>= fun pb -> return (apply pb t)

let pp_mkind out = function
  | MTyped ty -> Printf.fprintf out ": %a" pp_term ty
  | MType -> Printf.fprintf out ": *"
  | MSort -> Printf.fprintf out "= *"

let pp_mdecl out n (ctx,mk) = Printf.fprintf out "%a |- %i %a\n" pp_context ctx n pp_mkind mk

let pp_decls out m = IntMap.iter (fun i d -> pp_mdecl out i d) m

let pp_pair out (ctx,t1,t2) = Printf.fprintf out "%a |- %a == %a\n" pp_context ctx pp_term t1 pp_term t2

let pp_problem out pb = Printf.fprintf out "{ cpt=%i;\n%a\n%a\n%a\n }" pb.cpt pp_decls pb.decls S.pp pb.sigma  (pp_list "" pp_pair) pb.pairs

let pp_state = get >>= fun pb -> effectful (fun () ->
  Printf.printf "%a\n" pp_problem pb
  )


let var_get_type ctx lc x n = try let (_,_,ty) = List.nth ctx n in return (Subst.shift (n+1) ty)
  with | Failure _ -> raise (TypingError (VariableNotFound (lc,x,n,ctx)))

let rec expected_type sg ctx = function
  | Kind -> raise (TypingError KindIsNotTypable)
  | Type _ -> return mk_Kind
  | DB (lc,x,n) -> var_get_type ctx lc x n
  | Const (l,md,id) -> return (Signature.get_type sg l md id)
  | App (f,_,_) -> expected_type sg ctx f
  | Lam (lc,x,Some a,b) -> expected_type sg ((lc,x,a)::ctx) b >>= fun ty ->
      return (mk_Pi lc x a ty)
  | Lam (lc,_,None,_) -> raise (TypingError (DomainFreeLambda lc))
  | Pi (lc,x,a,b) -> expected_type sg ((lc,x,a)::ctx) b
  | Hole _ -> assert false
  | Meta (lc,s,x,ts) as mv -> meta_constraint mv >>= fun (_,ty0) ->
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

let pair_modify_side side f = pair_modify (fun (ctx,lop,rop) -> match side with
  | LEFT -> f lop >>= fun lop -> return [ctx,lop,rop]
  | RIGHT -> f rop >>= fun rop -> return [ctx,lop,rop])

let pair_symmetric side f = pair_modify (fun (ctx,lop,rop) -> match side with
  | LEFT -> f ctx lop rop
  | RIGHT -> f ctx rop lop)


(* Tries to unfold the meta at the head of the left (resp right) term *)
let meta_delta side = let delta t = get >>= fun pb -> begin match t with
  | Meta _ as m -> begin match S.meta_val pb.sigma m with
      | Some m' -> return m'
      | None -> zero Not_Applicable
      end
  | App (Meta _ as m,a,args) -> begin match S.meta_val pb.sigma m with
      | Some m' -> return (mk_App m' a args)
      | None -> zero Not_Applicable
      end
  | _ -> zero Not_Applicable
  end in pair_modify_side side delta

let step_reduce sg side = let step t = match Reduction.one_step sg t with
  | Some t' -> return t'
  | None -> zero Not_Applicable
  in pair_modify_side side step

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
let rec sanitize_term l = function
  | Kind | Type _ | Const _ as t -> Some t
  | DB (lc,x,n) -> map_opt (fun n -> mk_DB lc x n) (sanitize_index l n)
  | App (f,a,args) -> Opt.(Opt.fold (fun args t -> map_opt (fun t -> t::args) (sanitize_term l t))
                                    [] (List.rev_append args [a;f]) >>= function
      | f::a::args -> Some (mk_App f a args)
      | _ -> assert false)
  | Lam (lc,x,Some a,b) -> Opt.(sanitize_term l a >>= fun a -> Opt.(sanitize_term (true::l) b >>= fun b -> Some (mk_Lam lc x (Some a) b)))
  | Lam (lc,x,None,b) -> Opt.(sanitize_term (true::l) b >>= fun b -> Some (mk_Lam lc x None b))
  | Pi (lc,x,a,b) -> Opt.(sanitize_term l a >>= fun a -> Opt.(sanitize_term (true::l) b >>= fun b -> Some (mk_Pi lc x a b)))
  | Hole _ -> assert false
  | Meta (lc,s,n,ts) -> Opt.(Opt.fold (fun ts (x,t) -> map_opt (fun t -> (x,t)::ts) (sanitize_term l t))
                                 [] (List.rev ts) >>= fun ts ->
      Some (mk_Meta lc s n ts))

let rec sanitize_context l ctx = match l,ctx with
  | b::l, (lc,x,ty)::ctx -> let (l,ctx) = sanitize_context l ctx in
      if b then begin match sanitize_term l ty with
        | Some ty -> true::l,(lc,x,ty)::ctx
        | None -> false::l,ctx
        end
      else false::l,ctx
  | [],[] -> [],[]
  | _,_ -> assert false

let subst_intersection ts ts' = List.map2 (fun (_,t1) (_,t2) -> term_eq t1 t2) ts ts'

let context_project l ctx = let rec aux n acc = function
  | true::l,(lc,x,_)::ctx -> aux (n+1) ((mk_DB lc x n)::acc) (l,ctx)
  | false::l,(lc,x,_)::ctx -> aux n acc (l,ctx)
  | [],[] -> List.rev acc
  | _ -> assert false
  in aux 0 [] (l,ctx)

let meta_same = pair_modify (fun (ctx,lop,rop) -> begin match lop,rop with
  | Meta (lc,s,n,ts), Meta (_,_,n',ts') when (n=n') -> return (lc,s,n,ts,ts',[],[])
  | App (Meta (lc,s,n,ts),a,args), App (Meta (_,_,n',ts'),a',args') when (n=n') -> return (lc,s,n,ts,ts',a::args,a'::args')
  | _,_ -> zero Not_Applicable
  end >>= fun (lc,s,n,ts,ts',args,args') -> 
  get >>= fun pb -> match get_decl pb.decls n with
    | Some (mctx0,m) -> let inter = subst_intersection ts ts' in
        let (inter,mctx) = sanitize_context inter mctx0 in
        let m = match m with
          | MTyped ty -> map_opt (fun ty -> MTyped ty) (sanitize_term inter ty)
          | MType | MSort -> Some m in
        begin match m with
          | Some m -> new_meta mctx lc s m >>= fun mj ->
              let mj = subst_l (context_project inter mctx0) 0 mj in
              set_meta n mj >>= fun () ->
              begin match try Some (List.map2 (fun a b -> ctx,a,b) args args') with | Invalid_argument _ -> None with
                | Some l -> return l
                | None -> zero Not_Applicable
                end
          | None -> zero Not_Applicable
          end
    | None -> raise (TypingError (UnknownMeta (lc,s,n))))

(* returns l1,l2 such that l1++l2=l and |l1| = n *)
let list_slice n l = let rec aux acc n l = if n=0
  then (List.rev acc),l
  else match l with
    | x::l -> aux (x::acc) (n-1) l
    | [] -> assert false
  in aux [] n l

let meta_fo side = pair_symmetric side (fun ctx active passive -> match active,passive with
  | App (Meta _ as m,a,args), App (f,a',args') -> let alen = List.length args in let alen' = List.length args' in
      if alen > alen' then zero Not_Applicable
      else let (al1,al2) = list_slice (alen'-alen) (a'::args') in
        return ((ctx,m,mk_Appl f al1)::(List.map2 (fun t1 t2 -> (ctx,t1,t2)) (a::args) al2))
  | _ -> zero Not_Applicable)

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
let prune lc s y ts = get >>= fun pb -> match get_decl pb.decls y with
  | None -> raise (TypingError (UnknownMeta (lc,s,y)))
  | Some (mctx,mty) -> let filter = List.map (function | Some _ -> true | None -> false) ts in
      let filter,mctx' = sanitize_context filter mctx in
      begin match mty with
        | MTyped ty -> begin match sanitize_term filter ty with
            | Some ty' -> return (MTyped ty')
            | None -> zero Not_Applicable
            end
        | MType | MSort -> return mty
        end >>= fun mty' ->
      new_meta mctx' lc s mty' >>= fun mz ->
      let mz = subst_l (context_project filter mctx) 0 mz in
      set_meta y mz >>= fun () ->
      begin match mz with (* not sure about this *)
        | Meta (lc,s,z,_) -> return (mk_Meta lc s z (opt_filter filter ts))
        | _ -> assert false
        end

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
        else prune lc s y ts'
    end

let rec invert_add_lambdas ctx x argn varl t = if argn = 0 then return t
  else match varl with
  | v::varl -> var_get_type ctx dloc empty v >>= fun ty ->
    invert_term x varl 0 ty >>= fun ty ->
    invert_add_lambdas ctx x (argn-1) varl (mk_Lam dloc empty (Some ty) t)
  | [] -> assert false

let invert ctx x ts_var args_var t =
  let argn,varl = List.fold_left (fun (n,l) v -> (n+1,v::l)) (0,ts_var) args_var in
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
let meta_ensure_type sg m t = match m with
  | Meta (lc,s,n,_) -> get >>= fun pb -> begin match get_decl pb.decls n with
      | Some (mctx,mty) -> begin match mty with
          | MTyped ty -> expected_type sg mctx t >>= fun ty' ->
              return [mctx,ty,ty']
          | MType -> begin match t with
              | Kind -> return []
              | Meta (lc',s',x,_) -> begin match get_decl pb.decls x with
                  | Some (_,MType) -> return []
                  | Some (_,MSort) -> set_decl n (mctx,MSort) >>= fun () -> return []
                  | Some (_,MTyped _) -> expected_type sg mctx t >>= fun ty' ->
                      new_meta mctx lc s MSort >>= fun ty ->
                      set_decl n (mctx,MTyped ty) >>= fun () ->
                      return [mctx,ty,ty']
                  | None -> raise (TypingError (UnknownMeta (lc',s',x)))
                  end
              | _ -> expected_type sg mctx t >>= fun ty' ->
                  new_meta mctx lc s MSort >>= fun ty ->
                  set_decl n (mctx,MTyped ty) >>= fun () ->
                  return [mctx,ty,ty']
              end
          | MSort -> begin match t with
              | Kind -> return []
              | Meta (lc',s',x,_) -> begin match get_decl pb.decls x with
                  | Some (mctx',MType) -> set_decl x (mctx',MSort) >>= fun () -> return []
                  | Some (_,MSort) -> return []
                  | Some (mctx',MTyped _) -> expected_type sg mctx t >>= fun ty' ->
                      set_decl n (mctx,MTyped mk_Kind) >>= fun () ->
                      return [(mctx,t,mk_Type dloc);(mctx,ty',mk_Kind)]
                  | None -> raise (TypingError (UnknownMeta (lc',s',x)))
                  end
              | _ -> expected_type sg mctx t >>= fun ty' ->
                  set_decl n (mctx,MTyped mk_Kind) >>= fun () ->
                  return [(mctx,t,mk_Type dloc);(mctx,ty',mk_Kind)]
              end
          end
      | None -> raise (TypingError (UnknownMeta (lc,s,n)))
      end
  | _ -> assert false

let meta_inst sg side = pair_symmetric side (fun ctx active passive -> begin match active with
  | Meta _ -> return (active,[])
  | App (Meta _ as m,a,args) -> return (m,a::args)
  | _ -> zero Not_Applicable
  end >>= fun (m,args) -> match m with
  | Meta (lc,s,n,ts) -> begin match Opt.fold (fun vl -> function | (_,DB (_,_,n)) -> Some (n::vl) | _ -> None) [] ts with
    | Some ts_var -> begin match Opt.fold (fun vl -> function | DB (_,_,n) -> Some (n::vl) | _ -> None) [] args with
      | Some args_var -> return (n,ts_var,args_var)
      | None -> zero Not_Applicable
      end
    | None -> zero Not_Applicable
    end >>= fun (n,ts_var,args_var) ->
    let passive = Reduction.whnf sg passive in
    invert ctx n ts_var args_var passive >>= fun inst ->
    if meta_occurs n inst then zero Not_Applicable
    else meta_ensure_type sg m inst
  | _ -> assert false
  )

