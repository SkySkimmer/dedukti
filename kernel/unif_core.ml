open Basics
open Term
open Monads
open Typing

type pterm = pretyped term
type pcontext = pretyped context

module S = Msubst

let subst_l l n t = Subst.psubst_l (LList.of_list (List.map Lazy.from_val l)) n t
let lsubst_apply ts t = subst_l (List.map snd ts) 0 t

let mk_Appl t = function
  | a::args -> mk_App t a args
  | [] -> t

let mkind_map f = function
  | MTyped ty -> MTyped (f ty)
  | MType | MSort as m -> m

(*
The type of a metavariable is either a term, or the metavariable is Kind. There are 2 cases when a metavariable can be Kind: it is a sort or if it is typed it is typed by a sort.
*)
type mdecl = pcontext*mkind

(*
A guard takes terms of type A to type B in some context.
*)
type gdecl = pcontext*pterm*pterm

type pair = pcontext*pterm*pterm

(*
A unification problem is given by:
- some way to get fresh metavariable names
- type declarations for metavariables
- definitions for metavariables
- type declarations for guards
- unification pairs associated with guards
A guard is pass-through when there are no pairs associated with it.
The problem is solved when it contains no pairs.
*)

(*
NB: if guard #n is active then its pairs appear in the active field and not in the gpairs field.
If it has no pairs it appears nowhere.
*)
type problem =
 { mcpt:int; gcpt:int
 ; mdecls:mdecl IntMap.t; sigma:S.t
 ; gdecls:gdecl IntMap.t
 ; gpairs:(int*pair list) list
 ; active: (int*pair list) option (* Unification pairs we are currently working on.*)
 ; }

let fresh =
 {mcpt=0; gcpt=0
 ; mdecls=IntMap.empty; sigma=S.identity
 ; gdecls=IntMap.empty
 ; gpairs=[]
 ; active=None; }

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

(* monad basic operations end here *)

(** Printers *)

let pp_mkind out = function
  | MTyped ty -> Printf.fprintf out ": %a" pp_term ty
  | MType -> Printf.fprintf out ": *"
  | MSort -> Printf.fprintf out "= *"

let pp_mdecl out n (ctx,mk) = Printf.fprintf out "%a |- %i %a\n" pp_context ctx n pp_mkind mk

let pp_mdecls out m = IntMap.iter (fun i d -> pp_mdecl out i d) m

let pp_pair out (ctx,t1,t2) = Printf.fprintf out "%a |- %a == %a\n" pp_context ctx pp_term t1 pp_term t2

let pp_gdecl out n (ctx,a,b) = Printf.fprintf out "%a |- #%i : %a --> %a\n" pp_context ctx n pp_term a pp_term b

let pp_gdecls out m = IntMap.iter (fun i d -> pp_gdecl out i d) m

let pp_gpair out (n,l) = Printf.fprintf out "#%i when %a\nEnd #%i." n (pp_list "" pp_pair) l n

let pp_gpairs = pp_list "\n" pp_gpair

let pp_active out = function
  | None -> ()
  | Some(n,l) -> Printf.fprintf out "ACTIVE: %a\n" pp_gpair (n,l)

let pp_problem out pb = Printf.fprintf out "{ mcpt=%i; gcpt=%i;\n%a\n%a\n%a\n%a\n%a\n }\n" pb.mcpt pb.gcpt
    pp_mdecls pb.mdecls S.pp pb.sigma
    pp_gdecls pb.gdecls pp_gpairs pb.gpairs
    pp_active pb.active

let pp_state = get >>= fun pb -> effectful (fun () ->
  Printf.printf "%a\n" pp_problem pb
  )

(** Manipulators *)

module Problem = struct
  let get_mdecl pb lc s n = try IntMap.find n pb.mdecls with | Not_found -> raise (TypingError (UnknownMeta (lc,s,n)))
  
  let get_gdecl pb lc n = try IntMap.find n pb.gdecls with | Not_found -> raise (TypingError (UnknownGuard (lc,n)))
  
  let get_gpairs pb lc n = if S.guard_mem pb.sigma n then []
  else match pb.active with
    | Some (m,l) when (n=m) -> l
    | _ -> try let (_,l) = List.find (fun (m,_) -> n=m) pb.gpairs in l with | Not_found -> raise (TypingError (UnknownGuard (lc,n)))
  
  (* Removes the first element matching p from l. *)
  let list_pop p l = let rec aux acc = function
    | x::l -> if p x then x,List.rev_append acc l
              else aux (x::acc) l
    | [] -> raise Not_found
    in aux [] l
  
  let is_active_guard pb n = match pb.active with
    | Some (m,_) when (n=m) -> true
    | _ -> false

  let activate_nonempty pb = match pb.active with
    | Some _ -> Some pb
    | None -> begin match pb.gpairs with
      | x::gpairs' -> Some {pb with gpairs=gpairs'; active=Some x}
      | [] -> None
      end

  let swap_active pb = match pb.gpairs,pb.active with
    | p::l,Some p' -> {pb with gpairs=p'::l; active=Some p}
    | _,_ -> assert false
end

let raise e = effectful (fun () -> raise e)

let apply pb t = S.apply pb.sigma t
let ground pb t = S.to_ground pb.sigma t

(*
We can catch new pairs in
- add_pair
- add_guard
- pair_modify
*)

let rigid_head sg = function
  | Const (lc,m,v) | App (Const (lc,m,v),_,_) -> Signature.is_constant sg lc m v
  | App (Lam _,_,_) | Extra _ | App (Extra _,_,_) -> false
  | _ -> true

let flexible_head sg t = not (rigid_head sg t)

let rec concat_opt = function
  | (Some x)::l -> bind_opt (fun l -> Some (x@l)) (concat_opt l)
  | None::_ -> None
  | [] -> Some []

(* Do trivial operations on a pair
TODO: return ('a,'b) error where 'a = pair list and 'b = pair to indicate where non unifiability is.
May not reduce terms: we call process_pair on possibly non typed pairs, eg a::ctx,b,b' in binder cases.
 *)
let rec process_pair sg sigma (ctx,lop,rop) = let lop = S.head_delta sigma lop and rop = S.head_delta sigma rop in
  if flexible_head sg lop || flexible_head sg rop then Some [(ctx,lop,rop)]
  else match lop,rop with
    | Kind, Kind | Type _, Type _ -> Some []
    | DB (_,_,n), DB (_,_,m) when (n=m) -> Some []
    | Const (_,m,v), Const (_,m',v') when (ident_eq m m' && ident_eq v v') ->
        Some []
    | App (Const (_,m,v),a,args), App (Const (_,m',v'),a',args') when (ident_eq m m' && ident_eq v v') ->
        begin try concat_opt (List.map2 (fun a b -> process_pair sg sigma (ctx,a,b)) (a::args) (a'::args'))
        with | Invalid_argument _ -> None
        end
    | App (DB (_,_,n),a,args), App (DB (_,_,m),a',args') when (n=m) ->
        begin try concat_opt (List.map2 (fun a b -> process_pair sg sigma (ctx,a,b)) (a::args) (a'::args'))
        with | Invalid_argument _ -> None
        end
    | Pi (lc,x,a,b), Pi (_,_,a',b') ->
        bind_opt (fun l -> bind_opt (fun l' -> Some (l@l')) (process_pair sg sigma ((lc,x,a)::ctx,b,b'))) (process_pair sg sigma (ctx,a,a'))
    | Lam (lc,x,Some a,b), Lam (_,_,Some a',b') ->
        bind_opt (fun l -> bind_opt (fun l' -> Some (l@l')) (process_pair sg sigma ((lc,x,a)::ctx,b,b'))) (process_pair sg sigma (ctx,a,a'))
    | Lam _, Lam _ -> failwith "TODO: process_pair on domain free lambdas"
    | _,_ -> None (* both terms are rigid *)

let add_guard sg lc ctx a b t = get >>= fun pb ->
  match process_pair sg pb.sigma (ctx,a,b) with
    | None -> zero Not_Unifiable
    | Some [] -> return t
    | Some tpairs -> let lsubst = List.mapi (fun i (_,x,_) -> x,mk_DB dloc x i) ctx in
        let t' = mk_Guard lc pb.gcpt lsubst t in
        set { pb with gcpt=pb.gcpt+1; gdecls=IntMap.add pb.gcpt (ctx,a,b) pb.gdecls; gpairs=pb.gpairs@[pb.gcpt,tpairs] } >>
        return t'

let new_meta ctx lc s k = get >>= fun pb -> match k with
  | MSort -> let mj = mk_Meta lc s pb.mcpt [] in (* We can skip the context here since we know it's Type or Kind. Note that metas can become MSort without losing their context. *)
      set { pb with mcpt=pb.mcpt+1; mdecls=IntMap.add pb.mcpt ([],MSort) pb.mdecls } >>
      return mj
  | _ -> let substj = List.mapi (fun i (_,x,_) -> x,mk_DB dloc x i) ctx in
      let mj = mk_Meta lc s pb.mcpt substj in
      set { pb with mcpt=pb.mcpt+1; mdecls=IntMap.add pb.mcpt (ctx,k) pb.mdecls } >>
      return mj

let meta_decl lc s n = get >>= fun pb -> return (Problem.get_mdecl pb lc s n)

let guard_decl lc n = get >>= fun pb -> return (Problem.get_gdecl pb lc n)

let set_mdecl n d = modify (fun pb -> { pb with mdecls=IntMap.add n d pb.mdecls })

let set_meta n t = get >>= fun pb ->
  if S.meta_mem pb.sigma n then zero Not_Applicable
  else set { pb with sigma=S.meta_add pb.sigma n t }

let meta_constraint lc s n = meta_decl lc s n >>= function
  | (ctx,MTyped ty) -> return (ctx,ty)
  | (ctx,MType) -> new_meta ctx lc s MSort >>= fun mk ->
      set_mdecl n (ctx,MTyped mk) >>= fun () -> return (ctx,mk)
  | (ctx,MSort) -> set_mdecl n (ctx,MTyped mk_Kind) >>= fun () ->
      set_meta n (mk_Type dloc) >>= fun () -> return (ctx,mk_Kind)


let whnf sg t = get >>= fun pb -> return (S.whnf sg pb.sigma t)

let extra_val ex = get >>= fun pb -> return (S.extra_val pb.sigma ex)

let normalize = modify (fun pb -> let s = S.normalize pb.sigma in
  let md = IntMap.map (fun (ctx,ty) -> (List.map (fun (lc,x,t) -> (lc,x,S.apply s t)) ctx, mkind_map (S.apply s) ty)) pb.mdecls in
  let gd = IntMap.map (fun (ctx,a,b) -> (List.map (fun (lc,x,t) -> (lc,x,S.apply s t)) ctx, S.apply s a, S.apply s b)) pb.gdecls in
  let gp = List.map (fun (n,l) -> n,(List.map (fun (ctx,t1,t2) -> List.map (fun (lc,x,t) -> (lc,x,S.apply s t)) ctx, S.apply s t1, S.apply s t2) l)) pb.gpairs in
  let ap = match pb.active with
    | Some (n,l) -> Some (n,List.map (fun (ctx,t1,t2) -> (List.map (fun (lc,x,t) -> (lc,x,S.apply s t)) ctx, S.apply s t1, S.apply s t2)) l)
    | None -> None
    in
  {mcpt=pb.mcpt; gcpt=pb.gcpt; mdecls=md; sigma=s; gdecls=gd; gpairs=gp; active=ap; })

(** Retyping *)

let rec add_to_list2 l1 l2 lst =
  match l1, l2 with
    | [], [] -> Some lst
    | s1::l1, s2::l2 -> add_to_list2 l1 l2 ((s1,s2)::lst)
    | _,_ -> None

let rec are_convertible_lst sg : (pterm*pterm) list -> bool t = function
  | [] -> return true
  | (t1,t2)::lst ->
    begin
      ( if term_eq t1 t2 then return (Some lst)
        else
          whnf sg t1 >>= fun t1 -> whnf sg t2 >>= fun t2 -> match t1,t2 with
          | Kind, Kind | Type _, Type _ -> return (Some lst)
          | Const (_,m,v), Const (_,m',v') when ( ident_eq v v' && ident_eq m m' ) -> return (Some lst)
          | DB (_,_,n), DB (_,_,n') when ( n==n' ) -> return (Some lst)
          | App (f,a,args), App (f',a',args') ->
            return (add_to_list2 args args' ((f,f')::(a,a')::lst))
          | Lam (_,_,_,b), Lam (_,_,_,b') -> return (Some ((b,b')::lst))
          | Pi (_,_,a,b), Pi (_,_,a',b') -> return (Some ((a,a')::(b,b')::lst))
          | Extra (_,Pretyped,Meta(_,n,ts)), Extra (_,Pretyped,Meta(_,n',ts')) when ( n==n' ) ->
              return (add_to_list2 (List.map snd ts) (List.map snd ts') lst)
          | t1, t2 -> return None
      ) >>= function
      | None -> return false
      | Some lst2 -> are_convertible_lst sg lst2
    end

let are_convertible sg t1 t2 = are_convertible_lst sg [(t1,t2)]

module Retyping = Elaboration(struct
  type 'a tmp = 'a t
  type 'a t = 'a tmp
  
  let return = return
  let (>>=) = (>>=)
  let (>>) = (>>)

  type pextra = pretyped
  type extra = pretyped
  type ctx = pcontext
  type jdg = pcontext*pterm*pterm

  let  get_type ctx l x n =
    try
      let (_,_,ty) = List.nth ctx n in Subst.shift (n+1) ty
    with Failure _ ->
      Pervasives.raise (TypingError (VariableNotFound (l,x,n,ctx)))

  let judge ctx te ty = (ctx,te,ty)
  let jdg_ctx (ctx,_,_) = ctx
  let jdg_te (_,te,_) = te
  let jdg_ty (_,_,ty) = ty

  let to_context ctx = ctx

  let fail = zero

  let fold = fold

  let guard sg (ctx,te,ty) (_,ty_exp,_) = are_convertible sg ty ty_exp >>= function
    | true -> return (ctx,te,ty_exp)
    | false -> add_guard sg (get_loc te) ctx ty ty_exp te >>= fun te' ->
        return (ctx,te',ty_exp)

  let guard_sort sg jdg = let (ctx,te,ty) = jdg in whnf sg ty >>= function
    | Kind | Type _ -> return jdg
    | Extra (lc,Pretyped,Meta(s,n,_)) -> meta_decl lc s n >>= fun (mctx,mty) -> begin match mty with
        | MSort -> return jdg
        | MType -> set_mdecl n (mctx,MSort) >> return jdg
        | MTyped mty -> let lc = get_loc te in new_meta ctx lc (hstring "Sort") MSort >>= fun ms ->
            add_guard sg lc ctx ty ms te >>= fun te' ->
            return (ctx,te',ms)
        end
    | Extra (lc,Pretyped,_) -> let lc = get_loc te in new_meta ctx lc (hstring "Sort") MSort >>= fun ms ->
        add_guard sg lc ctx ty ms te >>= fun te' ->
        return (ctx,te',ms)
    | _ -> zero (SortExpected (te, ctx, ty))

  let guard_app sg jdg_f jdg_u = let (ctx,te_f,ty_f) = jdg_f in
    whnf sg ty_f >>= function
      | Pi (_,_,a,b) -> guard sg jdg_u (ctx,a,mk_Type dloc (* (x) *)) >>= fun (_,te_u,_) ->
          return (ctx,mk_App te_f te_u [],Subst.subst b te_u)
      | Extra  _ | App (Extra _,_,_) -> let (_,te_u,ty_u) = jdg_u in
          let ctx2 = (dloc,empty,ty_u)::ctx in
          new_meta ctx2 dloc empty MSort >>= fun ms ->
          new_meta ctx2 dloc empty (MTyped ms) >>= fun mk ->
          guard sg jdg_f (ctx,mk_Pi dloc empty ty_u mk,mk_Type dloc (* (x) *)) >>= fun (_,te_f,_) ->
          return (ctx,mk_App te_f te_u [],Subst.subst mk te_u)
      | _ -> zero (ProductExpected (te_f,ctx,ty_f))

  let guard_annot sg jdg = if !coc then guard_sort sg jdg else let (ctx,_,_) = jdg in guard sg jdg (ctx,mk_Type dloc,mk_Kind)
  let new_meta_annot ctx lc s = if !coc then new_meta ctx lc s MSort else return (mk_Type lc)

  let ctx_add sg l x jdg = let ctx0 = jdg_ctx jdg in
    guard_annot sg jdg >>= fun jdg ->
    return (jdg,(l,x,jdg_te jdg)::ctx0)

  let unsafe_add ctx l x t = (l,x,t)::ctx

  let reject_kind sg (ctx,te,ty) = whnf sg ty >>= function
    | Kind -> zero (InexpectedKind (te, ctx))
    | Extra (lc,Pretyped,Meta(s,n,_)) -> meta_constraint lc s n >>= fun _ -> return ()
    | _ -> return ()

  let whnf = whnf

  let check_subst check sg ctx ts mctx =
    fold (fun ts' ((x,t),(_,_,ty)) -> check sg t (ctx,lsubst_apply ts' ty,mk_Type dloc (* (x) *)) >>= fun (_,t',_) ->
        return ((x,t')::ts')) [] (List.rev_map2 (fun x y -> x,y) ts mctx)

  let infer_extra infer check sg ctx lc Pretyped = function
    | Meta (s,n,ts) -> meta_constraint lc s n >>= fun (mctx,mty) ->
        check_subst check sg ctx ts mctx >>= fun ts' ->
        return (ctx,mk_Meta lc s n ts',lsubst_apply ts' mty)
    | Guard (n,ts,t) -> guard_decl lc n >>= fun (gctx,gty_in,gty_out) ->
        check_subst check sg ctx ts gctx >>= fun ts' ->
        check sg t (ctx,lsubst_apply ts' gty_in,mk_Type dloc (* (x) *)) >>= fun (ctx,t',_) ->
        return (ctx,mk_Guard lc n ts' t',lsubst_apply ts' gty_out)
end)

let var_get_type ctx lc x n = try let (_,_,ty) = List.nth ctx n in return (Subst.shift (n+1) ty)
  with | Failure _ -> raise (TypingError (VariableNotFound (lc,x,n,ctx)))

(** Pair interface *)

(* returns None if there are no (unsolved) disagreement pairs *)
let inspect = get >>= fun pb -> match Problem.activate_nonempty pb with
  | Some pb' -> begin match pb'.active with
      | Some (_,x::_) -> set pb' >> return (Some x)
      | _ -> assert false
      end
  | None -> return None

(*
The first pair is used for f's argument.
NB: UNDEFINED BEHAVIOR if f modifies the active field.
*)
let pair_modify f = get >>= fun pb -> match pb.active with
  | Some (x,p::rem) -> f p >>= fun l -> modify (fun pb -> { pb with active=Some (x,List.append l rem) }) >>
      get >>= fun pb -> begin match pb.active with
        | Some (n,[]) -> set {pb with sigma=S.guard_add pb.sigma n; active=None} (* #n has no pairs left. *)
        | _ -> return ()
        end
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

let pair_convertible sg = pair_modify (fun (ctx,lop,rop) ->
  are_convertible sg lop rop >>= function
  | true -> return []
  | false -> zero Not_Applicable)

(* Tries to unfold the meta at the head of the left (resp right) term *)
let meta_delta side = pair_modify_side side (fun t -> get >>= fun pb -> match t with
  | Extra (_,Pretyped,ex) -> begin match S.extra_val pb.sigma ex with
      | Some m' -> return m'
      | None -> zero Not_Applicable
      end
  | App (Extra (_,Pretyped,ex),a,args) -> begin match S.extra_val pb.sigma ex with
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

let decompose = pair_modify (fun (ctx,t1,t2) -> match t1,t2 with
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
  | Extra (_,Pretyped,Meta(_,n,ts)), Extra (_,Pretyped,Meta(_,n',ts')) when ( n==n' ) ->
      return (List.map2 (fun (_,t1) (_,t2) -> (ctx,t1,t2)) ts ts')
  | Extra (_,Pretyped,Guard(n,ts,t)), Extra (_,Pretyped,Guard(n',ts',t')) when ( n==n' ) ->
      return ((ctx,t,t')::(List.map2 (fun (_,t1) (_,t2) -> (ctx,t1,t2)) ts ts'))
  | App _, _ | _, App _ | Extra _, _ | _, Extra _ -> zero Not_Applicable
  | Const _, _ | _, Const _ -> zero Not_Applicable
  | _, _ -> zero Not_Unifiable)

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
  | Extra (lc,Pretyped,ex) -> begin match S.extra_val sigma ex with
      | Some m' -> sanitize_term sigma l m'
      | None -> begin match ex with
          | Meta (s,n,ts) -> Opt.(Opt.fold (fun ts (x,t) -> map_opt (fun t -> (x,t)::ts) (sanitize_term sigma l t))
                                           [] (List.rev ts) >>= fun ts ->
                             Some (mk_Meta lc s n ts))
          | Guard (n,ts,t) -> Opt.(Opt.fold (fun ts' (x,t) -> map_opt (fun t' -> (x,t')::ts') (sanitize_term sigma l t))
                                            [] (List.rev ts) >>= fun ts' ->
                              sanitize_term sigma l t >>= fun t' ->
                              Some (mk_Guard lc n ts' t'))
          end
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
    | Extra (lc,Pretyped,Meta(s,k,_)) -> let mk = mk_Meta lc s k (context_project filter mctx) in
        set_meta n mk
    | _ -> assert false

(** REFINE and helpers *)

(* TODO: instead of (x=y) check if x appears in y's definition *)
let rec meta_occurs x = function
  | Kind | Type _ | DB _ | Const _ -> false
  | App (f,a,args) -> List.exists (meta_occurs x) (f::a::args)
  | Lam (_,_,Some a,b) | Pi (_,_,a,b) -> meta_occurs x a || meta_occurs x b
  | Lam (_,_,None,b) -> meta_occurs x b
  | Extra (_,Pretyped,Meta(_,y,ts)) -> (x=y) || List.exists (fun (_,t) -> meta_occurs x t) ts
  | Extra (_,Pretyped,Guard(_,ts,t)) -> List.exists (fun (_,t) -> meta_occurs x t) ts || meta_occurs x t


let refine_typed sg lc n ty_exp (ctx,t,ty) = are_convertible sg ty ty_exp >>= function
  | true -> set_meta n t
  | false -> add_guard sg lc ctx ty ty_exp t >>= fun t' ->
      set_meta n t' >>
      (* If ty and ty_exp are not convertible modulo sg and the problem, then non trivial unification has to be done, so there is a new guard *)
      modify Problem.swap_active

let refine sg lc s n t = if meta_occurs n t
  then zero Not_Applicable
  else meta_decl lc s n >>= fun (ctx,mty) -> begin match mty with
      | MTyped ty -> Retyping.infer sg ctx t >>= fun jdg ->
          refine_typed sg lc n ty jdg
      | MType -> begin match t with
        | Kind -> set_mdecl n (ctx,MSort) >> set_meta n t
        | Type _ -> set_mdecl n (ctx,MTyped mk_Kind) >> set_meta n t
        | Extra (lc',Pretyped,Meta(s',x,_)) -> meta_decl lc' s' x >>= begin function (* TODO: check_subst *)
            | (_,MType) -> set_meta n t
            | (_,MSort) -> set_mdecl n (ctx,MSort) >> set_meta n t
            | (_,MTyped _) -> new_meta ctx lc s MSort >>= fun ms ->
                set_mdecl n (ctx,MTyped ms) >>
                Retyping.infer sg ctx t >>= fun jdg ->
                refine_typed sg lc n ms jdg
            end
        | _ -> new_meta ctx lc s MSort >>= fun ms ->
            set_mdecl n (ctx,MTyped ms) >>
            Retyping.infer sg ctx t >>= fun jdg ->
            refine_typed sg lc n ms jdg
        end
      | MSort -> begin match t with
          | Kind -> set_meta n t
          | Type _ -> set_mdecl n (ctx,MTyped mk_Kind) >> set_meta n t
          | Extra (lc',Pretyped,Meta(s',x,_)) -> meta_decl lc' s' x >>= begin function (* TODO: check_subst *)
              | (mctx',MType) -> set_mdecl x (mctx',MSort) >> set_meta n t
              | (_,MSort) -> set_meta n t
              | (_,MTyped _) -> Retyping.infer sg ctx t >>= fun (_,t',ty) ->
                  are_convertible sg t' (mk_Type dloc) >>= begin function
                    | true -> set_mdecl n (ctx,MTyped mk_Kind) >> set_meta n (mk_Type lc)
                    | false -> zero (SortExpected (t,ctx,t))
                    end
              end
          | _ -> Retyping.infer sg ctx t >>= fun (_,t',ty) -> (* TODO: improve this *)
              are_convertible sg t' (mk_Type dloc) >>= begin function
                | true -> set_mdecl n (ctx,MTyped mk_Kind) >> set_meta n (mk_Type lc)
                | false -> zero (SortExpected (t,ctx,t))
                end
          end
      end

(*
split_app and helpers
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

