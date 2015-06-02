open Basics
open Term
open Rule
open Monads
open Unif_core
open Typing

module SS = Subst.S

module RMeta : sig
  include Meta with type pextra = untyped and type extra = pretyped
                and type ctx = pretyped context and type jdg = (pretyped context*pretyped term*pretyped term)
  
  type problem
  
  val extract : Signature.t -> 'a t -> 'a*problem
  
  val ground : problem -> pretyped term -> typed term
end = struct
  include Unif_core
  include Unifier

  type pextra = untyped
  type extra = pretyped
  type ctx = pretyped context
  type jdg = pretyped context*pretyped term*pretyped term
  
  let get_type ctx l x n =
    try
      let (_,_,ty) = List.nth ctx n in Subst.shift (n+1) ty
    with Failure _ ->
      raise (TypingError (VariableNotFound (l,x,n,ctx)))
  
  let judge ctx te ty = (ctx,te,ty)
  let jdg_ctx (ctx,_,_) = ctx
  let jdg_te (_,te,_) = te
  let jdg_ty (_,_,ty) = ty

  let to_context ctx = ctx

  let fail = zero

  let extract sg m = run m

  let unify_annot sg ctx t = if !coc then unify_sort sg ctx t else unify sg ctx t (mk_Type dloc)
  let new_meta_annot ctx lc s = if !coc then new_meta ctx lc s MSort else return (mk_Type lc)

  let ctx_add sg l x jdg = let ctx0 = jdg_ctx jdg in
    unify_annot sg ctx0 (jdg_ty jdg) >>= fun b ->
    if b then return ((l,x,jdg_te jdg)::ctx0)
    else fail (ConvertibilityError (jdg_te jdg, ctx0, mk_Type dloc, jdg_ty jdg))

  let unsafe_add ctx l x t = (l,x,t)::ctx

  let pi sg ctx t = whnf sg t >>= function
    | Pi (l,x,a,b) -> return (Some (l,x,a,b))
    | _ -> plus (let empty = Basics.empty in
        new_meta_annot ctx dloc empty >>= fun ms ->
        new_meta ctx dloc empty (MTyped ms) >>= fun mt ->
        let ctx2 = (dloc,empty,mt)::ctx in
        new_meta ctx2 dloc empty MSort >>= fun ml ->
        new_meta ctx2 dloc empty (MTyped ml) >>= fun mk ->
        let pi = mk_Pi dloc empty mt mk in
        unify sg ctx t pi >>= begin function
        | true -> return (Some (dloc,empty,mt,mk))
        | false -> zero Not_Unifiable
        end) (* This backtracking lets us forget newly introduced metavariables. *)
        (function | Not_Applicable | Not_Unifiable -> return None | e -> zero e)

  let infer_extra infer check sg ctx lc kind ex = match kind with
    | Untyped -> let {hole=s} = ex in
        new_meta ctx lc s MType >>= fun mk ->
        new_meta ctx lc s (MTyped mk) >>= fun mj ->
        return (judge ctx mj mk)
end

module Refiner = Elaboration(RMeta)
open RMeta

let inference sg (te:untyped term) : judgment =
  let (_,te,_),pb = extract sg (Refiner.infer sg [] te) in
    Typing.inference sg (ground pb te)

let checking sg (te:untyped term) (ty_exp:untyped term) : judgment =
  let (_,te,ty),pb = extract sg (Refiner.infer sg [] ty_exp >>= fun jdg_ty -> Refiner.check sg te jdg_ty) in
  let ty_r = ground pb ty and te_r = ground pb te in
    Typing.checking sg te_r ty_r

let check_rule sg (ctx,le,ri:rule) : unit =
(*
  let ((ctx,ri),pb) = extract sg (
    fold (fun ctx (l,id,ty) -> Refiner.infer sg ctx ty >>= fun jty -> ctx_add sg l id jty) [] (List.rev ctx) >>=
    fun ctx -> Refiner.infer_pattern sg ctx 0 SS.identity le >>=
    fun (ty_inf,sigma) ->
    let ri2 =
      if SS.is_identity sigma then ri else ( debug "%a" SS.pp sigma; (SS.apply sigma ri 0) ) in
    Refiner.infer sg ctx ri2 >>=
    fun (_,_,ty) -> unify sg ctx ty_inf ty >>=
    function
      | true -> return (ctx,ri)
      | false -> fail (ConvertibilityError (ri,ctx,ty_inf,ty))
    ) in
  let ctx = List.map (fun (l,id,ty) -> l,id,apply pb ty) ctx in
  let ri = apply pb ri in
  *)
    Typing.check_rule sg (ctx,le,ri)

