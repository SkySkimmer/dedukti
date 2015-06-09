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

  let guard_annot sg jdg = if !coc then guard_sort sg jdg else let (ctx,_,_) = jdg in guard sg jdg (ctx,mk_Type dloc,mk_Kind)
  let new_meta_annot ctx lc s = if !coc then new_meta ctx lc s MSort else return (mk_Type lc)

  let ctx_add sg l x jdg = let ctx0 = jdg_ctx jdg in
    guard_annot sg jdg >>= fun jdg ->
    return (jdg,(l,x,jdg_te jdg)::ctx0)

  let unsafe_add ctx l x t = (l,x,t)::ctx

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
      | _ -> fail (ProductExpected (te_f,ctx,ty_f))

  let infer_extra infer check sg ctx lc Untyped = function
    | U s -> new_meta ctx lc s MType >>= fun mk ->
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

