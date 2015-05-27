open Term
open Rule
open Basics

(** Type checking/inference *)

val coc : bool ref

type 'a judgment0 = private { ctx:'a; te:term; ty: term; }

module Context :
sig
  type t
  val empty : t
  val add : loc -> ident -> t judgment0 -> t
  val get_type : t -> loc -> ident -> int -> term
  val is_empty : t -> bool
end

type judgment = Context.t judgment0

(** {2 Meta aware operations} *)

module type Meta = sig
  include Monads.Monad
  
  val fail : Unif_core.typing_error -> 'a t

  val fold : ('a -> 'b -> 'a t) -> 'a -> 'b list -> 'a t
  
  val add : Signature.t -> loc -> ident -> judgment -> Context.t t
  
  val pi : Signature.t -> Context.t -> term -> (loc*ident*term*term) option t
  
  val unify : Signature.t -> context -> term -> term -> bool t
  val unify_sort : Signature.t -> context -> term -> bool t

  val new_meta : context -> loc -> ident -> mkind -> term t
  
  val meta_constraint : loc -> ident -> int -> (context * term) t
  
  val simpl : term -> term t
end

module KMeta : Meta with type 'a t = 'a

module RMeta : Meta

(** {2 Type Inference/Checking} *)

module type RefinerS = sig
  type 'a t

  val infer       : Signature.t -> Context.t -> term -> judgment t
  (** [infer sg ctx te] builds a typing judgment for the term [te] in the signature [sg] and context [ctx] *)

  val check       : Signature.t -> term -> judgment -> judgment t
  (** [check sg te ty] builds a typing judgment for the term [te] of type [ty.te]
  * in the signature [sg] and context [ty.ctx]. *)
  
  val infer_pattern : Signature.t -> Context.t -> int -> Subst.S.t -> pattern -> (term*Subst.S.t) t
end

module Refiner (M:Meta) : RefinerS with type 'a t = 'a M.t

module KRefine : RefinerS with type 'a t = 'a

module MetaRefine : RefinerS with type 'a t = 'a RMeta.t

val checking    : Signature.t -> term -> term -> judgment
(** [checking sg te ty] checks, in the empty context, that [ty] is the type of
  * [te]. [ty] is typechecked first. *)

val inference   : Signature.t -> term -> judgment
(** [inference sg ctx te] builds a typing judgment for the term [te] in the signature [sg] and empty context. *)

val check_rule  : Signature.t -> rule -> unit
(** [check_rule sg ru] checks that a rule is well-typed. *)

(** {2 Judgment Constructors (experimental)} *)
(*
type judgmentExn =
  | DistinctContexts
  | LambdaKind
  | LambdaEmptyContext
  | PiSort
  | PiEmptyContext
  | AppNotAPi
  | AppNotConvertible
  | ConvSort
  | ConvError

exception JudgmentExn of judgmentExn

val mk_Type     : Context.t -> loc -> judgment
val mk_Const    : Signature.t -> Context.t -> loc -> ident -> ident -> judgment
val mk_Var      : Context.t -> loc -> ident -> int -> judgment
val mk_App      : Signature.t -> judgment -> judgment -> judgment
val mk_Pi       : judgment -> judgment
val mk_Lam      : judgment -> judgment
val mk_Conv     : Signature.t -> judgment -> judgment -> judgment
*)
