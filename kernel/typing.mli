open Term
open Rule
open Basics

type typing_error =
  | KindIsNotTypable
  | ConvertibilityError : 'a term*'b context*'c term*'d term -> typing_error
  | VariableNotFound : loc*ident*int*'a context -> typing_error
  | SortExpected : 'a term*'b context*'c term -> typing_error
  | ProductExpected : 'a term*'b context*'c term -> typing_error
  | InexpectedKind : 'a term*'b context -> typing_error
  | DomainFreeLambda of loc
  | Not_Inferrable of loc*ident*int
  | Remaining_Guard of loc*int
  | UnknownMeta of loc*ident*int
  | UnknownGuard of loc*int
  | DecomposeDomainFreeLambdas
  | CannotSolveDeferred
  | Not_Unifiable
  | Not_Applicable

exception TypingError of typing_error

(** Type checking/inference *)

val coc : bool ref

type 'a judgment0 = private { ctx:'a; te:typed term; ty:typed term; }

module Context :
sig
  type t
  val empty : t
  val add : loc -> ident -> t judgment0 -> t
  val get_type : t -> loc -> ident -> int -> typed term
  val is_empty : t -> bool
end

type judgment = Context.t judgment0

(** {2 Meta aware operations} *)

module type Meta = sig
  include Monads.Monad

  type pextra
  type extra
  type ctx
  type jdg

  val get_type : ctx -> loc -> ident -> int -> extra term

  val judge : ctx -> extra term -> extra term -> jdg
  val jdg_ctx : jdg -> ctx
  val jdg_te : jdg -> extra term
  val jdg_ty : jdg -> extra term

  val to_context : ctx -> extra context

  val fail : typing_error -> 'a t

  val fold : ('a -> 'b -> 'a t) -> 'a -> 'b list -> 'a t

  val ctx_add : Signature.t -> loc -> ident -> jdg -> (jdg*ctx) t
  val unsafe_add : ctx -> loc -> ident -> extra term -> ctx

  val reject_kind : Signature.t -> jdg -> unit t

  val pi : Signature.t -> ctx -> extra term -> (loc*ident*extra term*extra term) option t

  (* If ctx |- te : ty and ctx |- ty_exp : *, cast te to ty_exp *)
  val cast : Signature.t -> jdg -> jdg -> jdg t
  (* If ctx |- te : ty, cast te to some sort s *)
  val cast_sort : Signature.t -> jdg -> jdg t

  val infer_extra : (Signature.t -> ctx -> pextra term -> jdg t) -> (Signature.t -> pextra term -> jdg -> jdg t) ->
                    Signature.t -> ctx -> loc -> pextra tkind -> pextra -> jdg t
end

(** {2 Type Inference/Checking} *)

module type ElaborationS = sig
  type 'a t

  type pextra
  type extra
  type ctx
  type jdg

  val infer       : Signature.t -> ctx -> pextra term -> jdg t
  (** [infer sg ctx te] builds a typing judgment for the term [te] in the signature [sg] and context [ctx] *)

  val check       : Signature.t -> pextra term -> jdg -> jdg t
  (** [check sg te ty] builds a typing judgment for the term [te] of type [ty.te]
  * in the signature [sg] and context [ty.ctx]. *)
end

module Elaboration (M:Meta) : ElaborationS with type 'a t = 'a M.t and type pextra = M.pextra and type extra = M.extra and type ctx = M.ctx and type jdg = M.jdg

module Checker : ElaborationS with type 'a t = 'a and type pextra = typed and type extra = typed and type ctx = Context.t and type jdg = judgment

val checking    : Signature.t -> typed term -> typed term -> judgment
(** [checking sg te ty] checks, in the empty context, that [ty] is the type of
  * [te]. [ty] is typechecked first. *)

val inference   : Signature.t -> typed term -> judgment
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
