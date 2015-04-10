open Term
open Rule
open Basics

(** Type checking/inference *)

val coc : bool ref

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
  | UnknownMeta of int

exception TypingError of typing_error

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

type candidate =
  | CTerm of term
  | CType
  | CSort

module type Meta = sig
  type 'a t
  
  val return : 'a -> 'a t
  val (>>=) : 'a t -> ('a -> 'b t) -> 'b t
  
  val fold : ('a -> 'b -> 'a t) -> 'a -> 'b list -> 'a t
  
  val add : Signature.t -> loc -> ident -> judgment -> Context.t t
  
  val whnf : Signature.t -> term -> term t
  
  val unify : Signature.t -> Context.t -> term -> candidate -> bool t
  (** [unify sg ctx t c] tries to unify t and c. It may add unsolved constraints to the problem. *)
  val new_meta : Context.t -> loc -> ident -> candidate -> term t
  
  val meta_constraint : term -> (Context.t * term) t
  
  val eval : term t -> term
  val evalj : judgment t -> judgment
  (** Beware: does not eval the context. *)
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
end

module Refiner (M:Meta) : RefinerS with type 'a t = 'a M.t

module KRefine : RefinerS with type 'a t = 'a KMeta.t

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
