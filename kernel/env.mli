(** The main functionalities of Dedukti:
 this is essentialy a wrapper around Signature, Typing and Reduction *)
open Basic
open Term
open Signature

type env_error =
  | EnvErrorType of Typing.typing_error
  | EnvErrorSignature of signature_error
  | KindLevelDefinition of loc*ident

(** {2 The Global Environment} *)

val init        : ident -> unit
(** [init name] initializes a new global environement giving it the name [name] *)

val get_name    : unit -> ident
(** [get_name ()] returns the name of environment/module *)

val get_type    : loc -> ident -> ident -> (typed term,signature_error) error
(** [get_type l md id] returns the type of the constant [md.id]. *)

val get_dtree   : loc -> ident -> ident -> ((int*Rule.dtree) option,signature_error) error
(** [get_dtree l md id] returns the decision/matching tree associated with [md.id]. *)

val export      : unit -> bool
(** [export ()] saves the current environment in a [*.dko] file*)

val declare_constant : loc -> ident -> untyped term -> (typed term,env_error) error
(** [declare_constant l id ty] declares the constant symbol [id] of type [ty]. *)

val declare_definable : loc -> ident -> untyped term -> (typed term,env_error) error
(** [declare_definable l id ty] declares the definable symbol [id] of type [ty]. *)

val define      : loc -> ident -> untyped term -> untyped term option -> ((typed term * typed term),env_error) error
(** [define l id body ty] defined the symbol [id] of type [ty] to be an alias of [body]. *)

val define_op   : loc -> ident -> untyped term -> untyped term option -> ((typed term * typed term),env_error) error
(** [define_op l id body ty] declares the symbol [id] of type [ty] and checks
* that [body] has this type (but forget it after). *)

val add_rules   : Rule.rule list -> (Rule.rule list,env_error) error
(** [add_rules rule_lst] adds a list of rule to a symbol. All rules must be on the
  * same symbol. *)

(** {2 Type checking/inference} *)

val infer       : untyped term -> (typed term,env_error) error

val check       : untyped term -> untyped term -> (unit,env_error) error

(** {2 Safe Reduction/Conversion} *)
(** terms are typechecked before the reduction/conversion *)

val hnf         : untyped term -> (typed term,env_error) error
val whnf        : untyped term -> (typed term,env_error) error
val snf         : untyped term -> (typed term,env_error) error
val one         : untyped term -> (typed term option,env_error) error

val are_convertible : untyped term -> untyped term -> (bool,env_error) error

val unsafe_snf : 'a term -> 'a term
