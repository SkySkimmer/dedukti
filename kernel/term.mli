open Basics

(** Lambda terms *)

(** {2 Terms} *)

type term = private
  | Kind                                (** Kind *)
  | Type  of loc                        (** Type *)
  | DB    of loc*ident*int              (** deBruijn indices *)
  | Const of loc*ident*ident            (** Global variable *)
  | App   of term * term * term list    (** f a1 [ a2 ; ... an ] , f not an App *)
  | Lam   of loc*ident*term option*term (** Lambda abstraction *)
  | Pi    of loc*ident*term*term        (** Pi abstraction *)
  | Hole  of loc*ident                  (** Raw placeholder *)
  | Meta  of loc*ident*int*(ident*term) list    (** Metavariable *)
(** The list attached to metavariables is in increasing DeBruijn order *)

val get_loc : term -> loc

val mk_Kind     : term
val mk_Type     : loc -> term
val mk_DB       : loc -> ident -> int -> term
val mk_Const    : loc -> ident -> ident -> term
val mk_Lam      : loc -> ident -> term option -> term -> term
val mk_App      : term -> term -> term list -> term
val mk_Pi       : loc -> ident -> term -> term -> term
val mk_Arrow    : loc -> term -> term -> term
val mk_Hole     : loc -> ident -> term
val mk_Meta     : loc -> ident -> int -> (ident*term) list -> term

(* Syntactic equality / Alpha-equivalence *)
val term_eq : term -> term -> bool

val pp_term     : out_channel -> term -> unit

(** {2 Contexts} *)

type context = ( loc * ident * term ) list
val pp_context  : out_channel -> context -> unit

(** {3 Unification candidates} *)

type mkind =
  | MTyped of term
  | MType
  | MSort

