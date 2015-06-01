open Term
open Rule
open Typing

(** The following pass refined terms to the corresponding functions in Typing *)

val checking    : Signature.t -> untyped term -> untyped term -> judgment

val inference   : Signature.t -> untyped term -> judgment

val check_rule  : Signature.t -> rule -> unit

