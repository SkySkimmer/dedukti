open Term
open Rule
open Typing

(** The following pass refined terms to the corresponding functions in Typing *)

val checking    : Signature.t -> term -> term -> judgment

val inference   : Signature.t -> term -> judgment

val check_rule  : Signature.t -> rule -> unit

