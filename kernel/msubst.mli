(** Substitutions of metavariables *)
open Term


type t

val identity : t

val add : t -> int -> term -> t

val apply : t -> term -> term
(** Recursive application. *)

val meta_raw : t -> int -> term option

val meta_val : t -> term -> term option
(** If the term is a metavariable and has a value in the substitution we apply it, otherwise return None. *)

val whnf : Signature.t -> t -> term -> term
(** Recursively apply Reduction.whnf and meta_val on the term's head. *)

val pp : out_channel -> t -> unit

