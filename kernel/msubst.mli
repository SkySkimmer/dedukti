(** Substitutions of metavariables *)
open Term


type t

val identity : t

val mem : t -> int -> bool

val add : t -> int -> pretyped term -> t

val apply : t -> pretyped term -> pretyped term

val to_ground : t -> pretyped term -> typed term option

val meta_raw : t -> int -> pretyped term option

val meta_val : t -> pretyped term -> pretyped term option
(** If the term is a metavariable and has a value in the substitution we apply it, otherwise return None. *)

val whnf : Signature.t -> t -> pretyped term -> pretyped term
(** Recursively apply Reduction.whnf and meta_val on the term's head. *)

val normalize : t -> t

val pp : out_channel -> t -> unit

