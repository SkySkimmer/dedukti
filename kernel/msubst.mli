(** Substitutions of metavariables and unfolding of guards *)
open Term


type t

val identity : t

val is_identity : t -> bool

val meta_mem : t -> int -> bool

val meta_add : t -> int -> pretyped term -> t

val guard_mem : t -> int -> bool

val guard_add : t -> int -> t

val apply : t -> pretyped term -> pretyped term

val to_ground : t -> pretyped term -> typed term

val extra_val : t -> pretyped -> pretyped term option
(** If the term is a metavariable and has a value in the substitution we apply it, otherwise return None. *)

val whnf : Signature.t -> t -> pretyped term -> pretyped term
(** Recursively apply Reduction.whnf and extra_val on the term's head. *)

val normalize : t -> t

val pp : out_channel -> t -> unit

