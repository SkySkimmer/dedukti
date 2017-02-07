(** Substitutions using DeBruijn indices. *)
open Term

val shift               : int -> 'a term -> 'a term
exception UnshiftExn
val unshift             : int -> 'a term -> 'a term

val psubst_l            : ('a term Lazy.t) Basic.LList.t -> int -> 'a term -> 'a term
(** Parallel substitution of lazy terms. *)

val subst               : 'a term -> 'a term -> 'a term
(** [subst te u] substitutes the deBruijn indice [0] with [u] in [te]. *)

module S :
sig
  type 'a t
  val identity : 'a t
  val add : 'a t -> Basic.ident -> int -> 'a term -> 'a t option
  val apply : 'a t -> 'a term -> int -> 'a term
  val merge : 'a t -> 'a t -> 'a t
  val is_identity : 'a t -> bool
  val pp : out_channel -> 'a t -> unit
end
