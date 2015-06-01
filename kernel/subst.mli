(** Substitutions using DeBruijn indices. *)
open Term

val shift               : 'a tkind -> int -> 'a term -> 'a term
exception UnshiftExn
val unshift             : 'a tkind -> int -> 'a term -> 'a term

val psubst_l            : 'a tkind -> ('a term Lazy.t) Basics.LList.t -> int -> 'a term -> 'a term
(** Parallel substitution of lazy terms. *)

val subst               : 'a tkind -> 'a term -> 'a term -> 'a term
(** [subst te u] substitutes the deBruijn indice [0] with [u] in [te]. *)

module S :
sig
  type 'a t
  val identity : 'a tkind -> 'a t
  val kind : 'a t -> 'a tkind
  val add : 'a t -> Basics.ident -> int -> 'a term -> 'a t option
  val apply : 'a t -> 'a term -> int -> 'a term
  val merge : 'a t -> 'a t -> 'a t
  val is_identity : 'a t -> bool
  val pp : out_channel -> 'a t -> unit
end
