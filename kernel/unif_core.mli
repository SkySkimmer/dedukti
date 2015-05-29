open Basics
open Term
open Monads
open Typing

(* A monad with effects, backtracking and restricted state operations *)
include Monad
include MonadS with type 'a t := 'a t
include EffectS with type 'a t := 'a t
include BacktrackS with type 'a t := 'a t and type err = typing_error

type problem

val pp_problem : out_channel -> problem -> unit

(** Wrapper around pp_problem *)
val pp_state : unit t

(* raises an exception if there are no successes *)
val run : 'a t -> 'a*problem
val apply : problem -> term -> term

type pair = context*term*term

val add_pair : Signature.t -> pair -> unit t

val add_sort_pair : Signature.t -> context -> term -> unit t

val new_meta : context -> loc -> ident -> mkind -> term t

val meta_constraint : loc -> ident -> int -> (context*term) t

val meta_decl : loc -> ident -> int -> (context*mkind) t

val whnf : Signature.t -> term -> term t

(*
This is only used before the pseudo-unification step of pattern checking.
TODO(future work): If possible we would like to use unification instead.
*)
val simpl : term -> term t

val normalize : unit t


(* returns Nothing if there are no (unsolved) disagreement pairs *)
val inspect : pair option t

type side = LEFT | RIGHT

val pp_side : out_channel -> side -> unit

(*
The terms of the pair are convertible modulo reduction and meta expansion
*)
val pair_convertible : Signature.t -> unit t

(*
Decompose the pair according to the common constructor of the terms:
- Psi, App c ts, App c' ts' -> Psi,c,c' and Psi,ts,ts' (fails if |ts| <> |ts'|)
- Psi,Pi a b, Pi a' b' -> Psi,a,a' and a::Psi,b,b'
- Psi,Type,Type -> []
- etc
*)
val decompose : unit t

(* Tries to unfold the meta at the head of the left (resp right) term *)
val meta_delta : side -> unit t

val step_reduce : Signature.t -> side -> unit t

val meta_same_same : unit t

val meta_same : unit t

val meta_inst : Signature.t -> side -> unit t


val split_app : int -> unit t

(* NB: assumes the filter and the meta's context have the same length. *)
val narrow_meta : loc -> ident -> int -> bool list -> unit t

