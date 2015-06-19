open Basics
open Term
open Monads
open Typing

type pterm = pretyped term
type pcontext = pretyped context

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
val apply : problem -> pterm -> pterm
val ground : problem -> pterm -> typed term

type pair = pcontext*pterm*pterm

(*
[add_guard sg lc ctx a b t] takes t of type a to type b by adding a guard
*)
val add_guard : Signature.t -> loc -> pcontext -> pterm -> pterm -> pterm -> pterm t

val new_meta : pcontext -> loc -> ident -> mkind -> pterm t

val meta_constraint : Signature.t -> loc -> ident -> int -> (pcontext*pterm) t

val meta_decl : loc -> ident -> int -> (pcontext*mkind) t

val whnf : Signature.t -> pterm -> pterm t

val extra_val : pretyped -> pterm option t

val are_convertible : Signature.t -> pterm -> pterm -> bool t

val normalize : unit t

(* Only call this on terms known to have a type modulo some meta_constraint calls *)
val expected_type : Signature.t -> pcontext -> pterm -> pterm t


(* returns Nothing if there are no (unsolved) disagreement pairs *)
val inspect : Signature.t -> pair option t

type side = LEFT | RIGHT

val pp_side : out_channel -> side -> unit

(*
The pterms of the pair are convertible modulo reduction and meta expansion
*)
val pair_convertible : Signature.t -> unit t

(*
Decompose the pair according to the common constructor of the pterms:
- Psi, App c ts, App c' ts' -> Psi,c,c' and Psi,ts,ts' (fails if |ts| <> |ts'|)
- Psi,Pi a b, Pi a' b' -> Psi,a,a' and a::Psi,b,b'
- Psi,Type,Type -> []
- etc
*)
val decompose : unit t

(* Tries to unfold the meta at the head of the left (resp right) pterm *)
val meta_delta : side -> unit t

val step_reduce : Signature.t -> side -> unit t

val split_app : int -> unit t

(* NB: assumes the filter and the meta's pcontext have the same length. *)
val narrow_meta : loc -> ident -> int -> bool list -> unit t

(*
[refine n t] when ctx |- ?n : ty and ctx |- t : ty' guards t to ty then sets ?n to it
Also occurs check
*)
val refine : Signature.t -> loc -> ident -> int -> pterm -> unit t


