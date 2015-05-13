open Basics
open Term
open Monads

module S = Msubst

type unification_error =
  | GenericFail

exception UnificationError of unification_error

type mdecl = context*int*mkind

type pair = context*term*term

type problem = { cpt:int; decls:mdecl list; sigma:S.t; pairs: pair list; }

let fresh = {cpt=0; decls=[]; sigma=S.identity; pairs=[]; }

(* A monad with effects, backtracking and restricted state operations *)
module Types = struct
  type err = unification_error
  type state = problem
end
module M0 = BacktrackF(IO)(Types)
module M = StateF(M0)(Types)
include M

include (MonadF(M) : module type of MonadF(M) with type 'a t := 'a t)

module MIO = Trans_IO(IO)(Trans_Trans(M0)(M))
include (MIO : module type of MIO with type 'a t := 'a t)

module MSB = State_Backtrack(M0)(M0)(Types)
include (MSB : module type of MSB with type 'a t := 'a t)

let run m = match IO.run (M0.run (M.run m fresh)) () with
  | Nil e -> raise (UnificationError e)
  | Cons (r,_) -> r


let apply pb t = assert false

let add_pair sg (ctx,t1,t2) = assert false

let new_meta ctx lc s k = assert false

let meta_constraint t = assert false


let whnf sg t = assert false

(*
This is only used in the pseudo-unification step of pattern checking.
TODO(future work): If possible we would like to use unification instead.
*)
let simpl t = assert false


(* returns Nothing if there are no (unsolved) disagreement pairs *)
let inspect = assert false


type ('a,'b) sum =
  | Inl of 'a
  | Inr of 'b
(* pair_conv (Inl t) checks if the left term of the current pair is convertible with t, then replaces it with t, else fails *)
let pair_conv sg o = assert false

(*
Decompose the pair according to the common constructor of the terms:
- Psi, App c ts, App c' ts' -> Psi,c,c' and Psi,ts,ts' (fails if |ts| <> |ts'|)
- Psi,Pi a b, Pi a' b' -> Psi,a,a' and a::Psi,b,b'
- Psi,Type,Type -> []
- etc
*)
let pair_decompose = assert false

(* Tries to unfold the meta at the head of the left (resp right) term *)
let pair_meta_unfold side = assert false


