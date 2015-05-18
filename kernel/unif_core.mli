open Basics
open Term
open Monads

type typing_error =
  | KindIsNotTypable
  | ConvertibilityError of term*context*term*term
  | VariableNotFound of loc*ident*int*context
  | SortExpected of term*context*term
  | ProductExpected of term*context*term
  | InexpectedKind of term*context
  | DomainFreeLambda of loc
  | MetaInKernel of loc*ident
  | InferSortMeta of loc*ident
  | UnknownMeta of loc*ident*int
  | ConvRule_Bad of term*term
  | DecomposeDomainFreeLambdas
  | CannotSolveDeferred
  | Not_Unifiable
  | Not_Applicable

exception TypingError of typing_error

(* A monad with effects, backtracking and restricted state operations *)
include Monad
include MonadS with type 'a t := 'a t
include EffectS with type 'a t := 'a t
include BacktrackS with type 'a t := 'a t and type err = typing_error

type problem

(* raises an exception if there are no successes *)
val run : 'a t -> 'a*problem
val apply : problem -> term -> term

type pair = context*term*term

val add_pair : Signature.t -> pair -> unit t

val new_meta : context -> loc -> ident -> mkind -> term t

val meta_constraint : term -> (context*term) t


val whnf : Signature.t -> term -> term t

(*
This is only used in the pseudo-unification step of pattern checking.
TODO(future work): If possible we would like to use unification instead.
*)
val simpl : term -> term t


(* returns Nothing if there are no (unsolved) disagreement pairs *)
val inspect : pair option t


type ('a,'b) sum =
  | Inl of 'a
  | Inr of 'b
(*
pair_conv (Inl t) checks if the left term of the current pair is convertible with t, then replaces it with t, else fails
Not really safe: t could be illtyped
*)
val pair_conv : Signature.t -> (term,term) sum -> unit t

(*
Decompose the pair according to the common constructor of the terms:
- Psi, App c ts, App c' ts' -> Psi,c,c' and Psi,ts,ts' (fails if |ts| <> |ts'|)
- Psi,Pi a b, Pi a' b' -> Psi,a,a' and a::Psi,b,b'
- Psi,Type,Type -> []
- etc
*)
val pair_decompose : unit t

(* Tries to unfold the meta at the head of the left (resp right) term *)
val pair_meta_unfold : (unit,unit) sum -> unit t


