open Basics
open Term

type refine_error =
  | UnknownMeta of int

exception RefineError of refine_error

type problem

type 'a t

val return : 'a -> 'a t

val (>>=) : 'a t -> ('a -> 'b t) -> 'b t

val extract : 'a t -> 'a*problem

val apply : problem -> term -> term

val simpl : term -> term t

val whnf : Signature.t -> term -> term t

val unify : Signature.t -> context -> term -> candidate -> bool t

val new_meta : context -> loc -> ident -> candidate -> term t

val meta_constraint : term -> (context*term) t

