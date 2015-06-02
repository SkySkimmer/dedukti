open Basics
open Term
open Unif_core

val unify : Signature.t -> pretyped context -> pretyped term -> pretyped term -> bool t

val unify_sort : Signature.t -> pretyped context -> pretyped term -> bool t

