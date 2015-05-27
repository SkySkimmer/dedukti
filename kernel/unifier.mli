open Basics
open Term
open Unif_core

val unify : Signature.t -> context -> term -> term -> bool t

val unify_sort : Signature.t -> context -> term -> bool t

