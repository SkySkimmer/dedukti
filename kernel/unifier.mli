open Basics
open Term
open Unif_core

val unify : Signature.t -> context -> term -> mkind -> bool t

val solve : unit t

