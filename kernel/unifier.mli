open Basics
open Term
open Unif_core

type pextra = untyped
type extra = pretyped
type ctx = pretyped context
type jdg = pretyped context*pretyped term*pretyped term

val cast : Signature.t -> jdg -> jdg -> jdg t

val cast_sort : Signature.t -> jdg -> jdg t

val reject_kind : Signature.t -> jdg -> unit t
