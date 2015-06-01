open Basics
open Term

type command =
  (* Reduction *)
  | Whnf of untyped term
  | Hnf of untyped term
  | Snf of untyped term
  | OneStep of untyped term
  | Conv of untyped term*untyped term
  (*Typing*)
  | Check of untyped term*untyped term
  | Infer of untyped term
  (* Misc *)
  | Gdt of ident option*ident
  | Print of string
  | Other of string*untyped term list

val mk_command : loc -> command -> unit

val print_command : Format.formatter -> command -> unit
