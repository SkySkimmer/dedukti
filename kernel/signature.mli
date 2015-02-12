(** Global Environment *)

open Basics
open Term
open Rule

val ignore_redecl       : bool ref
val autodep             : bool ref

type signature_error =
  | FailToCompileModule of loc*ident
  | UnmarshalBadVersionNumber of loc*string
  | UnmarshalSysError of loc*string*string
  | UnmarshalUnknown of loc*string
  | SymbolNotFound of loc*ident*ident
  | AlreadyDefinedSymbol of loc*ident
  | CannotBuildDtree of Dtree.dtree_error
  | CannotAddRewriteRules of loc*ident

exception SignatureError of signature_error

type dtree_or_def =
    | DoD_None
    | DoD_Def of term
    | DoD_Dtree of int*dtree

type t

val dummy               : t (*FIXME*)
val make                : ident -> t
val get_name            : t -> ident

val export              : t -> bool
val get_type            : t -> loc -> ident -> ident -> term
val get_dtree           : t -> loc -> ident -> ident -> dtree_or_def
val declare             : t -> loc -> ident -> term -> unit
val define              : t -> loc -> ident -> term -> term -> unit
val add_rules           : t -> Rule.rule list -> unit