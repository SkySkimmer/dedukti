open Basic
open Term

val mk_prelude     : loc -> ident -> unit

val mk_declaration : loc -> ident -> untyped term -> unit

val mk_definable   : loc -> ident -> untyped term -> unit

val mk_definition  : loc -> ident -> untyped term option -> untyped term -> unit

val mk_opaque      : loc -> ident -> untyped term option -> untyped term -> unit

val mk_rules       : Rule.rule list -> unit

val mk_command     : loc -> Cmd.command -> unit

val mk_ending      : unit -> unit
