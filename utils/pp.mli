(** Pretty printing. *)
open Basic
open Preterm
open Term
open Rule

val name                : ident ref
val print_db_enabled    : bool ref

val print_list  : string -> (Format.formatter -> 'a -> unit)
                  -> Format.formatter -> 'a list -> unit

val print_pterm : Format.formatter -> preterm -> unit

val print_ppattern : Format.formatter -> prepattern -> unit

val print_term  : Format.formatter -> 'a term -> unit

val print_pattern : Format.formatter -> pattern -> unit


val print_rule  : Format.formatter -> rule -> unit

val print_frule : Format.formatter -> rule_infos -> unit

val print_context: Format.formatter -> 'a context -> unit
