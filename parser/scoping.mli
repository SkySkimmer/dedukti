(** Scope managmement: from preterms to terms. *)
val name        : Basic.ident ref
val scope_term : Term.untyped Term.context -> Preterm.preterm -> Term.untyped Term.term
val scope_rule : Preterm.prule -> Rule.rule
