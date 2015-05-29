open Basics
open Term
open Rule

let color = ref true
let errors_in_snf = ref false

let colored n s =
  if !color then "\027[3" ^ string_of_int n ^ "m" ^ s ^ "\027[m"
  else s

let green = colored 2
let orange = colored 3
let red = colored 1

let success fmt =
  prerr_string (green "SUCCESS ") ;
  Printf.kfprintf (fun _ -> prerr_newline () ) stderr fmt

let prerr_loc lc =
  let (l,c) = of_loc lc in
    Printf.eprintf "line:%i column:%i " l c

let fail lc fmt =
  prerr_string (red "ERROR ") ;
  prerr_loc lc;
  Printf.kfprintf (fun _ -> prerr_newline () ; raise Exit) stderr fmt

let pp_context2 out = function
  | [] -> ()
  | (_::_) as ctx ->
    Printf.fprintf out " in context:\n%a" pp_context ctx

let fail_typing_error err =
  let open Typing in
    match err with
      | KindIsNotTypable -> fail dloc "Kind is not typable."
      | ConvertibilityError (te,ctx,exp,inf) ->
          let exp = if !errors_in_snf then Env.unsafe_snf exp else exp in
          let inf = if !errors_in_snf then Env.unsafe_snf inf else inf in
            fail (get_loc te)
              "Error while typing '%a'%a.\nExpected: %a\nInferred: %a."
              pp_term te pp_context2 ctx pp_term exp pp_term inf
      | VariableNotFound (lc,x,n,ctx) ->
          fail lc "The variable '%a' was not found in context %a.\n"
            pp_term (mk_DB lc x n) pp_context ctx
      | SortExpected (te,ctx,inf) ->
          let inf = if !errors_in_snf then Env.unsafe_snf inf else inf in
            fail (Term.get_loc te)
              "Error while typing '%a'%a.\nExpected: a sort.\nInferred: %a."
              pp_term te pp_context2 ctx pp_term inf
      | ProductExpected (te,ctx,inf) ->
          let inf = if !errors_in_snf then Env.unsafe_snf inf else inf in
            fail (get_loc te)
              "Error while typing '%a'%a.\nExpected: a product type.\nInferred: %a."
              pp_term te pp_context2 ctx pp_term inf
      | InexpectedKind (te,ctx) ->
          fail (get_loc te)
            "Error while typing '%a'%a.\nExpected: anything but Kind.\nInferred: Kind."
            pp_term te pp_context2 ctx
      | DomainFreeLambda lc ->
          fail lc "Cannot infer the type of domain-free lambda."
      | MetaInKernel (lc,s) -> fail lc "Unexpected metavariable \"%a\" in kernel mode." pp_ident s
      | InferSortMeta (lc,s) -> fail lc "TODO: implement type inference for sort meta (hit \"%a\")." pp_ident s
      | UnknownMeta (lc,s,n) -> fail lc "Unknown meta ?_%i{\"%a\"} encountered." n pp_ident s
      | DecomposeDomainFreeLambdas -> fail dloc "Cannot decompose a pair of domain free lambdas."
      | CannotSolveDeferred -> fail dloc "Cannot solve deferred constraints."
      | Not_Unifiable -> fail dloc "Non unifiable pair hit."
      | Not_Applicable -> fail dloc "All rules not applicable."

let fail_dtree_error err =
  let open Dtree in
    match err with
      | BoundVariableExpected pat ->
          fail (get_loc_pat pat)
            "The pattern '%a' is not a bound variable." pp_pattern pat
      | VariableBoundOutsideTheGuard te ->
          fail (get_loc te)
            "The term '%a' contains a variable bound outside the brackets."
            pp_term te
      | NotEnoughArguments (lc,id,n,nb_args,exp_nb_args) ->
          fail lc "The variable '%a' is applied to %i argument(s) (expected: at least %i)."
            pp_ident id nb_args exp_nb_args
      | HeadSymbolMismatch (lc,hd1,hd2) ->
          fail lc "Unexpected head symbol '%a' \ (expected '%a')."
            pp_ident hd1 pp_ident hd2
      | ArityMismatch (lc,id) ->
          fail lc
            "All the rewrite rules for \ the symbol '%a' should have the same arity."
            pp_ident id
      | UnboundVariable (lc,x,pat) ->
          fail lc "The variables '%a' is not bound in '%a'."
            pp_ident x pp_pattern pat
      | AVariableIsNotAPattern (lc,id) ->
          fail lc "A variable is not a valid pattern."
      | DistinctBoundVariablesExpected (lc,x) ->
          fail lc "The variable '%a' should be applied to distinct variables."
          pp_ident x

let fail_signature_error err =
  let open Signature in
    match err with
      | FailToCompileModule (lc,md) ->
          fail lc "Fail to compile dependency '%a'." pp_ident md
      | UnmarshalBadVersionNumber (lc,md) ->
          fail lc "Fail to open\ module '%s' (file generated by a different version?)." md
      | UnmarshalSysError (lc,md,msg) ->
          fail lc "Fail to open module '%s' (%s)." md msg
      | UnmarshalUnknown (lc,md) ->
          fail lc "Fail to open module '%s'." md
      | SymbolNotFound (lc,md,id) ->
          fail lc "Cannot find symbol '%a.%a'." pp_ident md pp_ident id
      | AlreadyDefinedSymbol (lc,id) ->
          fail lc "Already defined symbol '%a'." pp_ident id
      | CannotBuildDtree err -> fail_dtree_error err
      | CannotAddRewriteRules (lc,id) ->
          fail lc
            "Cannot add rewrite\ rules for the defined symbol '%a'." pp_ident id

let fail_env_error = function
  | Env.EnvErrorSignature e -> fail_signature_error e
  | Env.EnvErrorType e -> fail_typing_error e
  | Env.KindLevelDefinition (lc,id) ->
    fail lc "Cannot add a rewrite rule for '%a' since it is a kind." pp_ident id


