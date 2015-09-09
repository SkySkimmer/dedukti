open Basics
open Pp

(* ********************************* *)

let out = ref Format.std_formatter
let verbose = ref false

let set_debug_level lvl =
  if lvl > 0 then ( verbose := true; Pp.print_db_enabled := true )

let eprint lc fmt =
  if !verbose then (
  let (l,c) = of_loc lc in
    Printf.eprintf "line:%i column:%i " l c;
    Printf.kfprintf (fun _ -> prerr_newline () ) stderr fmt
  ) else
    Printf.ifprintf stderr fmt

(* ********************************* *)

let mk_prelude lc name =
  eprint lc "Module name is '%a'." pp_ident name;
  Env.init name;
  Format.fprintf !out "#NAME %a.@.@." print_ident name

let mk_declaration lc id pty : unit =
  eprint lc "Declaration of constant '%a'." pp_ident id;
  match Env.declare_constant lc id pty with
    | OK ty -> Format.fprintf !out "@[<2>%a :@ %a.@]@.@." print_ident id print_term ty
    | Err e -> Errors.fail_env_error e

let mk_definable lc id pty : unit =
  eprint lc "Declaration of definable '%a'." pp_ident id;
  match Env.declare_definable lc id pty with
    | OK ty -> Format.fprintf !out "@[<2>`%a :@ %a.@]@.@." print_ident id print_term ty
    | Err e -> Errors.fail_env_error e

let mk_definition lc id pty_opt pte : unit =
  eprint lc "Definition of symbol '%a'." pp_ident id ;
  match Env.define lc id pte pty_opt with
    | OK (te,ty) -> begin match pty_opt with
        | None -> Format.fprintf !out "@[<hv2>%a@ :=@ %a.@]@.@." print_ident id print_term te
        | Some pty ->
            Format.fprintf !out "@[<hv2>%a :@ %a@ :=@ %a.@]@.@."
              print_ident id print_term ty print_term te
        end
    | Err e -> Errors.fail_env_error e

let mk_opaque lc id pty_opt pte =
  eprint lc "Opaque definition of symbol '%a'." pp_ident id ;
  match Env.define_op lc id pte pty_opt with
    | OK (te,ty) -> begin match pty_opt with
        | None -> Format.fprintf !out "@[<hv2>{%a}@ :=@ %a.@]@.@." print_ident id print_term te
        | Some pty ->
            Format.fprintf !out "@[<hv2>{%a}@ :@ %a :=@ %a.@]@.@."
              print_ident id print_term ty print_term te
        end
    | Err e -> Errors.fail_env_error e

let mk_rules lst =
  List.iter (
    fun (ctx,pat,rhs) ->
      eprint (Rule.get_loc_pat pat) "%a" Rule.pp_rule (ctx,pat,rhs)
  ) lst ;
  match Env.add_rules lst with
    | OK lst -> Format.fprintf !out "@[<v0>%a@].@.@." (print_list "" print_rule) lst
    | Err e -> Errors.fail_env_error e

let mk_command lc cmd =
  Cmd.mk_command lc cmd;
  Format.fprintf !out "@[<2>%a@]@.@." Cmd.print_command cmd

let mk_ending () = ()

