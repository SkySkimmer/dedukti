open Basics
open Term
open Unif_core

let solve = inspect >>= function
  | Some _ -> zero CannotSolveDeferred
  | None -> return ()

let unify sg ctx t1 t2 = if Reduction.are_convertible sg t1 t2
  then return true
  else add_pair sg (ctx,t1,t2) >>= fun () -> solve >>= fun () -> return true

let unify_sort sg ctx = function
  | Kind | Type _ -> return true
  | Meta _ -> failwith "Not implemented: Unifier.unify_sort on meta"
  | _ -> return false
