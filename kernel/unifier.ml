open Basics
open Term
open Unif_core

let first_applicable l = let rec aux acc = function
  | m::l -> aux (plus acc (function | Not_Applicable -> m | e -> zero e)) l
  | [] -> acc
  in once (aux (zero Not_Applicable) (List.rev l))

let fully_backtracking l = let rec aux acc = function
  | m::l -> aux (plus acc (fun _ -> m)) l
  | [] -> acc
  in aux (zero Not_Applicable) (List.rev l)

let rec solve_pair sg p = fully_backtracking
  [ first_applicable [ meta_delta RIGHT; meta_delta LEFT ]
  ; first_applicable [ meta_same_same; meta_same ]
  ; meta_inst sg RIGHT; meta_fo RIGHT; meta_inst sg LEFT; meta_fo LEFT
  ; decompose
  ; step_reduce sg RIGHT; step_reduce sg LEFT]

let rec solve sg = inspect >>= function
  | Some p -> solve_pair sg p >>= fun () -> solve sg
  | None -> return ()

let unify sg ctx t1 t2 = if Reduction.are_convertible sg t1 t2
  then return true
  else add_pair sg (ctx,t1,t2) >>= fun () -> solve sg >>= fun () -> return true

let unify_sort sg ctx = function
  | Kind | Type _ -> return true
  | Meta _ -> failwith "Not implemented: Unifier.unify_sort on meta"
  | _ -> return false
