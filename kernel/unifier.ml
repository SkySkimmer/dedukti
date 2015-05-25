open Basics
open Term
open Unif_core

let first_applicable l = let rec aux = function
  | m::l -> plus m (function | Not_Applicable -> aux l | e -> zero e)
  | [] -> zero Not_Applicable
  in once (aux l)

let fully_backtracking l = let rec aux = function
  | m::l -> plus m (fun _ -> aux l)
  | [] -> zero Not_Applicable
  in aux l

let rec solve_pair sg p = fully_backtracking
  [ first_applicable [ meta_delta RIGHT; meta_delta LEFT ]
  ; first_applicable [ meta_same_same; meta_same ]
  ; meta_inst sg RIGHT; meta_fo RIGHT; meta_inst sg LEFT; meta_fo LEFT
  ; decompose
  ; step_reduce sg RIGHT; step_reduce sg LEFT]

let rec solve sg = normalize >>= fun () -> effectful (fun () -> Printf.printf "Solve step for ") >>= fun () -> pp_state >>= fun () ->
  inspect >>= function
  | Some p -> solve_pair sg p >>= fun () -> solve sg
  | None -> return ()

let unify sg ctx t1 t2 = if Reduction.are_convertible sg t1 t2
  then return true
  else add_pair sg (ctx,t1,t2) >>= fun () -> plus (once (solve sg) >>= fun () -> return true)
                                                  (function | Not_Unifiable -> return false | e -> zero e)

let unify_sort sg ctx = function
  | Kind | Type _ -> return true
  | t -> add_sort_pair sg ctx t >>= fun () -> plus (once (solve sg) >>= fun () -> return true)
                                                (function | Not_Unifiable -> return false | e -> zero e)

