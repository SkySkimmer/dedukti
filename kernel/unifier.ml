open Basics
open Term
open Unif_core

(** Rules *)

(** meta-fo *)

let meta_fo side (_,lop,rop) =
  let op = match side with | LEFT -> lop | RIGHT -> rop in
  match op with
    | App (Meta _, _, args) -> split_app (1+List.length args)
    | _ -> zero Not_Applicable

(** meta-deldeps *)

module IntSet = Set.Make(struct
  type t = int
  let compare = compare
end)

let filter_unique_vars subst args =
  let avars = List.fold_left (fun s t -> match t with | DB (_,_,n) -> IntSet.add n s | _ -> s) IntSet.empty args in
  let rec aux clean acc = function
    | (_,DB(_,_,n))::l -> let unique = not ((IntSet.mem n avars) || (List.exists (function | _,DB (_,_,m) -> n=m | _,_ -> false) l)) in
        aux (clean && unique) (unique::acc) l
    | _::l -> aux false (false::acc) l
    | [] -> clean, List.rev acc
    in
  aux true [] subst

let meta_deldeps side (ctx,lop,rop) =
  let active,passive = match side with | LEFT -> (lop,rop) | RIGHT -> (rop,lop) in
  begin match active with
    | App (Meta (lc,s,n,ts), a, args) -> return (lc,s,n,ts,a::args)
    | Meta (lc,s,n,ts) -> return (lc,s,n,ts,[])
    | _ -> zero Not_Applicable
    end >>= fun (lc,s,n,ts,args) ->
  let clean,filter = filter_unique_vars ts args in
  if clean then zero Not_Applicable else return () >>
  narrow_meta lc s n filter >>
  meta_delta side

(** Rule application *)

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
  ; meta_inst sg RIGHT; meta_fo RIGHT p; meta_deldeps RIGHT p
  ; meta_inst sg LEFT ; meta_fo LEFT p ; meta_deldeps LEFT  p
  ; decompose
  ; step_reduce sg RIGHT; step_reduce sg LEFT]

let rec solve sg = normalize >> (*effectful (fun () -> Printf.printf "Solve step for ") >> pp_state >>*)
  inspect >>= function
  | Some p -> solve_pair sg p >>= fun () -> solve sg
  | None -> return ()

let unify sg ctx t1 t2 = if Reduction.are_convertible sg t1 t2
  then return true
  else add_pair sg (ctx,t1,t2) >>= fun () -> plus (once (solve sg) >> return true)
                                                  (function | Not_Unifiable | Not_Applicable -> return false | e -> zero e)

let unify_sort sg ctx = function
  | Kind | Type _ -> return true
  | t -> add_sort_pair sg ctx t >>= fun () -> plus (once (solve sg) >>= fun () -> return true)
                                                (function | Not_Unifiable | Not_Applicable -> return false | e -> zero e)

