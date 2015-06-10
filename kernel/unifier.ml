open Basics
open Term
open Monads
open Unif_core
open Typing

type pextra = untyped
type extra = pretyped
type ctx = pretyped context
type jdg = pretyped context*pretyped term*pretyped term

(** Rules *)

(** meta-fo *)

let meta_fo side (_,lop,rop) =
  let op = match side with | LEFT -> lop | RIGHT -> rop in
  match op with
    | App (Extra (_,Pretyped,Meta _), _, args) -> split_app (1+List.length args)
    | _ -> zero Not_Applicable

(** meta-same-same *)

let meta_same_same sg (_,lop,rop) = match lop,rop with
  | Extra (_,Pretyped,Meta(_,n,ts)), Extra (_,Pretyped,Meta(_,m,ts')) when (n=m) ->
      let b = try List.for_all2 (fun (_,t1) (_,t2) -> term_eq t1 t2) ts ts' with | Invalid_argument _ -> assert false in
      if b then pair_convertible sg
      else zero Not_Applicable
  | App (Extra (_,Pretyped,Meta(_,n,ts)),_,_), App (Extra (_,Pretyped,Meta(_,m,ts')),_,_) when (n=m) ->
      let b = try List.for_all2 (fun (_,t1) (_,t2) -> term_eq t1 t2) ts ts' with | Invalid_argument _ -> assert false in
      if b then decompose
        (* Pair pre-processing may remove the meta-meta pair. If it doesn't it will be handled by the next solve step. *)
      else zero Not_Applicable
  | _ -> zero Not_Applicable

(** meta-same *)

let subst_intersection ts ts' = List.map2 (fun (_,t1) (_,t2) -> term_eq t1 t2) ts ts'

let meta_same sg (_,lop,rop) = match lop,rop with
  | Extra (lc,Pretyped,Meta(s,n,ts)), Extra (_,Pretyped,Meta(_,m,ts')) when (n=m) ->
      let filter = subst_intersection ts ts' in
      narrow_meta lc s n filter >>
      pair_convertible sg
  | App (Extra (lc,Pretyped,Meta(s,n,ts)),_,_), App (Extra (_,Pretyped,Meta(_,m,ts')),_,_) when (n=m) ->
      let filter = subst_intersection ts ts' in
      narrow_meta lc s n filter >>
      decompose
  | _ -> zero Not_Applicable

(** meta-inst *)

let var_get_type ctx lc x n = try let (_,_,ty) = List.nth ctx n in return (Subst.shift (n+1) ty)
  with | Failure _ -> raise (TypingError (VariableNotFound (lc,x,n,ctx)))

let find_unique p l = let rec aux i = function
  | x::l -> if p x then if List.exists p l then None else Some i
            else aux (i+1) l
  | [] -> None
  in aux 0 l

(*
y a metavariable, ts : (ident*term) option list
Indices which are None in ts should be irrelevant for y
*)
let prune lc s y ts = meta_decl lc s y >>= fun (mctx,mty) ->
  let filter = List.map (function | Some _ -> true | None -> false) ts in
  narrow_meta lc s y filter >>
  extra_val (Meta(s,y,(List.map (function | Some x -> x | None -> empty,mk_Kind) ts))) >>= function
    | Some mt -> return mt
    | None -> assert false

(*
We try to invert the term, and fail with Not_Applicable if an unknown variable or the forbidden metavariable appear.
If we fail for a term in a metavariable's substitution it should be pruned.
*)
let rec invert_term x vars q = function
  | Kind | Type _ | Const _ as t -> return t
  | DB (_,_,n) as t when (n<q) -> return t
  | DB (lc,x,n) -> begin match find_unique (fun m -> (n-q)=m) vars with
      | Some m -> return (mk_DB lc x (m+q))
      | None -> zero Not_Applicable
      end
  | App (f,a,args) -> fold (fun l t -> invert_term x vars q t >>= fun t' -> return (t'::l)) [] (f::a::args) >>= fun l ->
      begin match List.rev l with
        | f::a::args -> return (mk_App f a args)
        | _ -> assert false
        end
  | Lam (lc,y,Some a,b) -> invert_term x vars q a >>= fun a -> invert_term x vars (q+1) b >>= fun b -> return (mk_Lam lc y (Some a) b)
  | Lam (lc,y,None  ,b) -> invert_term x vars (q+1) b >>= fun b -> return (mk_Lam lc y None b)
  | Pi (lc,y,a,b) -> invert_term x vars q a >>= fun a -> invert_term x vars (q+1) b >>= fun b -> return (mk_Pi lc y a b)
  | Extra (lc,Pretyped,ex) -> extra_val ex >>= begin function
    | Some mt' -> invert_term x vars q mt'
    | None -> begin match ex with
        | Meta(s,y,ts) -> if x=y then zero Not_Applicable
            else fold (fun (l,clean) (y,t) -> once (plus
                (invert_term x vars q t >>= fun t -> return ((Some (y,t))::l,clean))
                (function | Not_Applicable -> return (None::l,false) | e -> zero e)
              )) ([],true) ts >>= fun (ts',clean) ->
              if clean then return (mk_Meta lc s y (List.rev_map (function | Some x -> x | None -> assert false) ts'))
              else prune lc s y (List.rev ts')
        | Guard(n,ts,t) -> (* TODO: maybe prune *)
            fold (fun l (y,t) -> invert_term x vars q t >>= fun t' -> return ((y,t')::l)) [] (List.rev ts) >>= fun ts' ->
            invert_term x vars q t >>= fun t' ->
            return (mk_Guard lc n ts' t')
        end
    end

let rec invert_add_lambdas ctx x argn varl t = if argn = 0 then return t
  else match varl with
  | v::varl -> var_get_type ctx dloc empty v >>= fun ty ->
    invert_term x varl 0 ty >>= fun ty ->
    invert_add_lambdas ctx x (argn-1) varl (mk_Lam dloc empty (Some ty) t)
  | [] -> assert false

let invert ctx x ts_var args_var t =
  let argn,varl = List.fold_left (fun (n,l) v -> (n+1,v::l)) (0,List.rev ts_var) args_var in
  invert_term x varl 0 t >>= fun t' ->
  invert_add_lambdas ctx x argn varl t'

let meta_inst sg side (ctx,lop,rop) = let (active,passive) = match side with | LEFT -> lop,rop | RIGHT -> rop,lop in
  begin match active with
    | Extra (_,Pretyped,_) -> return (active,[])
    | App (Extra (_,Pretyped,_) as m,a,args) -> return (m,a::args)
    | _ -> zero Not_Applicable
    end >>= fun (m,args) -> match m with
    | Extra (lc,Pretyped,Meta(s,n,ts)) -> begin match Opt.fold (fun vl -> function | (_,DB (_,_,n)) -> Some (n::vl) | _ -> None) [] ts with
        | Some ts_var -> begin match Opt.fold (fun vl -> function | DB (_,_,n) -> Some (n::vl) | _ -> None) [] args with
            | Some args_var -> return (lc,s,n,ts_var,args_var)
            | None -> zero Not_Applicable
            end
        | None -> zero Not_Applicable
        end >>= fun (lc,s,n,ts_var,args_var) ->
        whnf sg passive >>= fun passive ->
        invert ctx n ts_var args_var passive >>= fun inst ->
        refine sg lc s n inst
    | _ -> zero Not_Applicable


(** meta-deldeps *)

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
    | App (Extra (lc,Pretyped,Meta(s,n,ts)), a, args) -> return (lc,s,n,ts,a::args)
    | Extra (lc,Pretyped,Meta(s,n,ts)) -> return (lc,s,n,ts,[])
    | _ -> zero Not_Applicable
    end >>= fun (lc,s,n,ts,args) ->
  let clean,filter = filter_unique_vars ts args in
  if clean then zero Not_Applicable else return () >>
  narrow_meta lc s n filter >>
  meta_delta side

(** Rule application *)

let first_applicable l = let rec aux = function
  | [m] -> m
  | m::l -> plus m (function | Not_Applicable -> aux l | e -> zero e)
  | [] -> zero Not_Applicable
  in once (aux l)

let fully_backtracking l = let rec aux = function
  | [m] -> m
  | m::l -> plus m (fun _ -> aux l)
  | [] -> zero Not_Applicable
  in aux l

let rec solve_pair sg p = fully_backtracking
  [ pair_convertible sg
  ; first_applicable [ meta_delta RIGHT; meta_delta LEFT ]
  ; first_applicable [ meta_same_same sg p; meta_same sg p ]
  ; meta_inst sg RIGHT p; meta_fo RIGHT p; meta_deldeps RIGHT p
  ; meta_inst sg LEFT  p; meta_fo LEFT  p; meta_deldeps LEFT  p
  ; decompose
  ; step_reduce sg RIGHT; step_reduce sg LEFT]

let rec solve sg = normalize >> (*effectful (fun () -> Printf.printf "Solve step for ") >> pp_state >>*)
  inspect >>= function
  | Some p -> solve_pair sg p >> solve sg
  | None -> return ()

let guard sg (ctx,te,ty) (_,ty_exp,_) = are_convertible sg ty ty_exp >>= function
  | true -> return (ctx,te,ty_exp)
  | false -> add_guard sg (get_loc te) ctx ty ty_exp te >>= fun te' ->
      plus (once (solve sg) >> return (ctx,te',ty_exp))
           (function | Not_Unifiable -> zero (ConvertibilityError (te,ctx,ty_exp,ty)) | e -> zero e)

let guard_sort sg jdg = let (ctx,te,ty) = jdg in whnf sg ty >>= function
  | Kind | Type _ -> return jdg
  | _ -> let lc = get_loc te in new_meta ctx lc (hstring "Sort") MSort >>= fun ms ->
      add_guard sg lc ctx ty ms te >>= fun te' ->
      plus (once (solve sg) >> return (ctx,te',ms))
           (function | Not_Unifiable -> zero (SortExpected (te, ctx, ty)) | e -> zero e)

let reject_kind sg jdg = let (ctx,te,ty) = jdg in whnf sg ty >>= function
  | Kind -> zero (InexpectedKind (te, ctx))
  | Extra (lc,Pretyped,Meta(s,n,_)) -> meta_constraint lc s n >>= fun _ -> return ()
  | _ -> return ()

