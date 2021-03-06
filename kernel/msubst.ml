open Basic
open Term

let subst_l l n t = Subst.psubst_l (LList.of_list (List.map Lazy.from_val l)) n t

type t = pretyped term IntMap.t*IntSet.t

let identity = IntMap.empty,IntSet.empty

let is_identity (sigma,guards) = IntMap.is_empty sigma && IntSet.is_empty guards

let meta_mem (sigma,_) n = IntMap.mem n sigma

let meta_add (sigma,guards:t) (n:int) (t:pretyped term) : t =
  assert ( not ( IntMap.mem n sigma ) );
  IntMap.add n t sigma,guards

let guard_mem (_,guards:t) n = IntSet.mem n guards

let guard_add (sigma,guards) n = sigma,IntSet.add n guards

let extra_val (sigma,guards:t) : pretyped -> pretyped term option = function
  | Meta(_,n,ts) -> begin
    try let te0 = IntMap.find n sigma in
      let subst1 = List.map snd ts in
      let te = subst_l subst1 0 te0 in
      Some te
    with | Not_found -> None
    end
  | Guard(n,_,t) -> if IntSet.mem n guards then Some t else None

let apply (sigma:t) (t:pretyped term) : pretyped term =
  let rec aux = function
    | Kind | Type _ | Const _ | DB _ as t -> t
    | App (f,a,args) -> mk_App (aux f) (aux a) (List.map (aux) args)
    | Lam (l,x,Some a,te) -> mk_Lam l x (Some (aux a)) (aux te)
    | Lam (l,x,None,te) -> mk_Lam l x None (aux te)
    | Pi (l,x,a,b) -> mk_Pi l x (aux a) (aux b)
    | Extra (lc,Pretyped,ex) -> begin match extra_val sigma ex with
        | Some mt' -> aux mt'
        | None -> begin match ex with
            | Meta (s,n,ts) -> mk_Meta lc s n (List.map (fun (x,t) -> x,aux t) ts)
            | Guard (n,ls,t) -> mk_Guard lc n (List.map (fun (x,t) -> x,aux t) ls) (aux t)
            end
        end
  in if is_identity sigma then t else aux t

let to_ground (sigma:t) (t:pretyped term) : typed term =
  let rec aux : pretyped term -> typed term = function
    | Kind -> mk_Kind
    | Type l -> mk_Type l
    | DB (l,x,n) -> mk_DB l x n
    | Const (l,m,v) -> mk_Const l m v
    | App (f,a,args) -> mk_App (aux f) (aux a) (List.map aux args)
    | Lam (l,x,Some a,te) -> mk_Lam l x (Some (aux a)) (aux te)
    | Lam (l,x,None,te) -> mk_Lam l x None (aux te)
    | Pi (l,x,a,b) -> mk_Pi l x (aux a) (aux b)
    | Extra (lc,Pretyped,ex) -> begin match extra_val sigma ex with
        | Some mt' -> aux mt'
        | None -> let open Typing in begin match ex with
            | Meta (s,n,_) -> raise (TypingError (Not_Inferrable (lc,s,n)))
            | Guard (n,_,_) -> raise (TypingError (Remaining_Guard (lc,n)))
            end
        end
    in aux t

let rec head_delta sigma = function
  | Extra (_,Pretyped,ex) as mt -> begin match extra_val sigma ex with
      | Some mt' -> head_delta sigma mt'
      | None -> mt
      end
  | App (Extra (_,Pretyped,ex),a,args) as t -> begin match extra_val sigma ex with
      | Some mt' -> head_delta sigma (mk_App mt' a args)
      | None -> t
      end
  | t -> t

let rec whnf sg sigma t = match Reduction.whnf sg t with
  | Extra (_,Pretyped,ex) as mt -> begin match extra_val sigma ex with
      | Some mt' -> whnf sg sigma mt'
      | None -> mt
      end
  | App (Extra (_,Pretyped,ex), a, al) as t0 -> begin match extra_val sigma ex with
      | Some mt' -> whnf sg sigma (mk_App mt' a al)
      | None -> t0
      end
  | t0 -> t0

let rec add_to_list2 l1 l2 lst =
  match l1, l2 with
    | [], [] -> Some lst
    | s1::l1, s2::l2 -> add_to_list2 l1 l2 ((s1,s2)::lst)
    | _,_ -> None

let rec are_convertible_lst sg sigma : (pretyped term*pretyped term) list -> bool = function
  | [] -> true
  | (t1,t2)::lst ->
    begin
      match ( if term_eq t1 t2 then Some lst
        else
          match whnf sg sigma t1,whnf sg sigma t2 with
          | Kind, Kind | Type _, Type _ -> Some lst
          | Const (_,m,v), Const (_,m',v') when ( ident_eq v v' && ident_eq m m' ) -> Some lst
          | DB (_,_,n), DB (_,_,n') when ( n==n' ) -> Some lst
          | App (f,a,args), App (f',a',args') ->
            add_to_list2 args args' ((f,f')::(a,a')::lst)
          | Lam (_,_,_,b), Lam (_,_,_,b') -> Some ((b,b')::lst)
          | Pi (_,_,a,b), Pi (_,_,a',b') -> Some ((a,a')::(b,b')::lst)
          | Extra (_,Pretyped,Meta(_,n,ts)), Extra (_,Pretyped,Meta(_,n',ts')) when ( n==n' ) ->
              add_to_list2 (List.map snd ts) (List.map snd ts') lst
          | t1, t2 -> None
      ) with
      | None -> false
      | Some lst2 -> are_convertible_lst sg sigma lst2
    end

let are_convertible sg sigma t1 t2 = are_convertible_lst sg sigma [t1,t2]

let normalize sigma = IntMap.map (apply sigma) (fst sigma),snd sigma

let pp out (sigma,guards) =
  IntMap.iter
    (fun i t -> Printf.fprintf out "( ?_%i |-> %a )\n" i pp_term t)
    sigma;
  IntSet.iter
    (fun i -> Printf.fprintf out "( #%i x |-> x )\n" i)
    guards

