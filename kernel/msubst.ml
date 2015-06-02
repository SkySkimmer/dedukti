open Basics
open Term

type t = pretyped term IntMap.t

let identity = IntMap.empty

let subst_l l n t = Subst.psubst_l (LList.of_list (List.map Lazy.from_val l)) n t

let meta_raw (sigma:t) n = try Some (IntMap.find n sigma) with | Not_found -> None

let meta_val (sigma:t) : pretyped term -> pretyped term option = function
  | Extra (_,Pretyped,{meta=(_,n,ts)}) -> begin
    try let te0 = IntMap.find n sigma in
      let subst1 = List.map snd ts in
      let te = subst_l subst1 0 te0 in
      Some te
    with | Not_found -> None
    end
  | _ -> None

let apply (sigma:t) (t:pretyped term) : pretyped term =
  let rec aux = function
    | Kind | Type _ | Const _ | DB _ as t -> t
    | App (f,a,args) -> mk_App (aux f) (aux a) (List.map (aux) args)
    | Lam (l,x,Some a,te) -> mk_Lam l x (Some (aux a)) (aux te)
    | Lam (l,x,None,te) -> mk_Lam l x None (aux te)
    | Pi (l,x,a,b) -> mk_Pi l x (aux a) (aux b)
    | Extra (lc,Pretyped,{meta=(s,n,ts)}) as mt -> begin match meta_val sigma mt with
        | Some mt' -> aux mt'
        | None -> mk_Meta lc s n (List.map (fun (x,t) -> x,aux t) ts)
        end
  in if IntMap.is_empty sigma then t else aux t

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
    | Extra (lc,Pretyped,{meta=(s,n,ts)}) as mt -> begin match meta_val sigma mt with
        | Some mt' -> aux mt'
        | None -> let open Typing in raise (TypingError (Not_Inferrable (lc,s)))
        end
    in aux t

let rec whnf sg sigma t = match Reduction.whnf sg t with
  | Extra (_,Pretyped,_) as mt -> begin match meta_val sigma mt with
      | Some mt' -> whnf sg sigma mt'
      | None -> mt
      end
  | App (Extra (_,Pretyped,_) as mt, a, al) as t0 -> begin match meta_val sigma mt with
      | Some mt' -> whnf sg sigma (mk_App mt' a al)
      | None -> t0
      end
  | t0 -> t0

let mem sigma n = IntMap.mem n sigma

let add (sigma:t) (n:int) (t:pretyped term) : t =
  assert ( not ( IntMap.mem n sigma ) );
  IntMap.add n t sigma

let normalize sigma = IntMap.map (apply sigma) sigma

let pp out sigma =
  IntMap.iter
    (fun i t -> Printf.fprintf out "( ?_%i |-> %a )\n" i pp_term t)
    sigma

