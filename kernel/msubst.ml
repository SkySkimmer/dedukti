open Basics
open Term

module IntMap = Map.Make(
struct
  type t = int
  let compare = compare
end)

module S = struct
  type t = term IntMap.t
  
  let identity = IntMap.empty

  let subst_l l n t = Subst.psubst_l (LList.of_list (List.map Lazy.from_val l)) n t

  let meta_val (sigma:t) : term -> term option = function
    | Meta (_,_,n,ts) -> begin
      try let te0 = IntMap.find n sigma in
        let subst1 = List.map snd ts in Some (subst_l subst1 0 te0)
      with | Not_found -> None
      end
    | _ -> None

  let rec apply (sigma:t) : term -> term = function
    | Kind | Type _ | Const _ | Hole _ | DB _ as t -> t
    | App (f,a,args) -> mk_App (apply sigma f) (apply sigma a) (List.map (apply sigma) args)
    | Lam (l,x,Some a,te) -> mk_Lam l x (Some (apply sigma a)) (apply sigma te)
    | Lam (l,x,None,te) -> mk_Lam l x None (apply sigma te)
    | Pi (l,x,a,b) -> mk_Pi l x (apply sigma a) (apply sigma b)
    | Meta (lc,s,n,ts) as mt -> begin match meta_val sigma mt with
        | Some mt' -> apply sigma mt'
        | None -> mk_Meta lc s n (List.map (fun (x,t) -> x,apply sigma t) ts)
      end

  let rec whnf sg sigma t = match Reduction.whnf sg t with
    | Meta _ as mt -> begin match meta_val sigma mt with
        | Some mt' -> whnf sg sigma mt'
        | None -> mt
        end
    | App (Meta _ as mt, a, al) as t0 -> begin match meta_val sigma mt with
        | Some mt' -> whnf sg sigma (mk_App mt' a al)
        | None -> t0
        end
    | t0 -> t0

  let add (sigma:t) (n:int) (t:term) : t =
    assert ( not ( IntMap.mem n sigma ) );
    IntMap.add n t sigma
  
  let pp out sigma =
    IntMap.iter
      (fun i t -> Printf.fprintf out "( ?_%i -> %a )" i pp_term t)
      sigma
end
