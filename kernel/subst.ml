open Basics
open Term

let rec shift_rec (type a) (kind:a tkind) (r:int) (k:int) : a term -> a term = function
  | DB (_,x,n) as t -> if n<k then t else mk_DB dloc x (n+r)
  | App (f,a,args) ->
      mk_App (shift_rec kind r k f) (shift_rec kind r k a) (List.map (shift_rec kind r k) args )
  | Lam (_,x,_,f) -> mk_Lam dloc x None (shift_rec kind r (k+1) f)
  | Pi  (_,x,a,b) -> mk_Pi dloc x (shift_rec kind r k a) (shift_rec kind r (k+1) b)
  | Extra (_,ex) -> begin match kind with
      | Untyped -> mk_Extra dloc ex
      | Pretyped -> let { meta=(s,n,ts) } = ex in
          mk_Extra dloc (s,n,List.map (fun (x,t) -> x,shift_rec Pretyped r k t) ts)
      | Typed -> ex.exfalso
      end
  | Kind | Type _ | Const _ as t -> t

let shift kind r t = shift_rec kind r 0 t

exception UnshiftExn
let unshift (type a) (kind:a tkind) q (te:a term) =
  let rec aux k = function
  | DB (_,_,n) as t when n<k -> t
  | DB (l,x,n) ->
      if n-q-k >= 0 then mk_DB l x (n-q-k)
      else raise UnshiftExn
  | App (f,a,args) -> mk_App (aux k f) (aux k a) (List.map (aux k) args)
  | Lam (l,x,None,f) -> mk_Lam l x None (aux (k+1) f)
  | Lam (l,x,Some a,f) -> mk_Lam l x (Some (aux k a)) (aux (k+1) f)
  | Pi  (l,x,a,b) -> mk_Pi l x (aux k a) (aux (k+1) b)
  | Extra (l,ex) as t -> begin match kind with
      | Pretyped -> let { meta=(s,n,ts) } = ex in
          mk_Extra l (s,n,List.map (fun (x,t) -> x,aux k t) ts)
      | Untyped | Typed -> t
      end
  | Type _ | Kind | Const _ as t -> t
  in
    aux 0 te

let rec psubst_l (type a) (kind:a tkind) (args:(a term Lazy.t) LList.t) (k:int) (t:a term) : a term =
  let nargs = args.LList.len in
  match t with
    | Type _ | Kind | Const _ -> t
    | DB (_,x,n) when (n >= (k+nargs))  -> mk_DB dloc x (n-nargs)
    | DB (_,_,n) when (n < k)           -> t
    | DB (_,_,n) (* (k<=n<(k+nargs)) *) ->
        shift kind k ( Lazy.force (LList.nth args (n-k)) )
    | Lam (_,x,_,b)                     ->
        mk_Lam dloc x None (psubst_l kind args (k+1) b)
    | Pi  (_,x,a,b)                     ->
        mk_Pi dloc x (psubst_l kind args k a) (psubst_l kind args (k+1) b)
    | App (f,a,lst)                     ->
        mk_App (psubst_l kind args k f) (psubst_l kind args k a)
          (List.map (psubst_l kind args k) lst)
    | Extra (_,ex) as t -> begin match kind with
        | Pretyped -> let { meta=(s,n,ts) } = ex in
            mk_Extra dloc (s,n,List.map (fun (x,t) -> x,psubst_l kind args k t) ts)
        | Untyped | Typed -> t
        end

let subst (type a) (kind:a tkind) (te:a term) (u:a term) =
  let rec aux k = function
    | DB (l,x,n) as t ->
        if n = k then shift kind k u
        else if n>k then mk_DB l x (n-1)
        else (*n<k*) t
    | Type _ | Kind | Const _ as t -> t
    | Lam (_,x,_,b) -> mk_Lam dloc x None (aux (k+1) b)
    | Pi  (_,x,a,b) -> mk_Pi dloc  x (aux k a) (aux(k+1) b)
    | App (f,a,lst) -> mk_App (aux k f) (aux k a) (List.map (aux k) lst)
    | Extra (_,ex) as t -> begin match kind with
        | Pretyped -> let { meta=(s,n,ts) } = ex in
            mk_Meta dloc (s,n,List.map (fun (x,t) -> x,aux k t) ts)
        | Untyped | Typed -> t
        end
  in aux 0 te


module S =
struct
  type 'a t = 'a tkind*(ident*'a term) IntMap.t
  let identity k = k,IntMap.empty

  let apply (type a) (kind,sigma:a t) (te:a term) (q:int) : a term =
    let rec aux q = function
      | Kind | Type _ | Const _ as t -> t
      | DB (_,_,k) as t when k<q -> t
      | DB (_,_,k) as t (*when k>=q*) ->
          begin
            try shift kind q (snd (IntMap.find (k-q) sigma))
            with Not_found -> t
          end
      | App (f,a,args) -> mk_App (aux q f) (aux q a) (List.map (aux q) args)
      | Lam (l,x,Some ty,te) -> mk_Lam l x (Some (aux q ty)) (aux (q+1) te)
      | Lam (l,x,None,te) -> mk_Lam l x None (aux (q+1) te)
      | Pi (l,x,a,b) -> mk_Pi l x (aux q a) (aux (q+1) b)
      | Extra (l,ex) as t -> begin match kind with
          | Pretyped -> let { meta=(s,n,ts) } = ex in
              mk_Extra l (s,n,List.map (fun (x,t) -> x,aux q t) ts)
          | Untyped | Typed -> t
          end
    in
      aux q te

  let occurs (type a) (kind:a tkind) (n:int) (te:a term) : bool =
    let rec aux q = function
      | Kind | Type _ | Const _ -> false
      | DB (_,_,k) when k<q -> false
      | DB (_,_,k) (*when k>=q*) -> ( k-q == n )
      | App (f,a,args) -> List.exists (aux q) (f::a::args)
      | Lam (_,_,None,te) -> aux (q+1) te
      | Lam (_,_,Some ty,te) -> aux q ty || aux (q+1) te
      | Pi (_,_,a,b) -> aux q a || aux (q+1) b
      | Extra (_,ex) -> begin match kind with
          | Pretyped -> let { meta=(_,_,ts) } = ex in
              List.exists (fun (_,t) -> aux q t) ts
          | Untyped | Typed -> false
          end
    in aux 0 te

  let add (kind,sigma:'a t) (x:ident) (n:int) (t:'a term) : 'a t option =
    assert ( not ( IntMap.mem n sigma ) );
    if occurs kind 0 t then None
    else Some (kind, IntMap.add n (x,t) sigma)

  let merge (kind,s1) (_,s2) =
    let aux _ b1 b2 = match b1, b2 with
      | None, b | b, None -> b
      | Some b1, Some b2 -> assert false (*FIXME*)
    in
      kind,IntMap.merge aux s1 s2

  let is_identity (_,s) = IntMap.is_empty s

  let pp (out:out_channel) (kind,sigma:'a t) : unit =
    IntMap.iter (fun i (x,t) ->
        Printf.fprintf out "( %a[%i] = %a )" pp_ident x i (pp_term kind) t
      ) sigma
end
