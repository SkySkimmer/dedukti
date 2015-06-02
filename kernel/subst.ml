open Basics
open Term

let rec apply_db : type a. (int -> a term -> a term) -> int -> a term -> a term = fun aux q -> function
  | Kind | Type _ | Const _ as t -> t
  | DB _ as t -> aux q t
  | App (f,a,args) -> mk_App (apply_db aux q f) (apply_db aux q a) (List.map (apply_db aux q) args)
  | Lam (lc,x,a,b) -> mk_Lam lc x (map_opt (apply_db aux q) a) (apply_db aux (q+1) b)
  | Pi (lc,x,a,b) -> mk_Pi lc x (apply_db aux q a) (apply_db aux (q+1) b)
  | Extra (_,Untyped,_) as t -> t
  | Extra (lc,Pretyped,Meta(s,n,ts)) -> mk_Meta lc s n (List.map (fun (x,t) -> x,apply_db aux q t) ts)
  | Extra (_,Typed,ex) -> ex.exfalso

let rec shift_rec (r:int) (k:int) (t:'a term) = apply_db (fun k -> function
  | DB (lc,x,n) as t -> if n<k then t else mk_DB lc x (n+r)
  | _ -> assert false) k t

let shift r t = shift_rec r 0 t

exception UnshiftExn

let unshift q (te:'a term) : 'a term = apply_db (fun k -> function
  | DB (_,_,n) as t when n<k -> t
  | DB (lc,x,n) ->
      if n-q-k >= 0 then mk_DB lc x (n-q-k)
      else raise UnshiftExn
  | _ -> assert false) 0 te

let rec psubst_l (args:('a term Lazy.t) LList.t) (k:int) (t:'a term) : 'a term =
  let nargs = args.LList.len in
  apply_db (fun k -> function
    | DB (lc,x,n) when (n >= (k+nargs)) -> mk_DB lc x (n-nargs)
    | DB (_,_,n) as t when (n < k) -> t
    | DB (_,_,n) (* (k<=n<(k+nargs)) *) ->
        shift k ( Lazy.force (LList.nth args (n-k)) )
    | _ -> assert false) k t

let subst (te:'a term) (u:'a term) =
  apply_db (fun k -> function
    | DB (lc,x,n) as t ->
        if n = k then shift k u
        else if n>k then mk_DB lc x (n-1)
        else (*n<k*) t
    | _ -> assert false) 0 te

module S =
struct
  type 'a t = (ident*'a term) IntMap.t

  let identity = IntMap.empty

  let apply (sigma:'a t) (te:'a term) (q:int) : 'a term =
    apply_db (fun q -> function
      | DB (_,_,k) as t when k<q -> t
      | DB (_,_,k) as t (*when k>=q*) ->
          begin
            try shift q (snd (IntMap.find (k-q) sigma))
            with Not_found -> t
          end
      | _ -> assert false) q te

  let occurs (n:int) (te:'a term) : bool =
    let rec aux : type a. int -> a term -> bool = fun q -> function
      | Kind | Type _ | Const _ -> false
      | DB (_,_,k) when k<q -> false
      | DB (_,_,k) (*when k>=q*) -> ( k-q == n )
      | App (f,a,args) -> List.exists (aux q) (f::a::args)
      | Lam (_,_,None,te) -> aux (q+1) te
      | Lam (_,_,Some ty,te) -> aux q ty || aux (q+1) te
      | Pi (_,_,a,b) -> aux q a || aux (q+1) b
      | Extra (_,Untyped,_) -> false
      | Extra (_,Pretyped,Meta(_,_,ts)) -> List.exists (fun (_,t) -> aux q t) ts
      | Extra (_,Typed,ex) -> ex.exfalso
    in aux 0 te

  let add (sigma:'a t) (x:ident) (n:int) (t:'a term) : 'a t option =
    assert ( not ( IntMap.mem n sigma ) );
    if occurs 0 t then None
    else Some (IntMap.add n (x,t) sigma)

  let merge s1 s2 =
    let aux _ b1 b2 = match b1, b2 with
      | None, b | b, None -> b
      | Some b1, Some b2 -> assert false (*FIXME*)
    in
      IntMap.merge aux s1 s2

  let is_identity = IntMap.is_empty

  let pp (out:out_channel) (sigma:'a t) : unit =
    IntMap.iter (fun i (x,t) ->
        Printf.fprintf out "( %a[%i] = %a )" pp_ident x i pp_term t
      ) sigma
end
