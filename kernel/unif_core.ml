open Basics
open Term
open Monads

module S = Msubst

type typing_error =
  | KindIsNotTypable
  | ConvertibilityError of term*context*term*term
  | VariableNotFound of loc*ident*int*context
  | SortExpected of term*context*term
  | ProductExpected of term*context*term
  | InexpectedKind of term*context
  | DomainFreeLambda of loc
  | MetaInKernel of loc*ident
  | InferSortMeta of loc*ident
  | UnknownMeta of loc*ident*int
  | ConvRule_Bad of term*term
  | DecomposeDomainFreeLambdas
  | CannotSolveDeferred
  | Not_Unifiable
  | Not_Applicable

exception TypingError of typing_error

type mdecl = context*mkind

type pair = context*term*term

type problem = { cpt:int; decls:mdecl IntMap.t; sigma:S.t; pairs: pair list; }

let fresh = {cpt=0; decls=IntMap.empty; sigma=S.identity; pairs=[]; }

(* A monad with effects, backtracking and restricted state operations *)
module Types = struct
  type err = typing_error
  type state = problem
end
module M0 = BacktrackF(IO)(Types)
module M = StateF(M0)(Types)
include M

include MonadF(M)

include M.EffectT(struct
  type 'a t = 'a M0.t
  include M0.EffectT(IO)
end)

include M.BacktrackT(M0)

let run m = match IO.run (M0.run (M.run m fresh)) () with
  | Nil e -> raise (TypingError e)
  | Cons (r,_) -> r

let raise e = effectful (fun () -> raise e)

(* monad basic operations end here *)

let apply pb t = S.apply pb.sigma t

let add_pair sg p = modify (fun pb -> {pb with pairs=p::pb.pairs})

let new_meta ctx lc s k = get >>= fun pb ->
  let substj = List.mapi (fun i (_,x,_) -> x,mk_DB dloc x i) ctx in
  let mj = mk_Meta lc s pb.cpt substj in
  set { pb with cpt=pb.cpt+1; decls=IntMap.add pb.cpt (ctx,k) pb.decls } >>= fun () ->
  return mj

let get_decl decls n = try Some (IntMap.find n decls) with | Not_found -> None

let set_decl n d = modify (fun pb -> { pb with decls=IntMap.add n d pb.decls })

let set_meta n t = modify (fun pb -> { pb with sigma=S.add pb.sigma n t })

let meta_constraint = function
  | Meta (lc,s,n,_) -> get >>= fun pb -> begin match get_decl pb.decls n with
      | Some (ctx,MTyped ty) -> return (ctx,ty)
      | Some (ctx,MType) -> new_meta ctx lc s MSort >>= fun mk ->
          set_decl n (ctx,MTyped mk) >>= fun () -> return (ctx,mk)
      | Some (ctx,MSort) -> set_decl n (ctx,MTyped mk_Kind) >>= fun () ->
          set_meta n (mk_Type dloc) >>= fun () -> return (ctx,mk_Kind)
      | None -> raise (TypingError (UnknownMeta (lc,s,n)))
      end
  | _ -> assert false


let whnf sg t = get >>= fun pb -> return (S.whnf sg pb.sigma t)

(*
This is only used in the pseudo-unification step of pattern checking.
TODO(future work): If possible we would like to use unification instead.
*)
let simpl t = get >>= fun pb -> return (apply pb t)


(* returns None if there are no (unsolved) disagreement pairs *)
let inspect = get >>= function
  | { pairs = p::_ } -> return (Some p)
  | _ -> return None

(* f may do backtracking but may not modify the state *)
let pair_modify f = get >>= fun pb -> match pb.pairs with
  | p::rem -> f p >>= fun l -> set { pb with pairs=List.append l rem }
  | _ -> zero Not_Applicable

type side = LEFT | RIGHT

let pair_modify_side side f = pair_modify (fun (ctx,lop,rop) -> match side with
  | LEFT -> f lop >>= fun lop -> return [ctx,lop,rop]
  | RIGHT -> f rop >>= fun rop -> return [ctx,lop,rop])


(* Tries to unfold the meta at the head of the left (resp right) term *)
let meta_delta side = let delta t = get >>= fun pb -> begin match t with
  | Meta _ as m -> begin match S.meta_val pb.sigma m with
      | Some m' -> return m'
      | None -> zero Not_Applicable
      end
  | App (Meta _ as m,a,args) -> begin match S.meta_val pb.sigma m with
      | Some m' -> return (mk_App m' a args)
      | None -> zero Not_Applicable
      end
  | _ -> zero Not_Applicable
  end in pair_modify_side side delta

let step_reduce sg side = let step t = match Reduction.one_step sg t with
  | Some t' -> return t'
  | None -> zero Not_Applicable
  in pair_modify_side side step

(*
Decompose the pair according to the common constructor of the terms:
- Psi, App c ts, App c' ts' -> Psi,c,c' and Psi,ts,ts' (fails if |ts| <> |ts'|)
- Psi,Pi a b, Pi a' b' -> Psi,a,a' and a::Psi,b,b'
- Psi,Type,Type -> []
- etc
*)

let decompose = let pair_decompose (ctx,t1,t2) = match t1,t2 with
  | Kind, Kind | Type _, Type _ -> return []
  | Const (_,m,v), Const (_,m',v') when ( ident_eq v v' && ident_eq m m' ) -> return []
  | DB (_,_,n), DB (_,_,n') when (n=n') -> return []
  | App (f,a,args), App (f',a',args') ->
    begin match try Some (List.map2 (fun t1 t2 -> (ctx,t1,t2)) (f::a::args) (f'::a'::args')) with | Invalid_argument _ -> None with
        | Some l -> return l
        | None -> zero Not_Applicable
        end
  | Lam (_,x,Some a,b), Lam (_,_,Some a',b') -> return [(ctx,a,a');((dloc,x,a)::ctx,b,b')]
  | Lam (_,x,Some a,b), Lam (_,_,None,b') -> return [(dloc,x,a)::ctx,b,b']
  | Lam (_,_,None,b), Lam (_,y,Some a',b') -> return [((dloc,y,a')::ctx,b,b')]
  | Lam _, Lam _ -> zero DecomposeDomainFreeLambdas
  | Pi (_,x,a,b), Pi (_,_,a',b') -> return [(ctx,a,a');((dloc,x,a)::ctx,b,b')]
  | Meta (_,_,n,ts), Meta (_,_,n',ts') when ( n==n' ) -> effectful (fun () -> failwith "TODO: decompose meta pair")
  | _, _ -> zero Not_Unifiable
  in pair_modify pair_decompose

let meta_same_same = pair_modify (fun (ctx,lop,rop) -> match lop,rop with
  | Meta (_,_,n,ts), Meta (_,_,n',ts') when (n=n') ->
    let b = try List.for_all2 (fun (_,t1) (_,t2) -> term_eq t1 t2) ts ts' with | Invalid_argument _ -> false in
      if b then return [] else zero Not_Applicable
  | App (Meta (_,_,n,ts),a,args), App (Meta (_,_,n',ts'),a',args') when (n=n') ->
    let b = try List.for_all2 (fun (_,t1) (_,t2) -> term_eq t1 t2) ts ts' with | Invalid_argument _ -> false in
      if b then match try Some (List.map2 (fun t1 t2 -> ctx,t1,t2) (a::args) (a'::args')) with | Invalid_argument _ -> None with
          | Some l -> return l
          | None -> zero Not_Applicable
          else zero Not_Applicable
  | _,_ -> zero Not_Applicable)

