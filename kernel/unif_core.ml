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


type ('a,'b) sum =
  | Inl of 'a
  | Inr of 'b
(* pair_conv (Inl t) (resp Inr t) checks if the left (resp right) term of the current pair is convertible with t, then replaces it with t, else fails *)
let pair_conv sg o = get >>= fun pb -> match pb.pairs with
  | (ctx,lop,rop)::rem -> begin match o with
      | Inl t -> if Reduction.are_convertible sg t lop then return (ctx,t,rop) else zero (ConvRule_Bad (t,lop))
      | Inr t -> if Reduction.are_convertible sg t rop then return (ctx,lop,t) else zero (ConvRule_Bad (t,rop))
      end >>= fun (ctx,lop,rop) -> set { pb with pairs=(ctx,lop,rop)::rem }
  | _ -> zero Not_Applicable

(*
Decompose the pair according to the common constructor of the terms:
- Psi, App c ts, App c' ts' -> Psi,c,c' and Psi,ts,ts' (fails if |ts| <> |ts'|)
- Psi,Pi a b, Pi a' b' -> Psi,a,a' and a::Psi,b,b'
- Psi,Type,Type -> []
- etc
*)

let pair_decompose = get >>= fun pb -> match pb.pairs with
  | (ctx,t1,t2)::rem -> begin match t1,t2 with
      | Kind, Kind | Type _, Type _ -> return []
      | Const (_,m,v), Const (_,m',v') when ( ident_eq v v' && ident_eq m m' ) -> return []
      | DB (_,_,n), DB (_,_,n') when (n=n') -> return []
      | App (f,a,args), App (f',a',args') ->
        begin match try Some (List.rev_map2 (fun t1 t2 -> (ctx,t1,t2)) (f::a::args) (f'::a'::args')) with | Invalid_argument _ -> None with
            | Some l -> return l
            | None -> zero Not_Applicable
            end
      | Lam (_,x,Some a,b), Lam (_,_,Some a',b') -> return [((dloc,x,a)::ctx,b,b');(ctx,a,a')]
      | Lam (_,x,Some a,b), Lam (_,_,None,b') -> return [(dloc,x,a)::ctx,b,b']
      | Lam (_,_,None,b), Lam (_,y,Some a',b') -> return [((dloc,y,a')::ctx,b,b')]
      | Lam _, Lam _ -> zero DecomposeDomainFreeLambdas
      | Pi (_,x,a,b), Pi (_,_,a',b') -> return [((dloc,x,a)::ctx,b,b');(ctx,a,a')]
      | Meta (_,_,n,ts), Meta (_,_,n',ts') when ( n==n' ) -> effectful (fun () -> failwith "TODO: decompose meta pair")
      | _, _ -> zero Not_Unifiable
      end >>= fun l -> set {pb with pairs = List.rev_append l rem}
  | [] -> zero Not_Applicable

(* Tries to unfold the meta at the head of the left (resp right) term *)
let pair_meta_unfold side = assert false


