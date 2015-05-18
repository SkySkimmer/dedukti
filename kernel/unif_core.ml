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
  | CannotSolveDeferred
  | Not_Unifiable
  | Not_Applicable

exception TypingError of typing_error

type mdecl = context*int*mkind

type pair = context*term*term

type problem = { cpt:int; decls:mdecl list; sigma:S.t; pairs: pair list; }

let fresh = {cpt=0; decls=[]; sigma=S.identity; pairs=[]; }

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

(* monad basic operations end here *)

let apply pb t = S.apply pb.sigma t

let add_pair sg p = modify (fun pb -> {pb with pairs=p::pb.pairs})

let new_meta ctx lc s k = get >>= fun pb ->
  let substj = List.mapi (fun i (_,x,_) -> x,mk_DB dloc x i) ctx in
  let mj = mk_Meta lc s pb.cpt substj in
  set { pb with cpt=pb.cpt+1; decls=(ctx,pb.cpt,k)::pb.decls } >>= fun () ->
  return mj

let meta_constraint = function
  | Meta (lc,s,n,_) -> assert false
  | _ -> assert false


let whnf sg t = get >>= fun pb -> return (S.whnf sg pb.sigma t)

(*
This is only used in the pseudo-unification step of pattern checking.
TODO(future work): If possible we would like to use unification instead.
*)
let simpl t = get >>= fun pb -> return (apply pb t)


(* returns Nothing if there are no (unsolved) disagreement pairs *)
let inspect = get >>= function
  | { pairs = p::_ } -> return (Some p)
  | _ -> return None


type ('a,'b) sum =
  | Inl of 'a
  | Inr of 'b
(* pair_conv (Inl t) checks if the left term of the current pair is convertible with t, then replaces it with t, else fails *)
let pair_conv sg o = assert false

(*
Decompose the pair according to the common constructor of the terms:
- Psi, App c ts, App c' ts' -> Psi,c,c' and Psi,ts,ts' (fails if |ts| <> |ts'|)
- Psi,Pi a b, Pi a' b' -> Psi,a,a' and a::Psi,b,b'
- Psi,Type,Type -> []
- etc
*)

let pair_decompose = get >>= fun s -> match s.pairs with
  | (ctx,t1,t2)::rem -> begin match t1,t2 with
      | Kind, Kind | Type _, Type _ -> return []
      | _, _ -> zero Not_Unifiable
      end >>= fun l -> set {s with pairs = List.append l rem}
  | [] -> zero Not_Applicable

(* Tries to unfold the meta at the head of the left (resp right) term *)
let pair_meta_unfold side = assert false


