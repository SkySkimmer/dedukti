open Basics
open Term
open Rule
open Monads

type typing_error =
  | KindIsNotTypable
  | ConvertibilityError : 'a term*'b context*'c term*'d term -> typing_error
  | VariableNotFound : loc*ident*int*'a context -> typing_error
  | SortExpected : 'a term*'b context*'c term -> typing_error
  | ProductExpected : 'a term*'b context*'c term -> typing_error
  | InexpectedKind : 'a term*'b context -> typing_error
  | DomainFreeLambda of loc
  | Not_Inferrable of loc*ident*int
  | Remaining_Guard of loc*int
  | UnknownMeta of loc*ident*int
  | UnknownGuard of loc*int
  | DecomposeDomainFreeLambdas
  | CannotSolveDeferred
  | Not_Unifiable
  | Not_Applicable

exception TypingError of typing_error

let coc = ref false

type 'a judgment0 = { ctx:'a; te:typed term; ty:typed term; }

(* **** PSEUDO UNIFICATION ********************** *)

let rec add_to_list q lst args1 args2 =
  match args1,args2 with
    | [], [] -> lst
    | a1::args1, a2::args2 -> add_to_list q ((q,a1,a2)::lst) args1 args2
    | _, _ -> raise (Invalid_argument "add_to_list")

module SS = Subst.S

let unshift_reduce sg q t =
  try Some (Subst.unshift q t)
  with Subst.UnshiftExn ->
    ( try Some (Subst.unshift q (Reduction.snf sg t))
      with Subst.UnshiftExn -> None )

let pseudo_unification sg (q:int) (a:typed term) (b:typed term) : typed SS.t option =
  let rec aux (sigma:typed SS.t) : (int*typed term*typed term) list -> typed SS.t option = function
    | [] -> Some sigma
    | (q,t1,t2)::lst ->
        begin
          let t1' = Reduction.whnf sg (SS.apply sigma t1 q) in
          let t2' = Reduction.whnf sg (SS.apply sigma t2 q) in
            if term_eq t1' t2' then aux sigma lst
            else
              match t1', t2' with
                | Kind, Kind | Type _, Type _ -> aux sigma lst
                | DB (_,_,n), DB (_,_,n') when ( n=n' ) -> aux sigma lst
                | Const (_,md,id), Const (_,md',id') when
                    ( Basics.ident_eq id id' && Basics.ident_eq md md' ) ->
                    aux sigma lst

                | DB (_,x,n), t
                | t, DB (_,x,n) when n>=q ->
                  begin
                    match unshift_reduce sg q t with
                    | None -> None
                    | Some t' ->
                      ( match SS.add sigma x (n-q) t' with
                        | None -> assert false
                        | Some sigma2 -> aux sigma2 lst )
                  end

                | Pi (_,_,a,b), Pi (_,_,a',b') ->
                    aux sigma ((q,a,a')::(q+1,b,b')::lst)
                | Lam (_,_,_,b), Lam (_,_,_,b') ->
                    aux sigma ((q+1,b,b')::lst)

                | App (DB (_,_,n),_,_), _
                | _, App (DB (_,_,n),_,_) when ( n >= q ) ->
                    if Reduction.are_convertible sg t1' t2' then aux sigma lst
                    else None

                | App (Const (l,md,id),_,_), _
                | _, App (Const (l,md,id),_,_) when (not (Signature.is_constant sg l md id)) ->
                    if Reduction.are_convertible sg t1' t2' then aux sigma lst
                    else None

                | App (f,a,args), App (f',a',args') ->
                    (* f = Kind | Type | DB n when n<q | Pi _
                     * | Const md.id when (is_constant md id) *)
                    aux sigma ((q,f,f')::(q,a,a')::(add_to_list q lst args args'))

                | _, _ -> None
        end
  in
  if term_eq a b then Some SS.identity
  else aux SS.identity [(q,a,b)]

(* ********************** CONTEXT *)

module Context :
sig
  type t
  val empty : t
  val add : loc -> ident -> t judgment0 -> t
  val unsafe_add : t -> loc -> ident -> typed term -> t
  val get_type : t -> loc -> ident -> int -> typed term
  val is_empty : t -> bool
  val to_context : t -> typed context
  val destruct : t -> ((loc*ident*typed term)*t) option
end =
struct
  type t = typed context

  let empty = []
  let is_empty ctx = ( ctx=[] )
  let to_context ctx = ctx

  let add l x jdg : typed context =
    match jdg.ty with
      | Type _ -> (l,x,jdg.te) :: jdg.ctx
      | Kind when !coc -> (l,x,jdg.te) :: jdg.ctx
      (*Note that this and RMeta are the only places where the coc flag has an effect *)
      | _ -> raise (TypingError (ConvertibilityError
                                   (jdg.te, to_context jdg.ctx, mk_Type dloc, jdg.ty)))

  let unsafe_add ctx l x ty = (l,x,ty)::ctx

  let get_type ctx l x n =
    try
      let (_,_,ty) = List.nth ctx n in Subst.shift (n+1) ty
    with Failure _ ->
      raise (TypingError (VariableNotFound (l,x,n,ctx)))

  let destruct = function
    | [] -> None
    | a::b -> Some (a,b)
end

type judgment = Context.t judgment0

(* ********************** METAS *)

module type Meta = sig
  include Monads.Monad

  type pextra
  type extra
  type ctx
  type jdg

  val get_type : ctx -> loc -> ident -> int -> extra term

  val judge : ctx -> extra term -> extra term -> jdg
  val jdg_ctx : jdg -> ctx
  val jdg_te : jdg -> extra term
  val jdg_ty : jdg -> extra term

  val to_context : ctx -> extra context

  val fail : typing_error -> 'a t

  val fold : ('a -> 'b -> 'a t) -> 'a -> 'b list -> 'a t

  val ctx_add : Signature.t -> loc -> ident -> jdg -> (jdg*ctx) t
  val unsafe_add : ctx -> loc -> ident -> extra term -> ctx

  val pi : Signature.t -> ctx -> extra term -> (loc*ident*extra term*extra term) option t

  val cast : Signature.t -> jdg -> jdg -> jdg t
  val cast_sort : Signature.t -> jdg -> jdg t

  val infer_extra : (Signature.t -> ctx -> pextra term -> jdg t) -> (Signature.t -> pextra term -> jdg -> jdg t) ->
                    Signature.t -> ctx -> loc -> pextra tkind -> pextra -> jdg t
end

module KMeta : Meta with type 'a t = 'a and type pextra = typed and type extra = typed and type ctx = Context.t and type jdg = judgment
 = struct
  type 'a t = 'a
  
  type pextra = typed
  type extra = typed
  type ctx = Context.t
  type jdg = judgment
  
  let get_type = Context.get_type
  
  let judge ctx te ty = {ctx=ctx; te=te; ty=ty;}
  let jdg_ctx j = j.ctx
  let jdg_te j = j.te
  let jdg_ty j = j.ty
  
  let to_context ctx = Context.to_context ctx
  
  let return x = x
  let (>>=) x f = f x
  let (>>) x y = x;y

  let fail e = raise (TypingError e)

  let fold = List.fold_left
  
  let ctx_add _ lc x jdg = jdg,Context.add lc x jdg
  let unsafe_add = Context.unsafe_add
  
  let cast sg {ctx=ctx; te=te; ty=ty;} {te=ty_exp} =
    if Reduction.are_convertible sg ty ty_exp then {ctx=ctx; te=te; ty=ty_exp;}
    else fail (ConvertibilityError (te,Context.to_context ctx,ty_exp,ty))
  
  let cast_sort sg jdg = match jdg.ty with
    | Kind | Type _ -> jdg
    | _ -> fail (SortExpected (jdg.te, to_context jdg.ctx, jdg.ty))

  let pi sg ctx t = match Reduction.whnf sg t with
    | Pi (l,x,a,b) -> Some (l,x,a,b)
    | _ -> None
    
  let infer_extra infer check sg ctx lc kind ex = ex.exfalso

  let simpl x = x
end


(* ********************** TYPE CHECKING/INFERENCE  *)
module type ElaborationS = sig
  type 'a t

  type pextra
  type extra
  type ctx
  type jdg

  val infer       : Signature.t -> ctx -> pextra term -> jdg t

  val check       : Signature.t -> pextra term -> jdg -> jdg t
end

module Elaboration (M:Meta) = struct
  type 'a t = 'a M.t
  type pextra = M.pextra
  type extra = M.extra
  type ctx = M.ctx
  type jdg = M.jdg

  open M
  
  (* ********************** TERMS *)

  let rec infer sg (ctx:ctx) : pextra term -> jdg t = function
    | Kind -> fail (KindIsNotTypable)
    | Type l -> M.return (judge ctx (mk_Type l) mk_Kind)
    | DB (l,x,n) -> M.return (judge ctx (mk_DB l x n) (M.get_type ctx l x n))
    | Const (l,md,id) -> M.return (judge ctx (mk_Const l md id) (lift_term (Signature.get_type sg l md id)))
    | App (f,a,args) -> infer sg ctx f >>= fun jdg_f ->
        check_app sg jdg_f [] [] (a::args)
    | Pi (l,x,a,b) ->
        infer sg ctx a >>= fun jdg_a ->
        M.ctx_add sg l x jdg_a >>= fun (jdg_a,ctx2) ->
        infer sg ctx2 b >>= cast_sort sg >>= fun jdg_b ->
        M.return (judge ctx (mk_Pi l x (jdg_te jdg_a) (jdg_te jdg_b)) (jdg_ty jdg_b))
    | Lam  (l,x,Some a,b) ->
        infer sg ctx a >>= fun jdg_a ->
        M.ctx_add sg l x jdg_a >>= fun (jdg_a,ctx2) ->
        infer sg ctx2 b >>= fun jdg_b ->
          ( match jdg_ty jdg_b with (* Needs meta handling. Or we could say that if it's a meta we will error out in kernel mode. *)
              | Kind -> fail (InexpectedKind (jdg_te jdg_b, M.to_context (jdg_ctx jdg_b)))
              | _ -> M.return (judge ctx (mk_Lam l x (Some (jdg_te jdg_a)) (jdg_te jdg_b))
                       (mk_Pi l x (jdg_te jdg_a) (jdg_ty jdg_b)))
          )
    | Lam  (l,x,None,b) -> fail (DomainFreeLambda l)
    | Extra (l,kind,ex) -> infer_extra infer check sg ctx l kind ex

  and check sg (te:pextra term) (jty:jdg) : jdg t =
    let ty_exp = jdg_te jty in
    let ctx = jdg_ctx jty in
      match te with
        | Lam (l,x,None,u) ->
            ( M.pi sg ctx ty_exp >>= function
                | Some (l,x,a,b) -> let pi = mk_Pi l x a b in
                    let ctx2 = M.unsafe_add ctx l x a in
                    (* (x) might as well be Kind but here we do not care*)
                    check sg u (judge ctx2 b (mk_Type dloc (* (x) *))) >>= fun jdg_b ->
                      M.return (judge ctx (mk_Lam l x (Some a) (jdg_te jdg_b)) pi)
                | None -> fail (ProductExpected (te,M.to_context ctx,ty_exp))
            )
        | _ ->
          infer sg ctx te >>= fun jte ->
          M.cast sg jte jty

  and check_app sg jdg_f consumed_te consumed_ty = function
    | [] -> M.return jdg_f
    | u::atl -> let ctx = jdg_ctx jdg_f and te = jdg_te jdg_f and ty = jdg_ty jdg_f in
      begin M.pi sg ctx ty >>= function
        | Some (_,_,a,b) -> check sg u (judge ctx a (mk_Type dloc (* (x) *))) >>= fun u_inf ->
            check_app sg (judge ctx (mk_App te (jdg_te u_inf) []) (Subst.subst b (jdg_te u_inf)))
                         ((jdg_te u_inf)::consumed_te) (a::consumed_ty) atl
        | None -> fail (ProductExpected (te,M.to_context ctx,ty))
        end

end

module Checker = Elaboration(KMeta)

(* ********************** PATTERNS *)
let rec infer_pattern sg (ctx:Context.t) (q:int) (sigma:typed SS.t) (pat:pattern) : typed term*typed SS.t =
  match pat with
  | Pattern (l,md,id,args) ->
    let (_,ty,si) = List.fold_left (infer_pattern_aux sg ctx q)
      (mk_Const l md id,SS.apply sigma (Signature.get_type sg l md id) q,sigma) args
    in (ty,si)
  | Var (l,x,n,args) ->
    let (_,ty,si) = List.fold_left (infer_pattern_aux sg ctx q)
      (mk_DB l x n,SS.apply sigma (Context.get_type ctx l x n) q,sigma) args
    in (ty,si)
  | Brackets t -> ( (Checker.infer sg ctx t).ty, SS.identity )
  | Lambda (l,x,p) -> raise (TypingError (DomainFreeLambda l))

and infer_pattern_aux sg (ctx:Context.t) (q:int) (f,ty_f,sigma0:typed term*typed term*typed SS.t) (arg:pattern) : (typed term*typed term*typed SS.t) =
  match Reduction.whnf sg ty_f with
    | Pi (_,_,a,b) ->
        let sigma = check_pattern sg ctx q a sigma0 arg in
        let arg' = pattern_to_term arg in
        let b2 = SS.apply sigma b (q+1) in
        let arg2 = SS.apply sigma arg' q in
          ( Term.mk_App f arg' [], Subst.subst b2 arg2, sigma )
    | _ -> raise (TypingError (ProductExpected (f,Context.to_context ctx,ty_f)))

and check_pattern sg (ctx:Context.t) (q:int) (exp_ty:typed term) (sigma0:typed SS.t) (pat:pattern) : typed SS.t =
  match pat with
  | Lambda (l,x,p) ->
      begin
        match Reduction.whnf sg exp_ty with
          | Pi (l,x,a,b) ->
              let ctx2 = Context.unsafe_add ctx l x a in
                check_pattern sg ctx2 (q+1) b sigma0 p
          | _ -> raise (TypingError (ProductExpected (pattern_to_term pat,Context.to_context ctx,exp_ty)))
      end
   | Brackets t ->
     let _ = Checker.check sg t {ctx; te=exp_ty; ty=mk_Type dloc (* (x) *);} in
       SS.identity
  | _ ->
      begin
        let (inf_ty,sigma1) = infer_pattern sg ctx q sigma0 pat in
          match pseudo_unification sg q exp_ty inf_ty with
            | None ->
              raise (TypingError (ConvertibilityError (pattern_to_term pat,Context.to_context ctx,exp_ty,inf_ty)))
            | Some sigma2 -> SS.merge sigma1 sigma2
      end

(* **** REFINE AND CHECK ******************************** *)

let inference sg (te:typed term) : judgment =
    Checker.infer sg Context.empty te

let checking sg (te:typed term) (ty_exp:typed term) : judgment =
  let jty = Checker.infer sg Context.empty ty_exp in
    Checker.check sg te jty

let check_rule sg (ctx,le,ri:rule) : unit =
  let ctx =
    List.fold_left (fun ctx (l,id,ty) -> Context.add l id (Checker.infer sg ctx ty) )
      Context.empty (List.rev ctx) in
  let (ty_inf,sigma) = infer_pattern sg ctx 0 SS.identity le in
  let ri2 =
    if SS.is_identity sigma then ri
    else ( debug "%a" SS.pp sigma ; (SS.apply sigma ri 0) ) in
  let j_ri = Checker.infer sg ctx ri2 in
    if Reduction.are_convertible sg ty_inf j_ri.ty
      then ()
      else raise (TypingError (ConvertibilityError (ri,Context.to_context ctx,ty_inf,j_ri.ty)))

(* ********************** JUDGMENTS *)
(*
type judgmentExn =
  | DistinctContexts
  | LambdaKind
  | LambdaEmptyContext
  | PiSort
  | PiEmptyContext
  | AppNotAPi
  | AppNotConvertible
  | ConvSort
  | ConvError

exception JudgmentExn of judgmentExn
(* TODO check also the signature *)

let check_contexts ctx1 ctx2 =
  if ctx1 != ctx2 then raise (JudgmentExn DistinctContexts)

let mk_Type ctx l = { ctx=ctx; te=mk_Type l; ty= mk_Kind; }

let mk_Const sg ctx l md id =
  { ctx=ctx; te=mk_Const l md id; ty= Signature.get_type sg l md id; }

 let mk_Var ctx l x n =
  { ctx=ctx; te=mk_DB l x n; ty= Context.get_type ctx l x n }

let mk_App sg f arg =
  check_contexts f.ctx arg.ctx ;
  match Reduction.whnf sg f.ty with
    | Pi (_,_,a,b) ->
        if Reduction.are_convertible sg a arg.ty then
          { ctx=f.ctx; te=mk_App f.te arg.te []; ty=Subst.subst b arg.te; }
        else raise (JudgmentExn AppNotConvertible)
    | _ -> raise (JudgmentExn AppNotAPi)

let mk_Lam b =
  match b.ty with
    | Kind -> raise (JudgmentExn LambdaKind)
    | _ ->
        begin
          match Context.destruct b.ctx with
            | Some ((l,x,a),ctx') ->
                { ctx=ctx'; te=mk_Lam l x (Some a) b.te; ty=mk_Pi l x a b.ty }
            | None -> raise (JudgmentExn LambdaEmptyContext)
        end

let mk_Pi b =
  match b.ty with
    | Kind | Type _ as ty ->
        begin
          match Context.destruct b.ctx with
            | Some ((l,x,a),ctx') -> { ctx=ctx'; te=mk_Pi l x a b.te; ty=ty }
            | None -> raise (JudgmentExn PiEmptyContext)
        end
    | _ -> raise (JudgmentExn PiSort)

let mk_Conv sg a b =
  check_contexts a.ctx b.ctx;
  match b.ty with
    | Kind | Type _ ->
        if Reduction.are_convertible sg a.ty b.te then
          { ctx=a.ctx; te=a.te; ty=b.te }
        else raise (JudgmentExn ConvError)
    | _ -> raise (JudgmentExn ConvSort)
*)
