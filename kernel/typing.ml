open Basics
open Term
open Rule
open Monads

type typing_error =
  | KindIsNotTypable
  | ConvertibilityError : 'a tkind*'a term*'a context*'a term*'a term -> typing_error
  | VariableNotFound : 'a tkind*loc*ident*int*'a context -> typing_error
  | SortExpected : 'a tkind*'a term*'a context*'a term -> typing_error
  | ProductExpected : 'a tkind*'a term*'a context*'a term -> typing_error
  | InexpectedKind : 'a tkind*'a term*'a context -> typing_error
  | DomainFreeLambda of loc
  | MetaInKernel of loc*ident
  | InferSortMeta of loc*ident
  | UnknownMeta of loc*ident*int
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
  try Some (Subst.unshift Typed q t)
  with Subst.UnshiftExn ->
    ( try Some (Subst.unshift Typed q (Reduction.snf Typed sg t))
      with Subst.UnshiftExn -> None )

let pseudo_unification sg (q:int) (a:typed term) (b:typed term) : SS.t option =
  let rec aux (sigma:SS.t) : (int*typed term*typed term) list -> SS.t option = function
    | [] -> Some sigma
    | (q,t1,t2)::lst ->
        begin
          let t1' = Reduction.whnf Typed sg (SS.apply sigma t1 q) in
          let t2' = Reduction.whnf Typed sg (SS.apply sigma t2 q) in
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
                    if Reduction.are_convertible Typed sg t1' t2' then aux sigma lst
                    else None

                | App (Const (l,md,id),_,_), _
                | _, App (Const (l,md,id),_,_) when (not (Signature.is_constant sg l md id)) ->
                    if Reduction.are_convertible Typed sg t1' t2' then aux sigma lst
                    else None

                | App (f,a,args), App (f',a',args') ->
                    (* f = Kind | Type | DB n when n<q | Pi _
                     * | Const md.id when (is_constant md id) *)
                    aux sigma ((q,f,f')::(q,a,a')::(add_to_list q lst args args'))

                | _, _ -> None
        end
  in
  if term_eq Typed a b then Some (SS.identity Typed)
  else aux (SS.identity Typed) [(q,a,b)]

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
                                   (Typed, jdg.te, to_context jdg.ctx, mk_Type dloc, jdg.ty)))

  let unsafe_add ctx l x ty = (l,x,ty)::ctx

  let get_type ctx l x n =
    try
      let (_,_,ty) = List.nth ctx n in Subst.shift (n+1) ty
    with Failure _ ->
      raise (TypingError (VariableNotFound (Typed,l,x,n,ctx)))

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

  val ctx_add : Signature.t -> loc -> ident -> jdg -> ctx t
  val unsafe_add : ctx -> loc -> ident -> extra term -> ctx

  val pi : Signature.t -> ctx -> extra term -> (loc*ident*extra term*extra term) option t

  val unify : Signature.t -> ctx -> extra term -> extra term -> bool t
  val unify_sort : Signature.t -> ctx -> extra term -> bool t

  val infer_extra : (Signature.t -> ctx -> pextra term -> jdg t) -> (Signature.t -> pextra term -> jdg -> jdg t) ->
                    Signature.t -> ctx -> loc -> pextra -> jdg t

  val simpl : extra term -> extra term t
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
  
  let ctx_add _ = Context.add
  let unsafe_add = Context.unsafe_add
  
  let unify sg ctx t u = Reduction.are_convertible Typed sg t u

  let unify_sort sg ctx = function
    | Kind | Type _ -> true
    | _ -> false

  let pi sg ctx t = match Reduction.whnf Typed sg t with
    | Pi (l,x,a,b) -> Some (l,x,a,b)
    | _ -> None
    
  let infer_extra infer check sg ctx lc ex = ex.exfalso

  let simpl x = x
end


(* ********************** TYPE CHECKING/INFERENCE  *)
module type ElaborationS = sig
  type 'a t

  type pextra
  type ctx
  type jdg

  val infer       : Signature.t -> ctx -> pextra term -> jdg t

  val check       : Signature.t -> pextra term -> jdg -> jdg t

  val infer_pattern : Signature.t -> ctx -> int -> extra Subst.S.t -> pattern -> (extra term*extra Subst.S.t) t
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
    | Const (l,md,id) -> M.return (judge ctx (mk_Const l md id) (Signature.get_type sg l md id))
    | App (f,a,args) -> infer sg ctx f >>= fun jdg_f ->
        check_app sg jdg_f [] [] (a::args)
    | Pi (l,x,a,b) ->
        infer sg ctx a >>= fun jdg_a ->
        M.ctx_add sg l x jdg_a >>= fun ctx2 ->
        infer sg ctx2 b >>= fun jdg_b ->
        M.unify_sort sg ctx (jdg_ty jdg_b) >>= fun b -> if b
          then M.return (judge ctx (mk_Pi l x (jdg_te jdg_a) (jdg_te jdg_b)) (jdg_ty jdg_b))
          else fail (SortExpected (jdg_te jdg_b, M.to_context (jdg_ctx jdg_b), jdg_ty jdg_b))
    | Lam  (l,x,Some a,b) ->
        infer sg ctx a >>= fun jdg_a ->
        M.ctx_add sg l x jdg_a >>= fun ctx2 ->
        infer sg ctx2 b >>= fun jdg_b ->
          ( match jdg_ty jdg_b with (* Needs meta handling. Or we could say that if it it's a meta we will error out in kernel mode. *)
              | Kind -> fail (InexpectedKind (jdg_te jdg_b, M.to_context (jdg_ctx jdg_b)))
              | _ -> M.return (judge ctx (mk_Lam l x (Some (jdg_te jdg_a)) (jdg_te jdg_b))
                       (mk_Pi l x (jdg_te jdg_a) (jdg_ty jdg_b)))
          )
    | Lam  (l,x,None,b) -> infer sg ctx (mk_Lam l x (Some (mk_Hole l x)) b)
    | Hole (lc,s) ->
        M.new_meta ctx lc s MType >>= fun mk ->
        M.new_meta ctx lc s (MTyped mk) >>= fun mj ->
        M.return (judge ctx mj mk)
    | Meta (lc,s,n,ts) -> M.meta_constraint lc s n >>= fun (ctx0,ty0) ->
        check_subst sg ctx ts ctx0 >>= fun ts' ->
        M.return (judge ctx (mk_Meta lc s n ts') (subst_l (List.map snd ts') 0 ty0))

  and check sg (te:term) (jty:jdg) : jdg t =
    let ty_exp = jdg_te jty in
    let ctx = jdg_ctx jty in
      match te with (* Maybe do the match on term and type at the same time? In case type is a meta. *)
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
          M.unify sg ctx (jdg_ty jte) ty_exp >>= fun b -> if b
            then M.return (judge ctx (jdg_te jte) ty_exp)
            else fail (ConvertibilityError (te,M.to_context ctx,ty_exp,jdg_ty jte))

  and check_app sg jdg_f consumed_te consumed_ty args = 
    match args with
      | [] -> M.return jdg_f
      | u::atl -> let ctx = jdg_ctx jdg_f and te = jdg_te jdg_f and ty = jdg_ty jdg_f in
        begin M.pi sg ctx ty >>= function
          | Some (_,_,a,b) -> check sg u (judge ctx a (mk_Type dloc (* (x) *))) >>= fun u_inf ->
              check_app sg (judge ctx (mk_App te (jdg_te u_inf) []) (Subst.subst b (jdg_te u_inf)))
                           ((jdg_te u_inf)::consumed_te) (a::consumed_ty) atl
          | None -> fail (ProductExpected (te,M.to_context ctx,ty))
          end

  and check_subst sg ctx ts ctx0 =
    let rec aux sigma rho delta = match rho, delta with
      | [], [] -> M.return sigma
      | (x,te)::rho0, (_,_,ty0)::delta0 -> let ty = subst_l (List.map snd sigma) 0 ty0 in
          check sg te (judge ctx ty (mk_Type dloc (* (x) *))) >>= fun jdg ->
          aux ((x,jdg_te jdg)::sigma) rho0 delta0
      | _, _ -> assert false
      in
    aux [] (List.rev ts) (List.rev ctx0)


  (* ********************** PATTERNS *)
  
  let rec infer_pattern sg (ctx:ctx) (q:int) (sigma:SS.t) (pat:pattern) : (term*SS.t) t =
    match pat with
    | Pattern (l,md,id,args) ->
      M.fold (infer_pattern_aux sg ctx q)
        (mk_Const l md id,SS.apply sigma (Signature.get_type sg l md id) q,sigma) args >>= fun (_,ty,si) ->
      M.return (ty,si)
    | Var (l,x,n,args) ->
      M.fold (infer_pattern_aux sg ctx q)
        (mk_DB l x n,SS.apply sigma (M.get_type ctx l x n) q,sigma) args >>= fun (_,ty,si) ->
      M.return (ty,si)
    | Brackets t -> infer sg ctx t >>= fun jdg -> M.return ( jdg_ty jdg, SS.identity )
    | Lambda (l,x,p) -> fail (DomainFreeLambda l)

  and infer_pattern_aux sg (ctx:ctx) (q:int) (f,ty_f,sigma0:term*term*SS.t) (arg:pattern) : (term*term*SS.t) t =
    M.pi sg ctx ty_f >>= function
      | Some (_,_,a,b) ->
          check_pattern sg ctx q a sigma0 arg >>= fun sigma ->
          let arg' = pattern_to_term arg in
          let b2 = SS.apply sigma b (q+1) in
          let arg2 = SS.apply sigma arg' q in
          M.return ( Term.mk_App f arg' [], Subst.subst b2 arg2, sigma )
      | None -> fail (ProductExpected (f,M.to_context ctx,ty_f))

  and check_pattern sg (ctx:ctx) (q:int) (exp_ty:term) (sigma0:SS.t) (pat:pattern) : SS.t t =
    match pat with
    | Lambda (l,x,p) ->
        begin
          M.pi sg ctx exp_ty >>= function
            | Some (l,x,a,b) ->
                let ctx2 = M.unsafe_add ctx l x a in
                  check_pattern sg ctx2 (q+1) b sigma0 p
            | None -> fail (ProductExpected (pattern_to_term pat,M.to_context ctx,exp_ty))
        end
     | Brackets t ->
       check sg t (judge ctx exp_ty (mk_Type dloc (* (x) *))) >>= fun _ ->
         M.return SS.identity
    | _ ->
        begin
          infer_pattern sg ctx q sigma0 pat >>= fun (inf_ty,sigma1) ->
          M.simpl exp_ty >>= fun exp_ty ->
          M.simpl inf_ty >>= fun inf_ty ->
            match pseudo_unification sg q exp_ty inf_ty with
              | None ->
                fail (ConvertibilityError (pattern_to_term pat,M.to_context ctx,exp_ty,inf_ty))
              | Some sigma2 -> M.return (SS.merge sigma1 sigma2)
        end
end

module Checker = Elaboration(KMeta)

(* **** REFINE AND CHECK ******************************** *)

let inference sg (te:term) : judgment =
    Checker.infer sg Context.empty te

let checking sg (te:term) (ty_exp:term) : judgment =
  let jty = Checker.infer sg Context.empty ty_exp in
    Checker.check sg te jty

let check_rule sg (ctx,le,ri:rule) : unit =
  let ctx =
    List.fold_left (fun ctx (l,id,ty) -> Context.add l id (Checker.infer sg ctx ty) )
      Context.empty (List.rev ctx) in
  let (ty_inf,sigma) = Checker.infer_pattern sg ctx 0 SS.identity le in
  let ri2 =
    if SS.is_identity sigma then ri
    else ( debug "%a" SS.pp sigma ; (SS.apply sigma ri 0) ) in
  let j_ri = Checker.infer sg ctx ri2 in
    if KMeta.unify sg ctx ty_inf j_ri.ty
      then ()
      else KMeta.fail (ConvertibilityError (ri,Context.to_context ctx,ty_inf,j_ri.ty))

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
