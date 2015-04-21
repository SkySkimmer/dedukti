open Basics
open Term
open Rule

let coc = ref false

type 'a judgment0 = { ctx:'a; te:term; ty: term; }

let subst_l l n t = Subst.psubst_l (LList.of_list (List.map Lazy.from_val l)) n t

(* revseq n k = [n;n-1;..;k+1;k] *)
let rec revseq n k = if n<k then [] else n::(revseq (n-1) k)


(* ********************** ERROR MESSAGES *)

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
  | UnknownMeta of int

exception TypingError of typing_error

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

let pseudo_unification sg (q:int) (a:term) (b:term) : SS.t option =
  let rec aux (sigma:SS.t) : (int*term*term) list -> SS.t option = function
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
  val unsafe_add : t -> loc -> ident -> term -> t
  val get_type : t -> loc -> ident -> int -> term
  val is_empty : t -> bool
  val to_context : t -> (loc*ident*term) list
  val destruct : t -> ((loc*ident*term)*t) option
end =
struct
  type t = (loc*ident*term) list

  let empty = []
  let is_empty ctx = ( ctx=[] )
  let to_context ctx = ctx

  let add l x jdg : context =
    match jdg.ty with
      | Type _ -> (l,x,jdg.te) :: jdg.ctx
      | Kind when !coc -> (l,x,jdg.te) :: jdg.ctx
      (*Note that this is the only place where the coc flag has an effect *)
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

type candidate =
  | CTerm of term
  | CType
  | CSort

module type Meta = sig
  type 'a t
  
  val return : 'a -> 'a t
  val (>>=) : 'a t -> ('a -> 'b t) -> 'b t
  
  val fold : ('a -> 'b -> 'a t) -> 'a -> 'b list -> 'a t
  
  val add : Signature.t -> loc -> ident -> judgment -> Context.t t
  
  val pi : Signature.t -> Context.t -> term -> (loc*ident*term*term) option t
  
  val unify : Signature.t -> Context.t -> term -> candidate -> bool t
  val new_meta : Context.t -> loc -> ident -> candidate -> term t
  
  val meta_constraint : term -> (Context.t * term) t
  
  val simpl : term -> term t
end

module KMeta : Meta with type 'a t = 'a = struct
  type 'a t = 'a
  
  let return x = x
  let (>>=) x f = f x
  
  let fold = List.fold_left
  
  let add _ = Context.add
  
  let unify sg ctx t = function
    | CTerm u -> Reduction.are_convertible sg t u
    | CType -> failwith "cannot kernel unify with type"
    | CSort -> begin match t with
        | Kind | Type _ -> true
        | _ -> false
        end
  
  let pi sg ctx t = match Reduction.whnf sg t with
    | Pi (l,x,a,b) -> Some (l,x,a,b)
    | _ -> None
    
  let new_meta ctx l s _ = raise (TypingError (MetaInKernel (l,s)))
  
  let meta_constraint = function
    | Meta (l,s,_,_) -> raise (TypingError (MetaInKernel (l,s)))
    | _ -> assert false

  let simpl x = x
end

module RMeta : sig
  include Meta
  
  type problem
  
  val extract : 'a t -> 'a*problem
  
  val apply : problem -> term -> term
end = struct
  module S = Msubst.S
  
  type metainfo =
    | MetaDecl of Context.t*int*term (* ctx |- ?j : ty *)
    | MetaType of Context.t*int      (* either ctx |- ?j : s or ?j = Kind *)
    | MetaSort of Context.t*int      (* ?j = Type or Kind *)

  let pp_metainfo out = function
    | MetaDecl (ctx,n,ty) -> Printf.fprintf out "%a |- ?_%i : %a" pp_context (Context.to_context ctx) n pp_term ty
    | MetaType (ctx,n)    -> Printf.fprintf out "%a |- ?_%i : *" pp_context (Context.to_context ctx) n
    | MetaSort (ctx,n)    -> Printf.fprintf out "%a |- ?_%i sort" pp_context (Context.to_context ctx) n

  type problem = { cpt:int; decls: metainfo list; defs: S.t; }
  
  type 'a t = problem -> 'a * problem
  
  let return x pb = (x,pb)
  let (>>=) x f pb = let (x',pb') = x pb in f x' pb'
  
  let fold f x l = List.fold_left (fun a b -> a >>= fun a -> f a b) (return x) l
  
  let empty = { cpt=0; decls=[]; defs=S.identity; }
  
  let pp_problem out pb = Printf.fprintf out "cpt=%i;\n%a\n%a\n" pb.cpt (pp_list "\n" pp_metainfo) pb.decls S.pp pb.defs
  
  let whnf sg t pb = (S.whnf sg pb.defs t,pb)
  
  let new_meta ctx l s c pb = let substj = List.mapi (fun i (_,x,_) -> x,mk_DB dloc x i) (Context.to_context ctx) in
    let mj = mk_Meta l s pb.cpt substj in
    match c with
      | CTerm ty -> 
            (mj,{cpt=pb.cpt+1; decls=(MetaDecl (ctx,pb.cpt,ty))::pb.decls; defs=pb.defs;})
      | CType -> (mj,{cpt=pb.cpt+1; decls=(MetaType (ctx,pb.cpt))::pb.decls; defs=pb.defs;})
      | CSort -> (mj,{cpt=pb.cpt+1; decls=(MetaSort (ctx,pb.cpt))::pb.decls; defs=pb.defs;})

  let rec accessible n pb = function
    | Kind | Type _ | DB _ | Const _ | Hole _ -> false
    | App (f,a,args) -> List.exists (accessible n pb) (f::a::args)
    | Lam (_,_,None,u) -> accessible n pb u
    | Lam (_,_,Some a,u) -> accessible n pb a || accessible n pb u
    | Pi (_,_,a,b) -> accessible n pb a || accessible n pb b
    | Meta (_,_,m,ts) -> (n==m) || List.exists (fun (_,x) -> accessible n pb x) ts || ( match S.meta_raw pb.defs m with
        | Some t -> accessible n pb t
        | None -> false)

  let set_meta n t pb = if accessible n pb t
    then false,pb
    else true,{cpt=pb.cpt; decls=pb.decls; defs=S.add pb.defs n t}
  
  let set_decl d pb = let n = match d with | MetaDecl (_,n,_) | MetaType (_,n) | MetaSort (_,n) -> n in
    let rec aux s = function
      | MetaDecl (_,m,_) :: tl | MetaType (_,m) :: tl | MetaSort (_,m) :: tl when n=m -> List.rev_append s (d::tl)
      | d' :: tl -> aux (d'::s) tl
      | [] -> assert false
    in (),{cpt=pb.cpt; decls=aux [] pb.decls; defs=pb.defs;}
  
  (* We need to infer a type for gamma |- ?j[sigma].
     If delta |- ?j : t in the context we check gamma |- sigma : delta then return sigma(t)
     If delta |- ?j : * then we know that ?j <> Kind, then ?j : ?k with ?k = * and we are in the standard case
     If delta |- ?j = * then ?j = Type : Kind
  *)
  let meta_constraint = function
    | Meta (l,s,n,_) -> begin fun pb ->
      try (List.find (function
        | MetaDecl (_,m,_) | MetaType (_,m) | MetaSort (_,m) -> n=m) pb.decls),pb
      with | Not_found -> raise (TypingError (UnknownMeta n))
      end >>= begin function
        | MetaDecl (ctx,_,ty) -> return (ctx,ty)
        | MetaType (ctx,_) -> new_meta ctx l s CSort >>= fun mk ->
            set_decl (MetaDecl (ctx,n,mk)) >>= fun () -> return (ctx,mk)
        | MetaSort (ctx,_) -> set_decl (MetaDecl (ctx,n,mk_Kind)) >>= fun () ->
            set_meta n (mk_Type l) >>= fun _ -> return (ctx,mk_Kind)
        end
    | _ -> assert false
  
  let unify sg ctx t c =
    let rec aux ctx t1 t2 = whnf sg t1 >>= fun t1' -> whnf sg t2 >>= fun t2' ->
      if Reduction.are_convertible sg t1' t2'
        then return true
        else begin (*(fun pb -> Printf.eprintf "Unification: %a === %a\nunder %a\nwith %a.\n" pp_term t1 pp_term t2 pp_context (Context.to_context ctx) pp_problem pb; (),pb) >>= fun () ->*)
        match t1', t2' with
          | Meta (_,_,n,_), Meta (_,_,m,_) -> set_meta n t2' >>= (function | true -> return true | false -> set_meta m t1')
          | Meta (_,_,n,_), _ -> set_meta n t2'
          | _, Meta (_,_,n,_) -> set_meta n t1'
          | Pi (l,x,a1,b1), Pi(_,_,a2,b2) -> aux ctx a1 a2 >>= fun b -> if b
            then aux (Context.unsafe_add ctx l x a1) b1 b2
            else return false
          | _, _ -> (fun pb -> Printf.eprintf "Failed to unify %a === %a\nunder %a\nwith %a.\n" pp_term t1' pp_term t2' pp_context (Context.to_context ctx) pp_problem pb; (),pb) >>= fun () ->
              return false
      end in
    match c with
      | CTerm u -> aux ctx t u
      | CType -> failwith "Refine mode: cannot unify with type"
      | CSort -> begin match t with
          | Kind | Type _ -> return true
          | _ -> aux ctx t (mk_Type dloc) (* bad *)
          end
  
  let add sg l x jdg = (if !coc then unify sg jdg.ctx jdg.ty CSort else unify sg jdg.ctx jdg.ty (CTerm (mk_Type dloc))) >>= fun b ->
    if b then return (Context.unsafe_add jdg.ctx l x jdg.te)
    else raise (TypingError (ConvertibilityError
                                   (jdg.te, Context.to_context jdg.ctx, mk_Type dloc, jdg.ty)))
  
  let pi sg ctx t = whnf sg t >>= function
    | Pi (l,x,a,b) -> return (Some (l,x,a,b))
    | Meta _ | App (Meta _, _, _) -> let empty = Basics.empty in
        new_meta ctx dloc empty CSort >>= fun ms -> (* if !coc may be Kind *)
        new_meta ctx dloc empty (CTerm ms) >>= fun mt ->
        add sg dloc empty {ctx=ctx; te=mt; ty=ms;} >>= fun ctx2 ->
        new_meta ctx2 dloc empty CSort >>= fun ml ->
        new_meta ctx2 dloc empty (CTerm ml) >>= fun mk ->
        let pi = mk_Pi dloc empty mt mk in
        unify sg ctx t (CTerm pi) >>= begin function
        | true -> return (Some (dloc,empty,mt,mk))
        | false -> return None
        end
    | _ -> return None

  let extract f = f empty

  let apply pb t = S.apply pb.defs t

  let simpl t pb = apply pb t,pb
end

(* ********************** TYPE CHECKING/INFERENCE  *)
module type RefinerS = sig
  type 'a t

  val infer : Signature.t -> Context.t -> term -> judgment t

  val check : Signature.t -> term -> judgment -> judgment t

  val infer_pattern : Signature.t -> Context.t -> int -> Subst.S.t -> pattern -> (term*Subst.S.t) t
end

module Refiner (M:Meta) : RefinerS with type 'a t = 'a M.t = struct
  type 'a t = 'a M.t

  let (>>=) = M.(>>=)

  (* ********************** TERMS *)

  let rec infer sg (ctx:Context.t) : term -> judgment t = function
    | Kind -> raise (TypingError KindIsNotTypable)
    | Type l -> M.return { ctx=ctx; te=mk_Type l; ty= mk_Kind; }
    | DB (l,x,n) -> M.return { ctx=ctx; te=mk_DB l x n; ty= Context.get_type ctx l x n }
    | Const (l,md,id) -> M.return { ctx=ctx; te=mk_Const l md id; ty=Signature.get_type sg l md id; }
    | App (f,a,args) -> infer sg ctx f >>= fun jdg_f ->
        check_app sg jdg_f [] [] (a::args)
    | Pi (l,x,a,b) ->
        infer sg ctx a >>= fun jdg_a ->
        M.add sg l x jdg_a >>= fun ctx2 ->
        infer sg ctx2 b >>= fun jdg_b ->
        M.unify sg ctx jdg_b.ty CSort >>= fun b -> if b
          then M.return { ctx=ctx; te=mk_Pi l x jdg_a.te jdg_b.te; ty=jdg_b.ty }
          else raise (TypingError
                         (SortExpected (jdg_b.te, Context.to_context jdg_b.ctx, jdg_b.ty)))
    | Lam  (l,x,Some a,b) ->
        infer sg ctx a >>= fun jdg_a ->
        M.add sg l x jdg_a >>= fun ctx2 ->
        infer sg ctx2 b >>= fun jdg_b ->
          ( match jdg_b.ty with (* Needs meta handling. Or we could say that if it it's a meta we will error out in kernel mode. *)
              | Kind -> raise (TypingError
                                 (InexpectedKind (jdg_b.te, Context.to_context jdg_b.ctx)))
              | _ -> M.return { ctx=ctx; te=mk_Lam l x (Some jdg_a.te) jdg_b.te;
                       ty=mk_Pi l x jdg_a.te jdg_b.ty }
          )
    | Lam  (l,x,None,b) -> infer sg ctx (mk_Lam l x (Some (mk_Hole l x)) b)
    | Hole (lc,s) ->
        M.new_meta ctx lc s CType >>= fun mk ->
        M.new_meta ctx lc s (CTerm mk) >>= fun mj ->
        M.return {ctx=ctx; te=mj; ty=mk;}
    | Meta (lc,s,n,ts) as mv -> M.meta_constraint mv >>= fun (ctx0,ty0) ->
        check_subst sg ctx ts ctx0 >>= fun ts' ->
        M.return {ctx=ctx; te=mk_Meta lc s n ts'; ty=subst_l (List.map snd ts') 0 ty0;}

  and check sg (te:term) (jty:judgment) : judgment t =
    let ty_exp = jty.te in
    let ctx = jty.ctx in
      match te with (* Maybe do the match on term and type at the same time? In case type is a meta. *)
        | Lam (l,x,None,u) ->
            ( M.pi sg ctx ty_exp >>= function
                | Some (l,x,a,b) -> let pi = mk_Pi l x a b in
                    let ctx2 = Context.unsafe_add ctx l x a in
                    (* (x) might as well be Kind but here we do not care*)
                    check sg u { ctx=ctx2; te=b; ty=mk_Type dloc (* (x) *); } >>= fun jdg_b ->
                      M.return { ctx=ctx; te=mk_Lam l x None jdg_b.te; ty=pi; }
                | None -> raise (TypingError
                                (ProductExpected (te,Context.to_context jty.ctx,jty.te)))
            )
        | _ ->
          infer sg ctx te >>= fun jte ->
          M.unify sg ctx jte.ty (CTerm ty_exp) >>= fun b -> if b
            then M.return { ctx=ctx; te=jte.te; ty=ty_exp; }
            else raise (TypingError
                            (ConvertibilityError (te,Context.to_context ctx,ty_exp,jte.ty)))

  and check_app sg jdg_f consumed_te consumed_ty args = 
    match args with
      | [] -> M.return jdg_f
      | u::atl -> begin M.pi sg jdg_f.ctx jdg_f.ty >>= function
        | Some (_,_,a,b) -> check sg u {ctx=jdg_f.ctx; te=a; ty=mk_Type dloc} >>= fun u_inf ->
            check_app sg {ctx=jdg_f.ctx; te=mk_App jdg_f.te u_inf.te []; ty=Subst.subst b u_inf.te;} (u_inf.te::consumed_te) (a::consumed_ty) atl
        | None -> raise (TypingError (ProductExpected (jdg_f.te,Context.to_context jdg_f.ctx,jdg_f.ty)))
        end

  and check_subst sg ctx ts ctx0 =
    let rec aux sigma rho delta = match rho, delta with
      | [], [] -> M.return sigma
      | (x,te)::rho0, (_,_,ty0)::delta0 -> let ty = subst_l (List.map snd sigma) 0 ty0 in
          check sg te {ctx=ctx; te=ty; ty=mk_Type dloc;} >>= fun jdg ->
          aux ((x,jdg.te)::sigma) rho0 delta0
      | _, _ -> assert false
      in
    aux [] (List.rev ts) (List.rev (Context.to_context ctx0))


  (* ********************** PATTERNS *)
  
  let rec infer_pattern sg (ctx:Context.t) (q:int) (sigma:SS.t) (pat:pattern) : (term*SS.t) t =
    match pat with
    | Pattern (l,md,id,args) ->
      M.fold (infer_pattern_aux sg ctx q)
        (mk_Const l md id,SS.apply sigma (Signature.get_type sg l md id) q,sigma) args >>= fun (_,ty,si) ->
      M.return (ty,si)
    | Var (l,x,n,args) ->
      M.fold (infer_pattern_aux sg ctx q)
        (mk_DB l x n,SS.apply sigma (Context.get_type ctx l x n) q,sigma) args >>= fun (_,ty,si) ->
      M.return (ty,si)
    | Brackets t -> infer sg ctx t >>= fun jdg -> M.return ( jdg.ty, SS.identity )
    | Lambda (l,x,p) -> raise (TypingError (DomainFreeLambda l))

  and infer_pattern_aux sg (ctx:Context.t) (q:int) (f,ty_f,sigma0:term*term*SS.t) (arg:pattern) : (term*term*SS.t) t =
    M.pi sg ctx ty_f >>= function
      | Some (_,_,a,b) ->
          check_pattern sg ctx q a sigma0 arg >>= fun sigma ->
          let arg' = pattern_to_term arg in
          let b2 = SS.apply sigma b (q+1) in
          let arg2 = SS.apply sigma arg' q in
          M.return ( Term.mk_App f arg' [], Subst.subst b2 arg2, sigma )
      | None -> raise (TypingError ( ProductExpected (f,Context.to_context ctx,ty_f)))

  and check_pattern sg (ctx:Context.t) (q:int) (exp_ty:term) (sigma0:SS.t) (pat:pattern) : SS.t t =
    match pat with
    | Lambda (l,x,p) ->
        begin
          M.pi sg ctx exp_ty >>= function
            | Some (l,x,a,b) ->
                let ctx2 = Context.unsafe_add ctx l x a in
                  check_pattern sg ctx2 (q+1) b sigma0 p
            | None -> raise (TypingError ( ProductExpected (pattern_to_term pat,Context.to_context ctx,exp_ty)))
        end
     | Brackets t ->
       check sg t { ctx; te=exp_ty; ty=Term.mk_Type dloc; } >>= fun _ ->
         M.return SS.identity
    | _ ->
        begin
          infer_pattern sg ctx q sigma0 pat >>= fun (inf_ty,sigma1) ->
          M.simpl exp_ty >>= fun exp_ty ->
          M.simpl inf_ty >>= fun inf_ty ->
            match pseudo_unification sg q exp_ty inf_ty with
              | None ->
                raise (TypingError (ConvertibilityError (pattern_to_term pat,Context.to_context ctx,exp_ty,inf_ty)))
              | Some sigma2 -> M.return (SS.merge sigma1 sigma2)
        end
end

module KRefine : RefinerS with type 'a t = 'a
 = Refiner(KMeta)

module MetaRefine : RefinerS with type 'a t = 'a RMeta.t
 = Refiner(RMeta)

(* **** REFINE AND CHECK ******************************** *)

let inference sg (te:term) : judgment =
  let jdg0,pb = RMeta.extract (MetaRefine.infer sg Context.empty te) in
    KRefine.infer sg Context.empty (RMeta.apply pb jdg0.te)

let checking sg (te:term) (ty_exp:term) : judgment =
  let jdg_te,pb = RMeta.extract (RMeta.(>>=) (MetaRefine.infer sg Context.empty ty_exp) (fun jdg_ty -> MetaRefine.check sg te jdg_ty)) in
  let ty_r = RMeta.apply pb jdg_te.ty in let te_r = RMeta.apply pb jdg_te.te in
  let jty = KRefine.infer sg Context.empty ty_r in
    KRefine.check sg te_r jty

let check_rule sg (ctx,le,ri:rule) : unit =
  let ((ctx,ri),pb) = RMeta.extract (RMeta.(>>=)
    (RMeta.fold (fun ctx (l,id,ty) -> RMeta.(>>=) (MetaRefine.infer sg ctx ty) (RMeta.add sg l id)) Context.empty (List.rev ctx))
    (fun ctx -> RMeta.(>>=) (MetaRefine.infer_pattern sg ctx 0 SS.identity le)
    (fun (ty_inf,sigma) ->
    let ri2 =
      if SS.is_identity sigma then ri else ( debug "%a" SS.pp sigma; (SS.apply sigma ri 0) ) in
    RMeta.(>>=) (MetaRefine.infer sg ctx ri2)
    (fun j_ri -> RMeta.(>>=) (RMeta.unify sg ctx ty_inf (CTerm j_ri.ty))
    (function
      | true -> RMeta.return (ctx,ri)
      | false -> raise (TypingError (ConvertibilityError (ri,Context.to_context ctx,ty_inf,j_ri.ty)))
    ))))) in
  let ctx =
    List.fold_left (fun ctx (l,id,ty) -> Context.add l id (KRefine.infer sg ctx (RMeta.apply pb ty)) )
      Context.empty (List.rev (Context.to_context ctx)) in
  let (ty_inf,sigma) = KRefine.infer_pattern sg ctx 0 SS.identity le in
  let ri = RMeta.apply pb ri in
  let ri2 =
    if SS.is_identity sigma then ri
    else ( debug "%a" SS.pp sigma ; (SS.apply sigma ri 0) ) in
  let j_ri = KRefine.infer sg ctx ri2 in
    if KMeta.unify sg ctx ty_inf (CTerm j_ri.ty)
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
