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

exception TypingError of typing_error

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

type metainfo =
  | MetaDecl of Context.t*int*term
  | MetaSort of Context.t*int
  | MetaDef  of Context.t*int*term*term

let pp_metainfo out = function
  | MetaDecl (ctx,n,ty) -> Printf.fprintf out "%a |- ?_%i : %a" pp_context (Context.to_context ctx) n pp_term ty
  | MetaSort (ctx,n)    -> Printf.fprintf out "%a |- ?_%i : *" pp_context (Context.to_context ctx) n
  | MetaDef (ctx,n,te,ty) -> Printf.fprintf out "%a |- ?_%i := %a : %a" pp_context (Context.to_context ctx) n pp_term te pp_term ty

module type Meta = sig
  type t
  
  val empty : t
  
  val unify : Signature.t -> Context.t -> t -> term -> term -> t option
  
  val whnf : Signature.t -> t -> term -> term

  val unify_sort : Signature.t -> Context.t -> t -> term -> t option
  val new_sort : t -> Context.t -> loc -> ident -> t*term
  val new_meta : t -> Context.t -> loc -> ident -> term -> t*judgment
  val get_meta : t -> term -> metainfo
  
  val apply : t -> term -> term
end

module KMeta : Meta = struct
  type t = unit
  
  let empty = ()
  
  let unify sg _ _ t1 t2 = if Reduction.are_convertible sg t1 t2 then Some () else None
  
  let whnf sg _ = Reduction.whnf sg
  
  let unify_sort _ _ _ = function
    | Kind | Type _ -> Some ()
    | _ -> None
  
  let new_sort _ _ l s = raise (TypingError (MetaInKernel (l,s)))
  let new_meta _ _ l s _ = raise (TypingError (MetaInKernel (l,s)))
  let get_meta _ = function
    | Meta (lc,s,_,_) -> raise (TypingError (MetaInKernel (lc,s)))
    | _ -> assert false
  
  let apply _ t = t
end

module RMeta : Meta = struct
  type t = { cpt:int; decls: metainfo list; defs: (Context.t*int*term*term) list; }
  
  let empty = { cpt=0; decls=[]; defs=[]; }
  
  let pp_def out (ctx,n,te,ty) = pp_metainfo out (MetaDef (ctx,n,te,ty))
  
  let pp_problem out pb = Printf.fprintf out "cpt=%i;\n%a\n%a\n" pb.cpt (pp_list " ; " pp_metainfo) pb.decls (pp_list " ; " pp_def) pb.defs
  
  let meta_val pb = function
    | Meta (_,_,n,ts) -> begin
      try let (_,_,te0,_) = List.find (fun (_,m,_,_) -> n=m) pb.defs in
        let subst1 = List.rev ts in Some (subst_l subst1 0 te0)
      with | Not_found -> None
      end
    | _ -> None
  
  let rec whnf sg pb t = match Reduction.whnf sg t with
    | Meta _ as mt -> begin match meta_val pb mt with
        | Some mt' -> whnf sg pb mt'
        | None -> mt
        end
    | App (Meta _ as mt, a, al) as t0 -> begin match meta_val pb mt with
        | Some mt' -> whnf sg pb (mk_App mt' a al)
        | None -> t0
        end
    | t0 -> t0

  let new_sort pb ctx l s = let len = List.length (Context.to_context ctx) in
    let mk = mk_Meta dloc s pb.cpt (List.map (mk_DB dloc Basics.empty) (revseq (len-1) 0)) in
      {cpt=pb.cpt+1; decls=(MetaSort (ctx,pb.cpt))::pb.decls; defs=pb.defs;},mk
  
  let new_meta pb ctx l s ty = let len = List.length (Context.to_context ctx) in
    let mj = mk_Meta dloc s pb.cpt (List.map (mk_DB dloc Basics.empty) (revseq (len-1) 0)) in
      {cpt=pb.cpt+1; decls=(MetaDecl (ctx,pb.cpt,ty))::pb.decls; defs=pb.defs;},{ctx=ctx; te=mj; ty=ty;}
  
  let get_meta pb = function
    | Meta (_,_,n,_) -> begin try let (ctx,m,te,ty) = (List.find (fun (_,m,_,_) -> n=m) pb.defs) in MetaDef (ctx,m,te,ty)
        with | Not_found -> List.find (function | MetaSort (_,m) | MetaDecl (_,m,_) -> n=m
                                                | MetaDef _ -> assert false) pb.decls
        end
    | _ -> assert false
  
  let set_meta pb n t = match List.partition (function | MetaDecl (_,m,_) | MetaSort (_,m) -> n=m
                                                       | MetaDef _ -> assert false) pb.decls with
    | [info],decls -> let (ctx,ty) = (match info with
        | MetaDecl (ctx,_,ty) -> ctx,ty
        | MetaSort (ctx,_) -> ctx,mk_Kind (* Probably false. Can we set meta to Kind? *)
        | _ -> assert false) in
      {cpt=pb.cpt; decls=decls; defs=(ctx,n,t,ty)::pb.defs;}
    | _ -> assert false
  
  let unify sg ctx pb t1 t2 = let t1' = whnf sg pb t1 in let t2' = whnf sg pb t2 in
    if Reduction.are_convertible sg t1' t2'
      then Some pb
      else begin (*Printf.eprintf "Unification: %a === %a\nunder %a\nwith %a.\n" pp_term t1 pp_term t2 pp_context (Context.to_context ctx) pp_problem pb;*)
      match t1' with
        | Meta (_,_,n,ts) -> Some (set_meta pb n t2')
        | _ -> match t2' with
          | Meta (_,_,n,ts) -> Some (set_meta pb n t1')
          | _ -> None
    end

  let unify_sort sg ctx pb = function
    | Kind | Type _ -> Some pb
    | t -> unify sg ctx pb t (mk_Type dloc)
  
  let rec apply pb = function
    | Kind | Type _ | Const _ | DB _ as t -> t
    | App (f,a,args) -> mk_App (apply pb f) (apply pb a) (List.map (apply pb) args)
    | Lam (lc,x,None,te) -> mk_Lam lc x None (apply pb te)
    | Lam (lc,x,Some ty, te) -> mk_Lam lc x (Some (apply pb ty)) (apply pb te)
    | Pi (lc,x,a,b) -> mk_Pi lc x (apply pb a) (apply pb b)
    | Hole (lc,s) -> assert false
    | Meta (lc,s,n,ts) as mt -> begin match meta_val pb mt with
        | Some mt' -> apply pb mt'
        | None -> mk_Meta lc s n (List.map (apply pb) ts)
      end

end

(* ********************** TYPE CHECKING/INFERENCE FOR TERMS  *)
module type RefinerS = sig
  type meta_t

  val infer : Signature.t -> meta_t -> Context.t -> term -> meta_t*judgment

  val check : Signature.t -> meta_t -> term -> judgment -> meta_t*judgment
end

module Refiner (M:Meta) : RefinerS with type meta_t = M.t = struct
  type meta_t = M.t

  let rec infer sg (pb:M.t) (ctx:Context.t) : term -> M.t*judgment = function
    | Kind -> raise (TypingError KindIsNotTypable)
    | Type l ->
        pb,{ ctx=ctx; te=mk_Type l; ty= mk_Kind; }
    | DB (l,x,n) ->
        pb,{ ctx=ctx; te=mk_DB l x n; ty= Context.get_type ctx l x n }
    | Const (l,md,id) ->
        pb,{ ctx=ctx; te=mk_Const l md id; ty=Signature.get_type sg l md id; }
    | App (f,a,args) -> let (pb2,jdg_f) = infer sg pb ctx f in
        check_app sg pb2 jdg_f [] [] (a::args)
    | Pi (l,x,a,b) ->
        let pb2,jdg_a = check sg pb a {ctx=ctx; te=mk_Type dloc; ty=mk_Kind;} in
        let pb3,jdg_b = infer sg pb2 (Context.add l x jdg_a) b in
          ( match M.unify_sort sg ctx pb3 jdg_b.ty with
              | Some pb4 -> pb4,{ ctx=ctx; te=mk_Pi l x jdg_a.te jdg_b.te; ty=jdg_b.ty }
              | None -> raise (TypingError
                              (SortExpected (jdg_b.te, Context.to_context jdg_b.ctx, jdg_b.ty)))
          )
    | Lam  (l,x,Some a,b) ->
        let pb2,jdg_a = check sg pb a {ctx=ctx; te=mk_Type dloc; ty=mk_Kind;} in
        let pb3,jdg_b = infer sg pb2 (Context.add l x jdg_a) b in
          ( match M.unify sg ctx pb3 jdg_b.ty (mk_Type dloc) with (* b_ty is either Type or Kind, but we don't want Kind *)
              | None -> raise (TypingError
                                 (InexpectedKind (jdg_b.te, Context.to_context jdg_b.ctx)))
              | Some pb4 -> pb4,{ ctx=ctx; te=mk_Lam l x (Some jdg_a.te) jdg_b.te;
                       ty=mk_Pi l x jdg_a.te jdg_b.ty }
          )
    | Lam  (l,x,None,b) -> raise (TypingError (DomainFreeLambda l))
    | Hole (lc,s) -> let pb2,mk = M.new_sort pb ctx lc s in
        M.new_meta pb2 ctx lc s mk
    | Meta (lc,s,n,ts) as mv -> begin match M.get_meta pb mv with (* Check the indices once things happen *)
        | MetaDecl (ctx0,_,ty0) | MetaDef (ctx0,_,_,ty0) -> let len = List.length (Context.to_context ctx0) in
          let (pb1,_,ts1) = List.fold_left
              (fun (pb0,i,tjs) te_i -> let ty_i = Context.get_type ctx0 dloc empty i in
                 let subst1 = List.append (List.map (mk_DB dloc empty) (revseq (len-1) i)) tjs in
                 let ty_exp = subst_l subst1 0 ty_i in
                 let (pb1,jdg) = check sg pb0 te_i {ctx=ctx; te=ty_exp; ty=mk_Type dloc;} in
                   (pb1,i+1,jdg.te::tjs))
              (pb,0,[]) (List.rev ts) in
          let ts2 = List.rev ts1 in
            pb1,{ctx=ctx; te=mk_Meta lc s n ts2; ty=subst_l ts1 0 ty0;}
        | MetaSort _ -> raise (TypingError (InferSortMeta (lc,s)))
        end
    

  and check sg (pb:M.t) (te:term) (jty:judgment) : M.t*judgment =
    let ty_exp = jty.te in
    let ctx = jty.ctx in
      match te with
        | Lam (l,x,None,u) ->
            ( match M.whnf sg pb ty_exp with
                | Pi (_,_,a,b) as pi ->
                    let ctx2 = Context.unsafe_add ctx l x a in
                    (* (x) might as well be Kind but here we do not care*)
                    let pb2,jdg_b = check sg pb u { ctx=ctx2; te=b; ty=mk_Type dloc (* (x) *); } in
                      pb2,{ ctx=ctx; te=mk_Lam l x None jdg_b.te; ty=pi; }
                | _ -> raise (TypingError
                                (ProductExpected (te,Context.to_context jty.ctx,jty.te)))
            )
        | _ ->
          let pb2,jte = infer sg pb ctx te in
            match M.unify sg ctx pb2 jte.ty ty_exp with
              | Some pb3 -> pb3,{ ctx=ctx; te=jte.te; ty=ty_exp; }
              | None -> raise (TypingError (
                  ConvertibilityError (te,Context.to_context ctx,ty_exp,jte.ty)))

  and check_app sg pb jdg_f consumed_te consumed_ty args = 
    match args with
      | [] -> pb,jdg_f
      | u::atl -> begin match M.whnf sg pb jdg_f.ty with
        | Pi (_,_,a,b) -> let (pb2,u_inf) = check sg pb u {ctx=jdg_f.ctx; te=a; ty=mk_Type dloc} in
            check_app sg pb2 {ctx=jdg_f.ctx; te=mk_App jdg_f.te u_inf.te []; ty=Subst.subst b u_inf.te;} (u_inf.te::consumed_te) (a::consumed_ty) atl
        | Meta _ | App (Meta _, _, _) -> let ctx = jdg_f.ctx in
            let ctxlen = List.length (Context.to_context ctx) in let rlen = List.length consumed_te in
		    let (pb2,jdg_u) = infer sg pb ctx u in
		    let ctx0 = List.fold_right (fun ty ctx0 -> Context.add dloc empty {ctx=ctx0; te=ty; ty=mk_Type dloc;}) (jdg_u.ty::consumed_ty) ctx in
		    let (pb3,mk) = M.new_sort pb2 ctx0 dloc empty in (* mk new sort meta in consumed_ty ++ ctx *)
		    let subst_pre = List.append consumed_te (List.rev_map (mk_DB dloc empty) (revseq (1+rlen) (rlen+ctxlen))) in
		     (* variables in ctx need to be kept the same, but Subst.psubst_l would modify them if we didn't append a bunch of DB *)
		    let subst0 = (mk_DB dloc empty 0)::subst_pre in
		    let mk0 = subst_l subst0 0 mk in begin
		    match M.unify sg ctx pb3 jdg_f.ty (mk_Pi dloc empty jdg_u.ty mk0) with (* ty_f === Pi ty_u mk0 *)
		      | Some pb4 -> let subst1 = jdg_u.te::subst_pre in
		          let mk1 = subst_l subst1 0 mk in
		            check_app sg pb4 {ctx=ctx; te=mk_App jdg_f.te jdg_u.te []; ty=mk1;} (jdg_u.te::consumed_te) (jdg_u.ty::consumed_ty) atl
		      | None -> raise (TypingError (ProductExpected (jdg_f.te, Context.to_context ctx, jdg_f.ty)))
		    end
        | _ -> raise (TypingError (ProductExpected (jdg_f.te,Context.to_context jdg_f.ctx,jdg_f.ty)))
        end
(*  
    match M.whnf sg pb jdg_f.ty with
      | Pi (_,_,a,b) ->
          (* (x) might be Kind if CoC flag is on but it does not matter here *)
          let _ = check sg pb arg { ctx=jdg_f.ctx; te=a; ty=mk_Type dloc (* (x) *); } in
            { ctx=jdg_f.ctx; te=mk_App jdg_f.te arg []; ty=Subst.subst b arg; }
      | _ ->
          raise (TypingError (
            ProductExpected (jdg_f.te,Context.to_context jdg_f.ctx,jdg_f.ty)))
*)

end

module KRefine : RefinerS with type meta_t = KMeta.t
 = Refiner(KMeta)

module MetaRefine : RefinerS with type meta_t = RMeta.t
 = Refiner(RMeta)

let inference sg (te:term) : judgment =
  let pb,jdg0 = MetaRefine.infer sg RMeta.empty Context.empty te in
  let te0 = RMeta.apply pb jdg0.te in
    snd (KRefine.infer sg KMeta.empty Context.empty te0)

let checking sg (te:term) (ty_exp:term) : judgment =
  let pb,jdg_ty = MetaRefine.infer sg RMeta.empty Context.empty ty_exp in
  let pb2,jdg_te = MetaRefine.check sg pb te jdg_ty in
  let ty_r = RMeta.apply pb2 jdg_ty.te in let te_r = RMeta.apply pb2 jdg_te.te in
  let _,jty = KRefine.infer sg KMeta.empty Context.empty ty_r in
    snd (KRefine.check sg KMeta.empty te_r jty)

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

(* **** TYPE CHECKING/INFERENCE FOR PATTERNS ******************************** *)

let rec infer_pattern sg (ctx:Context.t) (q:int) (sigma:SS.t) (pat:pattern) : term*SS.t =
  match pat with
  | Pattern (l,md,id,args) ->
    let (_,ty,si) = List.fold_left (infer_pattern_aux sg ctx q)
        (mk_Const l md id,SS.apply sigma (Signature.get_type sg l md id) q,sigma) args in
    (ty,si)
  | Var (l,x,n,args) ->
    let (_,ty,si) = List.fold_left (infer_pattern_aux sg ctx q)
        (mk_DB l x n,SS.apply sigma (Context.get_type ctx l x n) q,sigma) args in
    (ty,si)
  | Brackets t -> ( (snd(KRefine.infer sg KMeta.empty ctx t)).ty, SS.identity )
  | Lambda (l,x,p) -> raise (TypingError (DomainFreeLambda l))

and infer_pattern_aux sg (ctx:Context.t) (q:int) (f,ty_f,sigma0:term*term*SS.t) (arg:pattern) : term*term*SS.t =
  match KMeta.whnf sg KMeta.empty ty_f with
    | Pi (_,_,a,b) ->
        let sigma = check_pattern sg ctx q a sigma0 arg in
        let arg' = pattern_to_term arg in
        let b2 = SS.apply sigma b (q+1) in
        let arg2 = SS.apply sigma arg' q in
        ( Term.mk_App f arg' [], Subst.subst b2 arg2, sigma )
    | ty_f -> raise (TypingError ( ProductExpected (f,Context.to_context ctx,ty_f)))

and check_pattern sg (ctx:Context.t) (q:int) (exp_ty:term) (sigma0:SS.t) (pat:pattern) : SS.t =
  match pat with
  | Lambda (l,x,p) ->
      begin
        match KMeta.whnf sg KMeta.empty exp_ty with
          | Pi (l,x,a,b) ->
              let ctx2 = Context.unsafe_add ctx l x a in
                check_pattern sg ctx2 (q+1) b sigma0 p
          | exp_ty -> raise (TypingError ( ProductExpected (pattern_to_term pat,Context.to_context ctx,exp_ty)))
      end
   | Brackets t ->
     ( ignore (KRefine.check sg KMeta.empty t { ctx; te=exp_ty; ty=Term.mk_Type dloc; });
       SS.identity )
  | _ ->
      begin
        let (inf_ty,sigma1) = infer_pattern sg ctx q sigma0 pat in
          match pseudo_unification sg q exp_ty inf_ty with
            | None ->
              raise (TypingError (ConvertibilityError (pattern_to_term pat,Context.to_context ctx,exp_ty,inf_ty)))
            | Some sigma2 -> SS.merge sigma1 sigma2
      end

(* ************************************************************************** *)

let check_rule sg (ctx,le,ri:rule) : unit =
  let ctx =
    List.fold_left (fun ctx (l,id,ty) -> Context.add l id (snd(KRefine.infer sg KMeta.empty ctx ty)) )
      Context.empty (List.rev ctx) in
  let (ty_inf,sigma) = infer_pattern sg ctx 0 SS.identity le in
  let ri2 =
    if SS.is_identity sigma then ri
    else ( debug "%a" SS.pp sigma ; (SS.apply sigma ri 0) ) in
  let _,j_ri = KRefine.infer sg KMeta.empty ctx ri2 in
    match KMeta.unify sg ctx KMeta.empty ty_inf j_ri.ty with
      | Some _ -> ()
      | None -> raise (TypingError (ConvertibilityError (ri,Context.to_context ctx,ty_inf,j_ri.ty)))

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
