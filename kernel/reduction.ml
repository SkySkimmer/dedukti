open Basic
open Term
open Rule

type 'a env = 'a term Lazy.t LList.t

type 'a state = {
  ctx:'a env;              (*context*)
  term : 'a term;          (*term to reduce*)
  stack : 'a stack;        (*stack*)
}
and 'a stack = 'a state list

let rec term_of_state {ctx;term;stack} =
  let t = ( if LList.is_empty ctx then term else Subst.psubst_l ctx 0 term ) in
    match stack with
      | [] -> t
      | a::lst -> mk_App t (term_of_state a) (List.map term_of_state lst)

let rec add_to_list2 l1 l2 lst =
  match l1, l2 with
    | [], [] -> Some lst
    | s1::l1, s2::l2 -> add_to_list2 l1 l2 ((s1,s2)::lst)
    | _,_ -> None

let rec split_stack (i:int) : 'a stack -> ('a stack*'a stack) option = function
  | l  when i=0 -> Some ([],l)
  | []          -> None
  | x::l        -> map_opt (fun (s1,s2) -> (x::s1,s2) ) (split_stack (i-1) l)

let rec safe_find m v = function
  | []                  -> None
  | (_,m',v',tr)::tl       ->
      if ident_eq v v' && ident_eq m m' then Some tr
      else safe_find m v tl

let rec add_to_list lst (s :'a stack) (s' :'a stack) =
  match s,s' with
    | [] , []           -> Some lst
    | x::s1 , y::s2     -> add_to_list ((x,y)::lst) s1 s2
    | _ ,_              -> None

let pp_env out (ctx:'a env) =
  let pp_lazy_term out lt = pp_term out (Lazy.force lt) in
    pp_list ", " pp_lazy_term out (LList.lst ctx)

let pp_state out { ctx; term; stack } =
   Printf.fprintf out "[ e=[...](%i) | %a | [...] ] { %a } "
     (LList.len ctx)
     pp_term term
     pp_term (term_of_state { ctx; term; stack })

let pp_stack out st =
  let aux out state =
    pp_term out (term_of_state state)
  in
    Printf.fprintf out "[ %a ]\n" (pp_list "\n | " aux) st

(* ********************* *)

let rec beta_reduce : 'a state -> 'a state = function
    (* Weak heah beta normal terms *)
    | { term=Type _ }
    | { term=Kind }
    | { term=Const _ }
    | { term=Pi _ }
    | { term=Extra _ }
    | { term=Lam _; stack=[] } as config -> config
    | { ctx={ LList.len=k }; term=DB (_,_,n) } as config when (n>=k) -> config
    (* DeBruijn index: environment lookup *)
    | { ctx; term=DB (_,_,n); stack } (*when n<k*) ->
        beta_reduce { ctx=LList.nil; term=Lazy.force (LList.nth ctx n); stack }
    (* Beta redex *)
    | { ctx; term=Lam (_,_,_,t); stack=p::s } ->
        beta_reduce { ctx=LList.cons (lazy (term_of_state p)) ctx; term=t; stack=s }
    (* Application: arguments go on the stack *)
    | { ctx; term=App (f,a,lst); stack=s } ->
        (* rev_map + rev_append to avoid map + append*)
        let tl' = List.rev_map ( fun t -> {ctx;term=t;stack=[]} ) (a::lst) in
          beta_reduce { ctx; term=f; stack=List.rev_append tl' s }

(* ********************* *)

type 'a find_case_ty =
  | FC_Lam of dtree*'a state
  | FC_Const of dtree*'a state list
  | FC_DB of dtree*'a state list
  | FC_None

let rec find_case (st:'a state) (cases:(case*dtree) list) : 'a find_case_ty =
  match st, cases with
    | _, [] -> FC_None
    | { term=Const (_,m,v); stack } , (CConst (nargs,m',v'),tr)::tl ->
        if ident_eq v v' && ident_eq m m' then
          ( assert (List.length stack == nargs);
            FC_Const (tr,stack) )
        else find_case st tl
    | { term=DB (l,x,n); stack } , (CDB (nargs,n'),tr)::tl ->
        if n==n' && (List.length stack == nargs) then (*TODO explain*)
             FC_DB (tr,stack)
        else find_case st tl
    | { ctx; term=Lam (_,_,_,_) } , ( CLam , tr )::tl ->
        begin
          match term_of_state st with
            | Lam (_,_,_,te) ->
                FC_Lam ( tr , { ctx=LList.nil; term=te; stack=[] } )
            | _ -> assert false
        end
    | _, _::tl -> find_case st tl


let rec reduce : type a. _ -> a state -> a state = fun sg st ->
  match beta_reduce st with
    | { ctx; term=Const (l,m,v); stack } as config ->
        begin
          match Signature.get_dtree sg l m v with
            | None -> config
            | Some (i,g) ->
                begin
                  match split_stack i stack with
                    | None -> config
                    | Some (s1,s2) ->
                        ( match rewrite sg s1 g with
                            | None -> config
                            | Some (ctx,term) -> reduce sg { ctx; term; stack=s2 }
                        )
                end
        end
    | config -> config

(*TODO implement the stack as an array ? (the size is known in advance).*)
and rewrite : type a. _ -> a stack -> _ -> (a env*a term) option = fun sg stack g ->
  let rec test ctx = function
    | [] -> true
    | (Linearity (t1,t2))::tl ->
      if are_convertible_lst sg [ term_of_state { ctx; term=lift_term t1; stack=[] },
                                  term_of_state { ctx; term=lift_term t2; stack=[] } ]
      then test ctx tl
      else false
    | (Bracket (t1,t2))::tl ->
      if are_convertible_lst sg [ term_of_state { ctx; term=lift_term t1; stack=[] },
                                  term_of_state { ctx; term=lift_term t2; stack=[] } ]
      then test ctx tl
      else
        failwith "Error while reducing a term: a guard was not satisfied." (*FIXME*)
  in
    (*dump_stack stack ; *)
    match g with
      | Switch (i,cases,def) ->
          begin
            let arg_i = reduce sg (List.nth stack i) in
              match find_case arg_i cases with
                | FC_DB (g,s) | FC_Const (g,s) -> rewrite sg (stack@s) g
                | FC_Lam (g,te) -> rewrite sg (stack@[te]) g
                | FC_None -> bind_opt (rewrite sg stack) def
          end
      | Test (Syntactic ord,[],right,def) ->
          begin
            match get_context_syn sg stack ord with
              | None -> bind_opt (rewrite sg stack) def
              | Some ctx -> Some (ctx, lift_term right)
          end
      | Test (Syntactic ord, eqs, right, def) ->
          begin
            match get_context_syn sg stack ord with
              | None -> bind_opt (rewrite sg stack) def
              | Some ctx ->
                  if test ctx eqs then Some (ctx, lift_term right)
                  else bind_opt (rewrite sg stack) def
          end
      | Test (MillerPattern lst, eqs, right, def) ->
          begin
              match get_context_mp sg stack lst with
                | None -> bind_opt (rewrite sg stack) def
                | Some ctx ->
                      if test ctx eqs then Some (ctx, lift_term right)
                      else bind_opt (rewrite sg stack) def
          end

and unshift : type a. _ -> _ -> a term -> a term = fun sg q te ->
  try Subst.unshift q te
  with Subst.UnshiftExn ->
    Subst.unshift q (snf sg te)

and get_context_syn : type a. _ -> a stack -> _ -> a env option = fun sg stack ord ->
  try Some (LList.map (
    fun p ->
      if ( p.depth = 0 ) then
        lazy (term_of_state (List.nth stack p.position) )
      else
        Lazy.from_val
          (unshift sg p.depth (term_of_state (List.nth stack p.position) ))
  ) ord )
  with Subst.UnshiftExn -> ( (*Print.debug "Cannot unshift";*) None )

and get_context_mp : type a. _ -> a stack -> _ -> a env option = fun sg stack pb_lst ->
  let aux (pb:abstract_pb)  =
    Lazy.from_val ( unshift sg pb.depth2 (
      (Matching.resolve pb.dbs (term_of_state (List.nth stack pb.position2))) ))
  in
  try Some (LList.map aux pb_lst)
  with
    | Subst.UnshiftExn
    | Matching.NotUnifiable -> None

(* ********************* *)

(* Weak Normal Form *)
and whnf : type a. _ -> a term -> a term = fun sg term -> term_of_state ( reduce sg { ctx=LList.nil; term; stack=[] } )

(* Strong Normal Form *)
and snf : type a. _ -> a term -> a term = fun sg t ->
  match whnf sg t with
    | Kind | Const _
    | DB _ | Type _ as t' -> t'
    | App (f,a,lst)     -> mk_App (snf sg f) (snf sg a) (List.map (snf sg) lst)
    | Pi (_,x,a,b)        -> mk_Pi dloc x (snf sg a) (snf sg b)
    | Lam (_,x,a,b)       -> mk_Lam dloc x None (snf sg b)
    | Extra (_,Untyped,_) as t' -> t'
    | Extra (lc,Pretyped,Meta(s,n,ts)) -> mk_Meta lc s n (List.map (fun (x,t) -> x,snf sg t) ts)
    | Extra (lc,Pretyped,Guard(n,ts,t)) -> mk_Guard lc n (List.map (fun (x,t) -> x,snf sg t) ts) (snf sg t)
    | Extra (_,Typed,ex) -> ex.exfalso

and are_convertible_lst : type a. _ -> (a term*a term) list -> bool = fun sg -> function
  | [] -> true
  | (t1,t2)::lst ->
    begin
      match (
        if term_eq t1 t2 then Some lst
        else
          match whnf sg t1, whnf sg t2 with
          | Kind, Kind | Type _, Type _ -> Some lst
          | Const (_,m,v), Const (_,m',v') when ( ident_eq v v' && ident_eq m m' ) -> Some lst
          | DB (_,_,n), DB (_,_,n') when ( n==n' ) -> Some lst
          | App (f,a,args), App (f',a',args') ->
            add_to_list2 args args' ((f,f')::(a,a')::lst)
          | Lam (_,_,_,b), Lam (_,_,_,b') -> Some ((b,b')::lst)
          | Pi (_,_,a,b), Pi (_,_,a',b') -> Some ((a,a')::(b,b')::lst)
          | Extra (_,Untyped,_), Extra (_,Untyped,_) -> Some lst
          | Extra (_,Pretyped,Meta(_,n,ts)), Extra (_,Pretyped,Meta(_,n',ts')) ->
              if n=n' then add_to_list2 (List.map snd ts) (List.map snd ts') lst
              else None
          | Extra (_,Typed,ex), Extra (_,Typed,_) -> ex.exfalso
          | t1, t2 -> None
      ) with
      | None -> false
      | Some lst2 -> are_convertible_lst sg lst2
    end

(* Head Normal Form *)
let rec hnf sg t =
  match whnf sg t with
    | Kind | Const _ | DB _ | Type _ | Pi (_,_,_,_) | Lam (_,_,_,_) | Extra _ as t' -> t'
    | App (f,a,lst) -> mk_App (hnf sg f) (hnf sg a) (List.map (hnf sg) lst)

(* Convertibility Test *)
let are_convertible sg t1 t2 = are_convertible_lst sg [(t1,t2)]

(* One-Step Reduction *)
let rec state_one_step (sg:Signature.t) : 'a state -> 'a state option = function
    (* Weak heah beta normal terms *)
    | { term=Type _ }
    | { term=Kind }
    | { term=Pi _ }
    | { term=Extra _}
    | { term=Lam _; stack=[] } -> None
    | { ctx={ LList.len=k }; term=DB (_,_,n) } when (n>=k) -> None
    (* DeBruijn index: environment lookup *)
    | { ctx; term=DB (_,_,n); stack } (*when n<k*) ->
        state_one_step sg { ctx=LList.nil; term=Lazy.force (LList.nth ctx n); stack }
    (* Beta redex *)
    | { ctx; term=Lam (_,_,_,t); stack=p::s } ->
        Some { ctx=LList.cons (lazy (term_of_state p)) ctx; term=t; stack=s }
    (* Application: arguments go on the stack *)
    | { ctx; term=App (f,a,lst); stack=s } ->
        (* rev_map + rev_append to avoid map + append*)
        let tl' = List.rev_map ( fun t -> {ctx;term=t;stack=[]} ) (a::lst) in
          state_one_step sg { ctx; term=f; stack=List.rev_append tl' s }
    (* Constant Application *)
    | { ctx; term=Const (l,m,v); stack } ->
        begin
          match Signature.get_dtree sg l m v with
            | None -> None
            | Some (i,g) ->
                begin
                  match split_stack i stack with
                    | None -> None
                    | Some (s1,s2) ->
                        ( match rewrite sg s1 g with
                            | None -> None
                            | Some (ctx,term) -> Some { ctx; term; stack=s2 }
                        )
                end
        end

let one_step sg t =
  map_opt term_of_state (state_one_step sg { ctx=LList.nil; term=t; stack=[] })
