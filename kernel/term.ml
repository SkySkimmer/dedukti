open Basics

(** {2 Terms/Patterns} *)

type 'a term =
  | Kind                                      (* Kind *)
  | Type  of loc                              (* Type *)
  | DB    of loc*ident*int                    (* deBruijn *)
  | Const of loc*ident*ident                  (* Global variable *)
  | App   of 'a term * 'a term * 'a term list (* f a1 [ a2 ; ... an ] , f not an App *)
  | Lam   of loc*ident*'a term option*'a term (* Lambda abstraction *)
  | Pi    of loc*ident*'a term*'a term        (* Pi abstraction *)
  | Extra of loc*'a tkind*'a

and lsubst = (ident*pretyped term) list

and 'a tkind =
  | Untyped : untyped tkind
  | Pretyped : pretyped tkind
  | Typed : typed tkind

and untyped = U of ident
and pretyped = 
  | Meta of ident*int*lsubst
  | Guard of int*lsubst*pretyped term
and typed = { exfalso : 'r. 'r }


type 'a context = ( loc * ident * 'a term ) list

let rec get_loc = function
  | Type l | DB (l,_,_) | Const (l,_,_) | Lam (l,_,_,_) | Pi (l,_,_,_) | Extra (l,_,_) -> l
  | Kind -> dloc
  | App (f,_,_) -> get_loc f

let mk_Kind             = Kind
let mk_Type l           = Type l
let mk_DB l x n         = DB (l,x,n)
let mk_Const l m v      = Const (l,m,v)
let mk_Lam l x a b      = Lam (l,x,a,b)
let mk_Pi l x a b       = Pi (l,x,a,b)
let mk_Arrow l a b      = Pi (l,qmark,a,b)
let mk_Extra l kind ex       = Extra (l,kind,ex)

let mk_Hole lc s = Extra (lc,Untyped,U s)
let mk_Meta lc s n ts = Extra (lc,Pretyped,Meta(s,n,ts))
let mk_Guard lc n ts t = Extra (lc,Pretyped,Guard(n,ts,t))

let mk_App f a1 args =
  match f with
    | App (f',a1',args') -> App (f',a1',args'@(a1::args))
    | _ -> App(f,a1,args)


let rec lift_term : type a. typed term -> a term = function
  | Kind | Type _ | DB _ | Const _ as t -> t
  | App (f,a,args) -> App (lift_term f, lift_term a, List.map lift_term args)
  | Lam (lc,x,Some a,b) -> Lam (lc,x,Some (lift_term a),lift_term b)
  | Lam (lc,x,None,b) -> Lam (lc,x,None,lift_term b)
  | Pi (lc,x,a,b) -> Pi (lc,x,lift_term a,lift_term b)
  | Extra (_,_,ex) -> ex.exfalso

let rec term_eq : type a. a term -> a term -> bool = fun t1 t2 ->
  (* t1 == t2 || *)
  match t1, t2 with
    | Kind, Kind | Type _, Type _ -> true
    | DB (_,_,n), DB (_,_,n') -> n==n'
    | Const (_,m,v), Const (_,m',v') -> ident_eq v v' && ident_eq m m'
    | App (f,a,l), App (f',a',l') ->
        ( try List.for_all2 term_eq (f::a::l) (f'::a'::l')
          with _ -> false )
    | Lam (_,_,a,b), Lam (_,_,a',b') -> term_eq b b'
    | Pi (_,_,a,b), Pi (_,_,a',b') -> term_eq a a' && term_eq b b'
    | Extra (_,Untyped,_), Extra (_,Untyped,_) -> true
    | Extra (_,Pretyped,Meta(_,n,ts)), Extra (_,Pretyped,Meta(_,n',ts')) when (n=n') ->
        lsubst_eq ts ts'
    | Extra (_,Pretyped,Guard(n,ls,t)), Extra (_,Pretyped,Guard(n',ls',t')) when (n=n') ->
        lsubst_eq ls ls' && term_eq t t'
    | Extra (_,Typed,ex), Extra (_,Typed,_) -> ex.exfalso
    | _, _  -> false

and lsubst_eq : lsubst -> lsubst -> bool = fun ls ls' ->
  try List.for_all2 (fun (_,t1) (_,t2) -> term_eq t1 t2) ls ls'
  with | Invalid_argument _ -> false

let rec pp_term : type a. _ -> a term -> unit = fun out -> function
  | Kind               -> output_string out "Kind"
  | Type _             -> output_string out "Type"
  | DB  (_,x,n)        -> Printf.fprintf out "%a[%i]" pp_ident x n
  | Const (_,m,v)      -> Printf.fprintf out "%a.%a" pp_ident m pp_ident v
  | App (f,a,args)     -> pp_list " " pp_term_wp out (f::a::args)
  | Lam (_,x,None,f)   -> Printf.fprintf out "%a => %a" pp_ident x pp_term f
  | Lam (_,x,Some a,f) -> Printf.fprintf out "%a:%a => %a" pp_ident x pp_term_wp a pp_term f
  | Pi  (_,x,a,b)      -> Printf.fprintf out "%a:%a -> %a" pp_ident x pp_term_wp a pp_term b
  | Extra (_,Untyped,U s) when (ident_eq s empty) -> Printf.fprintf out "?"
  | Extra (_,Untyped,U s) -> Printf.fprintf out "?{\"%a\"}" pp_ident s
  | Extra (_,Pretyped,Meta(s,n,ts)) when (ident_eq s empty) ->
      Printf.fprintf out "?_%i%a" n pp_lsubst ts
  | Extra (_,Pretyped,Meta(s,n,ts)) ->
      Printf.fprintf out "?{\"%a\"}_%i%a" pp_ident s n pp_lsubst ts
  | Extra (_,Pretyped,Guard(n,ls,t)) -> Printf.fprintf out "#%i%a %a" n pp_lsubst ls pp_term_wp t
  | Extra (_,Typed,ex) -> ex.exfalso

and pp_lsubst out ls = Printf.fprintf out "[%a]" (pp_list ";" (fun out (x,t) -> Printf.fprintf out "%a/%a" pp_ident x pp_term t)) ls

and pp_term_wp : type a. _ -> a term -> unit = fun out -> function
  | Kind | Type _ | DB _ | Const _ | Extra _ as t -> pp_term out t
  | t                                  -> Printf.fprintf out "(%a)" pp_term t

let pp_context out ctx =
  pp_list ", " (fun out (_,x,ty) ->
                   Printf.fprintf out "%a: %a" pp_ident x pp_term ty )
    out (List.rev ctx)


type mkind =
  | MTyped of pretyped term
  | MType
  | MSort

