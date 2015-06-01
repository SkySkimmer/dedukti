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
  | Extra of loc*'a


type 'a context = ( loc * ident * 'a term ) list

let rec get_loc = function
  | Type l | DB (l,_,_) | Const (l,_,_) | Lam (l,_,_,_) | Pi (l,_,_,_) | Extra (l,_) -> l
  | Kind -> dloc
  | App (f,_,_) -> get_loc f

let mk_Kind             = Kind
let mk_Type l           = Type l
let mk_DB l x n         = DB (l,x,n)
let mk_Const l m v      = Const (l,m,v)
let mk_Lam l x a b      = Lam (l,x,a,b)
let mk_Pi l x a b       = Pi (l,x,a,b)
let mk_Arrow l a b      = Pi (l,qmark,a,b)
let mk_Extra l ex       = Extra (l,ex)

let mk_App f a1 args =
  match f with
    | App (f',a1',args') -> App (f',a1',args'@(a1::args))
    | _ -> App(f,a1,args)

type untyped = { hole : ident }
type pretyped = { meta : ident*int*((ident*(pretyped term)) list) }
type typed = { exfalso : 'r. 'r }

type 'a tkind =
  | Untyped : untyped tkind
  | Pretyped : pretyped tkind
  | Typed : typed tkind

let rec generalize_typed = function
  | Kind | Type _ | DB _ | Const _ as t -> t
  | Lam (lc,x,Some a,b) -> Lam (lc,x,Some (generalize_typed a),generalize_typed b)
  | Lam (lc,x,None,b) -> Lam (lc,x,None,generalize_typed b)
  | Pi (lc,x,a,b) -> Pi (lc,x,generalize_typed a,generalize_typed b)
  | Extra (_,ex) -> ex.exfalso

let rec term_eq (type a) (k:a tkind) (t1:a term) (t2:a term) =
  (* t1 == t2 || *)
  match t1, t2 with
    | Kind, Kind | Type _, Type _ -> true
    | DB (_,_,n), DB (_,_,n') -> n==n'
    | Const (_,m,v), Const (_,m',v') -> ident_eq v v' && ident_eq m m'
    | App (f,a,l), App (f',a',l') ->
        ( try List.for_all2 (term_eq k) (f::a::l) (f'::a'::l')
          with _ -> false )
    | Lam (_,_,a,b), Lam (_,_,a',b') -> term_eq k b b'
    | Pi (_,_,a,b), Pi (_,_,a',b') -> term_eq k a a' && term_eq k b b'
    | Extra (_,ex), Extra (_,ex') -> begin match k with
        | Untyped -> true
        | Pretyped -> let { meta=(_,n,ts) } = ex and { meta=(_,n',ts') } = ex' in
            n=n' && (try List.for_all2 (fun (_,t1) (_,t2) -> term_eq t1 t2) ts ts'
                     with | Invalid_argument _ -> false)
        | Typed -> ex.exfalso
        end
    | _, _  -> false

let rec pp_term (type a) (k:a tkind) out : a term -> unit = function
  | Kind               -> output_string out "Kind"
  | Type _             -> output_string out "Type"
  | DB  (_,x,n)        -> Printf.fprintf out "%a[%i]" pp_ident x n
  | Const (_,m,v)      -> Printf.fprintf out "%a.%a" pp_ident m pp_ident v
  | App (f,a,args)     -> pp_list " " (pp_term_wp k) out (f::a::args)
  | Lam (_,x,None,f)   -> Printf.fprintf out "%a => %a" pp_ident x (pp_term k) f
  | Lam (_,x,Some a,f) -> Printf.fprintf out "%a:%a => %a" pp_ident x (pp_term_wp k) a (pp_term k) f
  | Pi  (_,x,a,b)      -> Printf.fprintf out "%a:%a -> %a" pp_ident x (pp_term_wp k) a (pp_term k) b
  | Extra (_,ex) -> begin match k with
      | Untyped -> let { hole=s } = ex in
          if ident_eq s empty then Printf.fprintf out "?"
          else Printf.fprintf out "?{\"%a\"}" pp_ident s
      | Pretyped -> let { meta=(s,n,ts) } = ex in if ident_eq s empty
          then Printf.fprintf out "?_%i[%a]" n (pp_list ";" (fun out (x,t) -> Printf.fprintf out "%a/%a" pp_ident x (pp_term Pretyped) t)) ts
          else Printf.fprintf out "?{\"%a\"}_%i[%a]" pp_ident s n (pp_list ";" (fun out (x,t) -> Printf.fprintf out "%a/%a" pp_ident x (pp_term Pretyped) t)) ts
      | Typed -> ex.exfalso
      end

and pp_term_wp k out = function
  | Kind | Type _ | DB _ | Const _ | Extra _ as t -> pp_term k out t
  | t                                  -> Printf.fprintf out "(%a)" (pp_term k) t

let pp_context k out ctx =
  pp_list ", " (fun out (_,x,ty) ->
                   Printf.fprintf out "%a: %a" pp_ident x (pp_term k) ty )
    out (List.rev ctx)


type mkind =
  | MTyped of pretyped term
  | MType
  | MSort

