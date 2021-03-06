open Basic

(** Lambda terms *)

(** {2 Terms} *)

type 'a term = private
  | Kind                                      (** Kind *)
  | Type  of loc                              (** Type *)
  | DB    of loc*ident*int                    (** deBruijn indices *)
  | Const of loc*ident*ident                  (** Global variable *)
  | App   of 'a term * 'a term * 'a term list (** f a1 [ a2 ; ... an ] , f not an App *)
  | Lam   of loc*ident*'a term option*'a term (** Lambda abstraction *)
  | Pi    of loc*ident*'a term*'a term        (** Pi abstraction *)
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

val get_loc : 'a term -> loc

val mk_Kind     : 'a term
val mk_Type     : loc -> 'a term
val mk_DB       : loc -> ident -> int -> 'a term
val mk_Const    : loc -> ident -> ident -> 'a term
val mk_Lam      : loc -> ident -> 'a term option -> 'a term -> 'a term
val mk_App      : 'a term -> 'a term -> 'a term list -> 'a term
val mk_Pi       : loc -> ident -> 'a term -> 'a term -> 'a term
val mk_Arrow    : loc -> 'a term -> 'a term -> 'a term
val mk_Extra    : loc -> 'a tkind -> 'a -> 'a term

val mk_Hole     : loc -> ident -> untyped term
val mk_Meta     : loc -> ident -> int -> lsubst -> pretyped term
val mk_Guard    : loc -> int -> lsubst -> pretyped term -> pretyped term

val lift_term : typed term -> 'a term

(* Syntactic equality / Alpha-equivalence *)
val term_eq : 'a term -> 'a term -> bool
val lsubst_eq : lsubst -> lsubst -> bool

val pp_term     : out_channel -> 'a term -> unit
val pp_lsubst   : out_channel -> lsubst  -> unit

(** {2 Contexts} *)

type 'a context = ( loc * ident * 'a term ) list
val pp_context  : out_channel -> 'a context -> unit

(** {3 Metavariable types} *)

type mkind =
  | MTyped of pretyped term
  | MType
  | MSort

