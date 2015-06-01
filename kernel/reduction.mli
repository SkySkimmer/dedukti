open Term
(** Term reduction and conversion test. *)

(** Head Normal Form *)
val hnf         : 'a tkind -> Signature.t -> 'a term -> 'a term

(** Weak Head Normal Form *)
val whnf        : 'a tkind -> Signature.t -> 'a term -> 'a term

(** Strong Normal Form *)
val snf         : 'a tkind -> Signature.t -> 'a term -> 'a term

(** Conversion Test *)
val are_convertible             : 'a tkind -> Signature.t -> 'a term -> 'a term -> bool

(**One Step Reduction*)
val one_step                    : 'a tkind -> Signature.t -> 'a term -> 'a term option
