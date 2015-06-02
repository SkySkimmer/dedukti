open Term
(** Term reduction and conversion test. *)

(** Head Normal Form *)
val hnf         : Signature.t -> 'a term -> 'a term

(** Weak Head Normal Form *)
val whnf        : Signature.t -> 'a term -> 'a term

(** Strong Normal Form *)
val snf         : Signature.t -> 'a term -> 'a term

(** Conversion Test *)
val are_convertible             : Signature.t -> 'a term -> 'a term -> bool

(**One Step Reduction*)
val one_step                    : Signature.t -> 'a term -> 'a term option
