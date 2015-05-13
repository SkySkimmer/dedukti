open Basics

module type Monad = sig
  type +'a t
  
  val return : 'a -> 'a t
  
  val (>>=) : 'a t -> ('a -> 'b t) -> 'b t
end

module type MonadS = sig
  type 'a t
  
  val fold : ('a -> 'b -> 'a t) -> 'a -> 'b list -> 'a t
end

module MonadF (M:Monad) : MonadS with type 'a t = 'a M.t

module ID : sig
  include Monad with type 'a t = 'a
end

module type EffectS = sig
  type 'a t
  
  val effectful : (unit -> 'a) -> 'a t
end

module IO : sig
  include Monad
  include EffectS with type 'a t := 'a t
  
  val run : 'a t -> unit -> 'a
end

module type MonadTrans = sig
  type 'a m
  type 'a t
  val lift : 'a m -> 'a t
end

module Trans_IO (M:EffectS) (T:MonadTrans with type 'a m = 'a M.t)
 : EffectS with type 'a t = 'a T.t

module Trans_Trans (T1:MonadTrans)(T2:MonadTrans with type 'a m = 'a T1.t)
 : MonadTrans with type 'a m = 'a T1.m and type 'a t = 'a T2.t

type ('a,'b,'e) list_view =
  | Nil of 'e
  | Cons of 'a*('e -> 'b)

module type BacktrackS = sig
  type 'a t
  type err

  val zero : err -> 'a t
  val plus : 'a t -> (err -> 'a t) -> 'a t
  
  val split : 'a t -> ('a, 'a t, err) list_view t
end

module BacktrackF (M:Monad) (E:sig type err end) : sig
  include Monad
  
  include MonadTrans with type 'a m = 'a M.t and type 'a t := 'a t
  
  include BacktrackS with type 'a t := 'a t and type err = E.err
  
  val run : 'a t -> ('a, 'a t, err) list_view M.t
end

module Backtrack_IO (M:Monad) (MIO:EffectS with type 'a t = 'a M.t) (E:sig type err end)
 : EffectS with type 'a t = 'a BacktrackF(M)(E).t

module type StateS = sig
  type 'a t
  type state

  val get : state t
  val set : state -> unit t
  val modify : (state -> state) -> unit t
end

module StateF (M:Monad) (S:sig type state end) : sig
  include Monad
  
  include MonadTrans with type 'a m = 'a M.t and type 'a t := 'a t
  
  include StateS with type 'a t := 'a t and type state = S.state
  
  val run : 'a t -> state -> ('a*state) M.t
end

module State_Backtrack (M:Monad) (B:BacktrackS with type 'a t = 'a M.t) (S:sig type state end)
 : BacktrackS with type 'a t = 'a StateF(M)(S).t and type err = B.err

