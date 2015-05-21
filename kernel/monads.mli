open Basics

(**
For effect kind Kind (eg State):
- KindS is the signature of the effect operations (eg type state; val get : state t)
- KindF is a functor adding the effects to a monad. Usually it takes a monad + some arguments (eg a type for the state)
- KindF(M)(Args).OtherT(MIsOther) passes effects of kind Other if they're available in M
*)

module type Monad = sig
  type +'a t
  
  val return : 'a -> 'a t
  
  val (>>=) : 'a t -> ('a -> 'b t) -> 'b t
end

module type MonadS = sig
  type 'a t
  
  val fold : ('a -> 'b -> 'a t) -> 'a -> 'b list -> 'a t
end

module MonadF (M:Monad) : MonadS with type 'a t := 'a M.t

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

module Opt : sig
  include Monad with type 'a t = 'a option
  include MonadS with type 'a t := 'a t
end

module type MonadT = sig
  type 'a m
  type 'a t
  val lift : 'a m -> 'a t
end

type ('a,'b,'e) list_view =
  | Nil of 'e
  | Cons of 'a*('e -> 'b)

module type BacktrackS = sig
  type 'a t
  type err

  val zero : err -> 'a t
  val plus : 'a t -> (err -> 'a t) -> 'a t
  
  val split : 'a t -> ('a, 'a t, err) list_view t
  
  val once : 'a t -> 'a t
end

module type StateS = sig
  type 'a t
  type state

  val get : state t
  val set : state -> unit t
  val modify : (state -> state) -> unit t
end

module BacktrackF (M:Monad) (E:sig type err end) : sig
  include Monad
  
  include MonadT with type 'a m = 'a M.t and type 'a t := 'a t
  
  include BacktrackS with type 'a t := 'a t and type err = E.err
  
  module EffectT(E:EffectS with type 'a t = 'a M.t) : EffectS with type 'a t := 'a t
  
  module StateT(S:StateS with type 'a t = 'a M.t) : StateS with type 'a t := 'a t
  
  val run : 'a t -> ('a, 'a t, err) list_view M.t
end

module StateF (M:Monad) (S:sig type state end) : sig
  include Monad
  
  include MonadT with type 'a m = 'a M.t and type 'a t := 'a t
  
  include StateS with type 'a t := 'a t and type state = S.state

  module EffectT(E:EffectS with type 'a t = 'a M.t) : EffectS with type 'a t := 'a t

  module BacktrackT(B:BacktrackS with type 'a t = 'a M.t) : BacktrackS with type 'a t := 'a t and type err = B.err
  
  val run : 'a t -> state -> ('a*state) M.t
end

