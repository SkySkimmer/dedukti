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

module MonadF (M:Monad) = struct
  include M
  
  let rec fold f acc = function
    | [] -> return acc
    | x::l -> f acc x >>= fun acc' -> fold f acc' l
end

module ID = struct
  type 'a t = 'a
  
  let return x = x
  
  let (>>=) m f = f m
end

module type EffectS = sig
  type 'a t
  
  val effectful : (unit -> 'a) -> 'a t
end

module IO = struct
  type 'a t = unit -> 'a
  
  let return x = fun () -> x
  
  let (>>=) m f = fun () -> f (m()) ()
  
  let effectful f = fun () -> f ()
  
  let run f () = f ()
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
end

module type StateS = sig
  type 'a t
  type state

  val get : state t
  val set : state -> unit t
  val modify : (state -> state) -> unit t
end

module BacktrackF (M:Monad) (E:sig type err end) = struct
  type err = E.err

  type 'a t =
    { k : 'r. ('a -> (err -> 'r M.t) -> 'r M.t) -> (err -> 'r M.t) -> 'r M.t }

  let return x =
    { k = fun sk fk -> sk x fk }

  let (>>=) m f =
    { k = fun sk fk -> m.k (fun a fk -> (f a).k sk fk) fk }

  type 'a m = 'a M.t
  let lift x =
    { k = fun sk fk -> M.(x >>= fun a -> sk a fk) }

  let zero e =
    { k = fun sk fk -> fk e }

  let plus m1 m2 =
    { k = fun sk fk -> m1.k sk (fun e -> (m2 e).k sk fk) }

  let reflect : ('a,'a t,err) list_view -> 'a t = function
      | Nil e -> zero e
      | Cons (x,l) -> plus (return x) l

  let split (m:'a t) : ('a, 'a t, err) list_view t =
    let sk x fk = M.return (Cons (x, fun e -> lift (fk e) >>= reflect)) in
    let fk e = M.return (Nil e) in
      lift (m.k sk fk)

  module EffectT(E:EffectS with type 'a t = 'a M.t) = struct
    let effectful f = lift (E.effectful f)
  end

  module StateT(S:StateS with type 'a t = 'a M.t) = struct
    type state = S.state

    let get = lift S.get

    let set s = lift (S.set s)
    
    let modify s = lift (S.modify s)
  end

  let run m =
    let sk x fk = M.return (Cons (x, fun e -> lift (fk e) >>= reflect)) in
    let fk e = M.return (Nil e) in
      m.k sk fk
end

module StateF (M:Monad) (S:sig type state end) = struct
  type state = S.state
  
  type 'a t =
    { k : 'r. ('a -> state -> 'r M.t) -> state -> 'r M.t }
  
  let return x =
    { k = fun c s -> c x s }
  
  let (>>=) (m:'a t) (f:'a -> 'b t) : 'b t =
    { k = fun c s -> m.k (fun a s' -> (f a).k c s') s }

  type 'a m = 'a M.t
  let lift m =
    { k = fun c s -> M.(m >>= fun x -> c x s) }
  
  let get =
    { k = fun c s -> c s s }
  
  let set s =
    { k = fun c _ -> c () s }

  let modify f =
    { k = fun c s -> c () (f s) }

  module EffectT(E:EffectS with type 'a t = 'a M.t) = struct
    let effectful f = lift (E.effectful f)
  end

  module BacktrackT(B:BacktrackS with type 'a t = 'a M.t) = struct
    type err = B.err

    let zero e = lift (B.zero e)

    let plus m1 m2 =
      { k = fun c s -> B.plus (m1.k c s) (fun e -> (m2 e).k c s) }

    let split m = failwith "TODO: pass split operation through state monad transformer."
  end

  let run {k} s =
    k (fun x s -> M.return (x,s)) s
end

