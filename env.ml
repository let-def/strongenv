open L

(* Untyped ident: a string and an integer *)

module Ident : sig
  type t
  val fresh : string -> t
  val name : t -> string
  val stamp : t -> int
end = struct
  type t = { name : string; stamp : int }
  let counter = ref 0
  let fresh name = incr counter; { name; stamp = !counter }
  let name t = t.name
  let stamp t = t.stamp
end

module Env : sig
  type +'a t
  val empty : 'a t
  val bind : string -> 'a -> 'a t -> 'a t * Ident.t
  val get : Ident.t -> 'a t -> 'a
  val update : Ident.t -> 'a -> 'a t -> 'a t
  val lookup : string -> 'a t -> ('a * Ident.t) option
end = struct
  type 'a t = (Ident.t * 'a) list
  let empty = []
  let bind k v t =  let k = Ident.fresh k in ((k, v) :: t, k)
  let rec get k = function
    | [] -> invalid_arg "Env.get: identifier not bound"
    | (k', v) :: _ when Ident.stamp k = Ident.stamp k' -> v
    | _ :: rest -> get k rest
  let update k v t = (k, v) :: t
  let rec lookup k = function
    | [] -> None
    | (k', v) :: _ when Ident.name k' = k -> Some (v, k')
    | _ :: rest -> lookup k rest
end

module EnvW : sig
  type -'w bindings
  type +'w bound

  type (-'w, +'a) env = ('w bindings, 'a Env.t) p
  type +'w ident = ('w bound, Ident.t) p

  val empty : (o, _) env

  type (_, 'a) bind =
      Bind : ('w1, 'w2) incl * ('w2, 'a) env * 'w2 ident -> ('w1, 'a) bind

  val bind : string -> 'a -> ('w, 'a) env -> ('w, 'a) bind
  val get : 'w ident -> ('w, 'a) env -> 'a
  val update : 'w ident -> 'a -> ('w, 'a) env -> ('w, 'a) env
  val lookup : string -> ('w, 'a) env -> ('a * 'w ident) option
end = struct
  type -'w bindings = 'w Prop.neg
  type +'w bound = 'w Prop.pos

  type (-'w, +'a) env = ('w bindings, 'a Env.t) p
  type +'w ident = ('w bound, Ident.t) p

  let empty : (o, _) env =
    Prop.assume_neg Env.empty

  type (_, 'a) bind =
      Bind : ('w1, 'w2) incl * ('w2, 'a) env * 'w2 ident -> ('w1, 'a) bind

  let bind k v t =
    let env, ident = Env.bind k v (t : _ env :> _ Env.t) in
    Bind (refl_sub, Prop.assume_neg env, Prop.assume_pos ident)

  let get id env = Env.get (drop id) (drop env)

  let update id v env =
    Prop.assume_neg (Env.update (drop id) v (drop env))

  let lookup name env =
    match Env.lookup name (drop env) with
    | None -> None
    | Some (v, id) -> Some (v, Prop.assume_pos id)
end

module EnvWF : sig
  type -'w bindings
  type +'w bound
  type +'w wf

  type (-'w, +'a) env = ('w bindings, 'a Env.t) p
  type +'w ident = ('w bound, Ident.t) p
  type ('w1, 'w2) fresh = private 'w2 ident
  type (+'w, +'v) v = ('w wf, 'v) p

  val empty : (o, _) env

  type (_, 'a) bind =
      Bind : ('w1, 'w2) fresh * ('w2, 'a) env -> ('w1, 'a) bind

  val ident : (_, 'w) fresh -> 'w ident
  val incl : ('w1, 'w2) fresh -> ('w1, 'w2) incl

  val wf : 'a -> ('w, 'a) v
  val bind : string -> ('w, 'a) v -> ('w, 'a) env -> ('w, 'a) bind
  val get : 'w ident -> ('w, 'a) env -> ('w, 'a) v
  val update : 'w ident -> ('w, 'a) v -> ('w, 'a) env -> ('w, 'a) env
  val lookup : string -> ('w, 'a) env -> (('w, 'a) v * 'w ident) option

  module Lift (T : sig type 'w t end ) : sig
    type t
    val pack : 'w w T.t -> ('w, t) v
    val unpack : ('w, t) v -> 'w w T.t
  end
end = struct
  type -'w bindings = 'w Prop.neg
  type +'w bound = 'w Prop.pos
  type +'w wf = 'w Prop.pos

  type (-'w, +'a) env = ('w bindings, 'a Env.t) p
  type +'w ident = ('w bound, Ident.t) p
  type ('w1, 'w2) fresh = 'w2 ident
  type (+'w, +'v) v = ('w wf, 'v) p

  let empty : (o, _) env =
    Prop.assume_neg Env.empty

  type (_, 'a) bind =
      Bind : ('w1, 'w2) fresh * ('w2, 'a) env -> ('w1, 'a) bind

  let wf v = Prop.assume_pos v

  let ident x = x
  let incl _ = unsafe_sub

  let bind k v t =
    let env, ident = Env.bind k (drop v) (drop t) in
    Bind (Prop.assume_pos ident, Prop.assume_neg env)

  let get id env = wf (Env.get (drop id) (drop env))

  let update id v env =
    Prop.assume_neg (Env.update (drop id) (drop v) (drop env))

  let lookup name env =
    match Env.lookup name (drop env) with
    | None -> None
    | Some (v, id) -> Some (wf v, Prop.assume_pos id)

  module Lift (T : sig type 'w t end ) : sig
    type t
    val pack : 'w w T.t -> ('w, t) v
    val unpack : ('w, t) v -> 'w w T.t
  end = struct
    include D0(T)
    let pack = pack_pos
    let unpack = unpack_pos
  end
end

module SystemF = struct
  open EnvWF

  type 'w typ =
    | VAR of 'w ident
    | ARR of 'w typ * 'w typ
    | LAM : ('w1, 'w2) fresh * 'w2 typ -> 'w1 typ

  module Typ = Lift(struct type 'w t = 'w typ end)
end
