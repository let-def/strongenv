type 'a world = 'a World.world
type ('w, 'a) v_strong = ('w, 'a) World.v_strong
type (+'w, 'a) v = ('w, 'a) World.v

module type CONTEXT = sig
  type 'a namespace

  (* Names *)
  module Ident : sig
    type (+'w, 'a) t = private
      { namespace : 'a namespace; stamp : 'w World.elt }
    val compare : ('w, 'a) t -> ('w, 'b) t -> ('a, 'b) Witness.order
    val retract : 'w1 world -> 'w2 world -> ('w1, 'w2) Witness.sub ->
      ('w2, 'a) t -> ('w1, 'a) t option
  end
  type ('w, 'a) ident = ('w, 'a) Ident.t

  (* Bindings *)
  type ('w1, 'w2, 'a) binder = private
    Binder of ('w1, 'w2) World.link * ('w2, 'a) ident * ('w1, 'a) v

  type 'w env
  type ('w, 'a) fresh =
      Fresh : ('w1, 'w2, 'a) binder * 'w2 env -> ('w1, 'a) fresh

  val empty : World.o env
  val world : 'w env -> 'w world
  val get : 'w env -> ('w, 'a) ident -> ('w, 'a) v
  val bind : 'w env -> 'a namespace -> ('w, 'a) v -> ('w, 'a) fresh
  val bind' : 'w env -> 'a namespace -> ('w, 'a) v_strong -> ('w, 'a) fresh
  val update : 'w env -> ('w, 'a) ident -> ('w, 'a) v -> ('w, 'a) fresh
  val update' : 'w env -> ('w, 'a) ident -> ('w, 'a) v_strong -> ('w, 'a) fresh
end

module Make_context (Namespace : Witness.ORDERED) :
  CONTEXT with type 'a namespace = 'a Namespace.t =
struct
  type 'a namespace = 'a Namespace.t

  (* Names *)
  module Ident = struct
    type (+'w, 'a) t = { namespace : 'a namespace; stamp : 'w World.elt }
    let compare (type a b) (a : ('w, a) t) (b : ('w, b) t) : (a, b) Witness.order =
      match Namespace.compare a.namespace b.namespace with
      | Eq ->
        Witness.order_compare (
          Int.compare
            (a.stamp : _ World.elt :> int)
            (b.stamp : _ World.elt :> int)
        )
      | (Lt | Gt) as a -> a

    let coerce_stamp (type w1 w2) ((module Sub) : (w1, w2) Witness.sub) stamp =
      let Refl = Sub.eq in
      (stamp : w1 World.elt :> w2 World.elt )

    let retract (type w1 w2) (w1 : w1 world) (w2 : w2 world)
        (w1w2 : (w1, w2) Witness.sub)
        ({namespace; stamp} : (w2, 'a) t) : (w1, 'a) t option =
      (* Faster implementation: stamp is not going to change,
         so just compare stamp and world, then use unsafe_eq to coerce *)
      let World.Minimal (l0, w0w2) = World.minimize w2 stamp in
      match World.chain w1 w1w2 (World.target l0) w0w2 with
      | World.Before _ -> None
      | World.Same -> Some { namespace; stamp = World.elt l0 }
      | World.After sub ->
        let stamp = coerce_stamp sub (World.elt l0) in
        Some { namespace; stamp }
  end
  type ('w, 'a) ident = ('w, 'a) Ident.t

  (* Bindings *)
  type ('w1, 'w2, 'a) binder =
    Binder of ('w1, 'w2) World.link * ('w2, 'a) ident * ('w1, 'a) v

  type +'w binding =
      Binding : ('w, 'a) ident * ('w, 'a) v -> 'w binding

  type 'w env = {
    world: 'w world;
    bindings : 'w binding Dbseq.t;
  }

  let empty = { world = World.empty; bindings = Dbseq.empty }

  let world t = t.world

  let ident_index (type w a) (env : w env) (ident : (w, a) ident) : int =
    let w_id = (World.card env.world :> int) in
    let b_id = (ident.Ident.stamp :> int) in
    (w_id - b_id - 1)

  let get (type w a) (env : w env) (ident : (w, a) ident) : (w, a) v =
    let index = ident_index env ident in
    let Binding (ident', v) = Dbseq.get index env.bindings  in
    match Ident.compare ident ident' with
    | Lt | Gt -> failwith "Internal error: unbound get"
    | Eq -> v

  type ('w, 'a) fresh =
      Fresh : ('w1, 'w2, 'a) binder * 'w2 env -> ('w1, 'a) fresh

  let binder (type w1 w2 a)
      (env : w1 env) (Binder (link, id, v) : (w1, w2, a) binder) : w2 env =
    let (module Sub) = World.sub link in
    let Refl = Sub.eq in
    let v = (v : (w1, a) v :> (w2, a) v) in
    let bindings = Dbseq.cons
        (Binding (id, v))
        (env.bindings : w1 binding Dbseq.t :> w2 binding Dbseq.t)
    in
    {world = World.target link; bindings}

  let bind (type w a) (env : w env) (namespace : a namespace)
      (v : (w, a) v) : (w, a) fresh =
    let World.Extension link = World.extend env.world in
    let binder' =
      Binder (link, {Ident. namespace; stamp = World.elt link}, v)
    in
    Fresh (binder', binder env binder')

  let bind' env namespace v =
    bind env namespace (World.v env.world v)

  let coerce_ident (type w1 w2 a) ((module Sub) : (w1, w2) Witness.sub)
      (id : (w1, a) ident) : (w2, a) ident =
    let Refl = Sub.eq in
    (id : (w1, a) ident :> (w2, a) ident)

  let update (type w a) (env : w env)
      (ident : (w, a) ident) (v : (w, a) v) : (w, a) fresh =
    let World.Extension (link : (w, _) World.link) = World.extend env.world in
    let index = ident_index env ident in
    let bindings = Dbseq.update env.bindings index
        (fun (Binding (ident', _v')) ->
           match Ident.compare ident ident' with
           | Lt | Gt -> failwith "Internal error: unbound update"
           | Eq -> Binding (ident, v))
    in
    let env = {env with bindings} and sub = World.sub link in
    let binder' = Binder (link, coerce_ident sub ident, v) in
    Fresh (binder', binder env binder')

  let update' env ident v =
    update env ident (World.v env.world v)
end
