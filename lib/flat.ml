type 'a world = 'a World.world
type ('w, 'a) v = ('w, 'a) World.v
type (+'w, 'a) v_weak = ('w, 'a) World.v_weak

module type CONTEXT = sig
  type 'a namespace

  (* Names *)
  module Ident : sig
    type (+'w, 'a) t = private
      { namespace : 'a namespace; stamp : 'w World.elt }
    val compare : ('w, 'a) t -> ('w, 'b) t -> ('a, 'b) Type.order
    val retract : 'w1 world -> 'w2 world -> ('w1, 'w2) World.sub ->
      ('w2, 'a) t -> ('w1, 'a) t option
  end
  type ('w, 'a) ident = ('w, 'a) Ident.t

  (* Bindings *)
  type ('w1, 'w2, 'a) binder = private
    Binder of ('w1, 'w2) World.link * ('w2, 'a) ident * ('w1, 'a) v_weak

  type ('w, 'v) transport
  module Transport : sig
    val source : ('w, 'v) transport -> 'w world
    val target : ('w, 'v) transport -> 'v world

    type ('v1, 'w2, 'ns) t_binder =
        Binder : ('w2, 'v2) transport * ('v1, 'v2, 'ns) binder
          -> ('v1, 'w2, 'ns) t_binder

    val ident : ('v, 'w) transport -> ('v, 'a) ident -> ('w, 'a) ident

    val binder : ('w1, 'w2, 'ns) binder -> ('w1, 'v1) transport ->
      ('v1, 'w2, 'ns) t_binder

    val sub : ('w1, 'w2) Type.sub ->
      'w1 world -> 'w2 world -> ('w1, 'w2) transport
    val compose :
      ('w1, 'w2) transport -> ('w2, 'w3) transport -> ('w1, 'w3) transport
  end

  type 'w env
  type ('w, 'a) fresh =
      Fresh : ('w1, 'w2, 'a) binder * 'w2 env -> ('w1, 'a) fresh

  val empty : World.o env
  val world : 'w env -> 'w world
  val get : 'w env -> ('w, 'a) ident -> ('w, 'a) v_weak
  val bind : 'w env -> 'a namespace -> ('w, 'a) v_weak -> ('w, 'a) fresh
  val bind' : 'w env -> 'a namespace -> ('w, 'a) v -> ('w, 'a) fresh
  val update : 'w env -> ('w, 'a) ident -> ('w, 'a) v_weak -> ('w, 'a) fresh
  val update' : 'w env -> ('w, 'a) ident -> ('w, 'a) v -> ('w, 'a) fresh
end

module type NEW_CONTEXT = sig
  include CONTEXT

  type configuration = {
    transport : 'w 'v 'a.  ('w, 'v) transport ->
      'a namespace -> ('w, 'a) v -> ('v, 'a) v
  }
  val configure : configuration -> unit
end

module Make_context (Namespace : World.ORDERED) :
  NEW_CONTEXT with type 'a namespace = 'a Namespace.t =
struct
  type 'a namespace = 'a Namespace.t
  type ('w, 'v) transport = {
    source: 'w world;
    target: 'v world;
    world: ('w, 'v) World.Transport.t;
  }

  type configuration = {
    transport : 'w 'v 'a.  ('w, 'v) transport ->
      'a namespace -> ('w, 'a) v -> ('v, 'a) v
  }
  let unconfigured = {
    transport = fun _ -> failwith
        "Flat.Context: module should be configured by calling configure method"
  }
  let configuration = ref unconfigured
  let configure config =
    if !configuration == unconfigured
    then configuration := config
    else failwith "Flat.Context: already configured"

  let transport t ns v =
    (!configuration).transport t ns v

  (* Names *)
  module Ident = struct
    type (+'w, 'a) t = { namespace : 'a namespace; stamp : 'w World.elt }
    let compare (type a b) (a : ('w, a) t) (b : ('w, b) t) : (a, b) World.order =
      match Namespace.compare a.namespace b.namespace with
      | Eq ->
        World.order_compare (
          Int.compare
            (a.stamp : _ World.elt :> int)
            (b.stamp : _ World.elt :> int)
        )
      | (Lt | Gt) as a -> a

    let coerce_stamp (type w1 w2) ((module Sub) : (w1, w2) World.sub) stamp =
      let Refl = Sub.eq in
      (stamp : w1 World.elt :> w2 World.elt )

    let retract (type w1 w2) (w1 : w1 world) (w2 : w2 world)
        (w1w2 : (w1, w2) World.sub)
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
    Binder of ('w1, 'w2) World.link * ('w2, 'a) ident * ('w1, 'a) v_weak

  module Transport : sig
    val source : ('w, 'v) transport -> 'w world
    val target : ('w, 'v) transport -> 'v world

    type ('v1, 'w2, 'ns) t_binder =
        Binder : ('w2, 'v2) transport * ('v1, 'v2, 'ns) binder
          -> ('v1, 'w2, 'ns) t_binder

    val ident : ('w, 'v) transport -> ('w, 'a) ident -> ('v, 'a) ident
    val binder : ('w1, 'w2, 'ns) binder -> ('w1, 'v1) transport ->
      ('v1, 'w2, 'ns) t_binder

    val sub : ('w1, 'w2) World.sub -> 'w1 world -> 'w2 world -> ('w1, 'w2) transport
    val compose :
      ('w1, 'w2) transport -> ('w2, 'w3) transport -> ('w1, 'w3) transport
  end = struct
    let source t = t.source
    let target t = t.target

    type ('v1, 'w2, 'ns) t_binder =
        Binder : ('w2, 'v2) transport * ('v1, 'v2, 'ns) binder
          -> ('v1, 'w2, 'ns) t_binder

    let mk world source target =
      {source; target; world}

    let ident (type w v a) (t: (w, v) transport) (id: (w, a) ident) : (v, a) ident =
      {id with stamp = World.Transport.elt id.stamp t.world}

    let sub (type w1 w2)
        (s: (w1, w2) World.sub) (w1 : w1 world) (w2 : w2 world)
      : (w1, w2) transport = mk (World.Transport.sub s) w1 w2

    let compose t1 t2 =
      mk (World.Transport.compose t1.world t2.world)
        t1.source t2.target

    let binder (type w1 w2 a v1)
        (Binder (link, id, v) : (w1, w2, a) binder)
        (t1: (w1, v1) transport) : (v1, w2, a) t_binder =
      let World.Transport.Link (wt2, link') =
        World.Transport.link t1.world t1.target link in
      let t2 = mk wt2 (World.target link) (World.target link') in
      let World.Unpack (w0, w0w1, v) = World.unpack (World.source link) v in
      let t0 =
        mk (World.Transport.compose (World.Transport.sub w0w1) t1.world)
          w0 t1.target
      in
      let v' : (v1, a) v_weak =
        World.v_weak t1.target (transport t0 id.namespace v)
      in
      Binder (t2, Binder (link', ident t2 id, v'))
  end

  type +'w binding =
      Binding : ('w, 'a) ident * ('w, 'a) v_weak -> 'w binding

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

  let get (type w a) (env : w env) (ident : (w, a) ident) : (w, a) v_weak =
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
    let v = (v : (w1, a) v_weak :> (w2, a) v_weak) in
    let bindings = Dbseq.add
        (Binding (id, v))
        (env.bindings : w1 binding Dbseq.t :> w2 binding Dbseq.t)
    in
    {world = World.target link; bindings}

  let bind (type w a) (env : w env) (namespace : a namespace)
      (v : (w, a) v_weak) : (w, a) fresh =
    let World.Extension link = World.extend env.world in
    let binder' =
      Binder (link, {Ident. namespace; stamp = World.elt link}, v)
    in
    Fresh (binder', binder env binder')

  let bind' env namespace v =
    bind env namespace (World.v_weak env.world v)

  let coerce_ident (type w1 w2 a) ((module Sub) : (w1, w2) World.sub)
      (id : (w1, a) ident) : (w2, a) ident =
    let Refl = Sub.eq in
    (id : (w1, a) ident :> (w2, a) ident)

  let update (type w a) (env : w env)
      (ident : (w, a) ident) (v : (w, a) v_weak) : (w, a) fresh =
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
    update env ident (World.v_weak env.world v)
end
