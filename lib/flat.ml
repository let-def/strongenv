(* Type equality *)
type (_, _) eq = Refl : ('a, 'a) eq
let refl_eq : ('a, 'a) eq = Refl

(* Sub-typing *)
module type SUB = sig type t type u = private t type s val eq : (s, u) eq end
type ('s, 't) sub = (module SUB with type s = 's and type t = 't)
let refl_sub (type a) =
  let module Sub = struct
    type t = a
    type u = a
    type s = a
    let eq = Refl
  end in ((module Sub) : (a, a) sub)

let trans_sub (type a b c)
    ((module AB) : (a, b) sub)
    ((module BC) : (b, c) sub) : (a, c) sub
  =
  let Refl = AB.eq in
  let Refl = BC.eq in
  let module Sub = struct
    type t = BC.t
    type u = AB.u
    type s = AB.s
    let eq : (s, u) eq = Refl
  end in
  ((module Sub) : (a, c) sub)

(* Typed-indexed ordering *)
type ('a, 'b) order = Lt | Eq : ('a, 'a) order | Gt

let order_compare c =
  if c < 0 then Lt
  else if c > 0 then Gt
  else Eq

module type ORDERED = sig
  type 'a t
  val compare : 'a t -> 'b t -> ('a, 'b) order
end

(* Worlds *)

module World : sig
  type o
  type 'w world
  type +'w elt = private int
  type ('w, 'a) v

  val empty : o world (* A world with no bindings *)

  type ('a, 'b) link
  type 'a extension = Extension : ('a, 'b) link -> 'a extension
  val extend : 'a world -> 'a extension
  val source : ('a, 'b) link -> 'a world
  val target : ('a, 'b) link -> 'b world
  val sub : ('a, 'b) link -> ('a, 'b) sub
  val elt : ('a, 'b) link -> 'b elt

  module type INDEXED = sig
    type 'w t
    type p
    val pack : 'w world -> 'w t -> ('w, p) v
    val unpack : 'w world -> ('w, p) v -> 'w t
  end

  module Indexed0 (P : sig type 'w t end) : INDEXED with type 'w t = 'w P.t

  module Transport : sig
    type ('w, 'v) t

    val sub : ('a, 'b) sub -> ('a, 'b) t
    val compose : ('a, 'b) t -> ('b, 'c) t -> ('a, 'c) t

    val elt : 'a elt -> ('a, 'b) t -> 'b elt

    type ('w1, 'v1, 'w2) t_link =
        Link : ('w2, 'v2) t * ('v1, 'v2) link -> ('w1, 'v1, 'w2) t_link
    val link : ('w1, 'v1) t -> 'v1 world -> ('w1, 'w2) link -> ('w1, 'v1, 'w2) t_link
  end

  type (+'w, 'a) v_weak
  val weaken : 'w world -> ('w, 'a) v -> ('w, 'a) v_weak
  type ('w, 'a) unpack =
      Unpack : 'w0 world * ('w0, 'w1) sub * ('w0, 'a) v -> ('w, 'a) unpack
  val unpack : 'w world -> ('w, 'a) v_weak -> ('w, 'a) unpack

  val unsafe_eq : 'w world -> ('w, o) eq
  val card : 'w world -> int
end = struct
  type o
  type 'w world = W : int -> o world [@@ocaml.unboxed]
  type +'w elt = int
  type (+'w, 'a) v = 'a

  let empty : o world = W 0

  type ('a, 'b) link = Link : int -> (o, o) link [@@ocaml.unboxed]
  type 'a extension = Extension : ('a, 'b) link -> 'a extension

  let extend (type w1) (W w : w1 world) : w1 extension =
    Extension (Link w)

  let source (type a b) (Link a : (a, b) link) : a world = W a
  let target (type a b) (Link a : (a, b) link) : b world = W (a + 1)
  let sub (type a b) (Link _ : (a, b) link) : (a, b) sub = refl_sub
  let elt (type a b) (Link a : (a, b) link) = a

  module type INDEXED = sig
    type 'w t
    type p
    val pack : 'w world -> 'w t -> ('w, p) v
    val unpack : 'w world -> ('w, p) v -> 'w t
  end

  module Indexed0 (P : sig type 'w t end) = struct
    type 'w t = 'w P.t
    type p = o P.t
    let pack (type w1) (W _ : w1 world) (p : w1 P.t) : (w1, p) v = p
    let unpack (type w1) (W _ : w1 world) (p : (w1, p) v) : w1 t = p
  end

  module Transport : sig
    type ('w, 'v) t

    val sub : ('a, 'b) sub -> ('a, 'b) t
    val compose : ('a, 'b) t -> ('b, 'c) t -> ('a, 'c) t

    val elt : 'a elt -> ('a, 'b) t -> 'b elt

    type ('w1, 'v1, 'w2) t_link =
        Link : ('w2, 'v2) t * ('v1, 'v2) link -> ('w1, 'v1, 'w2) t_link
    val link : ('w1, 'v1) t -> 'v1 world -> ('w1, 'w2) link -> ('w1, 'v1, 'w2) t_link
  end = struct
    type ('w, 'v) t = (int * int) list

    let sub _sub = []

    let compose t1 t2 =
      let rec aux = function
        | [], t2 -> t2
        | t1, [] -> t1
        | ((b1, o1) :: t1'), ((b2, o2) :: t2') ->
          if b2 = b1 + o1
          then (b1, o1 + o2) :: aux (t1', t2')
          else if b2 < b1 + o1
          then (b1, o1 + o2) :: aux (t1', t2)
          else (b2 + o1, o1 + o2) :: aux (t1, t2')
      in
      aux (t1, t2)

    type ('w1, 'v1, 'w2) t_link =
        Link : ('w2, 'v2) t * ('v1, 'v2) link -> ('w1, 'v1, 'w2) t_link

    let link (type w1 v1 w2)
        (_ : (w1, v1) t) (w : v1 world)
        (l1 : (w1, w2) link) : (w1, v1, w2) t_link =
      let Extension l2 = extend w in
      let elt1 = elt l1 and elt2 = elt l2 in
      let o = elt2 - elt1 in
      let t = if o > 0 then [elt1, o] else (assert (o = 0); []) in
      Link (t, l2)

    let rec elt a = function
      | [] -> a
      | (b, o) :: bs ->
        if a >= b then a + o else elt a bs
  end

  type (+'w, 'a) v_weak = V_weak : 'w_ world * ('w_, 'a) v -> ('w, 'a) v_weak
  let weaken (type w a) (w : w world) (v : (w, a) v) : (w, a) v_weak =
    V_weak (w, v)

  type ('w, 'a) unpack =
      Unpack : 'w0 world * ('w0, 'w1) sub * ('w0, 'a) v -> ('w, 'a) unpack
  let unpack (type w a) (W _ : w world)
      (V_weak ((W _ as w), v) : (w, a) v_weak) : (w, a) unpack =
    Unpack (w, refl_sub, v)

  let unsafe_eq (type w) (W _ : w world) : (w, o) eq = Refl
  let card (type o) (W w : o world) = w
end

type 'a world = 'a World.world
type ('w, 'a) v = ('w, 'a) World.v
type (+'w, 'a) v_weak = ('w, 'a) World.v_weak

(* Contexts *)

type name = string

module type PRE_CONTEXT = sig
  type 'a namespace

  (* Names *)
  module Ident : sig
    type (+'w, 'a) t = private
      { namespace : 'a namespace; name : name; stamp : 'w World.elt }
    val compare : ('w, 'a) t -> ('w, 'b) t -> ('a, 'b) order
    val compare_name : 'a namespace -> string -> ('w, 'b) t -> ('a, 'b) order
  end
  type ('w, 'a) ident = ('w, 'a) Ident.t

  (* Bindings *)
  type ('w1, 'w2, 'a) binder = private
    Binder of ('w1, 'w2) World.link * ('w2, 'a) ident * ('w1, 'a) v

  type 'w scope =
    | Bind : ('w1, 'w2, 'a) binder * 'w2 scope -> 'w1 scope
    | End : 'w scope

  module Path : sig
    type 'a pre =
      | Pre_ident : 'a namespace * name -> 'a pre
      | Pre_dot : _ pre * 'a namespace * name -> 'a pre
    val ident : 'a namespace -> name -> 'a pre
    val dot : 'a pre -> 'a namespace -> name -> 'a pre
    type (+'w, 'a) t = private
      | Ident : ('w, 'a) ident -> ('w, 'a) t
      | Dot : _ t * 'a namespace * name -> ('w, 'a) t
  end
  type ('w, 'a) path = ('w, 'a) Path.t
end

module type ENV = sig
  type 'a namespace
  type ('w, 'v) transport
  type (+'w, 'a) ident
  type 'a pre_path
  type (+'w, 'a) path
  type ('w1, 'w2, 'a) binder

  type 'w t
  val empty : unit -> World.o t
  val lookup : 'w t -> 'a namespace -> name -> ('w, 'a) ident option
  val find : 'w t -> 'a namespace -> name -> (('w, 'a) ident * ('w, 'a) v_weak) option
  val get : 'w t -> ('w, 'a) ident -> ('w, 'a) v_weak
  (*val lookup : 'w t -> 'a pre_path -> ('w, 'a) path option*)
  (*val find : 'w t -> 'a pre_path -> (('w, 'a) path * ('w, 'a) v) option*)
  (*val get : 'w t -> 'a namespace -> ('w, 'a) path -> ('w, 'a) v*)

  type ('w, 'a) fresh = Fresh : ('w1, 'w2, 'a) binder * 'w2 t -> ('w1, 'a) fresh
  val bind : 'w1 t -> 'a namespace -> name -> ('w1, 'a) v -> ('w1, 'a) fresh
  val binder : 'w1 t -> ('w1, 'w2, 'a) binder -> 'w2 t
  val update : 'w t -> ('w, 'a) ident -> ('w, 'a) v -> ('w, 'a) fresh

  module Transport : sig
    val source : ('w, 'v) transport -> 'w world
    val target : ('w, 'v) transport -> 'v world

    type ('v1, 'w1, 'v2, 'ns) t_binder =
        Binder : ('v2, 'w2) transport * ('w1, 'w2, 'ns) binder
          -> ('v1, 'w1, 'v2, 'ns) t_binder

    val ident : ('v, 'w) transport -> ('v, 'a) ident -> ('w, 'a) ident

    val binder : ('w1, 'w2, 'ns) binder -> ('w1, 'v1) transport ->
      ('w1, 'v1, 'w2, 'ns) t_binder

    val sub : ('w1, 'w2) sub -> 'w1 world -> 'w2 world -> ('w1, 'w2) transport
    val compose :
      ('w1, 'w2) transport -> ('w2, 'w3) transport -> ('w1, 'w3) transport
  end
end

module type NESTING = sig
  type 'a namespace
  (*type ('w, 'a) path*)
  type ('v, 'w) transport
  type 'w scope
  val project :
    'w world -> 'a namespace -> ('w, 'a) v -> 'w scope
  val transport :
    ('v, 'w) transport -> 'a namespace -> ('v, 'a) v -> ('w, 'a) v
end

module type CONTEXT = sig
  include PRE_CONTEXT

  type ('v, 'w) transport

  module Make_env
      (Nesting : NESTING with type 'a namespace := 'a namespace
                          (*and type ('w, 'a) path := ('w, 'a) path*)
                          and type ('v, 'w) transport := ('v, 'w) transport
                          and type 'w scope := 'w scope) :
    ENV with type 'a namespace := 'a namespace
         and type ('v, 'w) transport := ('v, 'w) transport
         and type ('w, 'a) ident := ('w, 'a) ident
         and type ('w1, 'w2, 'a) binder := ('w1, 'w2, 'a) binder
         and type 'a pre_path := 'a Path.pre
         and type ('w, 'a) path := ('w, 'a) path
end

module Make (Namespace : ORDERED) :
  CONTEXT with type 'a namespace = 'a Namespace.t =
struct
  type 'a namespace = 'a Namespace.t
  type ('w, 'v) transport = {
    nesting:
      'w 'v 'a . ('w, 'v) transport -> 'a namespace -> ('w, 'a) v -> ('v, 'a) v;
    source: 'w world;
    target: 'v world;
    world: ('w, 'v) World.Transport.t;
  }

  (* Names *)
  module Ident = struct
    type (+'w, 'a) t =
      { namespace : 'a namespace; name : name; stamp : 'w World.elt }
    let compare (type a b) (a : ('w, a) t) (b : ('w, b) t) : (a, b) order =
      match Namespace.compare a.namespace b.namespace with
      | Eq ->
        order_compare (
          match String.compare a.name b.name with
          | 0 -> Int.compare
                   (a.stamp : _ World.elt :> int)
                   (b.stamp : _ World.elt :> int)
          | n -> n
        )
      | (Lt | Gt) as a -> a

    let compare_name
        (type a b) (a : a namespace) name (b : (_, b) t)
      : (a, b) order =
      match Namespace.compare a b.namespace with
      | Eq -> order_compare (String.compare name b.name)
      | (Lt | Gt) as a -> a
  end
  type ('w, 'a) ident = ('w, 'a) Ident.t

  module Path = struct
    type 'a pre =
      | Pre_ident : 'a namespace * name -> 'a pre
      | Pre_dot : _ pre * 'a namespace * name -> 'a pre

    let ident ns name = Pre_ident (ns, name)
    let dot pre ns name = Pre_dot (pre, ns, name)

    type (+'w, 'a) t =
      | Ident : ('w, 'a) ident -> ('w, 'a) t
      | Dot : _ t * 'a namespace * name -> ('w, 'a) t

    (*FIXME: Remove that*)
    let _f x ns n = Dot (x, ns, n)
  end
  type ('w, 'a) path = ('w, 'a) Path.t

  (* Bindings *)
  type ('w1, 'w2, 'a) binder =
    Binder of ('w1, 'w2) World.link * ('w2, 'a) ident * ('w1, 'a) v

  type 'w scope =
    | Bind : ('w1, 'w2, 'a) binder * 'w2 scope -> 'w1 scope
    | End : 'w scope

  module type ENV =
    ENV with type 'a namespace := 'a namespace
         and type ('v, 'w) transport := ('v, 'w) transport
         and type ('w, 'a) ident := ('w, 'a) ident
         and type ('w1, 'w2, 'a) binder := ('w1, 'w2, 'a) binder
         and type 'a pre_path := 'a Path.pre
         and type ('w, 'a) path := ('w, 'a) path

  module Make_env
      (Nesting : NESTING with type 'a namespace := 'a namespace
                          and type ('v, 'w) transport := ('v, 'w) transport
                          and type 'w scope := 'w scope) :
    ENV =
  struct
    module Transport : sig
      val source : ('w, 'v) transport -> 'w world
      val target : ('w, 'v) transport -> 'v world

      type ('w1, 'v1, 'w2, 'ns) t_binder =
          Binder : ('w2, 'v2) transport * ('v1, 'v2, 'ns) binder
            -> ('w1, 'v1, 'w2, 'ns) t_binder

      val ident : ('w, 'v) transport -> ('w, 'a) ident -> ('v, 'a) ident
      val binder : ('w1, 'w2, 'ns) binder -> ('w1, 'v1) transport ->
        ('w1, 'v1, 'w2, 'ns) t_binder

      val sub : ('w1, 'w2) sub -> 'w1 world -> 'w2 world -> ('w1, 'w2) transport
      val compose :
        ('w1, 'w2) transport -> ('w2, 'w3) transport -> ('w1, 'w3) transport
    end = struct
      let source t = t.source
      let target t = t.target

      type ('w1, 'v1, 'w2, 'ns) t_binder =
          Binder : ('w2, 'v2) transport * ('v1, 'v2, 'ns) binder
            -> ('w1, 'v1, 'w2, 'ns) t_binder

      let mk world source target =
        {nesting = Nesting.transport; source; target; world}

      let ident (type w v a) (t: (w, v) transport) (id: (w, a) ident) : (v, a) ident =
        {id with stamp = World.Transport.elt id.stamp t.world}

      let binder (type w1 w2 a v1)
          (Binder (link, id, v) : (w1, w2, a) binder)
          (t: (w1, v1) transport) : (w1, v1, w2, a) t_binder =
        let World.Transport.Link (t', link') =
          World.Transport.link t.world t.target link in
        let t' = mk t' (World.target link) (World.target link') in
        let v' : (v1, a) v = Nesting.transport t id.namespace v in
        Binder (t', Binder (link', ident t' id, v'))

      let sub (type w1 w2) (s: (w1, w2) sub) (w1 : w1 world) (w2 : w2 world)
        : (w1, w2) transport = mk (World.Transport.sub s) w1 w2

      let compose t1 t2 =
        mk (World.Transport.compose t1.world t2.world)
          t1.source t2.target
    end

    type +'w binding =
        Binding : ('w, 'a) ident * ('w, 'a) v_weak -> 'w binding

    type 'w t = {
      world: 'w world;
      bindings : 'w binding list;
    }

    let empty () = { world = World.empty; bindings = [] }

    let lookup (type w a) (env : w t) (ns : a namespace) name
      : (w, a) ident option =
      let rec aux : w binding list -> (w, a) ident option = function
        | [] -> None
        | Binding (ident, _) :: tl ->
          begin match Ident.compare_name ns name ident with
            | Lt | Gt -> aux tl
            | Eq -> Some ident
          end
      in
      aux env.bindings

    let retract
        (type w1 w2) (env : w2 t) (w1 : w1 world) (_ : (w1, w2) sub) : w1 t =
      let Refl = World.unsafe_eq env.world in
      let Refl = World.unsafe_eq w1 in
      let bindings =
        let pred (Binding (ident, _)) =
          let stamp : _ World.elt :> int = ident.Ident.stamp in
          stamp < World.card w1
        in
        List.filter pred env.bindings
      in
      {world = w1; bindings}

    let base_find (type w a) (env : w t) (ns : a namespace) name
      : ((w, a) ident * (w, a) v_weak) option =
      let rec aux : w binding list -> ((w, a) ident * (w, a) v_weak) option =
        function
        | [] -> None
        | Binding (ident, v) :: tl ->
          begin match Ident.compare_name ns name ident with
            | Lt | Gt -> aux tl
            | Eq -> Some (ident, v)
          end
      in
      aux env.bindings

    let rec find_scope
      : type w a. w t -> a Path.pre -> ((w, a) path * (w, a) v_weak) option
      = fun env path ->
        match path with
        | Path.Pre_ident (ns, name) ->
          begin match base_find env ns name with
            | None -> None
            | Some (ident, v) ->
              let World.Unpack (w', _sub, v') = World.unpack env.world v in
              let scope = Nesting.project w' ns v' in
              assert false
          end
        | Path.Pre_dot (_pre, _ns, _name) ->
          assert false
          (*begin match find env pre with
            | None -> None
            | Some (path, v) ->
              let World.Unpack (w', _sub, v') = World.unpack env.world v in
              let scope = Nesting.project w' ns v' in
              assert false
          end*)

    let rec find
      : type w a. w t -> a Path.pre -> ((w, a) path * (w, a) v_weak) option
      = fun env path ->
        match path with
        | Path.Pre_ident (ns, name) ->
          begin match base_find env ns name with
            | None -> None
            | Some (ident, v) -> Some (Path.Ident ident, v)
          end
        | Path.Pre_dot (pre, ns, name) ->
          begin match find env pre with
            | None -> None
            | Some (path, v) ->
              let World.Unpack (w', _sub, v') = World.unpack env.world v in
              let scope = Nesting.project w' ns v' in
          end

    let get (type w a) (env : w t) (ident : (w, a) ident) : (w, a) v_weak =
      let rec aux : w binding list -> (w, a) v_weak = function
        | [] -> failwith "Internal error: unbound get"
        | Binding (ident', v) :: tl ->
          begin match Ident.compare ident ident' with
            | Lt | Gt -> aux tl
            | Eq -> v
          end
      in
      aux env.bindings

    (*let lookup : 'w t -> 'a pre_path -> ('w, 'a) path option
    let find : 'w t -> 'a pre_path -> (('w, 'a) path * ('w, 'a) v) option
    let get : 'w t -> 'a namespace -> ('w, 'a) path -> ('w, 'a) v*)

    type ('w, 'a) fresh = Fresh : ('w1, 'w2, 'a) binder * 'w2 t -> ('w1, 'a) fresh

    let binder (type w1 w2 a)
        (env : w1 t) (Binder (link, id, v) : (w1, w2, a) binder) : w2 t =
      let (module Sub) = World.sub link in
      let Refl = Sub.eq in
      let v = (World.weaken v : (w1, a) v_weak :> (w2, a) v_weak) in
      let bindings =
        Binding (id, v) ::
        (env.bindings : w1 binding list :> w2 binding list)
      in
      {world = World.target link; bindings}

    let bind (type w a) (env : w t) (namespace : a namespace)
        name (v : (w, a) v) : (w, a) fresh =
      let World.Extension link = World.extend env.world in
      let binder' =
        Binder (link, {Ident. name; namespace; stamp = World.elt link}, v)
      in
      Fresh (binder', binder env binder')

    let coerce_ident (type w1 w2 a) ((module Sub) : (w1, w2) sub)
        (id : (w1, a) ident) : (w2, a) ident =
      let Refl = Sub.eq in
      (id : (w1, a) ident :> (w2, a) ident)

    let update (type w a) (env : w t)
        (ident : (w, a) ident) (v : (w, a) v) : (w, a) fresh =
      let World.Extension (link : (w, _) World.link) = World.extend env.world in
      let sub = World.sub link in
      let binder' = Binder (link, coerce_ident sub ident, v) in
      Fresh (binder', binder env binder')
  end
end
