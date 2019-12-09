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

(* Worlds: finite sets (of names) that can be extended *)
module W : sig
  type o
  type 'a t
  type 'a world = 'a t
  type +'a lt = private int
  val zero : o t
  val weak : 'a t -> 'a lt

  type ('a, 'b) link
  type 'a succ = Succ : ('a, 'b) link -> 'a succ
  val succ : 'a t -> 'a succ
  val next : ('a, 'b) link -> 'b t
  val sub : ('a, 'b) link -> ('a, 'b) sub
  type (+'w, 'a) v

  module type INDEXED = sig
    type 'w t
    type p
    val pack : 'w world -> 'w t -> ('w, p) v
    val unpack : 'w world -> ('w, p) v -> 'w t
  end

  module Indexed0 (P : sig type 'w t end) : INDEXED with type 'w t = 'w P.t
end = struct
  type o
  type 'a t = T : int -> o t [@@unboxed]
  type 'a world = 'a t
  type +'a lt = int
  let zero : o t = T 0
  let weak (type a) (T a : a t) : a lt = a

  type ('a, 'b) link = Link : int -> (o, o) link [@@unboxed]
  type 'a succ = Succ : ('a, 'b) link -> 'a succ
  let succ (type a) (T a : a t) : a succ = Succ (Link (a + 1))
  let next (type a b) (Link b : (a, b) link) : b t = T b
  let sub (type a b) (Link _ : (a, b) link) : (a, b) sub = refl_sub

  type (+'w, 'a) v = 'a

  module type INDEXED = sig
    type 'w t
    type p
    val pack : 'w world -> 'w t -> ('w, p) v
    val unpack : 'w world -> ('w, p) v -> 'w t
  end
  module Indexed0 (P : sig type 'w t end) = struct
    type 'w t = 'w P.t
    type p = o P.t
    let pack (type w) (T _ : w world) (p : w P.t) : (w, p) v = p
    let unpack (type w) (T _ : w world) (p : (w, p) v) : w P.t = p
  end
end

type 'a world = 'a W.world
type ('w, 'a) v = ('w, 'a) W.v

(* Specification of identifiers *)
type name = string

module Path = struct
  type 'a t =
    | Ident of 'a
    | Dot of 'a t * name
  let rec bind f = function
    | Ident id -> f id
    | Dot (p, n) -> Dot (bind f p, n)
end

module type NAMESPACE = ORDERED

module type IDENT = sig
  type 'a namespace
  type (+'w, 'a) t = private
    { namespace : 'a namespace; name : name; stamp : 'w W.lt }
  val compare : ('w, 'a) t -> ('w, 'b) t -> ('a, 'b) order
  val compare_name :
    'a namespace -> string -> ('c, 'b) t -> ('a, 'b) order
end

module type SCOPE = sig
  (* Names *)
  type 'a namespace
  module Ident : IDENT with type 'a namespace := 'a namespace
  type ('w, 'a) ident = ('w, 'a) Ident.t
  type ('w, 'a) path = private ('w, 'a) ident Path.t

  (* Binding *)
  type ('w1, 'w2, 'a) binder = private
    ('w1, 'w2) W.link * ('w2, 'a) ident

  type ('w, 'a) fresh =
      Fresh : ('w1, 'w2, 'a) binder -> ('w1, 'a) fresh
  val fresh : 'w W.t -> 'a namespace -> name -> ('w, 'a) fresh

  (* Bindings *)
  type ('w1, 'w2) scope =
    | Bind : ('w1, 'w2) scope * ('w2, 'w3, 'a) binder * ('w2, 'a) v -> ('w1, 'w3) scope
    | Update : ('w1, 'w2) scope * ('w2, 'a) ident * ('w2, 'a) v -> ('w1, 'w2) scope
    | End : ('w, 'w) scope

  type 'w branch = Branch : ('w, 'a) scope -> 'w branch [@@unboxed]

  module Transport : sig
    type ('v, 'w) t
    type ('v1, 'w1, 'v2, 'ns) t_binder =
        Binder : ('v2, 'w2) t * ('w1, 'w2, 'ns) binder
          -> ('v1, 'w1, 'v2, 'ns) t_binder
    val path : ('v, 'w) t -> ('v, 'a) path -> ('w, 'a) path
    val binder : ('v1, 'w1) t -> ('v1, 'v2, 'ns) binder ->
      ('v1, 'w1, 'v2, 'ns) t_binder
  end
end

module type NESTING = sig
  type 'a namespace
  type ('w, 'a) path
  type ('v, 'w) transport
  type 'w branch

  type ns_module
  val modules : ns_module namespace
  val scope : 'w W.t -> ('w, ns_module) W.v -> 'w branch

  val transport :
    ('v, 'w) transport -> 'v world -> 'w world ->
    'a namespace -> ('v, 'a) W.v -> ('w, 'a) W.v
end

module type ENV = sig
  type 'a namespace
  type ('w1, 'w2) scope
  type ('w, 'a) ident
  type ('w, 'a) path
  type ('w1, 'w2, 'a) binder

  (* To type fork/merge: type ('w1, 'w2) t *)
  type 'w t
  val empty : W.o t
  val extend : 'w1 t -> ('w1, 'w2) scope -> 'w2 t

  val lookup : 'w t -> 'a namespace -> name Path.t -> ('w, 'a) path option
  val find : 'w t -> 'a namespace -> name Path.t -> (('w, 'a) path * ('w, 'a) v) option
  val get : 'w t -> 'a namespace -> ('w, 'a) path -> ('w, 'a) v

  type 'w fresh = Fresh : ('w1, 'w2, 'a) binder * 'w2 t -> 'w1 fresh
  val bind : 'w1 t -> 'a namespace -> name -> ('w1, 'a) v -> 'w1 fresh
  val update : 'w t -> ('w, 'a) ident -> ('w, 'a) v -> 'w t
  (*val open_ : 'w t -> ('w, Nesting.namespace) path -> ('w1, 'w2) t*)
  (*val scope : 'w t -> (W.o, 'w2) Scope.t .. should include Open*)
end

module type PREENV = sig
  include SCOPE

  module Make_env
      (Nesting : NESTING with type 'a namespace := 'a namespace
                          and type ('w, 'a) path := ('w, 'a) path
                          and type ('v, 'w) transport := ('v, 'w) Transport.t
                          and type 'w branch := 'w branch) :
    ENV with type 'a namespace := 'a namespace
         and type ('w1, 'w2) scope := ('w1, 'w2) scope
         and type ('w, 'a) ident := ('w, 'a) ident
         and type ('w, 'a) path := ('w, 'a) path
         and type ('w1, 'w2, 'a) binder := ('w1, 'w2, 'a) binder
end


module Make (Namespace : NAMESPACE) :
  PREENV with type 'a namespace = 'a Namespace.t =
struct
  type 'a namespace = 'a Namespace.t
  module Ident = struct
    type (+'w, 'a) t =
      { namespace : 'a Namespace.t; name : name; stamp : 'w W.lt }
    let compare (type a b) (a : ('w, a) t) (b : ('w, b) t) : (a, b) order =
      match Namespace.compare a.namespace b.namespace with
      | Eq ->
        order_compare (
          match String.compare a.name b.name with
          | 0 -> Int.compare
                   (a.stamp : _ W.lt :> int)
                   (b.stamp : _ W.lt :> int)
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
  type ('w, 'a) path = ('w, 'a) ident Path.t

  (* Binding *)
  type ('w1, 'w2, 'a) binder =
    ('w1, 'w2) W.link * ('w2, 'a) ident

  type ('w, 'a) fresh = Fresh : ('w1, 'w2, 'a) binder -> ('w1, 'a) fresh
  let fresh w namespace name =
    let W.Succ link = W.succ w in
    Fresh (link, { Ident. namespace; name; stamp = W.weak (W.next link) })

  (* Bindings *)
  type ('w1, 'w2) scope =
    | Bind : ('w1, 'w2) scope * ('w2, 'w3, 'a) binder * ('w2, 'a) v -> ('w1, 'w3) scope
    | Update : ('w1, 'w2) scope * ('w2, 'a) ident * ('w2, 'a) v -> ('w1, 'w2) scope
    | End : ('w, 'w) scope

  type 'w branch = Branch : ('w, 'a) scope -> 'w branch [@@unboxed]

  module Transport : sig
    type ('v, 'w) t
    type ('v1, 'w1, 'v2, 'ns) t_binder =
        Binder : ('v2, 'w2) t * ('w1, 'w2, 'ns) binder
          -> ('v1, 'w1, 'v2, 'ns) t_binder
    val path : ('v, 'w) t -> ('v, 'a) path -> ('w, 'a) path
    val binder : ('v1, 'w1) t -> ('v1, 'v2, 'ns) binder ->
      ('v1, 'w1, 'v2, 'ns) t_binder
  end = struct
    type ('v, 'w) t = {
      nesting :
        'v 'w 'a. ('v, 'w) t -> 'v world -> 'w world -> 'a namespace ->
        ('v, 'a) W.v -> ('w, 'a) W.v;
    }
    type ('v1, 'w1, 'v2, 'ns) t_binder =
        Binder : ('v2, 'w2) t * ('w1, 'w2, 'ns) binder
          -> ('v1, 'w1, 'v2, 'ns) t_binder
    let path _t _p = assert false
    let binder _t _b = assert false
  end

  module Make_env
      (Nesting : NESTING with type 'a namespace := 'a namespace
                          and type ('w, 'a) path := ('w, 'a) path
                          and type ('v, 'w) transport := ('v, 'w) Transport.t
                          and type 'w branch := 'w branch) :
    ENV with type 'a namespace := 'a namespace
         and type ('w1, 'w2) scope := ('w1, 'w2) scope
         and type ('w, 'a) ident := ('w, 'a) ident
         and type ('w, 'a) path := ('w, 'a) path
         and type ('w1, 'w2, 'a) binder := ('w1, 'w2, 'a) binder
  =
  struct
    type +'w binding = Binding : ('w, 'a) ident * ('w, 'a) v -> 'w binding
    type 'w bindings = 'w binding Bt1.t

    type 'w t = {
      bindings: 'w bindings;
      world : 'w W.t;
    }

    let empty : W.o t = {
      bindings = Bt1.leaf;
      world = W.zero;
    }

    let rec add_binding (Binding (ident, _) as binding) = function
      | Bt1.Leaf -> Bt1.node Bt1.leaf binding Bt1.leaf
      | Bt1.Node (_, left, (Binding (ident', _) as binding'), right) ->
        match Ident.compare ident ident' with
        | Lt -> Bt1.node (add_binding binding left) binding' right
        | Gt -> Bt1.node left binding' (add_binding binding right)
        | Eq -> Bt1.node left binding right

    let extend_bindings (type w1 w2 a)
        (env : w1 t)
        (link : (w1, w2) W.link)
        (ident : (w2, a) ident)
        (value : (w1, a) v)
      : w2 t
      =
      let (module Sub) = W.sub link in
      let Refl = Sub.eq in
      let world = W.next link in
      let bindings = (env.bindings : w1 bindings :> w2 bindings) in
      let value = (value : (w1, a) v :> (w2, a) v) in
      let bindings = add_binding (Binding (ident, value)) bindings in
      { world; bindings }

    let rec extend : type w1 w2. w1 t -> (w1, w2) scope -> w2 t =
      fun (env : w1 t) (scope : (w1, w2) scope) ->
      match scope with
      | End -> env
      | Update (prev, ident, value) ->
        let { world; bindings } = extend env prev in
        let bindings = add_binding (Binding (ident, value)) bindings in
        { world; bindings }
      | Bind (prev, binder, value) ->
        let (link, ident) = (binder : _ binder :> (_ * _)) in
        extend_bindings (extend env prev) link ident value

    let rec lookup_binding
      : type w a. a Namespace.t -> name -> w bindings ->
        ((w, a) path * (w, a) v) option
      = fun (ns : a Namespace.t) name -> function
        | Bt1.Leaf -> None
        | Bt1.Node (_, left, Binding (ident, value), right) ->
          match Ident.compare_name ns name ident with
          | Lt -> lookup_binding ns name left
          | Gt -> lookup_binding ns name right
          | Eq ->
            match lookup_binding ns name right with
            | Some _ as result -> result
            | None -> Some (Path.Ident ident, value)

    let find (env : 'w t) (ns: 'a Namespace.t) (path : name Path.t)
      : (('w, 'a) path * ('w, 'a) v) option =
      match path with
      | Path.Dot _ -> failwith "TODO: Path.Dot"
      | Path.Ident name -> lookup_binding ns name env.bindings

    let lookup env ns name =
      match find env ns name with
      | None -> None
      | Some (path, _) -> Some path

    let rec get_binding
      : type w a. a Namespace.t -> (w, a) ident -> w bindings -> (w, a) v
      = fun (ns : a Namespace.t) ident -> function
        | Bt1.Leaf -> failwith "Internal compiler error: unbound identifier"
        | Bt1.Node (_, left, Binding (ident', value), right) ->
          match Ident.compare ident ident' with
          | Lt -> get_binding ns ident left
          | Gt -> get_binding ns ident right
          | Eq -> value

    let get env ns path =
      match path with
      | Path.Dot _ -> failwith "TODO: Path.Dot"
      | Path.Ident ident -> get_binding ns ident env.bindings

    type 'w fresh = Fresh : ('w1, 'w2, 'a) binder * 'w2 t -> 'w1 fresh

    let bind (env : 'w t) (ns : 'a Namespace.t) name (value : ('w, 'a) v) : 'w fresh =
      let Fresh binder = fresh env.world ns name in
      let (link, ident) = (binder : _ binder :> (_ * _)) in
      Fresh (binder, extend_bindings env link ident value)

    let update (env : 'w t) (ident : ('w, 'a) ident) (value : ('w, 'a) v) : 'w t =
      let { world; bindings } = env in
      let bindings = add_binding (Binding (ident, value)) bindings in
      { world; bindings }
  end
end
