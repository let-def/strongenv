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

module type IDENT = sig
  module Namespace : ORDERED
  type (+'w, 'a) t = private
    { namespace : 'a Namespace.t; name : name; stamp : 'w W.lt }
  val compare : ('w, 'a) t -> ('w, 'b) t -> ('a, 'b) order
  val compare_name :
    'a Namespace.t -> string -> ('c, 'b) t -> ('a, 'b) order
end

module type SCOPE = sig
  (* Names *)
  module Namespace : ORDERED
  type 'a namespace = 'a Namespace.t
  module Ident : IDENT with module Namespace := Namespace
  type ('w, 'a) ident = ('w, 'a) Ident.t
  type ('w, 'a) path = private ('w, 'a) ident Path.t

  (* Binding *)
  type ('w1, 'w2, 'a) binder = private
    ('w1, 'w2) W.link * ('w2, 'a) ident

  type ('w, 'a) fresh =
      Fresh : ('w1, 'w2, 'a) binder -> ('w1, 'a) fresh
  val fresh : 'w W.t -> 'a namespace -> name -> ('w, 'a) fresh

  (* Bindings *)
  type ('w1, 'w2) t =
    | Bind : ('w1, 'w2) t * ('w2, 'w3, 'a) binder * 'a -> ('w1, 'w3) t
    | Update : ('w1, 'w2) t * ('w2, 'a) ident * 'a -> ('w1, 'w2) t
    | End : ('w, 'w) t

  type 'w branch = Branch : ('w, 'a) t -> 'w branch [@@unboxed]
end

module Make_scope (Namespace : ORDERED) :
  SCOPE with module Namespace = Namespace =
struct
  module Namespace = Namespace
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
  type ('w, 'a) path = private ('w, 'a) ident Path.t

  (* Binding *)
  type ('w1, 'w2, 'a) binder =
    ('w1, 'w2) W.link * ('w2, 'a) ident

  type ('w, 'a) fresh = Fresh : ('w1, 'w2, 'a) binder -> ('w1, 'a) fresh
  let fresh w namespace name =
    let W.Succ link = W.succ w in
    Fresh (link, { Ident. namespace; name; stamp = W.weak (W.next link) })

  (* Bindings *)
  type ('w1, 'w2) t =
    | Bind : ('w1, 'w2) t * ('w2, 'w3, 'a) binder * 'a -> ('w1, 'w3) t
    | Update : ('w1, 'w2) t * ('w2, 'a) ident * 'a -> ('w1, 'w2) t
    | End : ('w, 'w) t

  type 'w branch = Branch : ('w, 'a) t -> 'w branch [@@unboxed]

end
