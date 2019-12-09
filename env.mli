(* Type tricks *)

(* Type equality *)
type (_, _) eq = Refl : ('a, 'a) eq
val refl_eq : ('a, 'a) eq

(* Sub-typing *)
module type SUB = sig type t type u = private t type s val eq : (s, u) eq end
type ('s, 't) sub = (module SUB with type s = 's and type t = 't)
val refl_sub : ('a, 'a) sub
val trans_sub : ('a, 'b) sub -> ('b, 'c) sub -> ('a, 'c) sub

(* Typed-indexed ordering *)
type ('a, 'b) order = Lt | Eq : ('a, 'a) order | Gt
module type ORDERED =
  sig type 'a t val compare : 'a t -> 'b t -> ('a, 'b) order end

(* Worlds *)
type 'a world

module W : sig
  type o
  type 'a t = 'a world
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
end

type ('w, 'a) v = ('w, 'a) W.v

(* Names and qualified names *)

type name = string

module Path : sig
  type 'a t = Ident of 'a | Dot of 'a t * name
  val bind : ('a -> 'b t) -> 'a t -> 'b t
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

  type ('w, 'a) fresh = Fresh : ('w1, 'w2, 'a) binder -> ('w1, 'a) fresh
  val fresh : 'w W.t -> 'a namespace -> name -> ('w, 'a) fresh

  (* Bindings *)
  type ('w1, 'w2) scope =
    | Bind : ('w1, 'w2) scope * ('w2, 'w3, 'a) binder * ('w2, 'a) v -> ('w1, 'w3) scope
    | Update : ('w1, 'w2) scope * ('w2, 'a) ident * ('w2, 'a) v -> ('w1, 'w2) scope
    | End : ('w, 'w) scope

  type 'w branch = Branch : ('w, 'a) scope -> 'w branch [@@unboxed]

  type ('v1, 'w1) transport = {
    path : 'a. ('v1, 'a) path -> ('w1, 'a) path;
    binder : 'v2 'ns . ('v1, 'v2, 'ns) binder ->
                       ('v1, 'w1, 'v2, 'ns) transport_binder;
  }

  and ('v1, 'w1, 'v2, 'ns) transport_binder =
      Binder : ('v2, 'w2) transport * ('w1, 'w2, 'ns) binder
        -> ('v1, 'w1, 'v2, 'ns) transport_binder

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
                          and type ('v, 'w) transport := ('v, 'w) transport
                          and type 'w branch := 'w branch) :
    ENV with type 'a namespace = 'a namespace
         and type ('w1, 'w2) scope = ('w1, 'w2) scope
         and type ('w, 'a) ident = ('w, 'a) ident
         and type ('w, 'a) path = ('w, 'a) path
         and type ('w1, 'w2, 'a) binder = ('w1, 'w2, 'a) binder
end

module Make (Namespace : NAMESPACE) :
  PREENV with type 'a namespace = 'a Namespace.t
