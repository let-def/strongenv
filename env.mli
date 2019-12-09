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
  module Namespace : NAMESPACE
  type (+'w, 'a) t = private
    { namespace : 'a Namespace.t; name : name; stamp : 'w W.lt }
  val compare : ('w, 'a) t -> ('w, 'b) t -> ('a, 'b) order
  val compare_name :
    'a Namespace.t -> string -> ('c, 'b) t -> ('a, 'b) order
end

module type SCOPE = sig
  (* Names *)
  module Namespace : NAMESPACE
  type 'a namespace = 'a Namespace.t
  module Ident : IDENT with module Namespace := Namespace
  type ('w, 'a) ident = ('w, 'a) Ident.t
  type ('w, 'a) path = private ('w, 'a) ident Path.t

  (* Binding *)
  type ('w1, 'w2, 'a) binder = private
    ('w1, 'w2) W.link * ('w2, 'a) ident

  type ('w, 'a) fresh = Fresh : ('w1, 'w2, 'a) binder -> ('w1, 'a) fresh
  val fresh : 'w W.t -> 'a namespace -> name -> ('w, 'a) fresh

  (* Bindings *)
  type ('w1, 'w2) t =
    | Bind : ('w1, 'w2) t * ('w2, 'w3, 'a) binder * ('w2, 'a) v -> ('w1, 'w3) t
    | Update : ('w1, 'w2) t * ('w2, 'a) ident * ('w2, 'a) v -> ('w1, 'w2) t
    | End : ('w, 'w) t

  type 'w branch = Branch : ('w, 'a) t -> 'w branch [@@unboxed]
end

module type NESTING = sig
  module Namespace : NAMESPACE
  module Scope : SCOPE with module Namespace := Namespace

  type namespace
  val namespace : namespace Namespace.t
  val scope : 'w W.t -> ('w, namespace) W.v -> 'w Scope.branch

  type ('w1, 'w2) path_transport =
    { transport : 'a. ('w1, 'a) Scope.path -> ('w2, 'a) Scope.path }

  val transport :
    ('w1, 'w2) path_transport ->
    'a Scope.namespace -> ('w1, 'a) W.v -> ('w2, 'a) W.v
end

module type ENV = sig
  module Namespace : NAMESPACE
  module Scope : SCOPE
    with module Namespace := Namespace
  module Nesting : NESTING
    with module Namespace := Namespace
    with module Scope := Scope
  open Scope

  (* To type fork/merge: type ('w1, 'w2) t *)
  type 'w t
  val empty : W.o t
  val extend : 'w1 t -> ('w1, 'w2) Scope.t -> 'w2 t

  val lookup : 'w t -> 'a Namespace.t -> name Path.t -> ('w, 'a) path option
  val find : 'w t -> 'a Namespace.t -> name Path.t -> (('w, 'a) path * ('w, 'a) v) option
  val get : 'w t -> 'a Namespace.t -> ('w, 'a) path -> ('w, 'a) v

  type 'w fresh =
      Fresh : ('w1, 'w2, 'a) binder * ('w1, 'a) v * 'w2 t -> 'w1 fresh
  val bind : 'w1 t -> 'a namespace -> name -> ('w1, 'a) v -> 'w1 fresh
  val update : 'w t -> ('w, 'a) Ident.t -> ('w, 'a) v -> 'w t
  (*val open_ : 'w t -> ('w, Nesting.namespace) path -> ('w1, 'w2) t*)
  (*val scope : 'w t -> (W.o, 'w2) Scope.t .. should include Open*)
end

module Make_scope (Namespace : NAMESPACE) :
sig
  module Scope : SCOPE with module Namespace = Namespace

  module Make_env
      (Nesting : NESTING with module Namespace := Namespace
                          and module Scope := Scope) :
    ENV with module Namespace := Namespace
         and module Scope := Scope
         and module Nesting := Nesting
end
