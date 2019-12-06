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

(* Names and qualified names *)

type name = string

module Path : sig
  type 'a t = Ident of 'a | Dot of 'a t * name
  val bind : ('a -> 'b t) -> 'a t -> 'b t
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

  type ('w, 'a) fresh = Fresh : ('w1, 'w2, 'a) binder -> ('w1, 'a) fresh
  val fresh : 'w W.t -> 'a namespace -> name -> ('w, 'a) fresh

  (* Bindings *)
  type ('w1, 'w2) t =
    | Bind : ('w1, 'w2) t * ('w2, 'w3, 'a) binder * 'a -> ('w1, 'w3) t
    | Update : ('w1, 'w2) t * ('w2, 'a) ident * 'a -> ('w1, 'w2) t
    | End : ('w, 'w) t

  type 'w branch = Branch : ('w, 'a) t -> 'w branch [@@unboxed]
end

module Make_scope (Namespace : ORDERED) :
  SCOPE with module Namespace = Namespace

(*module type SCOPED = sig
  module Scope : SCOPE
  val scope :
    'a Scope.namespace -> 'w W.t -> ('w, 'a) W.v -> 'w Scope.branch option
  type ('w1, 'w2) path_transport = {
    transport : 'a. ('w1, 'a) Scope.path -> ('w2, 'a) Scope.path;
  }
  val transport :
    ('w1, 'w2) path_transport ->
    'a Scope.namespace -> ('w1, 'a) W.v -> ('w2, 'a) W.v
end

module type ENV = sig
  module Scope : SCOPE
  type ('w1, 'w2) env
  val empty : (W.o, W.o) env
  type ('w1, 'w2) extension =
      Extend : ('w2, 'w3) sub * ('w1, 'w3) env -> ('w1, 'w2) extension
  val extend : ('w1, 'w2) env -> ('w2, 'w3) Scope.t -> ('w1, 'w3) env
end*)
