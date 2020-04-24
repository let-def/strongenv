(* OK: sharing, recursion
   TODO: safe update
   TODO: lazy substitution
   TODO: inference variable (~ delayed name-allocation)
*)

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
val order_compare : int -> ('a, 'a) order

module type ORDERED = sig
  type 'a t
  val compare : 'a t -> 'b t -> ('a, 'b) order
end

(* World *)

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
end

type 'a world = 'a World.world
type ('w, 'a) v = ('w, 'a) World.v
type (+'w, 'a) v_weak = ('w, 'a) World.v_weak
type name = string

module type CONTEXT = sig
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

  type ('w, 'v) transport
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

  type 'w env
  module Env : sig
    type 'w env
    val empty : unit -> World.o env
    val lookup : 'w env -> 'a Path.pre -> ('w, 'a) path option
    val find : 'w env -> 'a Path.pre -> (('w, 'a) path * ('w, 'a) v) option
    val get : 'w env -> 'a namespace -> ('w, 'a) path -> ('w, 'a) v
  end
end

module Make_context (Namespace : ORDERED) : sig
  include CONTEXT
  module Configure(P : sig
      val project : 'w env -> 'a namespace -> ('w, 'a) v -> 'w scope
      val transport : ('w, 'v) transport -> 'a namespace -> ('w, 'a) v -> ('v, 'a) v
    end)() : sig end
end
