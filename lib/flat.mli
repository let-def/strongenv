(* OK: sharing, recursion
   TODO: safe update
   TODO: lazy substitution
*)

type 'w world = 'w World.world
type ('w, 'a) v_strong = ('w, 'a) World.v_strong
type (+'w, 'a) v = ('w, 'a) World.v

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
    Binder of ('w1, 'w2) World.link * ('w2, 'a) ident * ('w1, 'a) v

  type ('w, 'v) transport
  module Transport : sig
    val source : ('w, 'v) transport -> 'w world
    val target : ('w, 'v) transport -> 'v world

    type ('v1, 'w2, 'ns) t_binder =
        Binder : ('w2, 'v2) transport * ('v1, 'v2, 'ns) binder
          -> ('v1, 'w2, 'ns) t_binder

    val ident : ('w, 'v) transport -> ('w, 'a) ident -> ('v, 'a) ident

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
  val get : 'w env -> ('w, 'a) ident -> ('w, 'a) v
  val bind : 'w env -> 'a namespace -> ('w, 'a) v -> ('w, 'a) fresh
  val bind' : 'w env -> 'a namespace -> ('w, 'a) v_strong -> ('w, 'a) fresh
  val update : 'w env -> ('w, 'a) ident -> ('w, 'a) v -> ('w, 'a) fresh
  val update' : 'w env -> ('w, 'a) ident -> ('w, 'a) v_strong -> ('w, 'a) fresh
end

module type NEW_CONTEXT = sig
  include CONTEXT

  type configuration = {
    transport : 'w 'v 'a.  ('w, 'v) transport ->
      'a namespace -> ('w, 'a) v_strong -> ('v, 'a) v_strong
  }
  val configure : configuration -> unit
end

module Make_context (Namespace : Type.ORDERED) :
  NEW_CONTEXT with type 'a namespace = 'a Namespace.t
