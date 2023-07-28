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
  CONTEXT with type 'a namespace = 'a Namespace.t
