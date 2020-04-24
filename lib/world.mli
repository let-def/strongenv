include module type of struct include Type end

type o
type 'w world
type 'w t = 'w world
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

type 'w minimal = Minimal : ('w0, 'w1) link * ('w1, 'w2) sub -> 'w2 minimal
val minimize : 'w world -> 'w elt -> 'w minimal

type (+'w, 'a) v_weak
val weaken : 'w world -> ('w, 'a) v -> ('w, 'a) v_weak
type ('w, 'a) unpack =
    Unpack : 'w0 world * ('w0, 'w1) sub * ('w0, 'a) v -> ('w1, 'a) unpack
val unpack : 'w world -> ('w, 'a) v_weak -> ('w, 'a) unpack

val equal : ('w1, 'w2) sub -> 'w1 world -> 'w2 world -> ('w1, 'w2) eq option
val unsafe_eq : 'w world -> ('w, o) eq
val card : 'w world -> int

type ('w1, 'w2) chain =
  | Before : ('w1, 'w2) sub -> ('w1, 'w2) chain
  | Same   : ('w1, 'w1) chain
  | After  : ('w2, 'w1) sub -> ('w1, 'w2) chain

val chain :
  'wa world -> ('wa, 'w) sub ->
  'wb world -> ('wb, 'w) sub ->
  ('wa, 'wb) chain
