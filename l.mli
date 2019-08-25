(* Equality witness *)
type (_, _) eq = Refl : ('a, 'a) eq

(* Sub-typing witness *)
module type SUB = sig
  type t
  type u = private t
  type s
  val eq : (s, u) eq
end
type ('s, 't) sub = (module SUB with type s = 's and type t = 't)

(* Worlds *)
type o
type 'a w
type ('w1, 'w2) incl = ('w1 w, 'w2 w) sub
val origin : o w
val unsafe_eq : ('a w, o) eq
val unsafe_sub : ('a, 'b) incl
val refl_eq : ('a w, 'a w) eq
val refl_sub : ('a, 'a) incl

(* Properties *)
type (+'prop, +'v) p = private 'v

type witness
type 'a prop = ('a, witness) p
val witness : ('prop, 'v) p -> 'prop prop

val drop : (_, 'v) p -> 'v

module Prop : sig
  type +'a pos
  (* Covariant monotonic property.  If property holds in world [w1] and [w1
     <= w2], then property holds in [w2] *)

  type -'a neg
  (* Contravariant monotonic property.  If property holds in world [w1] and
     [w2 <= w1], then property holds in [w2] *)

  type 'a inv
  (* Invariant property.  If it holds in a specific world, we can't say
     anything about related worlds. *)

  (* Assume that the property holds for a specific value *)

  val assume_pos : 'v -> ('w pos, 'v) p
  val assume_neg : 'v -> ('w neg, 'v) p
  val assume_inv : 'v -> ('w inv, 'v) p
  (*external assume_pos' : 'v -> ('w pos, 'v) p = "%identity"
    external assume_neg' : 'v -> ('w neg, 'v) p = "%identity"
    external assume_inv' : 'v -> ('w inv, 'v) p = "%identity"*)

  (* Get the world in which a property holds *)

  val world_pos : ('w pos, _) p -> 'w w
  val world_neg : ('w neg, _) p -> 'w w
  val world_inv : ('w inv, _) p -> 'w w
  (*external world_pos' : ('w pos, _) p -> 'w w = "%ignore"
    external world_neg' : ('w neg, _) p -> 'w w = "%ignore"
    external world_inv' : ('w inv, _) p -> 'w w = "%ignore"*)
end

module D0 (T : sig type 'w t end) : sig
  type t
  val pack_pos : 'w w T.t -> ('w Prop.pos, t) p
  val unpack_pos : ('w Prop.pos, t) p -> 'w w T.t

  val pack_neg : 'w w T.t -> ('w Prop.neg, t) p
  val unpack_neg : ('w Prop.neg, t) p -> 'w w T.t

  val pack_inv : 'w w T.t -> ('w Prop.inv, t) p
  val unpack_inv : ('w Prop.inv, t) p -> 'w w T.t
end

module D1 (T : sig type ('w, 'a) t end) : sig
  type 'a t
  val pack_pos : ('w w, 'a) T.t -> ('w Prop.pos, 'a t) p
  val unpack_pos : ('w Prop.pos, 'a t) p -> ('w w, 'a) T.t

  val pack_neg : ('w w, 'a) T.t -> ('w Prop.neg, 'a t) p
  val unpack_neg : ('w Prop.neg, 'a t) p -> ('w w, 'a) T.t

  val pack_inv : ('w w, 'a) T.t -> ('w Prop.inv, 'a t) p
  val unpack_inv : ('w Prop.inv, 'a t) p -> ('w w, 'a) T.t
end
