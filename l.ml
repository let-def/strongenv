(* Base type relations *)
type (_, _) eq = Refl : ('a, 'a) eq

module type SUB = sig
  type t
  type u = private t
  type s
  val eq : (s, u) eq
end

type ('s, 't) sub = (module SUB with type s = 's and type t = 't)

(* Worlds *)
type o = unit
type 'a w = unit
type ('w1, 'w2) incl = ('w1 w, 'w2 w) sub
let origin = ()
let unsafe_eq : ('a w, o) eq = Refl
let unsafe_sub : ('a, 'b) incl =
  fun (type a b) ->
  let module Sub = struct
    type t = a w
    type u = a w
    type s = b w
    let eq = Refl
  end in ((module Sub) : (a w, b w) sub)

let refl_eq = unsafe_eq
let refl_sub = unsafe_sub

(* Properties *)
type (+'prop, +'v) p = 'v

type witness = unit
type 'a prop = ('a, witness) p
let witness : ('prop, 'v) p -> 'prop prop = ignore

let drop x = x

module Prop = struct
  type +'a pos = unit
  type -'a neg = unit
  type 'a inv = unit

  let assume_pos : 'v -> ('w pos, 'v) p = fun x -> x
  let assume_neg : 'v -> ('w neg, 'v) p = fun x -> x
  let assume_inv : 'v -> ('w inv, 'v) p = fun x -> x
  (*external assume_pos' : 'v -> ('w pos, 'v) p = "%identity"
    external assume_neg' : 'v -> ('w neg, 'v) p = "%identity"
    external assume_inv' : 'v -> ('w inv, 'v) p = "%identity"*)

  let world_pos : ('w pos, _) p -> 'w w = ignore
  let world_neg : ('w neg, _) p -> 'w w = ignore
  let world_inv : ('w inv, _) p -> 'w w = ignore
  (*external world_pos' : ('w pos, _) p -> 'w w = "%ignore"
    external world_neg' : ('w neg, _) p -> 'w w = "%ignore"
    external world_inv' : ('w inv, _) p -> 'w w = "%ignore"*)
end

type opaque = o w

module Lift0 (T : sig type 'w t end) : sig
  type t = opaque T.t

  val pack_pos : 'w w T.t -> ('w Prop.pos, t) p   (* = "%identity" *)
  val unpack_pos : ('w Prop.pos, t) p -> 'w w T.t (* = "%identity" *)

  val pack_neg : 'w w T.t -> ('w Prop.neg, t) p   (* = "%identity" *)
  val unpack_neg : ('w Prop.neg, t) p -> 'w w T.t (* = "%identity" *)

  val pack_inv : 'w w T.t -> ('w Prop.inv, t) p   (* = "%identity" *)
  val unpack_inv : ('w Prop.inv, t) p -> 'w w T.t (* = "%identity" *)
end = struct
  type t = opaque T.t

  let pack_pos = Prop.assume_pos
  let unpack_pos = drop

  let pack_neg = Prop.assume_neg
  let unpack_neg = drop

  let pack_inv = Prop.assume_inv
  let unpack_inv = drop
end

module Lift1 (T : sig type ('w, 'a) t end) : sig
  type 'a t = (opaque, 'a) T.t
  val pack_pos : ('w w, 'a) T.t -> ('w Prop.pos, 'a t) p   (* = "%identity" *)
  val unpack_pos : ('w Prop.pos, 'a t) p -> ('w w, 'a) T.t (* = "%identity" *)

  val pack_neg : ('w w, 'a) T.t -> ('w Prop.neg, 'a t) p   (* = "%identity" *)
  val unpack_neg : ('w Prop.neg, 'a t) p -> ('w w, 'a) T.t (* = "%identity" *)

  val pack_inv : ('w w, 'a) T.t -> ('w Prop.inv, 'a t) p   (* = "%identity" *)
  val unpack_inv : ('w Prop.inv, 'a t) p -> ('w w, 'a) T.t (* = "%identity" *)
end = struct
  type 'a t = (opaque, 'a) T.t

  let pack_pos = Prop.assume_pos
  let unpack_pos = drop

  let pack_neg = Prop.assume_neg
  let unpack_neg = drop

  let pack_inv = Prop.assume_inv
  let unpack_inv = drop
end
