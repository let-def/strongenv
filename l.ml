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

module Lift0 (T : sig type 'w t end) : sig
  type t
  val pack_pos : 'w w T.t -> ('w Prop.pos, t) p
  val unpack_pos : ('w Prop.pos, t) p -> 'w w T.t

  val pack_neg : 'w w T.t -> ('w Prop.neg, t) p
  val unpack_neg : ('w Prop.neg, t) p -> 'w w T.t

  val pack_inv : 'w w T.t -> ('w Prop.inv, t) p
  val unpack_inv : ('w Prop.inv, t) p -> 'w w T.t
end = struct
  type t = T : 'w w T.t -> t
  let pack_pos t = Prop.assume_pos (T t)
  let unpack_pos p = let (T t) = drop p in t

  let pack_neg t = Prop.assume_neg (T t)
  let unpack_neg p = let (T t) = drop p in t

  let pack_inv t = Prop.assume_inv (T t)
  let unpack_inv p = let (T t) = drop p in t
end

module Lift1 (T : sig type ('w, 'a) t end) : sig
  type 'a t
  val pack_pos : ('w w, 'a) T.t -> ('w Prop.pos, 'a t) p
  val unpack_pos : ('w Prop.pos, 'a t) p -> ('w w, 'a) T.t

  val pack_neg : ('w w, 'a) T.t -> ('w Prop.neg, 'a t) p
  val unpack_neg : ('w Prop.neg, 'a t) p -> ('w w, 'a) T.t

  val pack_inv : ('w w, 'a) T.t -> ('w Prop.inv, 'a t) p
  val unpack_inv : ('w Prop.inv, 'a t) p -> ('w w, 'a) T.t
end = struct
  type 'a t = T : ('w w, 'a) T.t -> 'a t
  let pack_pos t = Prop.assume_pos (T t)
  let unpack_pos p = let (T t) = drop p in t

  let pack_neg t = Prop.assume_neg (T t)
  let unpack_neg p = let (T t) = drop p in t

  let pack_inv t = Prop.assume_inv (T t)
  let unpack_inv p = let (T t) = drop p in t
end
