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
