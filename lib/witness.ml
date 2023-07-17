(* Type equality *)
type (_, _) eq = Refl : ('a, 'a) eq
let refl_eq : ('a, 'a) eq = Refl

(* Sub-typing *)
module type SUB = sig type t type u = private t type s val eq : (s, u) eq end
type ('s, 't) sub = (module SUB with type s = 's and type t = 't)
let refl_sub (type a) =
  let module Sub = struct
    type t = a
    type u = a
    type s = a
    let eq = Refl
  end in ((module Sub) : (a, a) sub)

let trans_sub (type a b c)
    ((module AB) : (a, b) sub)
    ((module BC) : (b, c) sub) : (a, c) sub
  =
  let Refl = AB.eq in
  let Refl = BC.eq in
  let module Sub = struct
    type t = BC.t
    type u = AB.u
    type s = AB.s
    let eq : (s, u) eq = Refl
  end in
  ((module Sub) : (a, c) sub)

(* Typed-indexed ordering *)
type ('a, 'b) order = Lt | Eq : ('a, 'a) order | Gt

let order_compare c =
  if c < 0 then Lt
  else if c > 0 then Gt
  else Eq

module type ORDERED = sig
  type 'a t
  val compare : 'a t -> 'b t -> ('a, 'b) order
end
