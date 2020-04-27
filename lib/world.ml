include Type

type o = |
type 'w world = W : int -> o world [@@ocaml.unboxed]
type 'w t = 'w world
type +'w elt = int
type (+'w, 'a) v = 'a

let empty : o world = W 0

type ('a, 'b) link = Link : int -> (o, o) link [@@ocaml.unboxed]
type 'a extension = Extension : ('a, 'b) link -> 'a extension

let extend (type w1) (W w : w1 world) : w1 extension =
  Extension (Link w)

let source (type a b) (Link a : (a, b) link) : a world = W a
let target (type a b) (Link a : (a, b) link) : b world = W (a + 1)
let sub (type a b) (Link _ : (a, b) link) : (a, b) sub = refl_sub
let elt (type a b) (Link a : (a, b) link) = a

module type INDEXED = sig
  type 'w t
  type p
  val pack : 'w world -> 'w t -> ('w, p) v
  val unpack : 'w world -> ('w, p) v -> 'w t
end

module Indexed0 (P : sig type 'w t end) = struct
  type 'w t = 'w P.t
  type p = o P.t
  let pack (type w1) (W _ : w1 world) (p : w1 P.t) : (w1, p) v = p
  let unpack (type w1) (W _ : w1 world) (p : (w1, p) v) : w1 t = p
end

module Transport : sig
  type ('w, 'v) t

  val sub : ('a, 'b) sub -> ('a, 'b) t
  val compose : ('a, 'b) t -> ('b, 'c) t -> ('a, 'c) t

  val elt : 'a elt -> ('a, 'b) t -> 'b elt

  type ('w1, 'v1, 'w2) t_link =
      Link : ('w2, 'v2) t * ('v1, 'v2) link -> ('w1, 'v1, 'w2) t_link
  val link : ('w1, 'v1) t -> 'v1 world -> ('w1, 'w2) link -> ('w1, 'v1, 'w2) t_link
end = struct
  type ('w, 'v) t = (int * int) list

  let sub _sub = []

  let compose t1 t2 =
    let rec aux = function
      | [], t2 -> t2
      | t1, [] -> t1
      | ((b1, o1) :: t1'), ((b2, o2) :: t2') ->
        if b2 = b1 + o1
        then (b1, o1 + o2) :: aux (t1', t2')
        else if b2 < b1 + o1
        then (b1, o1 + o2) :: aux (t1', t2)
        else (b2 + o1, o1 + o2) :: aux (t1, t2')
    in
    aux (t1, t2)

  type ('w1, 'v1, 'w2) t_link =
      Link : ('w2, 'v2) t * ('v1, 'v2) link -> ('w1, 'v1, 'w2) t_link

  let link (type w1 v1 w2)
      (_ : (w1, v1) t) (w : v1 world)
      (l1 : (w1, w2) link) : (w1, v1, w2) t_link =
    let Extension l2 = extend w in
    let elt1 = elt l1 and elt2 = elt l2 in
    let o = elt2 - elt1 in
    let t = if o > 0 then [elt1, o] else (assert (o = 0); []) in
    Link (t, l2)

  let rec elt a = function
    | [] -> a
    | (b, o) :: bs ->
      if a >= b then a + o else elt a bs
end

type 'w minimal = Minimal : ('w0, 'w1) link * ('w1, 'w2) sub -> 'w2 minimal
let minimize (type w) (W _ : w world) (elt : w elt) : w minimal =
  Minimal (Link elt, refl_sub)

type (+'w, 'a) v_weak = V_weak : 'w_ world * ('w_, 'a) v -> ('w, 'a) v_weak
let v_weak (type w a) (w : w world) (v : (w, a) v) : (w, a) v_weak =
  V_weak (w, v)

type ('w, 'a) unpack =
    Unpack : 'w0 world * ('w0, 'w1) sub * ('w0, 'a) v -> ('w1, 'a) unpack
let unpack (type w a) (W _ : w world)
    (V_weak ((W _ as w), v) : (w, a) v_weak) : (w, a) unpack =
  Unpack (w, refl_sub, v)

type (+'w, 'a) v_ref =
  | V_ref : { mutable w : o world; mutable v : (o, 'a) v } -> ('w, 'a) v_ref
let v_ref (type w a) (W _ as w : w world) (v : (w, a) v) : (w, a) v_ref =
  V_ref {w; v}

let v_set (type w' w) (V_ref r : (w,'a) v_ref)
    (W _ as w : w' world) (_ : (w',w) sub) (v : (w,'a) v) =
  r.w <- w;
  r.v <- v

let v_get (type w a) (W _ : w world) (V_ref { w; v } : (w, a) v_ref)
  : (w, a) unpack =
  Unpack (w, refl_sub, v)

let unsafe_eq (type w) (W _ : w world) : (w, o) eq = Refl
let card (type o) (W w : o world) = w

let equal (type w1 w2) (_ : (w1, w2) sub) (W w1 : w1 world) (W w2 : w2 world)
  : (w1, w2) eq option
  = if w1 = w2 then Some Refl else None

type ('w1, 'w2) chain =
  | Before : ('w1, 'w2) sub -> ('w1, 'w2) chain
  | Same   : ('w1, 'w1) chain
  | After  : ('w2, 'w1) sub -> ('w1, 'w2) chain

let chain (type wa wb w)
    (W wa : wa world) (_ : (wa, w) sub)
    (W wb : wb world) (_ : (wb, w) sub)
  : (wa, wb) chain
  = if wa < wb then Before refl_sub else if wa = wb then Same else After refl_sub
