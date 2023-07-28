open Strongenv
open Flat

module rec Syntax : sig
  type ('w, 'ns) path = ('w, 'ns) Context.ident
  type ('w1, 'w2, 'ns) binder = ('w1, 'w2, 'ns) Context.binder

  type ns_typ = Namespace.Type.p
  type ns_term = Namespace.Term.p

  type 'w typ =
    | Ty_var of ('w, ns_typ) path
    | Ty_arr of 'w typ * 'w typ
    | Ty_forall : ('w1, 'w2, ns_typ) binder * 'w2 typ -> 'w1 typ

  type 'w term =
    | Te_var of ('w, ns_term) path
    | Te_lam : ('w1, 'w2, ns_term) binder * 'w2 term -> 'w1 term
    | Te_app of 'w term * 'w term
    | Te_LAM : ('w1, 'w2, ns_typ) binder * 'w2 term -> 'w1 term
    | Te_APP of 'w term * 'w typ
end = Syntax

and Namespace : sig
  module Type : World.INDEXED with type 'w t = 'w Syntax.typ
  module Term : World.INDEXED with type 'w t = 'w Syntax.term

  type 'a t =
    | Type : Type.p t
    | Term : Term.p t

  include Witness.ORDERED with type 'a t := 'a t
end = struct
  module Type = World.Indexed0(struct type 'a t = 'a Syntax.typ end)
  module Term = World.Indexed0(struct type 'a t = 'a Syntax.term end)
  type 'a t =
    | Type : Type.p t
    | Term : Term.p t

  let compare (type a b) (a : a t) (b : b t) : (a, b) Witness.order =
    match a, b with
    | Type , Type -> Eq
    | Term , Term -> Eq
    | Type , Term -> Lt
    | Term , Type -> Gt
end

and Context : CONTEXT with type 'a namespace = 'a Namespace.t =
  Make_context(Namespace)

let id_equal id1 id2 =
  match Context.Ident.compare id1 id2 with
  | Eq -> true
  | Lt | Gt -> false

type ('w, 'a) ident = ('w, 'a) Context.ident

let retract_equiv (type w1 w2 w1' w2')
    (w1 : w1 world) (w1' : w1' world) (s1 : (w1, w1') Witness.sub)
    (w2 : w2 world) (w2' : w2' world) (s2 : (w2, w2') Witness.sub)
    (equiv : ((w1', 'a) ident * (w2', 'a) ident) list)
  : ((w1, 'a) ident * (w2, 'a) ident) list
  =
  List.filter_map (fun (id1, id2) ->
      match
        Context.Ident.retract w1 w1' s1 id1,
        Context.Ident.retract w2 w2' s2 id2
      with
      | Some id1, Some id2 -> Some (id1, id2)
      | _, _ -> None
    ) equiv

let extend_equiv (type w1 w2 w1' w2')
    (s1 : (w1, w1') Witness.sub) (s2 : (w2, w2') Witness.sub)
    (equiv : ((w1, 'a) ident * (w2, 'a) ident) list)
  : ((w1', 'a) ident * (w2', 'a) ident) list
  =
  let (module Sub1) = s1 in
  let Refl = Sub1.eq in
  let (module Sub2) = s2 in
  let Refl = Sub2.eq in
  (equiv
   :  ((w1, 'a) ident * (w2, 'a) ident) list
   :> ((w1', 'a) ident * (w2', 'a) ident) list)

let rec alpha_eq_typ : type wa wb.
  ((wa, Syntax.ns_typ) Context.ident *
   (wb, Syntax.ns_typ) Context.ident) list ->
  wa Syntax.typ -> wb Syntax.typ -> bool
  = fun equiv ty1 ty2 ->
    match ty1, ty2 with
    | Ty_arr (t1l, t1r), Ty_arr (t2l, t2r) ->
      alpha_eq_typ equiv t1l t2l && alpha_eq_typ equiv t1r t2r
    | Ty_var id1, Ty_var id2 ->
      List.exists
        (fun (id1', id2') -> id_equal id1 id1' && id_equal id2 id2')
        equiv
    | Ty_forall (b1, t1'), Ty_forall (b2, t2') ->
      let Context.Binder (l1, id1, pv1) = b1 in
      let Context.Binder (l2, id2, pv2) = b2 in
      let World.Unpack (wa0, wa0wa, v1) = World.unpack (World.source l1) pv1 in
      let World.Unpack (wb0, wb0wb, v2) = World.unpack (World.source l2) pv2 in
      let tv1 = Namespace.Type.unpack wa0 v1 in
      let tv2 = Namespace.Type.unpack wb0 v2 in
      alpha_eq_typ
        (retract_equiv
           wa0 (World.source l1) wa0wa
           wb0 (World.source l2) wb0wb
           equiv)
        tv1 tv2 &&
      alpha_eq_typ
        ((id1, id2) :: extend_equiv (World.sub l1) (World.sub l2) equiv)
        t1' t2'

    | (Ty_arr _ | Ty_var _ | Ty_forall _),
      (Ty_arr _ | Ty_var _ | Ty_forall _) ->
      false

