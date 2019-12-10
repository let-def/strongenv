open Env

module rec Syntax : sig
  type ('w, 'ns) path = ('w, 'ns) Scope.path
  type ('w1, 'w2, 'ns) binder = ('w1, 'w2, 'ns) Scope.binder

  type ns_typ = Namespace.Type.p
  type ns_term = Namespace.Term.p
  type ns_mod = Namespace.Mod_.p

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

  type 'w mod_ = unit
end = Syntax

and Namespace : sig
  module Type : W.INDEXED with type 'w t = 'w Syntax.typ
  module Term : W.INDEXED with type 'w t = 'w Syntax.term
  module Mod_ : W.INDEXED with type 'w t = 'w Syntax.mod_

  type 'a t =
    | Type : Type.p t
    | Term : Term.p t
    | Mod_ : Mod_.p t

  include ORDERED with type 'a t := 'a t
end = struct
  module Type = W.Indexed0(struct type 'a t = 'a Syntax.typ end)
  module Term = W.Indexed0(struct type 'a t = 'a Syntax.term end)
  module Mod_ = W.Indexed0(struct type 'a t = 'a Syntax.mod_ end)
  type 'a t =
    | Type : Type.p t
    | Term : Term.p t
    | Mod_ : Mod_.p t

  let compare (type a b) (a : a t) (b : b t) : (a, b) order =
    match a, b with
    | Type, Type -> Eq
    | Term, Term -> Eq
    | Mod_, Mod_ -> Eq
    | Type, (Term | Mod_) -> Lt
    | Term, Mod_ -> Lt
    | Term, Type -> Gt
    | Mod_,  (Type | Term) -> Gt
end

and Scope : PREENV with type 'a namespace = 'a Namespace.t = Make(Namespace)

module Env = Scope.Make_env (struct
    open Scope

    let project _w _ns _v = Branch End

    let rec transport_typ
      : type v w. (v, w) Transport.t -> v Syntax.typ -> w Syntax.typ
      = fun tp -> function
      | Ty_var path -> Ty_var (Transport.path tp path)
      | Ty_arr (t1, t2) -> Ty_arr (transport_typ tp t1, transport_typ tp t2)
      | Ty_forall (binder, typ) ->
        let Transport.Binder (tp', binder') = Transport.binder tp binder in
        Ty_forall (binder', transport_typ tp' typ)

    let rec transport_term
      : type v w. (v, w) Transport.t -> v Syntax.term -> w Syntax.term
      = fun tp -> function
      | Te_var path -> Te_var (Transport.path tp path)
      | Te_lam (binder, term) ->
        let Transport.Binder (tp', binder') = Transport.binder tp binder in
        Te_lam (binder', transport_term tp' term)
      | Te_app (te1, te2) ->
        Te_app (transport_term tp te1, transport_term tp te2)
      | Te_LAM (binder, term) ->
        let Transport.Binder (tp', binder') = Transport.binder tp binder in
        Te_LAM (binder', transport_term tp' term)
      | Te_APP (te1, ty1) ->
        Te_APP (transport_term tp te1, transport_typ tp ty1)

    let transport tp (type a) (w1 : 'w1 world) (w2 : 'w2 world)
        (ns : a Namespace.t) (v : (_, a) W.v) : (_, a) W.v =
      match ns with
      | Namespace.Term ->
        Namespace.Term.(pack w2 (transport_term tp (unpack w1 v)))
      | Namespace.Type ->
        Namespace.Type.(pack w2 (transport_typ tp (unpack w1 v)))
      | Namespace.Mod_ ->
        Namespace.Mod_.(pack w2 (unpack w1 v))
  end)
