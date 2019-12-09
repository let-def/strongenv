open Env

module rec Syntax : sig
  type ('w, 'ns) path = ('w, 'ns) Scope.path
  type ('w1, 'w2, 'ns) binder = ('w1, 'w2, 'ns) Scope.binder

  type ns_typ = Namespace.Type.p
  type ns_term = Namespace.Term.p

  type 'w typ =
    | Ty_var of ('w, ns_typ) path
    | Ty_arr of 'w typ * 'w typ
    | Ty_forall : ('w1, 'w2, ns_typ) binder * 'w2 typ -> 'w1 typ

  type 'w term =
    | Te_var of ('w, ns_term) path
    | Te_lam : ('w1, 'w2, ns_term) binder * 'w2 term -> 'w1 term
    | Te_app of ('w, ns_term) path * ('w, ns_term) path
    | Te_LAM : ('w1, 'w2, ns_typ) binder * 'w2 term -> 'w1 term
    | Te_APP of ('w, ns_term) path * ('w, ns_typ) path

  type 'w mod_
end = Syntax

and Namespace : sig
  module Type : W.INDEXED with type 'w t = 'w Syntax.typ
  module Term : W.INDEXED with type 'w t = 'w Syntax.term

  type 'a t =
    | Type : Type.p t
    | Term : Term.p t

  include ORDERED with type 'a t := 'a t
end = struct
  module Type = W.Indexed0(struct type 'a t = 'a Syntax.typ end)
  module Term = W.Indexed0(struct type 'a t = 'a Syntax.term end)
  type 'a t =
    | Type : Type.p t
    | Term : Term.p t

  let compare (type a b) (a : a t) (b : b t) : (a, b) order =
    match a, b with
    | Type , Type -> Eq
    | Term , Term -> Eq
    | Type , Term -> Lt
    | Term , Type -> Gt
end

and Scope : PREENV with type 'a namespace = 'a Namespace.t = Make(Namespace)
