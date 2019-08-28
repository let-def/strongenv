open L
(* Il faut commencer par lire L, c'est là qu'est le gros de l'encodage.
   Dans ce module on l'utilise pour représenter des environnements avec des
   garanties plus fortes. *)

(* Les identificateurs non-typés : juste une chaîne et un entier unique.  *)

module Ident : sig
  type t
  val fresh : string -> t
  val name : t -> string
  val stamp : t -> int
end = struct
  type t = { name : string; stamp : int }
  let counter = ref 0
  let fresh name = incr counter; { name; stamp = !counter }
  let name t = t.name
  let stamp t = t.stamp
end

(* Les environnements non typés :
   une liste associative entre un identificateur et un type ['a].  *)
module Env : sig
  type +'a t
  val empty : 'a t

  val bind : Ident.t -> 'a -> 'a t -> 'a t
  (* Lier un nom produit un nouvel identificateur.
     Si l'identificateur est déjà dans l'environnement, échoue avec l'exception
     [Invalid_argument "Env.bind: identifier already bound"].
  *)

  val get : Ident.t -> 'a t -> 'a
  (* Récupérer un identificateur doit toujours réussir.
     C'est une erreur run-time / exception de ne pas trouver de liaison. *)

  val update : Ident.t -> 'a -> 'a t -> 'a t
  (* Mettre à jour un identificateur. *)

  val lookup : string -> 'a t -> ('a * Ident.t) option
  (* Chercher un nom dans un environnement peut échouer.
     Mais si ça réussit, on recupère aussi l'identificateur. *)
end = struct
  type 'a t = (Ident.t * 'a) list
  let empty = []

  let rec mem k = function
    | [] -> false
    | (k', _) :: t -> Ident.stamp k = Ident.stamp k' || mem k t

  let bind k v t =
    if mem k t then invalid_arg "Env.bind: identifier already bound";
    ((k, v) :: t)

  let rec get k = function
    | [] -> invalid_arg "Env.get: identifier not bound"
    | (k', v) :: _ when Ident.stamp k = Ident.stamp k' -> v
    | _ :: rest -> get k rest
  let update k v t = (k, v) :: t
  let rec lookup k = function
    | [] -> None
    | (k', v) :: _ when Ident.name k' = k -> Some (v, k')
    | _ :: rest -> lookup k rest
end

(* Premier raffinement: environnement et identifiants indicés par un "monde".
   Comme ça on peut enforcer le succès de "get".
   Le monde peut s'interpréter comme un ensemble d'identificateurs liés dans un
   environnement.  *)
module EnvW : sig

  type -'w bindings
  (* La propriété "liés un ensemble d'identificateurs".
     Elle est négative : si un environnement lie un grand ensemble, il lie
     aussi un de ses sous-ensembles (avec moins d'identificateurs). *)

  type +'w bound
  (* La propriété "être lié dans un ensemble d'identificateurs".
     Elle est positive : si un identifcateur est lié dans un environnement, il
     est lié aussi un sur-ensemble. *)

  type (-'w, +'a) env = ('w bindings, 'a Env.t) p
  (* Un environnement est un Env.t qui a la propriété de lier tout les bindings
     de ['w]. *)

  val empty : (o, _) env
  (* L'environnement d'origine ne lie rien. On utilise [o] comme indice de ce
     monde de départ. *)

  type +'w ident = ('w bound, Ident.t) p
  (* Un identificateur est un Ident.t qui a la propriété d'être lié dans ['w]. *)

  type ('w1, 'w2) link = private 'w2 ident
  (* Un lien entre deux mondes: il témoigne que rajouter l'identificateur dans
     ['w1] aboutit à ['w2] (en gros w2 = w1 U {cet_ident}).
     Il est possible que w2 = w1, si l'identificateur était déjà lié. Peu
     importe, l'important est d'avoir la certitude qu'il sera lié dans [w2]
     (attention, ce n'est pas toujours le comportement souhaité, mais pour un
     typeur non-dépendant ça suffit :)).
     C'est à la fois un identificateur qui est lié dans [w2] et une preuve que
     [w2 >= w1]. *)

  val ident : ('w1, 'w2) link -> 'w2 ident
  (* Récupérer l'identificateur introduit par un lien. *)

  val incl : ('w1, 'w2) link -> ('w1, 'w2) incl
  (* Récupérer le témoins de l'inclusion des mondes liés. *)

  type 'w fresh = Fresh : ('w1, 'w2) link -> 'w1 fresh
  val fresh : string -> 'w fresh
  (* Création d'un nouveau lien: il connecte un monde existant et un nouveau
     monde.  L'indice du nouveau monde est une existentielle. C'est comme ça
     qu'on produit un nouveau "nom" pour chaque extension d'un environnement.
     E.g:
         (* env : (#w0, value) Env.t *)
       let Fresh link_a = Env.fresh "a" in
       let env = Env.bind (Env.ident link_a) v1 env in
         (* env : (#w1, value) Env.t
            link_a : (#w0, #w1) Env.link *)
       let Fresh link_b = Env.fresh "a" in
       let env = Env.bind (Env.ident link_b) v2 env in
         (* env : (#w2, value) Env.t
            link_b : (#w1, #w2) Env.link *)
       ...
  *)

  val bind : ('w1, 'w2) link -> 'a -> ('w1, 'a) env -> ('w2, 'a) env
  (* Introduit une nouvelle liaison dans l'environnement.
     Introduire deux fois la même liaison est une erreur à l'exécution.  *)

  val get : 'w ident -> ('w, 'a) env -> 'a
  (* Récupérer le contenu d'un identificateur ne peut a priori plus échouer *)

  val update : 'w ident -> 'a -> ('w, 'a) env -> ('w, 'a) env
  (* ... *)

  val lookup : string -> ('w, 'a) env -> ('a * 'w ident) option
  (* Par rapport au lookup précédent: l'identificateur est bien typé dans le
     monde courant. *)

end = struct
  (* bindings et bound: alias des propriétés négatives et positives *)
  type -'w bindings = 'w Prop.neg
  type +'w bound = 'w Prop.pos

  type (-'w, +'a) env = ('w bindings, 'a Env.t) p
  type +'w ident = ('w bound, Ident.t) p
  type ('w1, 'w2) link = 'w2 ident

  (* Le reste de l'implémentation _wrap_ Env non-typé :
     - décorer les valeurs avec une propriété avant des les exposer
       (Prop.assume_...)
     - enlever la décoration quand on récupère une valeur (drop)
  *)
  let empty : (o, _) env =
    Prop.assume_neg Env.empty

  let ident x = x
  let incl _ = unsafe_sub

  type 'w fresh = Fresh : ('w1, 'w2) link -> 'w1 fresh
  let fresh name = Fresh (Prop.assume_pos (Ident.fresh name))

  let bind k v t =
    let env = Env.bind (drop k) v (drop t) in
    Prop.assume_neg env

  let get id env = Env.get (drop id) (drop env)

  let update id v env =
    Prop.assume_neg (Env.update (drop id) v (drop env))

  let lookup name env =
    match Env.lookup name (drop env) with
    | None -> None
    | Some (v, id) -> Some (v, Prop.assume_pos id)
end

(* Le problème se complique : maintenant qu'on peut garantir qu'un
   identificateur est dans un environnement, on peut vouloir parler de valeurs
   bien formées dans cet environnement.

   Par exemple avec :
     val find_type : 'w ident -> ('w, type_decl) env -> type_decl
   on a oublié que le type_decl retourné est bien formé dans 'w.
   Une meilleure signature serait
     val find_type : 'w ident -> ('w, type_decl) env -> 'w type_decl

   C'est ce que l'on se propose de résoudre ici.

   Une autre définition serait:
     val find_type : 'w1 ident -> ('w1, type_decl) env ->
     exists 'w2, 'w2 <= 'w1, 'w2 type_decl
   Il existe un sous-ensemble de 'w1 dans lequel la déclaration est bien
   formée. C'est un peu plus fin, cela dépend des propriétés qu'on recherche.
*)
module EnvWF : sig
  type -'w bindings
  type +'w bound

  (* Comme précédemment *)
  type (-'w, +'a) env = ('w bindings, 'a Env.t) p
  val empty : (o, _) env

  type +'w ident = ('w bound, Ident.t) p

  type ('w1, 'w2) link = private 'w2 ident
  val ident : (_, 'w) link -> 'w ident
  val incl : ('w1, 'w2) link -> ('w1, 'w2) incl

  type 'w fresh = Fresh : ('w1, 'w2) link -> 'w1 fresh
  val fresh : string -> 'w fresh

  (* Bonne formation des valeurs *)
  type +'w wf (* la propriété être "bien-formé" dans le monde 'w *)

  (* Une valeur bien formé: une type quelconque avec la propriété wf *)
  type (+'w, +'v) v = ('w wf, 'v) p

  (* Assumer qu'une valeur est bien formée. *)
  val wf : 'a -> ('w, 'a) v

  (* Bind, get, update, lookup... Recoivent maintenant des valeurs décorées
     avec wf *)
  val bind : ('w1, 'w2) link -> ('w, 'a) v -> ('w1, 'a) env -> ('w2, 'a) env
  val get : 'w ident -> ('w, 'a) env -> ('w, 'a) v
  val update : 'w ident -> ('w, 'a) v -> ('w, 'a) env -> ('w, 'a) env
  val lookup : string -> ('w, 'a) env -> (('w, 'a) v * 'w ident) option

  (* Subtilité : pour pouvoir utiliser la prop wf avec un type paramétrique
     ML normal, on crée un type [montype'] tels que ['w w montype] et [('w,
     montype') v] soient isomorphes. *)
  module Lift (T : sig type 'w t end ) : sig
    type t
    val pack : 'w w T.t -> ('w, t) v
    val unpack : ('w, t) v -> 'w w T.t
  end
end = struct
  type -'w bindings = 'w Prop.neg
  type +'w bound = 'w Prop.pos
  type +'w wf = 'w Prop.pos

  type (-'w, +'a) env = ('w bindings, 'a Env.t) p

  let empty : (o, _) env =
    Prop.assume_neg Env.empty

  type +'w ident = ('w bound, Ident.t) p
  let ident x = x
  let incl _ = unsafe_sub

  type ('w1, 'w2) link = 'w2 ident
  type 'w fresh = Fresh : ('w1, 'w2) link -> 'w1 fresh
  let fresh name = Fresh (Prop.assume_pos (Ident.fresh name))

  type (+'w, +'v) v = ('w wf, 'v) p
  let wf v = Prop.assume_pos v

  let bind k v t =
    Prop.assume_neg (Env.bind (drop k) (drop v) (drop t))

  let get id env = wf (Env.get (drop id) (drop env))

  let update id v env =
    Prop.assume_neg (Env.update (drop id) (drop v) (drop env))

  let lookup name env =
    match Env.lookup name (drop env) with
    | None -> None
    | Some (v, id) -> Some (wf v, Prop.assume_pos id)

  module Lift (T : sig type 'w t end ) : sig
    type t
    val pack : 'w w T.t -> ('w, t) v
    val unpack : ('w, t) v -> 'w w T.t
  end = struct
    include Lift0(T)
    let pack = pack_pos
    let unpack = unpack_pos
  end
end

(* Enfin, un exemple avec les types de System F *)

module SystemF = struct
  open EnvWF

  (* La difficulté est FORALL qui introduit un nouvel identificateur de
     type.  *)
  type 'w typ =
    | VAR of 'w ident
    | ARR of 'w typ * 'w typ
    | FORALL : ('w1, 'w2) link * 'w2 typ -> 'w1 typ

  module Typ = Lift(struct type 'w t = 'w typ end)
  (* Un environnement de types peut maintenant être représenté par
     [('w, Typ.t) env]. Il faudra utiliser Typ.pack et Typ.unpack pour
     retrouver un ['w w typ]. *)
end
