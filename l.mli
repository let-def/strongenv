(* Le système de type d'OCaml assure avant tout la sûreté à l'exécution :
   pas de segfault.
   On peut encoder des invariants plus subtiles avec des types abstraits ou
   privés: entiers positifs, listes triés, etc.

   Ces propriétés simples ont un côté absolu : un entier est positif ou non.
   Pour la liste triée c'est de prime abord un peu moins vrai : elle est triée
   relativement à une relation d'ordre.
   En pratique, on travaille avec un nombre faible de relations d'ordres, le
   plus souvent une seule par type. On pourra donc abstraire la notion de
   relation d'ordre avec un foncteur (comme c'est fait dans Map et Set).

   En revanche il y a des propriétés plus subtiles que l'on ne peut pas
   capturer (facilement) avec cette approche.
   Par exemple les entiers positifs plus petit qu'une certaine borne,
   déterminée à l'execution. Très utile pour garantir des manipulations
   correctes d'indices.
   Cela peut s'encoder aussi au niveau du système de module avec un peu
   d'inconfort.  (Voir par exemple les modules Finite, Partition et Valmari de
   https://github.com/let-def/grenier/tree/master/valmari).

   C'est encore plus compliqué pour un environnement de typage : quand on
   l'étend, tout les identificateurs précédents sont encore liés dedans, on
   aimerait se souvenir qu'il est sûr d'y accéder.
   C'est une propriété monotone, la liaison de nouveaux identificateurs
   engendre un ordre partiel entre les environnements.

   Dans ce module, on propose un encodage pour ces propriétés monotones.
   Un environnement ['w env] a un paramètre fantôme ['w], appelé "world", qui
   représente une position dans cet ordre partiel.
   Étendre l'environnement produit un type ['w2 env] tel que ['w :> 'w2]:
   on reflète la relation d'ordre dynamique, entre environnements étendus, dans
   la relation de sous-typage.

   Un identificateur reçoit alors le type [+'w ident]: un identificateur est
   covariant.  S'il est valide dans un environnement plus petit, il est alors
   aussi valide dans un environnement plus grand.
   On observe que ces garanties plus forte n'ont pas de coût à l'exécution: le
   sous-typage est gratuit, et toutes les propriétés que nous encodons n'ont
   aucun contenu calculatoire.
*)


(* Relations entre types *)
(* ********************* *)

(* Témoins d'égalité. Rien d'extraordinaire jusque-là. *)
type (_, _) eq = Refl : ('a, 'a) eq

(* Un encodage de témoins de sous-typage, pour des types abstraits.
   L'idée est de produire un module qui prouve qu'un type [u] est un sous-type
   d'un type [t] en utilisant les types privés.
   On en fait un module de première-class [(s, t) sub], qui, s'il est
   dépaqueté, convaint le typeur que (s :> t) (le type s peut-être coercé en
   t).

   Le dépaquetage manuel est modérément verbeux.  Si [val x : (s, t) sub], il
   faut écrire:

    let (module Sub) = x in
    let Refl = Sub.eq in
    [... dans ce contexte, (s :> t)].

   C'est entièrement mécanique, on peut imaginer une réecriture :

     [%subtype x] (expr)
   ~>
     let (module Sub) = x in
     let Refl = Sub.eq in
     expr
*)
module type SUB = sig
  type t
  type u = private t
  type s
  val eq : (s, u) eq
end
type ('s, 't) sub = (module SUB with type s = 's and type t = 't)

(* Worlds
   ======

   L'encodage des mondes.  Ce seront les éléments de notre relation d'ordre
   partiel.  L'idée est d'avoir un type avec un seul habitant, par exemple:

   type 'a w = Unit : unit w

   Ainsi, si on a une valeur [x : a w] où [a] est un type abstrait,
   on matchant sur Unit on peut retrouver l'égalité entre [a] et [unit].

   Le jeu va être de cacher cette égalité au niveau des types et de ne la
   révéler que selon des circonstances déterminées dynamiquement.

   Par exemple, voici un encodage de chaînes de caractère fortement typée.
   Leur type est ['w strong_string], tels que:
     soit [v1 : w1 strong_string] et [v2 : w2 strong_string],
     (w1 = w2) <=> (String.equal v1 v2).

   L'égalité des paramètres est équivalente à l'égalité des chaînes en tant que
   valeur.

   module Strong_string : sig
     type 'w t
     type fresh = Fresh : 'w t -> fresh
     val pack : string -> fresh
     val unpack : fresh -> string
     val equal : 'w1 t -> 'w2 t -> ('w1, 'w2) eq option
   end = struct
     type 'w t = Strong : unit string
     type fresh = Fresh : 'w t -> fresh
     let pack s = Fresh s
     let equal
         (type w1 w2)
         (Strong s1 : w1 t)
         (Strong s2 : w2 t)
       : (w1, w2) eq option =
       if String.equal s1 s2 then Some Refl else None
   end

   On révèle sélectivement l'égalité (triviale).

   L'encodage ci-dessous est un peu plus alambiqué: l'objectif est d'avoir les
   mêmes propriétés qu'avec [Strong_string] mais sans avoir besoin du GADT
   Strong, juste [type 'w t = private string].
*)

type o (* Ci-dessus, on a utilisé unit comme "monde par défaut".
          [o] est un alias d'unit, pour éviter les confusions avec des
          utilisations normales d'[unit]. *)
type 'a w (* Le type des mondes. Le paramètre ['a] est un type quelconque qui
             sert à les distinguer.
             [int w], [string w], sont des exemples valide de mondes.
             On révèlera sélectivement l'égalité ou l'inclusion entre mondes:
             - le type [(int w, string w) eq] pour [int =w string], et
             - le type [(int, string) incl] pour [int <=w string]
          *)
type ('w1, 'w2) incl = ('w1 w, 'w2 w) sub

(* Un monde par défaut, quand on manque d'imagination pour le choix d'indice *)
val origin : o w

(* Pattern matcher sur [unsafe_eq] révèle l'égalité entre monde quelconques. *)
val unsafe_eq : ('a w, o) eq

(* Pattern matcher sur [unsafe_sub] révèle l'inclusion entre monde quelconques. *)
val unsafe_sub : ('a, 'b) incl

(* Cas safe: réfléxivité de l'égalité et de l'inclusion *)
val refl_eq : ('a w, 'a w) eq
val refl_sub : ('a, 'a) incl

(* Encodage des propriétés
   ======================= *)

(* Le type [(prop, value) p] témoigne qu'une valeur de type [value] a la
   propriété [prop]. *)
type (+'prop, +'v) p = private 'v

(* On peut oublier qu'une valeur satisfait une propriété, il ne nous reste plus
   que la valeur *)
val drop : (_, 'v) p -> 'v

(* À ignorer pour l'instant. *)
type witness
type 'a prop = ('a, witness) p
val witness : ('prop, 'v) p -> 'prop prop

(* Chaque propriété à un type.
   Le module [Prop] expose les 3 familles de propriétés:
   - expansive, positive ou covariante, une propriété qui devient vrai à un
     certain moment.  Si la propriété est vraie dans [w1] et [w1 <= w2], la
     propriété est vraie dans [w2].
   - recessive, negative ou contravariante, une propriété qui devient fausse à
     un certain moment.  Si la propriété est vraie dans [w1] et [w2 <= w1], la
     propriété est vraie dans [w2].
   - invariante: la propriété est vraie à un moment, on ne peut rien dire sur
     les autres moments.

   Les propriétés utilisateurs sont définis en aliasant et cachant les
   propriétés de base.
   Par exemple, pour encoder le fait d'être bien formé dans un environnement,
   on définira:

     module Wellformed : sig
       type 'w wf (* on cache l'implémentation de wellformed *)

       val wf_world : ('w wf, _) p -> 'w w
       (* Une astuce d'encodage. D'autres primitives de la biliothèque ont
          besoin de connaître le monde associé à une propriété. En gros
          l'important pour "prouver" qu'un type utilisateur est une propriété
          est de fournir une fonction qui donne le monde dans lequel elle est
          vraie *)

       ...
       (* ici on définit des primitives pour introduire le fait d'être bien
          formé. La plus naïve par exemple :
          val assume_wellformed : typ -> ('w wf, typ) p

          Qui assume qu'un type quelconque est bien formé. À utiliser avec
          parcimonie, ou bien exposer des primitives plus fines, selon les
          invariants qui nous intéresse.
       *)

     end = struct
       type 'w wf = 'w Prop.pos (* être bien formé est une propriété positive:
                                   si      Gamma |- T wellformed
                                   alors   Gamma ; Delta |- T wellformed *)
       let wf_world = Prop.world_pos
       ...
     end
*)
module Prop : sig
  type +'a pos
  type -'a neg
  type 'a inv

  val assume_pos : 'v -> ('w pos, 'v) p
  val assume_neg : 'v -> ('w neg, 'v) p
  val assume_inv : 'v -> ('w inv, 'v) p
  (*external assume_pos' : 'v -> ('w pos, 'v) p = "%identity"
    external assume_neg' : 'v -> ('w neg, 'v) p = "%identity"
    external assume_inv' : 'v -> ('w inv, 'v) p = "%identity"*)

  val world_pos : ('w pos, _) p -> 'w w
  val world_neg : ('w neg, _) p -> 'w w
  val world_inv : ('w inv, _) p -> 'w w
  (*external world_pos' : ('w pos, _) p -> 'w w = "%ignore"
    external world_neg' : ('w neg, _) p -> 'w w = "%ignore"
    external world_inv' : ('w inv, _) p -> 'w w = "%ignore"*)

  (* Les external sont là pour se convaincre qu'il n'y a pas de contenu
     calculatoire associé à la gestion des propriétés.
     OUF, pas besoin de réécrire en C++ pour les PERF ! *)
end

(* Un dernier problème à résoudre avant de pouvoir utiliser les mondes
   librement.
   En OCaml, c'est facile de quantifier sur un type ground. Sauf que maintenant
   on se retrouve avec beaucoup plus de types paramétriques.

   Par exemple pour un environnement de typage dont les valeurs sont paramétrés
   par un monde on voudrait idéalement :

     type ('w, 'v) table
     val lookup : ('w, 'v) table -> string -> ('w 'v) option

   Si un lookup réussit, on récupère une valeur de type `'v` dans le monde
   `'w`. On encode ça avec une défonctionnalisation quelque chose proche des
   "lightweight higher-kinded types" de Jeremy et Leo.
   (Comme nos propriétés n'ont pas de contenu calculatoire, on a même pas
   besoin d'Obj.magic!)

   En fait on passe par un foncteur qui, pour un type utilisateur ['a u], crée
   un type [t] et un isomorphisme entre ['w w u] et [('w prop, t)]:
   si une valeur [u] est paramétrée par un monde ['w w], elle est équivalente à
   une valeur [t] avec une certaine propriété à l'indice ['w].
*)
module Lift0 (T : sig type 'w t end) : sig
  type t
  val pack_pos : 'w w T.t -> ('w Prop.pos, t) p
  val unpack_pos : ('w Prop.pos, t) p -> 'w w T.t

  val pack_neg : 'w w T.t -> ('w Prop.neg, t) p
  val unpack_neg : ('w Prop.neg, t) p -> 'w w T.t

  val pack_inv : 'w w T.t -> ('w Prop.inv, t) p
  val unpack_inv : ('w Prop.inv, t) p -> 'w w T.t
end

module Lift1 (T : sig type ('w, 'a) t end) : sig
  type 'a t
  val pack_pos : ('w w, 'a) T.t -> ('w Prop.pos, 'a t) p
  val unpack_pos : ('w Prop.pos, 'a t) p -> ('w w, 'a) T.t

  val pack_neg : ('w w, 'a) T.t -> ('w Prop.neg, 'a t) p
  val unpack_neg : ('w Prop.neg, 'a t) p -> ('w w, 'a) T.t

  val pack_inv : ('w w, 'a) T.t -> ('w Prop.inv, 'a t) p
  val unpack_inv : ('w Prop.inv, 'a t) p -> ('w w, 'a) T.t
end
