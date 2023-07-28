(** Extension

    Add the necessary things to encode GADTs:
    - equality constraints
    - existentials
    - scopes

    On scoping representation:
    - add type constructors, detect scope escape
    - add level to every type expression, to implement other Remy's
      optimizations
      -> once we have type constructors, we can introduce non principal
         constructs. Detect them
    - implement Lionel Parreaux's subtyping as a fancy example
    - for a cleaner presentation: abstract some invariants
      -> if repr returns a Ty_var, it is not unified
      -> a generalized level cannot appear in unification
    - support for patterns,
      -> GADT patterns, that introduce existentials and universals

    Ko:
    - add support for module systems. Module system is orthogonal to strongenv.
  *)

open Strongenv

type var = string

module Source = struct

  type typ =
    | Unit
    | Var of var
    | Arr of typ * typ
    | Eq of typ * typ

  type lam =
    | Var of var
    | Lam of var * lam
    | App of lam * lam
    | Let of var * lam * lam
    | New of var * lam
    | Use of {
        witness: lam;
        witness_types: typ * typ;
        body: lam
      }

  module Infix = struct
    let (!) x = Var x
    let (let-) (name, value) f = Let (name, value, f (Var name))
    let (%) x y = App (x, y)
    let (@->) name body = Lam (name, body)
  end
end

module rec Syntax : sig
  type ('w, 'ns) ident = ('w, 'ns) Context.ident
  type ('w1, 'w2, 'ns) binder = ('w1, 'w2, 'ns) Context.binder

  type ns_level = Namespace.Level.p
  type ns_value = Namespace.Value.p
  type ns_rigid = Namespace.Rigid.p

  type 'w level = { mutable level_repr : 'w level_repr; }
  and 'w level_repr =
    | Fresh of {
        gensym: int ref;
        world: 'w World.t;
        mutable variables : 'w typ list;
      }
    | Generalized of 'w typ list

  and 'w scope = Scope : {
    scope: 'w0 World.t;
    scope_sub : ('w0, 'w) Witness.sub;
  } -> 'w scope

  and 'w typ = {
    id: int;
    mutable scope: 'w scope;
    mutable level: 'w level;
    (* invariant: scope <= level *)
    mutable repr: 'w typ_desc;
    (* forall succ \in repr,
         succ.scope >= scope && succ.level <= level *)
  }

  and 'w typ_desc =
    | Ty_unit
    | Ty_var
    | Ty_link of 'w typ
    | Ty_arr of 'w typ * 'w typ
    | Ty_eq of 'w typ * 'w typ
    | Ty_rigid of ('w, ns_rigid) ident

  type 'w term_desc =
    | Te_var of (('w, ns_value) ident, var) result
    | Te_lam : ('w1, 'w2, ns_value) binder * 'w2 term -> 'w1 term_desc
    | Te_app of 'w term * 'w term
    | Te_let : {
        level: ('w, 'wl, ns_level) binder;
        bound: 'wl term;
        binder: ('w, 'wb, ns_value) binder;
        body: 'wb term;
      } -> 'w term_desc
    | Te_new : {
        var: ('w, 'wl, ns_rigid) binder;
        body: 'wl term;
      } -> 'w term_desc
    | Te_use of {
        witness: 'w term;
        witness_types: 'w typ * 'w typ;
        body: 'w term;
      }

  and 'w term = {
    typ: 'w typ;
    desc: 'w term_desc;
  }

end = Syntax

and Namespace : sig
  module Level : World.INDEXED with type 'w t = 'w Syntax.level
  module Value : World.INDEXED with type 'w t = 'w Syntax.typ
  module Rigid : World.INDEXED with type 'w t = ('w Syntax.typ * 'w Syntax.scope) option

  type 'a t =
    | Level : Level.p t
    | Value : Value.p t
    | Rigid : Rigid.p t

  include Witness.ORDERED with type 'a t := 'a t
end = struct
  module Level = World.Indexed0(struct type 'w t = 'w Syntax.level end)
  module Value = World.Indexed0(struct type 'w t = 'w Syntax.typ end)
  module Rigid = World.Indexed0(struct type 'w t = ('w Syntax.typ * 'w Syntax.scope) option end)

  type 'a t =
    | Level : Level.p t
    | Value : Value.p t
    | Rigid : Rigid.p t

  let compare (type a b) (a : a t) (b : b t) : (a, b) Witness.order =
    match a, b with
    | Level , Level -> Eq
    | Value , Value -> Eq
    | Rigid , Rigid -> Eq
    | Level , (Value | Rigid) -> Lt
    | (Rigid | Value), Level -> Gt
    | Rigid , Value -> Gt
    | Value , Rigid -> Lt
end

and Context : Flat.CONTEXT with type 'a namespace = 'a Namespace.t =
  Flat.Make_context(Namespace)

let rec repr (typ : _ Syntax.typ) = match typ.repr with
  | Syntax.Ty_link typ' -> repr typ'
  (*| Syntax.Ty_rigid r ->
    let Unpack (_w', _sub, v) = World.unpack w (Context.get ctx r) in
    begin match v with
      | None -> typ
      | Some (typ', scope) ->
        instance (inner_scope typ.scope scope) typ.level typ'
    end*)
  | _ -> typ

module Env : sig
  type 'w level = ('w, Syntax.ns_level) World.v
  type 'w t
  type ('w, 'a) fresh =
      Fresh : ('w1, 'w2, 'a) Context.binder * 'w2 t -> ('w1, 'a) fresh
  val make : unit -> (World.o, Syntax.ns_level) fresh
  val get : 'w t -> ('w, 'a) Context.ident -> ('w, 'a) World.v
  val find : 'w t -> 'a Namespace.t -> var -> ('w, 'a) Context.ident option
  val bind : 'w t -> 'a Namespace.t -> var -> ('w, 'a) World.v -> ('w, 'a) fresh
  val bind' : 'w t -> 'a Namespace.t -> var -> ('w, 'a) World.v_strong -> ('w, 'a) fresh

  val world : 'w t -> 'w World.t
  val new_var : 'w Syntax.scope -> 'w Syntax.level -> 'w Syntax.typ

  val get_level : 'w t -> 'w Syntax.level

  val enter_level : 'w t -> ('w, Syntax.ns_level) fresh
  val generalize_level : ('w1, 'w2, Syntax.ns_level) Context.binder ->
    unit * ('w2 Syntax.typ -> 'w1 Syntax.typ)

  val escape_typ : ('w1, 'w2, Syntax.ns_value) Context.binder ->
    ('w2 Syntax.typ -> 'w1 Syntax.typ)

  module type FRESH = sig
    type w
    val level : (World.o, w, Syntax.ns_level) Context.binder
    val env : w t
  end
  module Make() : FRESH

  val initial_scope : 'w t -> 'w Syntax.scope
end = struct
  type 'w level = ('w, Syntax.ns_level) World.v

  module Index = struct
    type +'w entry =
        Entry : ('w, 'a) Context.ident -> 'w entry [@@ocaml.unboxed]

    type 'w t = ('w entry, var) Bt2.t

    let empty = Bt2.leaf

    let compare (type a b) (ns: a Namespace.t) var (ns': b Namespace.t) var'
      : (a, b) Witness.order =
      match Namespace.compare ns ns' with
      | Witness.Lt -> Witness.Lt
      | Witness.Gt -> Witness.Gt
      | Witness.Eq -> Witness.order_compare (String.compare var var')

    let find (type a) (ns : a Namespace.t) var =
      let rec aux : 'w t -> ('w, a) Context.ident option = function
        | Bt2.Leaf -> None
        | Bt2.Node (_, l, Entry ident, var', r) ->
          begin match compare ns var ident.namespace var' with
            | Witness.Lt -> aux l
            | Witness.Gt -> aux r
            | Witness.Eq -> Some ident
          end
      in
      aux

    let add (type w a) (ident : (w, a) Context.ident) var =
      let rec aux : w t -> w t = function
        | Bt2.Leaf -> Bt2.node Bt2.leaf (Entry ident) var Bt2.leaf
        | Bt2.Node (_, l, Entry ident', var', r) ->
          begin match compare ident.namespace var ident'.namespace var' with
            | Witness.Lt -> aux l
            | Witness.Gt -> aux r
            | Witness.Eq -> Bt2.node l (Entry ident) var' r
          end
      in
      aux

    let coerce (type w1 w2) (link : (w1, w2) World.link) w =
      let (module Sub) = World.sub link in
      let Refl = Sub.eq in
      (w : w1 t :> w2 t)

  end

  type 'w t = {
    context: 'w Context.env;
    index: 'w Index.t;
    level: World.o Syntax.level;
  }

  type ('w, 'a) fresh =
      Fresh : ('w1, 'w2, 'a) Context.binder * 'w2 t -> ('w1, 'a) fresh

  let make () =
    let level =
      let gensym = ref 0 and world = World.empty and variables = [] in
      {Syntax.level_repr = Syntax.Fresh {gensym; world; variables}}
    in
    let Context.Fresh (binder, context) =
      Context.bind' Context.empty Namespace.Level
        (Namespace.Level.pack World.empty level)
    in
    Fresh (binder, { context; index = Index.empty; level })

  module type FRESH = sig
    type w
    val level : (World.o, w, Syntax.ns_level) Context.binder
    val env : w t
  end

  let pack_fresh
      (type w)
      (level : (World.o, w, Syntax.ns_level) Context.binder)
      (env : w t) : (module FRESH)
    =
    let module M = struct
      type nonrec w = w
      let level = level
      let env = env
    end in
    (module M)

  module Make() : FRESH =
    (val (let Fresh (binder, env) = make () in pack_fresh binder env))

  let get t ident = Context.get t.context ident

  let find t ns var = Index.find ns var t.index

  let world t = Context.world t.context

  let get_level (type w) (t : w t) : w Syntax.level =
    let Witness.Refl = World.unsafe_eq (Context.world t.context) in
    t.level

  let pack_level (type w)
      (w : w World.t) (l : w Syntax.level) : World.o Syntax.level =
    let Witness.Refl = World.unsafe_eq w in l

  let bind t ns var v =
    let Context.Fresh (binder, context) = Context.bind t.context ns v in
    let Context.Binder (link, ident, _) = binder in
    let index = Index.add ident var (Index.coerce link t.index) in
    Fresh (binder, {level = t.level; index; context})

  let bind' t ns var v =
    let Context.Fresh (binder, context) = Context.bind' t.context ns v in
    let Context.Binder (link, ident, _) = binder in
    let index = Index.add ident var (Index.coerce link t.index) in
    Fresh (binder, {level = t.level; index; context})

  let new_var scope level = match level.Syntax.level_repr with
    | Syntax.Generalized _ ->
      failwith "Generating fresh variable in an already generalized level"
    | Syntax.Fresh f ->
      let Syntax.Scope s = scope in
      assert (World.card s.scope <= World.card f.world);
      let id = !(f.gensym) in
      incr f.gensym;
      let ty = {
        Syntax.
        id;
        scope;
        level;
        repr = Ty_var;
      } in
      f.variables <- ty :: f.variables;
      ty

  let new_level world = function
    | { Syntax.level_repr = Syntax.Generalized _ } ->
      failwith "Cannot begin level from generalized level"
    | { Syntax.level_repr = Syntax.Fresh {gensym; _} } ->
      { Syntax.level_repr = Syntax.Fresh {gensym; world; variables = []} }

  let enter_level t =
    let world = Context.world t.context in
    let level = new_level world (get_level t) in
    let Context.Fresh (binder, context) =
      Context.bind' t.context Namespace.Level
        (Namespace.Level.pack world level)
    in
    let Context.Binder (link, _, _) = binder in
    let level = pack_level world level in
    Fresh (binder, { context; index = Index.coerce link t.index; level })

  let escape_typ (type w1 w2)
      (Context.Binder (link, _, _) : (w1, w2, _) Context.binder) =
    let Witness.Refl = World.unsafe_eq (World.source link) in
    let Witness.Refl = World.unsafe_eq (World.target link) in
    (fun (ty : w2 Syntax.typ) ->
       (ty : w1 Syntax.typ))

  let generalize_level (type w1 w2)
      (Context.Binder (link, _, level) as binder : (w1, w2, _) Context.binder) =
    let World.Unpack (w0, _, level) = World.unpack (World.source link) level in
    let level = Namespace.Level.unpack w0 level in
    match level with
    | { Syntax.level_repr = Syntax.Generalized _ } ->
      failwith "Level already generalized"
    | { Syntax.level_repr = Syntax.Fresh f } as level ->
      let generalized =
        List.fold_left (fun gen var ->
            let ty = repr var in
            match ty.repr with
            | Ty_var ->
              if ty.level == level then
                (ty :: gen)
              else (
                begin match ty.level.level_repr with
                  | Syntax.Generalized _ ->
                    failwith "Broken invariant: unification variable \
                              in generalized level"
                  | Syntax.Fresh f' -> f'.variables <- ty :: f'.variables
                end;
                gen
              )
            | _ ->
              gen
          ) [] f.variables
      in
      level.level_repr <- Syntax.Generalized generalized;
      ((), escape_typ binder)

  let initial_scope env =
    Syntax.Scope {scope = World.empty;
                  scope_sub = World.smallest_world (world env)}
end

module Typed = struct
  let inner_scope (Syntax.Scope t1 as s1) (Syntax.Scope t2 as s2) =
    if World.card t1.scope < World.card t2.scope then
      s1
    else
      s2

  let outer_level l1 l2 =
    match l1.Syntax.level_repr, l2.Syntax.level_repr with
    | Fresh f1, Fresh f2 ->
      if (World.card f1.world < World.card f2.world) then
        l1
      else
        l2
    | _ -> assert false

  let coerce_typ (type w1 w2)
      (w1 : w1 World.t)
      (w2 : w2 World.t)
      (_sub : (w1, w2) Witness.sub)
      (typ : w1 Syntax.typ)
      : w2 Syntax.typ
      =
      let Witness.Refl = World.unsafe_eq w1 in
      let Witness.Refl = World.unsafe_eq w2 in
      typ

  let coerce_scope
      (type w1 w2)
      (sub : (w1, w2) Witness.sub)
      (Scope {scope; scope_sub} : w1 Syntax.scope)
      : w2 Syntax.scope
    =
    Scope {scope; scope_sub = Witness.trans_sub scope_sub sub}

  let instance (type w)
      (scope : w Syntax.scope)
      (level : w Syntax.level)
      (typ : w Syntax.typ)
    : w Syntax.typ =
    let module Table = Hashtbl.Make(struct
        type t = w Syntax.typ
        let hash t = t.Syntax.id
        let equal t1 t2 = t1 == t2
      end)
    in
    let table = Table.create 7 in
    let rec aux typ : w Syntax.typ =
      let typ = repr typ in
      match Table.find_opt table typ with
      | Some typ' -> typ'
      | None ->
        let var = Env.new_var (inner_scope typ.scope scope) level in
        Table.add table typ var;
        var.repr <- (match typ.repr with
          | Ty_link _ -> assert false
          | Ty_unit -> Ty_unit
          | Ty_var -> Ty_var
          | Ty_arr (t1, t2) ->
            Ty_arr (aux t1, aux t2)
          | Ty_eq (t1, t2) ->
            Ty_eq (aux t1, aux t2)
          | Ty_rigid r ->
            Ty_rigid r
          );
        var
    in
    aux typ

  let rec expand ctx w (typ : _ Syntax.typ) =
    let typ = repr typ in
    match typ.repr with
    | Ty_rigid r ->
      let Unpack (w', sub, v) = World.unpack w (Context.get ctx r) in
      let eqn = Namespace.Rigid.unpack w' v in
      begin match eqn with
        | None -> typ
        | Some (typ', scope) ->
          expand ctx w
            (instance (inner_scope typ.scope (coerce_scope sub scope)) typ.level
               (coerce_typ w' w sub typ'))
      end
    | _ -> typ

  let rec unify ctx w mode t1 t2 =
    let t1 = expand ctx w t1 and t2 = expand ctx w t2 in
    if t1 != t2 then (
      let r1 = t1.repr and r2 = t2.repr in
      let scope = inner_scope t1.scope t2.scope in
      let level = outer_level t1.level t2.level in
      t2.scope <- scope;
      t2.level <- level;
      t1.repr <- Ty_link t2;
      match r1, r2 with
      | Ty_var, _ -> ()
      | _, Ty_var ->
        t1.repr <- r1;
        t1.scope <- scope;
        t1.level <- level;
        t2.repr <- Ty_link t1
      | Ty_rigid r1, Ty_rigid r2 when r1 = r2 ->
        ()
      | Ty_rigid _r, _ ->
        ()
        (*begin match mode with


          end*)
        (* Next step:
           - reify, turn unification variables into rigid variables *)
      | _, Ty_rigid _r ->
        ()
      | Ty_unit, Ty_unit -> ()
      | Ty_arr (t11, t12), Ty_arr (t21, t22)
      | Ty_eq (t11, t12), Ty_eq (t21, t22) ->
        unify ctx w mode t11 t21;
        unify ctx w mode t12 t22;
      | Ty_link _, _ | _, Ty_link _ ->
        assert false
      | _ ->
        failwith "Unification failure"
    )

  let mk typ desc = { Syntax. typ; desc }

  let begin_level world = function
    | { Syntax.level_repr = Syntax.Generalized _ } ->
      failwith "Cannot begin level from generalized level"
    | { Syntax.level_repr = Syntax.Fresh f } ->
      let level_repr = Syntax.Fresh {
          gensym = f.gensym;
          world;
          variables = []
        } in
      { Syntax. level_repr }

  let rec reconstruct : type w. w Env.t -> Source.lam -> w Syntax.term =
    fun env -> function
    | Source.Var name ->
      let ident, typ = match Env.find env Namespace.Value name with
        | Some ident ->
          let Unpack (w', sub, typ) = World.unpack (Env.world env) (Env.get env ident) in
          let typ = Namespace.Value.unpack w' typ in
          let typ = coerce_typ w' (Env.world env) sub typ in
          (Ok ident, instance (Env.initial_scope env) (Env.get_level env) typ)
        | None ->
          failwith "Unbound identifier"
          (*prerr_endline ("Unbound variable " ^ name);
            (Error name, Env.new_var env)*)
      in
      mk typ (Syntax.Te_var ident)
    | Source.Lam (var, lam) ->
      let tvar = Env.new_var (Env.initial_scope env) (Env.get_level env) in
      let Env.Fresh (binder, env) =
        Env.bind' env Namespace.Value var
          (Namespace.Value.pack (Env.world env) tvar)
      in
      let lam = reconstruct env lam in
      let typ = Env.escape_typ binder lam.typ in
      mk (Syntax.Ty_arr (tvar, typ)) (Syntax.Te_lam (binder, lam))
    | Source.App (lm1, lm2) ->
      let lm1 = reconstruct env lm1 in
      let lm2 = reconstruct env lm2 in
      let lhs = Env.new_var env in
      let rhs = Env.new_var env in
      unify lm1.typ (Syntax.Ty_arr (lhs, rhs));
      unify lm2.typ lhs;
      mk rhs (Syntax.Te_app (lm1, lm2))
    | Source.Let (var, lm1, lm2) ->
      let Env.Fresh (level, env') = Env.enter_level env in
      let bound = reconstruct env' lm1 in
      let (), commute = Env.generalize_level level in
      let Env.Fresh (binder, env') =
        Env.bind' env Namespace.Value var
          (Namespace.Value.pack (Env.world env) (commute bound.typ))
      in
      let body = reconstruct env' lm2 in
      mk (Env.escape_typ binder body.typ)
        (Syntax.Te_let {level; bound; binder; body})

  let print_tvar ppf tvar =
    match repr (Syntax.Ty_var tvar) with
    | Syntax.Ty_arr _ -> assert false
    | Syntax.Ty_var tvar -> Format.fprintf ppf "#%d" tvar.Syntax.id

  let print_tvars ppf = function
    | [] -> ()
    | x :: xs ->
      Format.fprintf ppf "@ @[<hov>%a%a@]."
        print_tvar x
        (fun ppf xs ->
           List.iter (fun x -> Format.fprintf ppf "@ %a" print_tvar x) xs)
        xs

  let print_level ppf (Context.Binder (link, _id, level)) =
    let World.Unpack (w0, _w0w1, level)
      = World.unpack (World.source link) level in
    let level = Namespace.Level.unpack w0 level in
    match level.level_repr with
    | Syntax.Fresh _ ->
      Format.fprintf ppf "<non-generalized level>"
    | Syntax.Generalized tvars ->
      print_tvars ppf tvars

  let rec print_term
    : type w. Format.formatter -> w Syntax.term -> unit
    = fun ppf {Syntax. typ; desc} ->
      Format.fprintf ppf "@[(@[%a@]@ @[:@ %a@])@]"
        print_term_desc desc print_typ typ

  and print_term_desc
    : type w. Format.formatter -> w Syntax.term_desc -> unit
    = fun ppf -> function
      | Syntax.Te_var (Ok {Context.Ident. namespace = _; stamp}) ->
        Format.fprintf ppf "@@%d" (stamp :> int)
      | Syntax.Te_var (Error name) -> Format.fprintf ppf "%s@@unbound" name
      | Syntax.Te_lam (
          Context.Binder (_, {Context.Ident. namespace = _; stamp}, _),
          body
        ) ->
        Format.fprintf ppf
          "@[\\@@%d@ -> %a@]" (stamp :> int) print_term body
      | Syntax.Te_app (tlm1, tlm2) ->
        Format.fprintf ppf "@[<2>%a@ %a@]"
          print_term tlm1 print_term tlm2
      | Syntax.Te_let {
          level; bound; body;
          binder = Context.Binder (_, {Context.Ident. namespace = _; stamp}, _);
        } ->
        Format.fprintf ppf "@[@[<2>let @@%d@ =%a@ %a@]@ in@;%a@]"
          (stamp :> int)
          print_level level
          print_term bound print_term body

  and print_typ
    : type w. Format.formatter -> w Syntax.typ -> unit
    = fun ppf typ -> match repr typ with
      | Syntax.Ty_arr (lhs, rhs) ->
        Format.fprintf ppf "%a@ ->@ %a" print_typ_lhs lhs print_typ rhs
      | Syntax.Ty_var tvar -> print_tvar ppf tvar

  and print_typ_lhs
    : type w. Format.formatter -> w Syntax.typ -> unit
    = fun ppf typ -> match repr typ with
      | Syntax.Ty_arr _ as typ -> Format.fprintf ppf "@[(%a)@]" print_typ typ
      | Syntax.Ty_var tvar -> print_tvar ppf tvar
end

let () =
  let module Initial = Env.Make() in
  let tast =
    Typed.reconstruct Initial.env
      Source.Infix.(let- app = "app", "f" @-> "x" @-> !"f" % !"x" in app)
  in
  Format.printf "%a\n%!" Typed.print_term tast
