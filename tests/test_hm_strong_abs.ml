type var = string

module Source = struct
  type term =
    | Var of var
    | Lam of var * term
    | App of term * term
    | Let of var * term * term

  module Infix = struct
    let (!) x = Var x
    let (let-) (name, value) f = Let (name, value, f (Var name))
    let (%) x y = App (x, y)
    let (@->) name body = Lam (name, body)
  end
end

module SemAst : sig
  type ns_level
  type ns_value

  type 'a namespace =
    | Level : ns_level namespace
    | Value : ns_value namespace

  module Context : Flat.NEW_CONTEXT with type 'a namespace = 'a namespace

  type ('w, 'ns) ident = ('w, 'ns) Context.ident
  type ('w1, 'w2, 'ns) binder = ('w1, 'w2, 'ns) Context.binder

  type 'w level
  type 'w ty_var

  type 'w typ = private
    | Ty_var of 'w ty_var
    | Ty_arr of 'w typ * 'w typ
  val repr : 'w typ -> 'w typ

  type 'w term = private {
    typ: 'w typ;
    desc: 'w term_desc;
  }

  and 'w term_desc =
    | Te_var of (('w, ns_value) ident, var) result
    | Te_lam : ('w1, 'w2, ns_value) binder * 'w2 term -> 'w1 term_desc
    | Te_app of 'w term * 'w term
    | Te_let : {
        level: ('w, 'wl, ns_level) binder;
        bound: 'wl term;
        binder: ('w, 'wb, ns_value) binder;
        body: 'wb term;
      } -> 'w term_desc

  module Namespace : sig
    module Level : World.INDEXED with type 'w t = 'w level and type p = ns_level
    module Value : World.INDEXED with type 'w t = 'w typ and type p = ns_value

    type 'a t = 'a namespace =
      | Level : Level.p t
      | Value : Value.p t

    include World.ORDERED with type 'a t := 'a t
  end

  module Env : sig
    type 'w level = ('w, ns_level) World.v
    type 'w t
    type ('w, 'a) fresh =
        Fresh : ('w1, 'w2, 'a) Context.binder * 'w2 t -> ('w1, 'a) fresh
    val make : unit -> (World.o, ns_level) fresh
    val get : 'w t -> ('w, 'a) Context.ident -> ('w, 'a) World.v
    val find : 'w t -> 'a Namespace.t -> var -> ('w, 'a) Context.ident option
    val bind : 'w t -> 'a Namespace.t -> var -> ('w, 'a) World.v -> ('w, 'a) fresh
    val bind' : 'w t -> 'a Namespace.t -> var -> ('w, 'a) World.v_strong -> ('w, 'a) fresh

    val world : 'w t -> 'w World.t
    val new_var : 'w t -> 'w typ

    val enter_level : 'w t -> ('w, ns_level) fresh
    val generalize_level : ('w1, 'w2, ns_level) Context.binder ->
      unit * ('w2 typ -> 'w1 typ)

    val commute_typ : ('w1, 'w2, ns_value) Context.binder ->
      ('w2 typ -> 'w1 typ)

    module type FRESH = sig
      type w
      val level : (World.o, w, ns_level) Context.binder
      val env : w t
    end
    module Make() : FRESH
  end

  module Types :
  sig
    val unify : 'w typ -> 'w typ -> unit
    val instance : 'w Env.t -> ('w, ns_value) World.v -> 'w typ
    val arrow : 'w typ -> 'w typ -> 'w typ
  end

  module Terms :
  sig
    val mk : 'w typ -> 'w term_desc -> 'w term
  end

  module Print :
  sig
    val print_tvar : Format.formatter -> 'a ty_var -> unit
    val print_tvars : Format.formatter -> 'a ty_var list -> unit
    val print_level : Format.formatter -> ('a, 'b, ns_level) binder -> unit
    val print_term : Format.formatter -> 'w term -> unit
    val print_term_desc : Format.formatter -> 'w term_desc -> unit
    val print_typ : Format.formatter -> 'w typ -> unit
    val print_typ_lhs : Format.formatter -> 'w typ -> unit
  end

end = struct
  module rec Syntax : sig
    type ('w, 'ns) ident = ('w, 'ns) Context.ident
    type ('w1, 'w2, 'ns) binder = ('w1, 'w2, 'ns) Context.binder

    type ns_level = Namespace.Level.p
    type ns_value = Namespace.Value.p

    type 'w level = { mutable level_repr : 'w level_repr; }
    and 'w level_repr =
      | Fresh of {
          gensym: int ref;
          world: 'w World.t;
          mutable variables : 'w ty_var list;
        }
      | Generalized of 'w ty_var list

    and 'w ty_var = {
      mutable id: int;
      mutable level: 'w level;
      mutable repr: 'w typ;
    }

    and 'w typ =
      | Ty_var of 'w ty_var
      | Ty_arr of 'w typ * 'w typ

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

    and 'w term = {
      typ: 'w typ;
      desc: 'w term_desc;
    }

  end = Syntax

  and Namespace : sig
    module Level : World.INDEXED with type 'w t = 'w Syntax.level
    module Value : World.INDEXED with type 'w t = 'w Syntax.typ

    type 'a t =
      | Level : Level.p t
      | Value : Value.p t

    include World.ORDERED with type 'a t := 'a t
  end = struct
    module Level = World.Indexed0(struct type 'a t = 'a Syntax.level end)
    module Value = World.Indexed0(struct type 'a t = 'a Syntax.typ end)
    type 'a t =
      | Level : Level.p t
      | Value : Value.p t

    let compare (type a b) (a : a t) (b : b t) : (a, b) World.order =
      match a, b with
      | Level , Level -> Eq
      | Value , Value -> Eq
      | Level , Value -> Lt
      | Value , Level -> Gt
  end

  and Context : Flat.NEW_CONTEXT with type 'a namespace = 'a Namespace.t =
    Flat.Make_context(Namespace)

  include Syntax

  module Level = Namespace.Level
  module Value = Namespace.Value
  type 'a namespace = 'a Namespace.t =
      | Level : Level.p namespace
      | Value : Value.p namespace

  let rec repr typ = match typ with
    | Ty_arr _ -> typ
    | Ty_var t when t.repr == typ -> typ
    | Ty_var t ->
      let typ = repr t.repr in
      if typ != t.repr then (
        t.repr <- typ;
        match typ with
        | Syntax.Ty_var t' ->
          begin match t'.level.level_repr, t.level.level_repr with
            | r1, r2 when r1 == r2 -> ()
            | Syntax.Fresh f1, Syntax.Fresh f2 ->
              assert (World.card f1.world < World.card f2.world)
            | _ -> failwith "Broken invariant: unification variable \
                             crossing generalized levels"
          end;
          t.level <- t'.level
        | Syntax.Ty_arr _ -> ()
      );
      typ

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
    val new_var : 'w t -> 'w Syntax.typ

    val enter_level : 'w t -> ('w, Syntax.ns_level) fresh
    val generalize_level : ('w1, 'w2, Syntax.ns_level) Context.binder ->
      unit * ('w2 Syntax.typ -> 'w1 Syntax.typ)

    val commute_typ : ('w1, 'w2, Syntax.ns_value) Context.binder ->
      ('w2 Syntax.typ -> 'w1 Syntax.typ)

    module type FRESH = sig
      type w
      val level : (World.o, w, Syntax.ns_level) Context.binder
      val env : w t
    end
    module Make() : FRESH
  end = struct
    type 'w level = ('w, Syntax.ns_level) World.v

    module Index = struct
      type +'w entry =
          Entry : ('w, 'a) Context.ident -> 'w entry [@@ocaml.unboxed]

      type 'w t = ('w entry, var) Bt2.t

      let empty = Bt2.leaf

      let compare (type a b) (ns: a Namespace.t) var (ns': b Namespace.t) var'
        : (a, b) Type.order =
        match Namespace.compare ns ns' with
        | Type.Lt -> Type.Lt
        | Type.Gt -> Type.Gt
        | Type.Eq -> Type.order_compare (String.compare var var')

      let find (type a) (ns : a Namespace.t) var =
        let rec aux : 'w t -> ('w, a) Context.ident option = function
          | Bt2.Leaf -> None
          | Bt2.Node (_, l, Entry ident, var', r) ->
            begin match compare ns var ident.namespace var' with
              | Type.Lt -> aux l
              | Type.Gt -> aux r
              | Type.Eq -> Some ident
            end
        in
        aux

      let add (type w a) (ident : (w, a) Context.ident) var =
        let rec aux : w t -> w t = function
          | Bt2.Leaf -> Bt2.node Bt2.leaf (Entry ident) var Bt2.leaf
          | Bt2.Node (_, l, Entry ident', var', r) ->
            begin match compare ident.namespace var ident'.namespace var' with
              | Type.Lt -> aux l
              | Type.Gt -> aux r
              | Type.Eq -> Bt2.node l (Entry ident) var' r
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
      let World.Refl = World.unsafe_eq (Context.world t.context) in
      t.level

    let pack_level (type w)
        (w : w World.t) (l : w Syntax.level) : World.o Syntax.level =
      let World.Refl = World.unsafe_eq w in l

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

    let new_var t = match get_level t with
      | { Syntax.level_repr = Syntax.Generalized _ } ->
        failwith "Generating fresh variable in an already generalized level"
      | { Syntax.level_repr = Syntax.Fresh f } as level ->
        let id = !(f.gensym) in
        incr f.gensym;
        let rec tvar = { Syntax. id; repr; level }
        and repr = Syntax.Ty_var tvar in
        f.variables <- tvar :: f.variables;
        repr

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

    let commute_typ (type w1 w2)
        (Context.Binder (link, _, _) : (w1, w2, _) Context.binder) =
      let World.Refl = World.unsafe_eq (World.source link) in
      let World.Refl = World.unsafe_eq (World.target link) in
      (fun (ty : w2 Syntax.typ) -> (ty : w1 Syntax.typ))

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
              match repr var.Syntax.repr with
              | Syntax.Ty_var var' when var' == var ->
                if var'.level == level then
                  (var' :: gen)
                else (
                  begin match var'.level.level_repr with
                    | Syntax.Generalized _ ->
                      failwith "Broken invariant: unification variable \
                                in generalized level"
                    | Syntax.Fresh f' -> f'.variables <- var' :: f'.variables
                  end;
                  gen
                )
              | Syntax.Ty_arr _ | Syntax.Ty_var _ -> gen
            ) [] f.variables
        in
        level.level_repr <- Syntax.Generalized generalized;
        ((), commute_typ binder)
  end

  module Types = struct
    let rec unify t1 t2 =
      if t1 != t2 then match repr t1, repr t2 with
        | t1, t2 when t1 == t2 -> ()
        | Syntax.Ty_arr (t11, t12), Syntax.Ty_arr (t21, t22) ->
          unify t11 t21;
          unify t12 t22;
        | (Syntax.Ty_var v, (Syntax.Ty_arr _ as t'))
        | ((Syntax.Ty_arr _ as t'), Syntax.Ty_var v) ->
          begin match v.level.level_repr with
            | Syntax.Generalized _ ->
              failwith "Cannot unify generalized variable"
            | Syntax.Fresh _ -> ()
          end;
          v.repr <- t'
        | (Syntax.Ty_var v1 as t1), (Syntax.Ty_var v2 as t2) ->
          begin match v1.level.level_repr, v2.level.level_repr with
            | (Syntax.Generalized _, _) | (_, Syntax.Generalized _) ->
              failwith "Cannot unify generalized variable"
            | Syntax.Fresh f1, Syntax.Fresh f2 ->
              if (World.card f1.world < World.card f2.world) then (
                v2.repr <- t1;
                v2.level <- v1.level
              ) else (
                v1.repr <- t2;
                v1.level <- v2.level
              )
          end

    let cast (type w1 w2) (w1: w1 World.t) (w2: w2 World.t) (t: w1 Syntax.typ)
      : w2 Syntax.typ =
      let World.Refl = World.unsafe_eq w1 in
      let World.Refl = World.unsafe_eq w2 in
      t

    let instance (type w2)
        (env : w2 Env.t) (typ : (w2, Syntax.ns_value) World.v)
      : w2 Syntax.typ =
      let vars = Hashtbl.create 7 in
      let w2 = Env.world env in
      let World.Unpack (w0, _w0w1, v) = World.unpack w2 typ in
      let typ = Namespace.Value.unpack w0 v in
      let rec aux : type w1. w1 Syntax.typ -> w2 Syntax.typ =
        fun typ -> match repr typ with
          | Syntax.Ty_arr (t1, t2) -> Syntax.Ty_arr (aux t1, aux t2)
          | Syntax.Ty_var var as typ ->
            begin match var.level.level_repr with
              | Syntax.Fresh f ->
                (* variable is bound in a lower level, it is safe to upcast *)
                cast f.world w2 typ
              | Syntax.Generalized _ ->
                begin match Hashtbl.find vars var.id with
                  | var -> var
                  | exception Not_found ->
                    let var' = Env.new_var env in
                    Hashtbl.replace vars var.id var';
                    var'
                end
            end
      in
      aux typ

    let arrow t1 t2 = Ty_arr (t1, t2)
  end

  module Terms =
  struct
    let mk typ desc = { Syntax. typ; desc }
  end

  module Print =
  struct
    let print_tvar ppf tvar =
      match repr (Ty_var tvar) with
      | Ty_arr _ -> assert false
      | Ty_var tvar -> Format.fprintf ppf "#%d" tvar.id

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
      | Fresh _ ->
        Format.fprintf ppf "<non-generalized level>"
      | Generalized tvars ->
        print_tvars ppf tvars

    let rec print_term
      : type w. Format.formatter -> w term -> unit
      = fun ppf { typ; desc} ->
        Format.fprintf ppf "@[(@[%a@]@ @[:@ %a@])@]"
          print_term_desc desc print_typ typ

    and print_term_desc
      : type w. Format.formatter -> w term_desc -> unit
      = fun ppf -> function
        | Te_var (Ok {Context.Ident. namespace = _; stamp}) ->
          Format.fprintf ppf "@@%d" (stamp :> int)
        | Te_var (Error name) -> Format.fprintf ppf "%s@@unbound" name
        | Te_lam (
            Context.Binder (_, {Context.Ident. namespace = _; stamp}, _),
            body
          ) ->
          Format.fprintf ppf
            "@[\\@@%d@ -> %a@]" (stamp :> int) print_term body
        | Te_app (tlm1, tlm2) ->
          Format.fprintf ppf "@[<2>%a@ %a@]"
            print_term tlm1 print_term tlm2
        | Te_let {
            level; bound; body;
            binder = Context.Binder (_, {Context.Ident. namespace = _; stamp}, _);
          } ->
          Format.fprintf ppf "@[@[<2>let @@%d@ =%a@ %a@]@ in@;%a@]"
            (stamp :> int)
            print_level level
            print_term bound print_term body

    and print_typ
      : type w. Format.formatter -> w typ -> unit
      = fun ppf typ -> match repr typ with
        | Ty_arr (lhs, rhs) ->
          Format.fprintf ppf "%a@ ->@ %a" print_typ_lhs lhs print_typ rhs
        | Ty_var tvar -> print_tvar ppf tvar

    and print_typ_lhs
      : type w. Format.formatter -> w typ -> unit
      = fun ppf typ -> match repr typ with
        | Ty_arr _ as typ -> Format.fprintf ppf "@[(%a)@]" print_typ typ
        | Ty_var tvar -> print_tvar ppf tvar
  end
end

open SemAst

let rec reconstruct : type w. w Env.t -> Source.term -> w SemAst.term =
  fun env -> function
    | Source.Var name ->
      let ident, typ = match Env.find env Namespace.Value name with
        | Some ident ->
          let typ = Env.get env ident in
          (Ok ident, Types.instance env typ)
        | None ->
          prerr_endline ("Unbound variable " ^ name);
          (Error name, Env.new_var env)
      in
      Terms.mk typ (SemAst.Te_var ident)
    | Source.Lam (var, lam) ->
      let tvar = Env.new_var env in
      let Env.Fresh (binder, env) =
        Env.bind' env Namespace.Value var
          (Namespace.Value.pack (Env.world env) tvar)
      in
      let lam = reconstruct env lam in
      let typ = Env.commute_typ binder lam.typ in
      Terms.mk (Types.arrow tvar typ) (SemAst.Te_lam (binder, lam))
    | Source.App (lm1, lm2) ->
      let lm1 = reconstruct env lm1 in
      let lm2 = reconstruct env lm2 in
      let lhs = Env.new_var env in
      let rhs = Env.new_var env in
      Types.unify lm1.typ (Types.arrow lhs rhs);
      Types.unify lm2.typ lhs;
      Terms.mk rhs (SemAst.Te_app (lm1, lm2))
    | Source.Let (var, lm1, lm2) ->
      let Env.Fresh (level, env') = Env.enter_level env in
      let bound = reconstruct env' lm1 in
      let (), commute = Env.generalize_level level in
      let Env.Fresh (binder, env') =
        Env.bind' env Namespace.Value var
          (Namespace.Value.pack (Env.world env) (commute bound.typ))
      in
      let body = reconstruct env' lm2 in
      Terms.mk (Env.commute_typ binder body.typ)
        (SemAst.Te_let {level; bound; binder; body})

let () =
  let module Initial = Env.Make() in
  let tast =
    reconstruct Initial.env
      Source.Infix.(let- app = "app", "f" @-> "x" @-> !"f" % !"x" in app)
  in
  Format.printf "%a\n%!" Print.print_term tast
