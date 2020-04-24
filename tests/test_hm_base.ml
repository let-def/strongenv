type var = string

module Source = struct

  type lam =
    | Var of var
    | Lam of var * lam
    | App of lam * lam
    | Let of var * lam * lam

  module Infix = struct
    let (!) x = Var x
    let (let-) (name, value) f = Let (name, value, f (Var name))
    let (%) x y = App (x, y)
    let (@->) name body = Lam (name, body)
  end
end

module Typed = struct
  type typ =
    | TArrow of typ * typ
    | TVar of tvar

  and tvar = { id: int; mutable repr: typ; mutable level: int }

  type tlam = {
    typ: typ;
    lam: lam;
  }
  and lam =
    | Var of string
    | Lam of string * tlam
    | App of tlam * tlam
    | Let of string * tvar list * tlam * tlam

  let poly = max_int

  let rec repr typ = match typ with
    | TArrow _ -> typ
    | TVar t when t.repr == typ -> typ
    | TVar t ->
      let typ = repr t.repr in
      if typ != t.repr then (
        t.repr <- typ;
        match typ with
        | TVar t' ->
          assert (t'.level <= t.level && t.level < poly);
          t.level <- t'.level
        | TArrow _ -> ()
      );
      typ

  let rec unify t1 t2 =
    if t1 != t2 then match repr t1, repr t2 with
      | t1, t2 when t1 == t2 -> ()
      | TArrow (t11, t12), TArrow (t21, t22) ->
        unify t11 t21;
        unify t12 t22;
      | (TVar v, (TArrow _ as t')) | ((TArrow _ as t'), TVar v) ->
        v.repr <- t'
      | (TVar v1 as t1), (TVar v2 as t2) ->
        if v1.level < v2.level then (
          assert (v2.level < poly);
          v2.repr <- t1;
          v2.level <- v1.level
        ) else (
          assert (v1.level < poly);
          v1.repr <- t2;
          v1.level <- v2.level
        )

  type level = {
    gensym: int ref;
    level: int;
    mutable variables: tvar list;
    parent: level;
  }

  let mk typ lam = { typ; lam }

  let first_level () =
    let rec self =
      { gensym = ref 0; level = 0; variables = []; parent = self }
    in
    self

  let new_var level =
    let id = !(level.gensym) in
    incr level.gensym;
    let rec tvar = { id; repr; level = level.level } and repr = TVar tvar in
    level.variables <- tvar :: level.variables;
    repr

  let begin_level parent =
    let gensym = parent.gensym in
    let level = parent.level + 1 in
    let variables = [] in
    { gensym; level; variables; parent }

  let end_level { level; variables; parent; gensym = _ } =
    List.fold_left (fun gen var ->
        match repr var.repr with
        | TVar var' when var' == var ->
          if var'.level < level then (
            parent.variables <- var' :: parent.variables;
            gen
          ) else (
            var'.level <- poly;
            (var' :: gen)
          )
        | TArrow _ | TVar _ -> gen
      ) [] variables

  let instance level typ =
    let vars = Hashtbl.create 7 in
    let rec aux typ = match repr typ with
      | TArrow (t1, t2) -> TArrow (aux t1, aux t2)
      | TVar var when var.level = poly ->
        begin match Hashtbl.find vars var.id with
        | var -> var
        | exception Not_found ->
          let var' = new_var level in
          Hashtbl.replace vars var.id var';
          var'
        end
      | TVar _ as ty -> ty
    in
    aux typ

  let rec reconstruct level ctx = function
    | Source.Var (var) ->
      let typ = match List.assoc var ctx with
        | typ -> instance level typ
        | exception Not_found ->
          prerr_endline ("Unbound variable " ^ var);
          new_var level
      in
      mk typ (Var var)
    | Source.Lam (var, lam) ->
      let tvar = new_var level in
      let lam = reconstruct level ((var, tvar) :: ctx) lam in
      mk (TArrow (tvar, lam.typ)) (Lam (var, lam))
    | Source.App (lm1, lm2) ->
      let lm1 = reconstruct level ctx lm1 in
      let lm2 = reconstruct level ctx lm2 in
      let lhs = new_var level in
      let rhs = new_var level in
      unify lm1.typ (TArrow (lhs, rhs));
      unify lm2.typ lhs;
      mk rhs (App (lm1, lm2))
    | Source.Let (var, lm1, lm2) ->
      let level' = begin_level level in
      let lm1 = reconstruct level' ctx lm1 in
      let tvars = end_level level' in
      let lm2 = reconstruct level ((var, lm1.typ) :: ctx) lm2 in
      mk lm2.typ (Let (var, tvars, lm1, lm2))

  let print_tvar ppf tvar =
    Format.fprintf ppf "#%d" tvar.id

  let print_tvars ppf = function
    | [] -> ()
    | x :: xs ->
      Format.fprintf ppf "@ @[<hov>%a%a@]."
        print_tvar x
        (fun ppf xs ->
           List.iter (fun x -> Format.fprintf ppf "@ %a" print_tvar x) xs)
        xs

  let rec print_tlam ppf {typ; lam} =
    Format.fprintf ppf "@[(@[%a@]@ @[:@ %a@])@]"
      print_lam lam print_typ typ

  and print_lam ppf = function
    | Var var -> Format.fprintf ppf "%s" var
    | Lam (var, tlam) -> Format.fprintf ppf "@[\\%s@ -> %a@]" var print_tlam tlam
    | App (tlm1, tlm2) ->
      Format.fprintf ppf "@[<2>%a@ %a@]"
        print_tlam tlm1 print_tlam tlm2
    | Let (var, tvars, lhs, rhs) ->
      Format.fprintf ppf "@[@[<2>let %s@ =%a@ %a@]@ in@;%a@]"
        var print_tvars tvars print_tlam lhs print_tlam rhs

  and print_typ ppf typ = match repr typ with
    | TArrow (lhs, rhs) ->
      Format.fprintf ppf "%a@ ->@ %a" print_typ_lhs lhs print_typ rhs
    | TVar tvar -> print_tvar ppf tvar

  and print_typ_lhs ppf typ = match repr typ with
    | TArrow _ as typ -> Format.fprintf ppf "@[(%a)@]" print_typ typ
    | TVar tvar -> print_tvar ppf tvar
end
