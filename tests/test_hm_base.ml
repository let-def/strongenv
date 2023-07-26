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
    | TVar of ty_var

  and ty_var = { id: int; mutable repr: typ; mutable level: level }

  and level = { mutable level_repr : level_repr; }

  and level_repr =
    | Fresh of {
        gensym: int ref;
        depth: int;
        mutable variables : ty_var list;
      }
    | Generalized of ty_var list

  type tlam = {
    typ: typ;
    lam: lam;
  }
  and lam =
    | Var of string
    | Lam of string * tlam
    | App of tlam * tlam
    | Let of string * ty_var list * tlam * tlam

  let is_fresh level = match level.level_repr with
    | Fresh _ -> true
    | Generalized _ -> false

  let is_generalized level = match level.level_repr with
    | Fresh _ -> false
    | Generalized _ -> true

  let rec repr typ = match typ with
    | TArrow _ -> typ
    | TVar t when t.repr == typ -> typ
    | TVar t ->
      let typ = repr t.repr in
      if typ != t.repr then (
        t.repr <- typ;
        match typ with
        | TVar t' ->
          begin match t.level.level_repr, t'.level.level_repr with
            | Fresh t1, Fresh t2 ->
              assert (t2.depth <= t1.depth)
            | Generalized _, Generalized _ -> ()
            | _ -> assert false
          end;
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
        begin match v1.level.level_repr, v2.level.level_repr with
          | Generalized _, _ | _, Generalized _ -> assert false
          | Fresh l1, Fresh l2 ->
            if l1.depth < l2.depth then (
              v2.repr <- t1;
              v2.level <- v1.level
            ) else (
              v1.repr <- t2;
              v1.level <- v2.level
            )
        end

  let mk typ lam = { typ; lam }

  let first_level () =
    {level_repr = Fresh { gensym = ref 0; depth = 0; variables = [] }}

  let new_var level =
    match level.level_repr with
    | Generalized _ -> assert false
    | Fresh l ->
      let id = !(l.gensym) in
      incr l.gensym;
      let rec tvar = { id; repr; level } and repr = TVar tvar in
      l.variables <- tvar :: l.variables;
      repr

  let begin_level parent =
    match parent.level_repr with
    | Generalized _ -> assert false
    | Fresh {gensym; depth; _} ->
      {level_repr = Fresh { gensym; depth = depth + 1; variables = [] }}

  let end_level level =
    match level.level_repr with
    | Generalized _ -> assert false
    | Fresh l ->
      let generalized =
        List.fold_left (fun gen var ->
            match repr var.repr with
            | TVar var' when var' == var ->
              if var.level == level then
                (var :: gen)
              else
                begin match var.level.level_repr with
                  | Generalized _ -> assert false
                  | Fresh l' ->
                    l'.variables <- var :: l'.variables;
                    gen
                end
            | TArrow _ | TVar _ -> gen
          ) [] l.variables
      in
      level.level_repr <- Generalized generalized;
      generalized

  let instance level typ =
    let vars = Hashtbl.create 7 in
    let rec aux typ = match repr typ with
      | TArrow (t1, t2) -> TArrow (aux t1, aux t2)
      | TVar var when is_generalized var.level ->
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

let () =
  let level = Typed.first_level () in
  let tast =
    Typed.reconstruct level []
      Source.Infix.(let- app = "app", "f" @-> "x" @-> !"f" % !"x" in app)
  in
  Format.printf "%a\n%!" Typed.print_tlam tast
