open Z3
open Z3aux
open Language

let rec collapse_forall prop =
  match prop with
  | Forall { qv; body } ->
      let vars, body = collapse_forall body in
      (qv :: vars, body)
  | _ -> ([], prop)

let rec collapse_exist prop =
  match prop with
  | Exists { qv; body } ->
      let vars, body = collapse_exist body in
      (qv :: vars, body)
  | _ -> ([], prop)

let to_z3 ctx prop =
  let rec aux prop =
    match prop with
    | Implies (p1, p2) -> Boolean.mk_implies ctx (aux p1) (aux p2)
    | Ite (p1, p2, p3) -> Boolean.mk_ite ctx (aux p1) (aux p2) (aux p3)
    | Not p -> Boolean.mk_not ctx (aux p)
    | And ps -> Boolean.mk_and ctx (List.map aux ps)
    | Or ps -> Boolean.mk_or ctx (List.map aux ps)
    | Iff (p1, p2) -> Boolean.mk_iff ctx (aux p1) (aux p2)
    | Forall _ ->
        let qvs, body = collapse_forall prop in
        let qv_expr_list =
          List.map (fun { x; ty } -> tpedvar_to_z3 ctx (ty, x)) qvs
        in
        make_forall ctx qv_expr_list (aux body)
    | Exists _ ->
        let qvs, body = collapse_exist prop in
        let qv_expr_list =
          List.map (fun { x; ty } -> tpedvar_to_z3 ctx (ty, x)) qvs
        in
        make_exists ctx qv_expr_list (aux body)
    | Lit lit -> Litencoding.typed_lit_to_z3 ctx lit
  in
  aux prop
