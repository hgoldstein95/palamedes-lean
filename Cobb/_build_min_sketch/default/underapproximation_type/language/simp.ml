(** The code is specified for exists in the inferred type *)

open Language
open FrontendTyped

let peval_lit lit =
  match lit.x with
  | AAppOp (op, [ a; b ]) when String.equal "==" op.x ->
      if eq_lit Nt.eq a.x b.x then (AC (B true)) #: lit.ty else lit
  | _ -> lit

let match_var_eq_typed_lit x lit =
  match lit.x with
  | AAppOp (op, [ a; b ]) when String.equal "==" op.x ->
      if eq_lit Nt.eq x a.x then Some b.x
      else if eq_lit Nt.eq x b.x then Some a.x
      else None
  | _ -> None

let match_var_eq_prop x prop =
  let rec aux prop =
    match prop with
    | Lit lit -> match_var_eq_typed_lit x lit
    | And props -> (
        match List.filter_map aux props with [] -> None | lit :: _ -> Some lit)
    | _ -> None
  in
  aux prop

let rec peval_prop prop =
  match prop with
  | Lit lit -> Lit (peval_lit lit)
  | Implies (p1, p2) -> Implies (peval_prop p1, peval_prop p2)
  | Iff (p1, p2) -> Iff (peval_prop p1, peval_prop p2)
  | Ite (p1, p2, p3) -> Ite (peval_prop p1, peval_prop p2, peval_prop p3)
  | And ps -> smart_and (List.map peval_prop ps)
  | Or ps -> smart_or (List.map peval_prop ps)
  | Not p -> Not (peval_prop p)
  | Exists { qv; body } -> (
      match match_var_eq_prop (AVar qv) body with
      | None -> Exists { qv; body = peval_prop body }
      | Some lit -> peval_prop @@ subst_prop_instance qv.x lit body)
  | Forall { qv; body } -> Forall { qv; body = peval_prop body }
