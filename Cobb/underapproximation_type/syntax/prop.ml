open Sexplib.Std
open Mtyped
module Nt = Normalty.Ntyped
open Lit

type 't prop =
  | Lit of ('t, 't lit) typed
  | Implies of 't prop * 't prop
  | Ite of 't prop * 't prop * 't prop
  | Not of 't prop
  | And of 't prop list
  | Or of 't prop list
  | Iff of 't prop * 't prop
  | Forall of { qv : (('t, string) typed[@bound]); body : 't prop }
  | Exists of { qv : (('t, string) typed[@bound]); body : 't prop }
[@@deriving sexp]

let rec eq_prop eq (a : 't prop) (b : 't prop) : bool =
  match (a, b) with
  | Lit a, Lit b -> typed_eq eq a b
  | Implies (a0, a1), Implies (b0, b1) -> eq_prop eq a0 b0 && eq_prop eq a1 b1
  | Ite (a0, a1, a2), Ite (b0, b1, b2) ->
      eq_prop eq a0 b0 && eq_prop eq a1 b1 && eq_prop eq a2 b2
  | Not a, Not b -> eq_prop eq a b
  | And a, And b ->
      List.length a = List.length b && List.for_all2 (eq_prop eq) a b
  | Or a, Or b ->
      List.length a = List.length b && List.for_all2 (eq_prop eq) a b
  | Iff (a0, a1), Iff (b0, b1) -> eq_prop eq a0 b0 && eq_prop eq a1 b1
  | Forall { qv = a0; body = a1 }, Forall { qv = b0; body = b1 } ->
      typed_eq String.equal a0 b0 && eq_prop eq a1 b1
  | Exists { qv = a0; body = a1 }, Exists { qv = b0; body = b1 } ->
      typed_eq String.equal a0 b0 && eq_prop eq a1 b1
  | _ -> false

(** TODO: Ideally, test that these two are equivalent
  * Probably not fully true because typed_eq is suspicious *)
let _sexp_eq_prop p1 p2 =
  Sexplib.Sexp.equal
    (sexp_of_prop Nt.sexp_of_t p1)
    (sexp_of_prop Nt.sexp_of_t p2)

let rec fv_prop (prop_e : 't prop) =
  match prop_e with
  | Lit _t__tlittyped0 -> [] @ typed_fv_lit _t__tlittyped0
  | Implies (_tprop0, _tprop1) -> ([] @ fv_prop _tprop1) @ fv_prop _tprop0
  | Ite (_tprop0, _tprop1, _tprop2) ->
      (([] @ fv_prop _tprop2) @ fv_prop _tprop1) @ fv_prop _tprop0
  | Not _tprop0 -> [] @ fv_prop _tprop0
  | And _tproplist0 -> [] @ List.concat (List.map fv_prop _tproplist0)
  | Or _tproplist0 -> [] @ List.concat (List.map fv_prop _tproplist0)
  | Iff (_tprop0, _tprop1) -> ([] @ fv_prop _tprop1) @ fv_prop _tprop0
  | Forall { qv; body } ->
      Zzdatatype.Datatype.List.substract_elm (typed_eq String.equal)
        ([] @ fv_prop body)
        qv
  | Exists { qv; body } ->
      Zzdatatype.Datatype.List.substract_elm (typed_eq String.equal)
        ([] @ fv_prop body)
        qv

and typed_fv_prop (prop_e : ('t, 't prop) typed) = fv_prop prop_e.x

let rec subst_prop (string_x : string) f (prop_e : 't prop) =
  match prop_e with
  | Lit _t__tlittyped0 -> Lit (typed_subst_lit string_x f _t__tlittyped0)
  | Implies (_tprop0, _tprop1) ->
      Implies (subst_prop string_x f _tprop0, subst_prop string_x f _tprop1)
  | Ite (_tprop0, _tprop1, _tprop2) ->
      Ite
        ( subst_prop string_x f _tprop0,
          subst_prop string_x f _tprop1,
          subst_prop string_x f _tprop2 )
  | Not _tprop0 -> Not (subst_prop string_x f _tprop0)
  | And _tproplist0 -> And (List.map (subst_prop string_x f) _tproplist0)
  | Or _tproplist0 -> Or (List.map (subst_prop string_x f) _tproplist0)
  | Iff (_tprop0, _tprop1) ->
      Iff (subst_prop string_x f _tprop0, subst_prop string_x f _tprop1)
  | Forall { qv; body } ->
      if String.equal qv.x string_x then Forall { qv; body }
      else Forall { qv; body = subst_prop string_x f body }
  | Exists { qv; body } ->
      if String.equal qv.x string_x then Exists { qv; body }
      else Exists { qv; body = subst_prop string_x f body }

and typed_subst_prop (string_x : string) f (prop_e : ('t, 't prop) typed) =
  prop_e #-> (subst_prop string_x f)

let rec map_prop (f : 't -> 's) (prop_e : 't prop) =
  match prop_e with
  | Lit _t__tlittyped0 -> Lit (typed_map_lit f _t__tlittyped0)
  | Implies (_tprop0, _tprop1) ->
      Implies (map_prop f _tprop0, map_prop f _tprop1)
  | Ite (_tprop0, _tprop1, _tprop2) ->
      Ite (map_prop f _tprop0, map_prop f _tprop1, map_prop f _tprop2)
  | Not _tprop0 -> Not (map_prop f _tprop0)
  | And _tproplist0 -> And (List.map (map_prop f) _tproplist0)
  | Or _tproplist0 -> Or (List.map (map_prop f) _tproplist0)
  | Iff (_tprop0, _tprop1) -> Iff (map_prop f _tprop0, map_prop f _tprop1)
  | Forall { qv; body } -> Forall { qv = qv #=> f; body = map_prop f body }
  | Exists { qv; body } -> Exists { qv = qv #=> f; body = map_prop f body }

and typed_map_prop (f : 't -> 's) (prop_e : ('t, 't prop) typed) =
  prop_e #=> f #-> (map_prop f)

let fv_prop_id e = fv_typed_id_to_id fv_prop e
let typed_fv_prop_id e = fv_typed_id_to_id typed_fv_prop e

let subst_prop_instance x instance e =
  subst_f_to_instance subst_prop x instance e

let typed_subst_prop_instance x instance e =
  subst_f_to_instance typed_subst_prop x instance e
(* Generated from _prop.ml *)

(* force *)
let prop_force_typed_lit_opt prop =
  match prop with Lit lit -> Some lit | _ -> None

let rec eq_prop_under_alpha_equivalence_helper
    (mapping : (string * string) list) (a : 't prop) (b : 't prop) : bool =
  match (a, b) with
  | Lit a, Lit b ->
      eq_lit_helper Constant.equal_constant
        (fun s1 s2 : bool ->
          if String.equal s1 s2 then true
          else (
            Printf.printf "s1: %s, s2: %s" s1 s2;

            match List.assoc_opt s1 mapping with
            | Some s1' ->
                Printf.printf "s1': %s" s1';
                String.equal s1' s2
            | None -> false))
        a.x b.x
  | Implies (a0, a1), Implies (b0, b1) ->
      eq_prop_under_alpha_equivalence_helper mapping a0 b0
      && eq_prop_under_alpha_equivalence_helper mapping a1 b1
  | Ite (a0, a1, a2), Ite (b0, b1, b2) ->
      eq_prop_under_alpha_equivalence_helper mapping a0 b0
      && eq_prop_under_alpha_equivalence_helper mapping a1 b1
      && eq_prop_under_alpha_equivalence_helper mapping a2 b2
  | Not a, Not b -> eq_prop_under_alpha_equivalence_helper mapping a b
  | And a, And b ->
      List.length a = List.length b
      && List.for_all2 (eq_prop_under_alpha_equivalence_helper mapping) a b
  | Or a, Or b ->
      List.length a = List.length b
      && List.for_all2 (eq_prop_under_alpha_equivalence_helper mapping) a b
  | Iff (a0, a1), Iff (b0, b1) ->
      eq_prop_under_alpha_equivalence_helper mapping a0 b0
      && eq_prop_under_alpha_equivalence_helper mapping a1 b1
  | Forall { qv = a0; body = a1 }, Forall { qv = b0; body = b1 }
    when typed_eq String.equal a0 b0 ->
      eq_prop_under_alpha_equivalence_helper mapping a1 b1
  | Exists { qv = a0; body = a1 }, Exists { qv = b0; body = b1 }
    when typed_eq String.equal a0 b0 ->
      eq_prop_under_alpha_equivalence_helper mapping a1 b1
  | Forall { qv = a0; body = a1 }, Forall { qv = b0; body = b1 } ->
      eq_prop_under_alpha_equivalence_helper ((a0.x, b0.x) :: mapping) a1 b1
  | Exists { qv = a0; body = a1 }, Exists { qv = b0; body = b1 } ->
      eq_prop_under_alpha_equivalence_helper ((a0.x, b0.x) :: mapping) a1 b1
  | _ -> false

let eq_prop_under_alpha_equivalence (a : 't prop) (b : 't prop) : bool =
  eq_prop_under_alpha_equivalence_helper [] a b

let rec simplify prop =
  match prop with
  | Lit _ -> prop
  | Implies (p, q) -> (
      match (simplify p, simplify q) with
      | Lit { x = AC (B true); _ }, q -> q
      | p, Lit { x = AC (B true); _ } -> p
      | Lit { x = AC (B false); _ }, _ ->
          Lit { x = AC (B true); ty = Nt.Ty_bool }
      | _, Lit { x = AC (B false); _ } ->
          Lit { x = AC (B true); ty = Nt.Ty_bool }
      | p, q -> Implies (p, q))
  | And [] -> Lit { x = AC (B true); ty = Ty_bool }
  | And [ p ] -> simplify p
  | And ps -> (
      let ps = List.map simplify ps in
      let ps =
        List.filter
          (fun p -> not (p = Lit { x = AC (B true); ty = Nt.Ty_bool }))
          ps
      in
      match ps with
      | x when List.mem (Lit { x = AC (B false); ty = Nt.Ty_bool }) x ->
          Lit { x = AC (B false); ty = Ty_bool }
      | [] -> Lit { x = AC (B true); ty = Ty_bool }
      | [ p ] -> p
      | _ -> And ps)
  | Or [] -> Lit { x = AC (B false); ty = Ty_bool }
  | Or [ p ] -> simplify p
  | Or ps -> (
      let ps = List.map simplify ps in
      let ps =
        List.filter
          (fun p -> not (p = Lit { x = AC (B false); ty = Nt.Ty_bool }))
          ps
      in
      match ps with
      | x when List.mem (Lit { x = AC (B true); ty = Nt.Ty_bool }) x ->
          Lit { x = AC (B true); ty = Ty_bool }
      | [] -> Lit { x = AC (B false); ty = Ty_bool }
      | [ p ] -> p
      | _ -> Or ps)
  | Iff (p, q) -> simplify (And [ Implies (p, q); Implies (q, p) ])
  | Not p -> (
      match simplify p with
      | Lit { x = AC (B true); _ } -> Lit { x = AC (B false); ty = Ty_bool }
      | Lit { x = AC (B false); _ } -> Lit { x = AC (B true); ty = Ty_bool }
      | Not p -> p
      | p -> Not p)
  | Ite (c, t, e) -> (
      match simplify c with
      | Lit { x = AC (B true); _ } -> simplify t
      | Lit { x = AC (B false); _ } -> simplify e
      | c -> Ite (c, simplify t, simplify e))
  | Forall { qv; body } -> Forall { qv; body = simplify body }
  | Exists { qv; body } -> (
      match simplify body with
      | Lit { x = AC (B true); _ } -> Lit { x = AC (B true); ty = Ty_bool }
      | Lit { x = AC (B false); _ } -> Lit { x = AC (B false); ty = Ty_bool }
      | Lit { x = Lit.AVar { x; _ }; _ } when String.equal x qv.x ->
          Lit { x = AC (B true); ty = Ty_bool }
      | Not (Lit { x = Lit.AVar { x; _ }; _ }) when String.equal x qv.x ->
          Lit { x = AC (B true); ty = Ty_bool }
      | body -> Exists { qv; body })

let from_lit { x; ty } =
  Lit
    (Lit.AAppOp
       ( "==" #: (Nt.Ty_arrow (ty, Nt.Ty_arrow (ty, Nt.Ty_bool))),
         [ (Lit.AVar "v" #: ty) #: ty; (Lit.AVar x #: ty) #: ty ] ))
    #: Nt.Ty_bool

let from_const c = Lit (Lit.AC c) #: (Constant.constant_to_nt c)
