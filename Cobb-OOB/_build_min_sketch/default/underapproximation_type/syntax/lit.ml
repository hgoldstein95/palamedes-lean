open Sexplib.Std
open Mtyped
open Constant

type 't lit =
  | AC of constant
  | AVar of (('t, string) typed[@free])
  | ATu of ('t, 't lit) typed list
  | AProj of ('t, 't lit) typed * int
  | AAppOp of ('t, string) typed * ('t, 't lit) typed list
[@@deriving sexp]

(* Factored out string equivalence to allow for alpha equivalent literal checks*)
let rec eq_lit_helper (eq : 'a -> 'a -> bool)
    (eq_str : string -> string -> bool) p1 p2 =
  match (p1, p2) with
  | AC c1, AC c2 -> equal_constant c1 c2
  | AVar v1, AVar v2 -> typed_eq eq_str v1 v2
  | ATu l1, ATu l2 ->
      List.length l1 = List.length l2
      && List.for_all2 (typed_eq (eq_lit_helper eq eq_str)) l1 l2
  | AProj (l1, i1), AProj (l2, i2) ->
      typed_eq (eq_lit_helper eq eq_str) l1 l2 && i1 = i2
  | AAppOp (op1, l1), AAppOp (op2, l2) ->
      typed_eq eq_str op1 op2
      && List.length l1 = List.length l2
      && List.for_all2 (typed_eq (eq_lit_helper eq eq_str)) l1 l2
  | _ -> false

let eq_lit eq p1 p2 = eq_lit_helper eq String.equal p1 p2

let _sexp_eq_lit p1 p2 =
  Sexplib.Sexp.equal (sexp_of_lit Nt.sexp_of_t p1) (sexp_of_lit Nt.sexp_of_t p2)

let rec fv_lit (lit_e : 't lit) =
  match lit_e with
  | AC _ -> []
  | AVar _t_stringtyped0 -> [] @ [ _t_stringtyped0 ]
  | ATu _t__tlittypedlist0 ->
      [] @ List.concat (List.map typed_fv_lit _t__tlittypedlist0)
  | AProj (_t__tlittyped0, _) -> [] @ typed_fv_lit _t__tlittyped0
  | AAppOp (_, _t__tlittypedlist1) ->
      [] @ List.concat (List.map typed_fv_lit _t__tlittypedlist1)

and typed_fv_lit (lit_e : ('t, 't lit) typed) = fv_lit lit_e.x

let rec subst_lit (string_x : string) f (lit_e : 't lit) =
  match lit_e with
  | AC constant0 -> AC constant0
  | AVar _t_stringtyped0 ->
      if String.equal _t_stringtyped0.x string_x then f _t_stringtyped0
      else AVar _t_stringtyped0
  | ATu _t__tlittypedlist0 ->
      ATu (List.map (typed_subst_lit string_x f) _t__tlittypedlist0)
  | AProj (_t__tlittyped0, int1) ->
      AProj (typed_subst_lit string_x f _t__tlittyped0, int1)
  | AAppOp (_t_stringtyped0, _t__tlittypedlist1) ->
      AAppOp
        ( _t_stringtyped0,
          List.map (typed_subst_lit string_x f) _t__tlittypedlist1 )

and typed_subst_lit (string_x : string) f (lit_e : ('t, 't lit) typed) =
  lit_e #-> (subst_lit string_x f)

let rec map_lit : 't 's. ('t -> 's) -> 't lit -> 's lit =
 fun f lit_e ->
  match lit_e with
  | AC constant0 -> AC constant0
  | AVar _t_stringtyped0 -> AVar _t_stringtyped0 #=> f
  | ATu _t__tlittypedlist0 ->
      ATu (List.map (fun e -> typed_map_lit f e) _t__tlittypedlist0)
  | AProj (_t__tlittyped0, int1) -> AProj (typed_map_lit f _t__tlittyped0, int1)
  | AAppOp (_t_stringtyped0, _t__tlittypedlist1) ->
      AAppOp
        (_t_stringtyped0 #=> f, List.map (typed_map_lit f) _t__tlittypedlist1)

and typed_map_lit :
      't 's. ('t -> 's) -> ('t, 't lit) typed -> ('s, 's lit) typed =
 fun f lit_e -> lit_e #=> f #-> (map_lit f)

let fv_lit_id e = fv_typed_id_to_id fv_lit e
let typed_fv_lit_id e = fv_typed_id_to_id typed_fv_lit e
let subst_lit_instance x instance e = subst_f_to_instance subst_lit x instance e

let typed_subst_lit_instance x instance e =
  subst_f_to_instance typed_subst_lit x instance e
(* Generated from _lit.ml *)

(* force *)
let typed_lit_force_aappop_opt (lit, op) =
  match lit.x with
  | AAppOp ({ x; _ }, args) when String.equal x op -> Some args
  | _ -> None

let typed_lit_force_avar_opt lit =
  match lit.x with AVar id -> Some id | _ -> None

let typed_lit_force_ac_opt lit = match lit.x with AC c -> Some c | _ -> None
