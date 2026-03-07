open Mtyped
open Sexplib.Std

type constant =
  | U
  | B of bool
  | I of int
  | Tu of constant list
  | Dt of string * constant list
[@@deriving sexp]

let rec constant_to_nt c =
  let open Nt in
  match c with
  | U -> unit_ty
  | B _ -> bool_ty
  | I _ -> int_ty
  | Tu l -> Nt.Ty_tuple (List.map constant_to_nt l)
  | Dt _ -> failwith "Not implemented"

let compare_constant e1 e2 =
  Sexplib.Sexp.compare (sexp_of_constant e1) (sexp_of_constant e2)

let rec equal_constant e1 e2 =
  match (e1, e2) with
  | U, U -> true
  | B b1, B b2 -> b1 = b2
  | I i1, I i2 -> i1 = i2
  | Tu l1, Tu l2 ->
      List.length l1 = List.length l2 && List.for_all2 equal_constant l1 l2
  | Dt (s1, l1), Dt (s2, l2) -> s1 = s2 && List.for_all2 equal_constant l1 l2
  | _ -> false

let _sexp_equal_constant e1 e2 =
  Sexplib.Sexp.equal (sexp_of_constant e1) (sexp_of_constant e2)
(* Generated from _constant.ml *)
