open Sexplib.Std
open Sugar
open Ppx_compare_lib.Builtin
open Ppx_hash_lib.Std.Hash.Builtin

type t =
  | Ty_any (* parsing only *)
  | Ty_unknown (* parsing only *)
  | Ty_var of string (* parsing only *)
  | Ty_unit
  | Ty_int
  | Ty_nat
  | Ty_bool
  | Ty_arrow of t * t
  | Ty_tuple of t list
  | Ty_uninter of string
  | Ty_constructor of (string * t list)
  | Ty_record of (string * t) list
[@@deriving sexp, compare, hash]

let _unique_type_var_name = ref 0

let new_type_var () =
  let res = Ty_var (spf "t%i" !_unique_type_var_name) in
  _unique_type_var_name := !_unique_type_var_name + 1;
  res

let is_base_tp = function
  | Ty_unit | Ty_int | Ty_nat | Ty_bool | Ty_uninter _ | Ty_constructor _ ->
      true
  | _ -> false

let is_basic_tp = function
  | Ty_unit | Ty_int | Ty_nat | Ty_bool | Ty_uninter _ -> true
  | _ -> false

let is_dt = function Ty_constructor _ -> true | _ -> false

let fst_ty = function
  | Ty_tuple [ a; _ ] -> a
  | _ -> _failatwith __FILE__ __LINE__ "fst_ty"

let snd_ty = function
  | Ty_tuple [ _; a ] -> a
  | _ -> _failatwith __FILE__ __LINE__ "snd_ty"

let eq x y =
  let rec aux (x, y) =
    match (x, y) with
    | Ty_any, Ty_any -> true
    | Ty_unknown, Ty_unknown -> true
    | Ty_var x, Ty_var y -> String.equal x y
    | Ty_unit, Ty_unit -> true
    | Ty_int, Ty_int -> true
    | Ty_nat, Ty_nat -> true
    | Ty_bool, Ty_bool -> true
    | Ty_uninter name1, Ty_uninter name2 -> String.equal name1 name2
    | Ty_arrow (x, x'), Ty_arrow (y, y') -> aux (x, y) && aux (x', y')
    | Ty_tuple xs, Ty_tuple ys ->
        if List.length xs == List.length ys then
          List.for_all aux @@ List.combine xs ys
        else false
    | Ty_constructor (id1, args1), Ty_constructor (id2, args2) ->
        String.equal id1 id2
        && List.length args1 == List.length args2
        && List.for_all2 (fun a b -> aux (a, b)) args1 args2
    | Ty_record l1, Ty_record l2 ->
        let l1 = List.sort Stdlib.compare l1 in
        let l2 = List.sort Stdlib.compare l2 in
        List.equal
          (fun (x1, t1) (x2, t2) -> String.equal x1 x2 && aux (t1, t2))
          l1 l2
    (* To allow pattern matching on bool's*)
    | Ty_bool, Ty_constructor ("bool", []) | Ty_constructor ("bool", []), Ty_bool -> true
    | _ -> false
  in
  aux (x, y)

let get_record_types = function
  | Ty_record l -> l
  | _ -> _failatwith __FILE__ __LINE__ "die"

let destruct_arr_tp tp =
  let rec aux = function
    | Ty_arrow (t1, t2) ->
        let argsty, bodyty = aux t2 in
        (t1 :: argsty, bodyty)
    | ty -> ([], ty)
  in
  aux tp

let rec construct_arr_tp = function
  | [], retty -> retty
  | h :: t, retty -> Ty_arrow (h, construct_arr_tp (t, retty))

let to_smtty t =
  let aux = function
    | Ty_bool -> Smtty.Bool
    | Ty_int -> Smtty.Int
    | Ty_nat -> Smtty.Int
    | Ty_constructor _ -> Smtty.Dt
    | _ ->
        let () =
          Printf.printf "t: %s\n" @@ Sexplib.Sexp.to_string @@ sexp_of_t t
        in
        _failatwith __FILE__ __LINE__ "not a basic type"
  in
  aux t

let default_ty = Ty_unknown
let unit_ty = Ty_unit
let int_ty = Ty_int
let nat_ty = Ty_nat
let bool_ty = Ty_bool
let uninter_ty name = Ty_uninter name
let mk_arr t1 t2 = Ty_arrow (t1, t2)
let mk_tuple ts = match ts with [ t ] -> t | _ -> Ty_tuple ts
let mk_record ts = Ty_record ts

let get_argty = function
  | Ty_arrow (t1, _) -> t1
  | _ -> _failatwith __FILE__ __LINE__ "?"

let get_retty = function
  | Ty_arrow (_, t2) -> t2
  | _ -> _failatwith __FILE__ __LINE__ "?"

(* type unification *)
open Zzdatatype.Datatype

let subst t (id, ty) =
  let rec aux t =
    match t with
    | Ty_unknown | Ty_any | Ty_unit | Ty_int | Ty_nat | Ty_bool | Ty_uninter _
      ->
        t
    | Ty_var x -> if String.equal x id then ty else t
    | Ty_arrow (t1, t2) -> Ty_arrow (aux t1, aux t2)
    | Ty_tuple xs -> Ty_tuple (List.map aux xs)
    | Ty_constructor (id, args) -> Ty_constructor (id, List.map aux args)
    | Ty_record l -> Ty_record (List.map (fun (x, t) -> (x, aux t)) l)
  in
  aux t

let subst_m m t = StrMap.fold (fun id ty t -> subst t (id, ty)) m t
let layout t = Sexplib.Sexp.to_string @@ sexp_of_t t
let subst_on_sol (i, t) m = StrMap.map (fun t' -> subst t' (i, t)) m

let subst_on_cs (i, t) cs =
  List.map (fun (t1, t2) -> (subst t1 (i, t), subst t2 (i, t))) cs

let type_unification_v2 m (cs : (t * t) list) =
  let rec aux m cs =
    match cs with
    | [] -> Some m
    | (t1, t2) :: cs -> (
        match (t1, t2) with
        | Ty_any, _ | _, Ty_any | Ty_unknown, _ | _, Ty_unknown -> aux m cs
        | Ty_var n, _ ->
            let m = subst_on_sol (n, t2) m in
            let cs = subst_on_cs (n, t2) cs in
            aux (StrMap.add n t2 m) cs
        | _, Ty_var n ->
            let m = subst_on_sol (n, t1) m in
            let cs = subst_on_cs (n, t1) cs in
            aux (StrMap.add n t1 m) cs
        | Ty_constructor (id1, ts1), Ty_constructor (id2, ts2) ->
            if String.equal id1 id2 && List.length ts1 == List.length ts2 then
              aux m (List.combine ts1 ts2 @ cs)
            else None
        | Ty_arrow (t11, t12), Ty_arrow (t21, t22) ->
            aux m ((t11, t21) :: (t12, t22) :: cs)
        (* unfold singleton tuple *)
        | Ty_tuple [ t1 ], _ -> aux m ((t1, t2) :: cs)
        | _, Ty_tuple [ t2 ] -> aux m ((t1, t2) :: cs)
        | Ty_tuple ts1, Ty_tuple ts2 when List.length ts1 == List.length ts2 ->
            aux m (List.combine ts1 ts2 @ cs)
        | Ty_record l1, Ty_record l2 ->
            let tab = Hashtbl.create (List.length l1) in
            let () = List.iter (fun (x, t) -> Hashtbl.add tab x t) l1 in
            let cs =
              List.fold_left
                (fun res (x, t) ->
                  match Hashtbl.find_opt tab x with
                  | None ->
                      _failatwith __FILE__ __LINE__
                        (spf "connot find feild %s" x)
                  | Some t' -> (t', t) :: res)
                cs l2
            in
            aux m cs
        | _, _ -> if eq t1 t2 then aux m cs else None)
  in
  aux m cs

let __type_unify_ (pprint : t -> string) file line m t1 t2 =
  (* let () = Printf.printf "unify %s --> %s\n" (layout t1) (layout t2) in *)
  let rec unify m (t1, t2) =
    let t1 = subst_m m t1 in
    let t2 = subst_m m t2 in
    (* let () = Printf.printf "one %s --> %s\n" (layout t1) (layout t2) in *)
    match (t1, t2) with
    | Ty_any, _ -> (m, t2)
    | Ty_unknown, _ -> (m, t2)
    | Ty_var n, t2 -> (
        match StrMap.find_opt m n with
        | Some _ -> _failatwith __FILE__ __LINE__ (n ^ layout t2)
        | None ->
            let m = StrMap.add n t2 m in
            (m, t2))
    | Ty_constructor (id1, ts1), Ty_constructor (id2, ts2) ->
        let id = _check_equality file line String.equal id1 id2 in
        let m, ts =
          List.fold_left
            (fun (m, ts) (t1, t2) ->
              let m, t = unify m (t1, t2) in
              (m, ts @ [ t ]))
            (m, []) (List.combine ts1 ts2)
        in
        (m, Ty_constructor (id, ts))
    | Ty_arrow (t11, t12), Ty_arrow (t21, t22) ->
        let m, t1 = unify m (t11, t21) in
        let m, t2 = unify m (t12, t22) in
        (m, Ty_arrow (t1, t2))
    (* unfold singleton tuple *)
    | Ty_tuple [ t1 ], _ -> unify m (t1, t2)
    | _, Ty_tuple [ t2 ] -> unify m (t1, t2)
    | Ty_tuple ts1, Ty_tuple ts2 when List.length ts1 == List.length ts2 ->
        let m, ts =
          List.fold_left
            (fun (m, ts) (t1, t2) ->
              let m, t = unify m (t1, t2) in
              (m, ts @ [ t ]))
            (m, []) (List.combine ts1 ts2)
        in
        (m, Ty_tuple ts)
    | Ty_record l1, Ty_record l2 when List.length l1 == List.length l2 ->
        let tab = Hashtbl.create (List.length l1) in
        let () = List.iter (fun (x, t) -> Hashtbl.add tab x t) l1 in
        let m, l =
          List.fold_left
            (fun (m, l) (x, t) ->
              match Hashtbl.find_opt tab x with
              | None ->
                  _failatwith __FILE__ __LINE__ (spf "connot find feild %s" x)
              | Some t' ->
                  let m, t = unify m (t', t) in
                  (m, (x, t) :: l))
            (m, []) l2
        in
        (m, Ty_record l)
    | _, Ty_any -> (m, t1)
    | _, Ty_unknown -> (m, t1)
    | _, Ty_var _ ->
        (* (m, t1) *)
        _failatwith file line "argment should not contain type var"
    | _, _ ->
        ( m,
          try _check_equality file line eq t1 t2
          with e ->
            Printf.printf "%s != %s\n" (layout t1) (layout t2);
            raise e )
  in
  try unify m (t1, t2)
  with e ->
    Printf.printf "Type unify error: %s ==> %s\n" (pprint t1) (pprint t2);
    Printf.printf "Precisely: %s ==> %s\n" (layout t1) (layout t2);
    raise e

let __type_unify_v1 pprint file line t1 t2 =
  snd @@ __type_unify_ pprint file line StrMap.empty t1 t2

let __type_unify_v2 (pprint : t -> string) file line t1 t2 =
  let m = type_unification_v2 StrMap.empty [ (t1, t2) ] in
  let error_print () =
    Printf.printf "Type unify error: %s ==> %s\n" (pprint t1) (pprint t2);
    _failatwith file line "normal type check error"
  in
  match m with
  | Some m ->
      let t1, t2 = map2 (subst_m m) (t1, t2) in
      __type_unify_v1 pprint file line t1 t2
      (* if not (eq t1 t2) then ( *)
      (*   Printf.printf "Precisely: %s ==> %s\n" (layout t1) (layout t2); *)
      (*   error_print ()) *)
      (* else t2 *)
  | None -> error_print ()

let __type_unify = __type_unify_v2
