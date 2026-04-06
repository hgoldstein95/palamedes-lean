type ('t, 'a) typed = { x : 'a; ty : 't } [@@deriving sexp]

let _get_ty x = x.ty
let _get_x x = x.x
let ( #: ) x ty = { x; ty }

let ( #-> ) : 't 'a 'b. ('t, 'a) typed -> ('a -> 'b) -> ('t, 'b) typed =
 fun { x; ty } f -> (f x) #: ty

let ( #=> ) : 't 's 'a. ('t, 'a) typed -> ('t -> 's) -> ('s, 'a) typed =
 fun { x; ty } f -> x #: (f ty)

let __force_typed file line { x; ty } =
  match ty with
  | Some ty -> x #: ty
  | None -> Sugar._failatwith file line "binding variables must be typed"

let strict_typed_eq eq_t eq_x a b = eq_t a.ty b.ty && eq_x a.x b.x
let typed_eq eq a b = eq a.x b.x
let fv_typed_id_to_id f e = List.map (fun x -> x.x) @@ f e
let subst_f_to_instance subst x lit e = subst x (fun _ -> lit) e
(* let sexp_of_polyt _ = Sexplib.Sexp.unit *)

(* let typed_subtract a b = *)
(*   Zzdatatype.Datatype.List.substract (typed_eq String.equal) a b *)

(* let subtract a b = Zzdatatype.Datatype.List.substract String.equal a b *)
