open Language
open Sugar
open Feature
open FrontendTyped

type t = { ftab : feature_tab; fvec_tab : (int, label) Hashtbl.t }

let init (ftab : feature_tab) (verifier : Feature.t prop -> bool) =
  let vec_num = pow 2 (List.length ftab) in
  let fvec_tab = Hashtbl.create vec_num in
  let rec aux i =
    if i == vec_num then ()
    else if verifier (feature_id_to_prop ftab i) then (
      Hashtbl.add fvec_tab i Unknown;
      aux (i + 1))
    else aux (i + 1)
  in
  let () = aux 0 in
  { ftab; fvec_tab }

let get_prop_by_filter f { ftab; fvec_tab } =
  let fvecs =
    Hashtbl.fold (fun fv b l -> if f b then fv :: l else l) fvec_tab []
  in
  (* let _ = Printf.printf "len(fvecs) = %i\n" (List.length fvecs) in *)
  match fvecs with
  | [] -> mk_false
  | _ ->
      let props = List.map (feature_id_to_prop ftab) fvecs in
      (* let props = List.rev props in *)
      let res = Or props in
      (* let () = Printf.printf "\t%s\n" (layout_prop res) in *)
      res

let pick_by_filter f { fvec_tab; _ } =
  Hashtbl.fold
    (fun fv b res ->
      match res with Some _ -> res | None -> if f b then Some fv else None)
    fvec_tab None

let pick_unknown =
  pick_by_filter (fun b -> match b with Unknown -> true | _ -> false)

let update { fvec_tab; _ } id label = Hashtbl.replace fvec_tab id label
