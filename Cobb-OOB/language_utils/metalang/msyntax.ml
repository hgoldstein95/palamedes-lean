open Ocaml5_parser
open Convention
open Mutils
open Zzdatatype.Datatype
(* open Parsetree *)
(* open Sugar *)

let handle_type_declaration predefine (sourcefile : string) : string =
  let structure = Frontend.parse ~sourcefile in
  (* let _ = Printf.printf "%s\n" @@ Pprintast.string_of_structure structure in *)
  (* let item = *)
  (*   match structure_get_valuedefs structure with *)
  (*   | [ (flag, vbs) ] -> desc_to_structure_item @@ Pstr_value (flag, vbs) *)
  (*   | _ -> _failatwith __FILE__ __LINE__ "die" *)
  (* in *)
  (* let _ = Printf.printf "%s\n" @@ Pprintast.string_of_structure [ item ] in *)
  (* let _ = failwith "end" in *)
  let tyds = structure_get_typedefs structure in
  let ctx = tyd_to_ctx tyds in
  let fv_code =
    mk_multi_rec_funcdef_args @@ List.concat
    @@ List.map (Mkfv.mk predefine)
    @@ StrMap.to_kv_list ctx
  in
  let subst_code =
    mk_multi_rec_funcdef_args @@ List.concat
    @@ List.map (Mksubst.mk predefine)
    @@ StrMap.to_kv_list ctx
  in
  let map_code =
    mk_multi_rec_funcdef_args @@ List.concat
    @@ List.map (Mkmap.mk predefine)
    @@ StrMap.to_kv_list ctx
  in
  let res = structure @ [ fv_code; subst_code; map_code ] in
  let fvid_code =
    List.concat @@ List.map (Mkfvid.mk predefine) @@ StrMap.to_kv_list ctx
  in
  let substInstance_code =
    List.concat
    @@ List.map (Mksubstinstance.mk predefine)
    @@ StrMap.to_kv_list ctx
  in
  let compare_code =
    List.concat @@ List.map (Mkcompare.mk predefine) @@ StrMap.to_kv_list ctx
  in
  let eq_code =
    List.concat @@ List.map (Mkequal.mk predefine) @@ StrMap.to_kv_list ctx
  in
  let res = res @ fvid_code @ substInstance_code @ compare_code @ eq_code in
  let res = Pprintast.string_of_structure res in
  let sourcefile = List.last @@ String.split_on_char '/' sourcefile in
  Printf.sprintf "%s\n(* Generated from %s *)\n" res sourcefile
