let universe_label = ref 0

let name () =
  let n = Printf.sprintf "idx%i" !universe_label in
  universe_label := !universe_label + 1;
  n

let name_tab = Hashtbl.create 100

open Printf

let split_char = '_'

let unique_ name =
  match Hashtbl.find_opt name_tab name with
  | Some n ->
      Hashtbl.replace name_tab name (n + 1);
      sprintf "%s%c%i" name split_char (n + 1)
  | None ->
      Hashtbl.add name_tab name 0;
      sprintf "%s%c%i" name split_char 0

let unique name =
  let prefix, name =
    match String.split_on_char split_char name with
    | [ x ] -> (None, x)
    | [ x; _ ] -> (None, x)
    | [ p; x; _ ] -> (Some p, x)
    | _ -> failwith "die"
  in
  let name = unique_ name in
  match prefix with
  | None -> name
  | Some p -> p ^ String.make 1 split_char ^ name

let unique_with_prefix p name =
  let _, name =
    match String.split_on_char split_char name with
    | [ x ] -> (None, x)
    | [ x; _ ] -> (None, x)
    | [ p; x; _ ] -> (Some p, x)
    | _ -> failwith "die"
  in
  let name = unique_ name in
  p ^ String.make 1 split_char ^ name

let has_been_uniqified name =
    match String.split_on_char split_char name with
    | [_; y] when int_of_string_opt y |> Option.is_some -> true
      | _ -> false