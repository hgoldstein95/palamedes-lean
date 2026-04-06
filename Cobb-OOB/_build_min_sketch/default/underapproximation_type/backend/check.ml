open Z3
open Solver
open Goal
module Env = Zzenv
(* open Z3aux *)

type smt_result = SmtSat of Model.model | SmtUnsat | Timeout

let solver_result solver =
  (* let _ = printf "solver_result\n" in *)
  match check solver [] with
  | UNSATISFIABLE -> SmtUnsat
  | UNKNOWN ->
      (* raise (InterExn "time out!") *)
      Printf.printf "\ttimeout\n";
      Timeout
  | SATISFIABLE -> (
      match Solver.get_model solver with
      | None -> failwith "never happen"
      | Some m -> SmtSat m)

let get_int m i =
  match Model.eval m i true with
  | None -> failwith "get_int"
  | Some v ->
      (* printf "get_int(%s)\n" (Expr.to_string i); *)
      int_of_string @@ Arithmetic.Integer.numeral_to_string v

let get_bool_str m i =
  match Model.eval m i true with None -> "none" | Some v -> Expr.to_string v

let get_int_name ctx m name =
  get_int m @@ Arithmetic.Integer.mk_const_s ctx name

let get_pred m predexpr =
  match Model.eval m predexpr true with
  | None -> failwith "get pred"
  | Some v -> Z3aux.z3expr_to_bool v

(* let get_unknown_fv ctx m unknown_fv =
  List.map (fun (_, b) -> get_pred m (Boolean.mk_const_s ctx b)) unknown_fv *)

let rlimit = ref 200000000
let optional_timeout = ref None

let smt_format_file ?(double_check = false) ~optional_timeout ~rlimit filename
    solver =
  (match optional_timeout with
  | Some x -> Printf.printf "Timeout: %d\n" x
  | None -> print_endline "No timeout");
  let oc = open_out filename in
  let prelude =
    "(set-option :rlimit " ^ string_of_int rlimit ^ ")\n"
    ^ Option.fold ~none:""
        ~some:(fun x -> "(set-option :timeout " ^ string_of_int x ^ ")\n")
        optional_timeout
  in
  let query = Z3.Solver.to_string solver in
  let postlude = "\n(check-sat)\n" in
  let postlude = if double_check then postlude ^ postlude else postlude in
  Printf.fprintf oc "%s%s%s" prelude query postlude;
  (* Printf.printf "%s%s%s" prelude query postlude; *)
  close_out oc

let first_matching (deferreds : 'a Async.Deferred.t list)
    (predicate : 'a -> 'a option) : 'a option Async.Deferred.t =
  let open Async in
  let result_ivar = Ivar.create () in

  let handle d =
    don't_wait_for
      ( d >>| fun value ->
        let pred = predicate value in
        if Option.is_some pred then Ivar.fill_if_empty result_ivar pred;
        () )
  in

  List.iter handle deferreds;

  (* Also wait for all to complete in case none match *)
  don't_wait_for
    (Deferred.all deferreds >>| fun _ -> Ivar.fill_if_empty result_ivar None);

  Ivar.read result_ivar

let smt_predicate result =
  if Core.String.is_substring ~substring:"unsat" result then Some "unsat"
  else if Core.String.is_substring ~substring:"sat" result then Some "sat"
  else None

let process_command cmd =
  match String.split_on_char ' ' cmd with
  | prog :: args -> (prog, args)
  | [] -> failwith "Empty command"

let run_first_to_decision_alt commands =
  let open Async in
  Thread_safe.block_on_async_exn (fun () ->
      let deferred_commands =
        List.map
          (fun cmd ->
            let prog, args = process_command cmd in
            Process.create_exn ~prog ~args () >>= fun proc ->
            (* Have to use up stdin and stderr because somehow these don't close
            otherwise? *)
            Writer.close (Process.stdin proc) >>= fun () ->
            let stderr_drain = Reader.drain (Process.stderr proc) in
            Reader.contents (Process.stdout proc) >>= fun output ->
            stderr_drain >>= fun () ->
            Process.wait proc >>| fun _ -> output)
          commands
      in
      first_matching deferred_commands smt_predicate
      >>| Option.value ~default:"unknown")

let run_z3_in_process solver : smt_result =
  (* TODO: Use stdin instead for parallelism *)
  let filename = "subtyping_temp_file.smt2" in
  let filename2 = "subtyping_temp_file_double.smt2" in
  smt_format_file ~optional_timeout:!optional_timeout ~rlimit:!rlimit filename
    solver;
  let command = "z3 " ^ filename in
  let command2 = "z3 proof=true " ^ filename in

  smt_format_file
    ~optional_timeout:
      (Option.map (fun timeout -> timeout / 2) !optional_timeout)
    ~rlimit:(!rlimit / 2) ~double_check:true filename2 solver;

  let command3 = "z3 proof=true " ^ filename2 in

  let status = run_first_to_decision_alt [ command; command2; command3 ] in

  print_endline "----------------";
  print_endline status;
  print_endline "----------------";
  if status = "unsat" (* status = WEXITED 0 *) then SmtUnsat else Timeout

let smt_solve ctx assertions =
  (* let _ = printf "check\n" in *)
  let solver = mk_solver ctx None in
  let g = mk_goal ctx true false false in
  let _ = Goal.add g assertions in

  (* let g = Goal.simplify g None in *)
  (* let g = *)
  (*   Tactic.(ApplyResult.get_subgoal (apply (mk_tactic ctx "snf") g None) 0) *)
  (* in *)
  (* let () = *)
  (*   Printf.printf "Goal: %s\n\n" *)
  (*   @@ Zzdatatype.Datatype.List.split_by "\n" Expr.to_string *)
  (*   @@ Goal.get_formulas g *)
  (* in *)
  let _ = Solver.add solver (get_formulas g) in

  (* Solver.to_string solver |> print_endline; *)
  (*  let _, res = Sugar.clock (fun () -> solver_result solver) in *)
  let res = run_z3_in_process solver in
  res

let extend =
  [
    ("len", [ "hd"; "tl"; "emp" ]);
    ("leaf", [ "root"; "lch"; "rch" ]);
    ("root", [ "leaf"; "lch"; "rch" ]);
    ( "rb_root",
      [
        "rb_leaf";
        "rb_root_color";
        "num_black";
        "no_red_red";
        "rb_lch";
        "rb_rch";
      ] );
    ( "rb_leaf",
      [
        "rb_root";
        "rb_root_color";
        "num_black";
        "no_red_red";
        "rb_lch";
        "rb_rch";
      ] );
    ( "num_black",
      [
        "rb_root"; "rb_root_color"; "rb_leaf"; "no_red_red"; "rb_lch"; "rb_rch";
      ] );
    ( "no_red_red",
      [ "rb_root"; "rb_root_color"; "rb_leaf"; "num_black"; "rb_lch"; "rb_rch" ]
    );
    ( "typing",
      [
        "is_const";
        "is_var";
        "is_abs";
        "is_app";
        "num_app";
        "stlc_ty_nat";
        "stlc_ty_arr1";
        "stlc_ty_arr2";
        "stlc_const";
        "stlc_id";
        "stlc_app1";
        "stlc_app2";
        "stlc_abs_ty";
        "stlc_abs_body";
        "stlc_tyctx_emp";
        "stlc_tyctx_hd";
        "stlc_tyctx_tl";
      ] );
  ]

let query_counter = ref 0

let smt_neg_and_solve ctx axioms vc =
  query_counter := !query_counter + 1;
  let open Language.FrontendTyped in
  let current_mps = prop_get_mp vc in
  let current_mps =
    List.concat
    @@ List.map
         (fun mp ->
           match
             List.find_opt (fun (name, _) -> String.equal name mp) extend
           with
           | Some (_, res) -> mp :: res
           | _ -> [ mp ])
         current_mps
  in
  (* let _ = *)
  (*   Printf.printf "current_mps: %s\n" *)
  (*     (Zzdatatype.Datatype.StrList.to_string current_mps) *)
  (* in *)
  let axioms =
    List.filter
      (fun a ->
        let mps = prop_get_mp a in
        List.for_all (fun mp -> List.exists (String.equal mp) current_mps) mps)
      axioms
  in

  (*   let () = Printf.printf "Num of axioms: %i\n" (List.length axioms) in *)

  (* let () = List.iter (fun a -> Printf.printf "%s\n" (layout_prop a)) axioms in *)

  (* let () = failwith "end" in *)
  let assertions = List.map (Propencoding.to_z3 ctx) (axioms @ [ Not vc ]) in

  (* let () =
       List.iter (fun a -> Printf.printf "%s\n" (Expr.to_string a)) assertions
     in *)
  (*   print_endline "End Axioms"; *)
  let time_t, res = Sugar.clock (fun () -> smt_solve ctx assertions) in
  let () =
    Env.show_debug_stat @@ fun _ -> Pp.printf "Z3 solving time: %0.4fs\n" time_t
  in
  res

exception SMTTIMEOUT

let debug_counter = ref 0
let smt_timeout_flag = ref false

(** Unsat means true; otherwise means false *)
let handle_check_res query_action =
  let time_t, res = Sugar.clock query_action in
  let () =
    Env.show_debug_stat @@ fun _ ->
    Pp.printf "@{<bold>Solving time: %.2f@}\n" time_t
  in
  (* let () = *)
  (*   if 18 == !debug_counter then failwith "end" *)
  (*   else debug_counter := !debug_counter + 1 *)
  (* in *)
  smt_timeout_flag := false;
  match res with
  | SmtUnsat -> true
  | SmtSat model ->
      ( Env.show_log "model" @@ fun _ ->
        Printf.printf "model:\n%s\n"
        @@ Sugar.short_str 1000 @@ Z3.Model.to_string model );
      false
  | Timeout ->
      (Env.show_debug_queries @@ fun _ -> Pp.printf "@{<bold>SMTTIMEOUT@}\n");
      smt_timeout_flag := true;
      false
