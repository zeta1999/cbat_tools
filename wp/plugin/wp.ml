(***************************************************************************)
(*                                                                         *)
(*  Copyright (C) 2018/2019 The Charles Stark Draper Laboratory, Inc.      *)
(*                                                                         *)
(*  This file is provided under the license found in the LICENSE file in   *)
(*  the top-level directory of this project.                               *)
(*                                                                         *)
(*  This work is funded in part by ONR/NAWC Contract N6833518C0107.  Its   *)
(*  content does not necessarily reflect the position or policy of the US  *)
(*  Government and no official endorsement should be inferred.             *)
(*                                                                         *)
(***************************************************************************)

open Core_kernel
open Bap_main
open Bap.Std
open Bap_wp
include Self()

module Cmd = Bap_main.Extension.Command
module Typ = Bap_main.Extension.Type

module Comp = Compare
module Pre = Precondition
module Env = Environment
module Constr = Constraint

module Utils = struct

  let missing_func_msg (func : string) : string =
    Format.sprintf "Missing function: %s is not in binary." func

  let diff_arch_msg (arch1 : Arch.t) (arch2 : Arch.t) : string =
    Format.sprintf "Binaries are of two different architectures: %s vs %s"
      (Arch.to_string arch1) (Arch.to_string arch2)

  let invalid_file_count_msg files =
    Format.sprintf "CBAT can only analyze one binary for a single analysis or \
                    two binaries for a comparative analysis. Number of \
                    binaries provided: %d." (List.length files)

  let load_proj_error_msg msg =
    Format.sprintf "Error loading project: %s\n%!" msg

  let loader = "llvm"

  let load_proj loader filepath =
    let input = Project.Input.file ~loader ~filename:filepath in
    match Project.create input with
    | Ok proj -> proj
    | Error e ->
      let msg = Error.to_string_hum e in
      failwith (load_proj_error_msg msg)

  let find_func_err (subs : Sub.t Seq.t) (func : string) : Sub.t =
    match Seq.find ~f:(fun s -> String.equal (Sub.name s) func) subs with
    | None -> failwith (missing_func_msg func)
    | Some f -> f

  (* Not efficient, but easier to read *)
  let find_func_in_one_of (f : string) ~to_find:(to_find : Sub.t Seq.t)
      ~to_check:(to_check : Sub.t Seq.t) : Sub.t list =
    match Seq.find ~f:(fun s -> String.equal (Sub.name s) f) to_find with
    | None -> if Option.is_some (Seq.find ~f:(fun s -> String.equal (Sub.name s) f) to_check)
      then []
      else failwith (missing_func_msg f)
    | Some f -> [f]

  let update_default_num_unroll (num_unroll : int option) : unit =
    match num_unroll with
    | Some n -> Pre.num_unroll := n
    | None -> ()

  let match_inline (to_inline : string option) (subs : (Sub.t Seq.t)) : Sub.t Seq.t =
    match to_inline with
    | None -> Seq.empty
    | Some to_inline -> let inline_pat = Re.Posix.re to_inline |> Re.Posix.compile in
      let filter_subs = Seq.filter ~f:(fun s -> Re.execp inline_pat (Sub.name s)) subs in
      let () =
        if Seq.length_is_bounded_by ~min:1 filter_subs then
          info "Inlining functions: %s\n" (filter_subs |> Seq.to_list |> List.to_string ~f:Sub.name)
        else
          warning "No matches on inlining\n"
      in
      filter_subs

  let varset_to_string (vs : Var.Set.t) : string =
    vs
    |> Var.Set.to_sequence
    |> Seq.to_list
    |> List.to_string ~f:Var.to_string

end

module Analysis = struct

  type options =
    {
      precond : string;
      postcond : string;
      find_null_derefs : bool;
      compare_func_calls : bool;
      compare_final_reg_values : string list;
      loop_unroll : int option;
      print_paths : bool;
      inline : string option;
      gdb_filename : string option;
      bildb_output : string option;
      use_constant_chaosing : bool;
      mem_offset : bool;
      print_constr : string list
    }

let func_calls (flag : bool) : (Comp.comparator * Comp.comparator) option =
  if flag then
    Some Comp.compare_subs_fun
  else
    None

let final_reg_values
    (regs : string list)
    ~orig:(sub1, env1 : Sub.t * Env.t)
    ~modif:(sub2, env2 : Sub.t * Env.t)
  : (Comp.comparator * Comp.comparator) option =
  if List.is_empty regs then
    None
  else begin
    let input = Var.Set.union
        (Pre.get_vars env1 sub1) (Pre.get_vars env2 sub2) in
    let output = Var.Set.union
        (Pre.get_output_vars env1 sub1 regs)
        (Pre.get_output_vars env2 sub2 regs) in
    debug "Input: %s%!" (Utils.varset_to_string input);
    debug "Output: %s%!" (Utils.varset_to_string output);
    Some (Comp.compare_subs_eq ~input ~output)
  end

let smtlib ~postcond:(postcond : string) ~precond:(precond : string)
  : (Comp.comparator * Comp.comparator) option =
  if String.is_empty postcond && String.is_empty precond then
    None
  else
    Some (Comp.compare_subs_smtlib ~smtlib_post:postcond ~smtlib_hyp:precond)

let sp (arch : Arch.t) : (Comp.comparator * Comp.comparator) option =
  match arch with
  | `x86_64 -> Some Comp.compare_subs_sp
  | _ ->
    error "CBAT can only generate hypotheses about the stack pointer and \
           memory for the x86_64 architecture.\n%!";
    None

(* Returns a list of postconditions and a list of hypotheses based on the flags
   set from the command line. *)
let comparators_of_options
    ~orig:(sub1, env1 : Sub.t * Env.t)
    ~modif:(sub2, env2 : Sub.t * Env.t)
    (opts : options)
  : Comp.comparator list * Comp.comparator list =
  let arch = Env.get_arch env1 in
  let comps =
    [ func_calls opts.compare_func_calls;
      final_reg_values opts.compare_final_reg_values
        ~orig:(sub1, env1) ~modif:(sub2, env2);
      smtlib ~postcond:opts.postcond ~precond:opts.precond;
      sp arch ]
    |> List.filter_opt
  in
  let comps =
    if List.is_empty comps then
      [Comp.compare_subs_empty_post]
    else
      comps
  in
  List.unzip comps

  (* If an offset is specified, generates a function of the address of a memory read in
     the original binary to the address plus an offset in the modified binary. *)
  let get_mem_offsets (ctx : Z3.context) (opts : options) (file1 : string) (file2 : string)
    : Constr.z3_expr -> Constr.z3_expr =
    if opts.mem_offset then
      let get_symbols file =
        (* Chopping off the bpj to get the original binaries rather than the saved
           project files. *)
        file
        |> String.chop_suffix_exn ~suffix:".bpj"
        |> Symbol.get_symbols
      in
      let syms_orig = get_symbols file1 in
      let syms_mod = get_symbols file2 in
      Symbol.offset_constraint ~orig:syms_orig ~modif:syms_mod ctx
    else
      fun addr -> addr

  (* Generate the exp_conds for the original binary based on the flags passed in
     from the CLI. Generating the memory offsets requires the environment of
     the modified binary. *)
  let exp_conds_orig (opts : options) (env_mod : Env.t) (file1 : string) (file2 : string)
    : Env.exp_cond list =
    let ctx = Env.get_context env_mod in
    let offsets =
      get_mem_offsets ctx opts file1 file2
      |> Pre.mem_read_offsets env_mod
    in
    if opts.find_null_derefs then
      [Pre.non_null_load_assert; Pre.non_null_store_assert; offsets]
    else
      [offsets]

  (* Generate the exp_conds for the modified binary based on the flags passed in
     from the CLI. *)
  let exp_conds_mod (opts : options) : Env.exp_cond list =
    if opts.find_null_derefs then
      [Pre.non_null_load_vc; Pre.non_null_store_vc]
    else
      []

  let single (ctx : Z3.context) (var_gen : Env.var_gen) (file : string) (func : string)
      (opts : options) : Constr.t * Env.t * Env.t =
    let proj = Utils.load_proj Utils.loader file in
    let arch = Project.arch proj in
    let subs = proj |> Project.program |> Term.enum sub_t in
    let main_sub = Utils.find_func_err subs func in
    let to_inline = Utils.match_inline opts.inline subs in
    let exp_conds = exp_conds_mod opts in
    let env = Pre.mk_env ctx var_gen ~subs ~arch ~to_inline
        ~use_fun_input_regs:opts.use_constant_chaosing ~exp_conds in
    (* call visit sub with a dummy postcondition to fill the
       environment with variables *)
    let true_constr = Env.trivial_constr env in
    let _, env = Pre.visit_sub env true_constr main_sub in
    (* Remove the constants generated and stored in the environment because they aren't
       going to be used in the wp analysis. *)
    let env = Env.clear_consts env in
    let hyps, env = Pre.init_vars (Pre.get_vars env main_sub) env in
    let hyps = (Pre.set_sp_range env) :: hyps in
    let post =
      if String.is_empty opts.postcond then
        true_constr
      else
        Z3_utils.mk_smtlib2_single env opts.postcond
    in
    let pre, env = Pre.visit_sub env post main_sub in
    let pre = Constr.mk_clause [Z3_utils.mk_smtlib2_single env opts.precond] [pre] in
    let pre = Constr.mk_clause hyps [pre] in
    Format.printf "\nSub:\n%s\nPre:\n%a\n%!"
      (Sub.to_string main_sub) Constr.pp_constr pre;
    (pre, env, env)

  let comparative
      (ctx : Z3.context)
      (var_gen : Env.var_gen)
      (file1 : string)
      (file2 : string)
      (func : string)
      (opts : options)
    : Constr.t * Env.t * Env.t =
    let proj1 = Utils.load_proj Utils.loader file1 in
    let proj2 = Utils.load_proj Utils.loader file2 in
    let prog1 = Project.program proj1 in
    let prog2 = Project.program proj2 in
    let arch1 = Project.arch proj1 in
    let arch2 = Project.arch proj2 in
    let () =
      if not @@ Arch.equal arch1 arch2 then
        failwith (Utils.diff_arch_msg arch1 arch2)
    in
    let subs1 = Term.enum sub_t prog1 in
    let subs2 = Term.enum sub_t prog2 in
    let main_sub1 = Utils.find_func_err subs1 func in
    let main_sub2 = Utils.find_func_err subs2 func in
    let env2 =
      let to_inline2 = Utils.match_inline opts.inline subs2 in
      let exp_conds2 = exp_conds_mod opts in
      let env2 = Pre.mk_env ctx var_gen ~subs:subs2 ~arch:arch2 ~to_inline:to_inline2
          ~use_fun_input_regs:opts.use_constant_chaosing ~exp_conds:exp_conds2 in
      let env2 = Env.set_freshen env2 true in
      let _, env2 = Pre.init_vars (Pre.get_vars env2 main_sub2) env2 in
      env2
    in
    let env1 =
      let to_inline1 = Utils.match_inline opts.inline subs1 in
      let exp_conds1 = exp_conds_orig opts env2 file1 file2 in
      let env1 = Pre.mk_env ctx var_gen ~subs:subs1 ~arch:arch1 ~to_inline:to_inline1
          ~use_fun_input_regs:opts.use_constant_chaosing ~exp_conds:exp_conds1 in
      let _, env1 = Pre.init_vars (Pre.get_vars env1 main_sub1) env1 in
      env1
    in
    let posts, hyps =
      comparators_of_options ~orig:(main_sub1, env1) ~modif:(main_sub2, env2) opts
    in
    let pre, env1, env2 =
      Comp.compare_subs ~postconds:posts ~hyps:hyps
        ~original:(main_sub1, env1) ~modified:(main_sub2, env2)
    in
    Format.printf "\nComparing\n\n%s\nand\n\n%s\n%!"
      (Sub.to_string main_sub1) (Sub.to_string main_sub2);
    (pre, env1, env2)

  let run files func options =
    let ctx = Env.mk_ctx () in
    let var_gen = Env.mk_var_gen () in
    let solver = Z3.Solver.mk_simple_solver ctx in
    Utils.update_default_num_unroll options.loop_unroll;
    let pre, env1, env2 =
      (* Determine whether to perform a single or comparative analysis. *)
      match files with
      | [file] -> single ctx var_gen file func options
      | [file1; file2] -> comparative ctx var_gen file1 file2 func options
      | fs -> Format.printf "%s\n%!" (Utils.invalid_file_count_msg fs); exit 1
    in
    let result = Pre.check ~print_constr:options.print_constr solver ctx pre in
    let () = match options.gdb_filename with
      | None -> ()
      | Some f -> Output.output_gdb solver result env2 ~func:func ~filename:f in
    let () = match options.bildb_output with
      | None -> ()
      | Some f -> Output.output_bildb solver result env2 f in
    Output.print_result solver result pre ~print_path:options.print_paths
      ~orig:env1 ~modif:env2

end

module Cli = struct

  let name = "wp"

  let doc = "CBAT is a comparative analysis tool. It can compare two binaries \
             and check that they behave in the same way. It can also be used \
             to check a single binary for certain behaviors."

  (* Mandatory arguments. *)
  let files = Cmd.arguments Typ.file
      ~doc:"Path(s) to one or two binaries to analyze. If two binaries are \
            specified, WP will run a comparative analysis."

  let func = Cmd.parameter (Typ.some Typ.string) "func"
      ~doc:"Function to run the wp analysis on. If no function is specified or \
            the function cannot be found in the binary, the analysis should \
            fail."

  (* Arguments that determine which properties CBAT should analyze. *)
  let precond = Cmd.parameter Typ.string "precond"
      ~doc:"Precondition in SMT-LIB format that will be used as a hypothesis \
            to the precondition calculated during the WP analysis. If no \
            precondition is specified, a trivial precondition of `true' will \
            be used."

  let postcond = Cmd.parameter Typ.string "postcond"
      ~doc:"Postcondition in SMT-LIB format. This is the postcondition that \
            will be used to calculate the weakest precondition. If no \
            postcondition is specified, a trivial postcondition of `true' will \
            be used."

  let find_null_derefs = Cmd.flag "find-null-derefs"
      ~doc:"If set, CBAT will check for inputs that would result in a null \
            dereferencing. In the case of a comparative analysis, CBAT checks \
            for inputs that would cause a null dereference in the modified \
            binary, assuming that the same dereference in the original \
            binary is not a null dereference."

  let compare_func_calls = Cmd.flag "compare-function-calls"
      ~doc:"This flag only works on two binaries, so /path/to/exe1 and \
            /path/to/exe2 must be provided. If present, this flag checks the \
            function calls that occur in both binaries. If a function is not \
            called in the original binary, CBAT checks if the same functon \
            is also not invoked in the modified binary."

  let compare_final_reg_values =
    Cmd.parameter (Typ.list Typ.string) "compare-final-reg-values"
      ~doc:"This flag only works on two binaries, so /path/to/exe1 and \
            /path/to/exe2 must be provided. If this option is set, CBAT \
            will compare the final values stored in the specified registers at \
            the end of the function's execution."

  (* Options. *)
  let loop_unroll = Cmd.parameter (Typ.some Typ.int) "loop-unroll"
      ~doc:"Amount of times to unroll each loop. By default, CBAT will unroll \
            each loop 5 times."

  let print_paths = Cmd.flag "print-paths"
      ~doc:"If set, prints out the execution path that results in a refuted \
            goal and the register values at each branch in the path. The path \
            contains information about whether a branch has been taken and the \
            address of the branch if found."

  let inline = Cmd.parameter (Typ.some Typ.string) "inline"
      ~doc:"Functions to inline at a function call site  as specified by a \
            POSIX regular expression on the name of the target function. \
            If not inlined, summaries are used at function call time. The \
            to inline all function calls is `.*'. For example, `foo|bar' will \
            inline the functions `foo' and `bar'."

  let gdb_filename = Cmd.parameter (Typ.some Typ.string) "gdb-filename"
      ~doc:"In the case CBAT determines input registers that result in a \
            refuted goal, this flag outputs gdb script to the filename \
            specified. This script sets a breakpoint at the the start of the \
            function being analyzed, and sets the registers and memory to the \
            values specified in the countermodel."

  let bildb_output = Cmd.parameter (Typ.some Typ.string) "bildb-output"
      ~doc:"In the case CBAT determins input registers that result in a refuted \
            goal, this flag outputs a BilDB YAML file to the filename specified. \
            This file sets the registers and memory to the values specified in the \
            countermodel found during WP analysis, allowing BilDB to follow the \
            same execution trace."

  let use_constant_chaosing = Cmd.flag "use-constant-chaosing"
      ~doc:"If set, CBAT will make all chaosed functions return a constant \
            (chaosed) value. This flag has no effect on nondeterministic \
            functions."

  let mem_offset = Cmd.flag "mem-offset"
      ~doc:"If set, maps the symbols in the data and bss sections from their \
            addresses in the original binary to their addresses in the \
            modified binary. This flag is still experimental."

  let print_constr = Cmd.parameter (Typ.list Typ.string) "print-constr"
      ~as_flag:["internal"; "smtlib"]
      ~doc:"If set, the preconditions and Z3's SMT-LIB 2 are both printed. One \
            or both outputs can be explicitly called with the respective names \
            internal and smtlib, which will print only what is stated. Both \
            can also be called like --wp-print-constr=internal,smtlib. If the \
            flag is not called, it defaults to printing neither."

  let grammar = Cmd.(
      args
      $ func
      $ precond
      $ postcond
      $ find_null_derefs
      $ compare_func_calls
      $ compare_final_reg_values
      $ loop_unroll
      $ print_paths
      $ inline
      $ gdb_filename
      $ bildb_output
      $ use_constant_chaosing
      $ mem_offset
      $ print_constr
      $ files)

  let missing_func_msg = "Function is not provided for analysis."

  (* Ensures the user inputted a function for analysis. *)
  let check_func (func : string option) : string =
    match func with
    | Some f -> f
    | None -> Format.printf "%s\n%!" missing_func_msg; exit 1

  let callback
      (func : string option)
      (precond : string)
      (postcond : string)
      (find_null_derefs : bool)
      (compare_func_calls : bool)
      (compare_final_reg_values : string list)
      (loop_unroll : int option)
      (print_paths : bool)
      (inline : string option)
      (gdb_filename : string option)
      (bildb_output : string option)
      (use_constant_chaosing : bool)
      (mem_offset : bool)
      (print_constr : string list)
      (files : string list)
      (_ : ctxt)
    =
    let func = check_func func in
    let options = Analysis.(
        {
          precond = precond;
          postcond = postcond;
          find_null_derefs = find_null_derefs;
          compare_func_calls = compare_func_calls;
          compare_final_reg_values = compare_final_reg_values;
          loop_unroll = loop_unroll;
          print_paths = print_paths;
          inline = inline;
          gdb_filename = gdb_filename;
          use_constant_chaosing = use_constant_chaosing;
          mem_offset = mem_offset;
          print_constr = print_constr
        })
    in
    Analysis.run files func options;
    Ok ()

end

let () =
  Cmd.declare Cli.name Cli.grammar Cli.callback ~doc:Cli.doc
