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
open Bap.Std
open Bap_wp
include Self()

module Cmd = Bap_main.Extension.Command
module Typ = Bap_main.Extension.Type

module Comp = Compare
module Pre = Precondition
module Env = Environment
module Constr = Constraint

type flags =
  {
    compare: bool;
    file1 : string;
    file2 : string;
    func : string;
    check_calls : bool;
    inline : string option;
    pre_cond : string;
    post_cond : string;
    num_unroll : int option;
    output_vars : string list;
    gdb_filename : string option;
    bildb_output : string option;
    print_path : bool;
    use_fun_input_regs : bool;
    mem_offset : bool;
    check_null_deref : bool;
    print_constr : string list;
  }

let missing_func_msg (func : string) : string =
  Format.sprintf "Missing function: %s is not in binary." func

let diff_arch_msg (arch1 : Arch.t) (arch2 : Arch.t) : string =
  Format.sprintf "Binaries are of two different architectures: %s vs %s"
    (Arch.to_string arch1) (Arch.to_string arch2)

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

(* If an offset is specified, generates a function of the address of a memory read in
   the original binary to the address plus an offset in the modified binary. *)
let get_mem_offsets (ctx : Z3.context) (flags : flags)
  : Constr.z3_expr -> Constr.z3_expr =
  if flags.mem_offset then
    let get_symbols file =
      (* Chopping off the bpj to get the original binaries rather than the saved
         project files. *)
      file
      |> String.chop_suffix_exn ~suffix:".bpj"
      |> Symbol.get_symbols
    in
    let syms_orig = get_symbols flags.file1 in
    let syms_mod = get_symbols flags.file2 in
    Symbol.offset_constraint ~orig:syms_orig ~modif:syms_mod ctx
  else
    fun addr -> addr

(* Generate the exp_conds for the original binary based on the flags passed in
   from the CLI. Generating the memory offsets requires the environment of
   the modified binary. *)
let exp_conds_orig (flags : flags) (env_mod : Env.t) : Env.exp_cond list =
  let ctx = Env.get_context env_mod in
  let offsets =
    get_mem_offsets ctx flags
    |> Pre.mem_read_offsets env_mod
  in
  if flags.check_null_deref then
    [Pre.non_null_load_assert; Pre.non_null_store_assert; offsets]
  else
    [offsets]

(* Generate the exp_conds for the modified binary based on the flags passed in
   from the CLI. *)
let exp_conds_mod (flags : flags) : Env.exp_cond list =
  if flags.check_null_deref then
    [Pre.non_null_load_vc; Pre.non_null_store_vc]
  else
    []

let analyze_proj (ctx : Z3.context) (var_gen : Env.var_gen) (proj : project)
    (flags : flags) : Constr.t * Env.t * Env.t =
  let arch = Project.arch proj in
  let subs = proj |> Project.program |> Term.enum sub_t in
  let main_sub = find_func_err subs flags.func in
  let to_inline = match_inline flags.inline subs in
  let exp_conds = exp_conds_mod flags in
  let env = Pre.mk_env ctx var_gen ~subs ~arch ~to_inline
      ~use_fun_input_regs:flags.use_fun_input_regs ~exp_conds in
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
    if String.is_empty flags.post_cond then
      true_constr
    else
      Z3_utils.mk_smtlib2_single env flags.post_cond
  in
  let pre, env = Pre.visit_sub env post main_sub in
  let pre = Constr.mk_clause [Z3_utils.mk_smtlib2_single env flags.pre_cond] [pre] in
  let pre = Constr.mk_clause hyps [pre] in
    (* Print statement for constraint-style prover output: *)
    Format.printf "\nSub:\n%s\nPre:\n%!" (Sub.to_string main_sub);
  (pre, env, env)

let check_calls (flag : bool) : (Comp.comparator * Comp.comparator) option =
  if flag then
    Some Comp.compare_subs_fun
  else
    None

let output_vars
    (flag : string list)
    ~orig:(sub1, env1 : Sub.t * Env.t)
    ~modif:(sub2, env2 : Sub.t * Env.t)
  : (Comp.comparator * Comp.comparator) option =
  if List.is_empty flag then
    None
  else begin
    let input = Var.Set.union
        (Pre.get_vars env1 sub1) (Pre.get_vars env2 sub2) in
    let output = Var.Set.union
        (Pre.get_output_vars env1 sub1 flag)
        (Pre.get_output_vars env2 sub2 flag) in
    debug "Input: %s%!" (varset_to_string input);
    debug "Output: %s%!" (varset_to_string output);
    Some (Comp.compare_subs_eq ~input ~output)
  end

let smtlib
    ~post_cond:(post_cond : string)
    ~pre_cond:(pre_cond : string)
  : (Comp.comparator * Comp.comparator) option =
  if String.is_empty post_cond && String.is_empty pre_cond then
    None
  else
    Some (Comp.compare_subs_smtlib ~smtlib_post:post_cond ~smtlib_hyp:pre_cond)

let sp (arch : Arch.t) : (Comp.comparator * Comp.comparator) option =
  match arch with
  | `x86_64 -> Some Comp.compare_subs_sp
  | _ ->
    error "CBAT can only generate hypotheses about the stack pointer and \
           memory for the x86_64 architecture.\n%!";
    None

(* Returns a list of postconditions and a list of hypotheses based on the flags
   set from the command line. *)
let comparators_of_flags
    ~orig:(sub1, env1 : Sub.t * Env.t)
    ~modif:(sub2, env2 : Sub.t * Env.t)
    (flags : flags)
  : Comp.comparator list * Comp.comparator list =
  let arch = Env.get_arch env1 in
  let comps =
    [ check_calls flags.check_calls;
      output_vars flags.output_vars ~orig:(sub1, env1) ~modif:(sub2, env2);
      smtlib ~post_cond:flags.post_cond ~pre_cond:flags.pre_cond;
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

let compare_projs (ctx : Z3.context) (var_gen : Env.var_gen) (proj : project)
    (flags : flags) : Constr.t * Env.t * Env.t =
  let prog1 = Program.Io.read flags.file1 in
  let prog2 = Program.Io.read flags.file2 in
  (* Currently using the dummy binary's project to determine the architecture
     until we discover a better way of determining the architecture from a program. *)
  let arch = Project.arch proj in
  let subs1 = Term.enum sub_t prog1 in
  let subs2 = Term.enum sub_t prog2 in
  let main_sub1 = find_func_err subs1 flags.func in
  let main_sub2 = find_func_err subs2 flags.func in
  let env2 =
    let to_inline2 = match_inline flags.inline subs2 in
    let exp_conds2 = exp_conds_mod flags in
    let env2 = Pre.mk_env ctx var_gen ~subs:subs2 ~arch:arch ~to_inline:to_inline2
        ~use_fun_input_regs:flags.use_fun_input_regs ~exp_conds:exp_conds2 in
    let env2 = Env.set_freshen env2 true in
    let _, env2 = Pre.init_vars (Pre.get_vars env2 main_sub2) env2 in
    env2
  in
  let env1 =
    let to_inline1 = match_inline flags.inline subs1 in
    let exp_conds1 = exp_conds_orig flags env2 in
    let env1 = Pre.mk_env ctx var_gen ~subs:subs1 ~arch:arch ~to_inline:to_inline1
        ~use_fun_input_regs:flags.use_fun_input_regs ~exp_conds:exp_conds1 in
    let _, env1 = Pre.init_vars (Pre.get_vars env1 main_sub1) env1 in
    env1
  in
  let posts, hyps =
    comparators_of_flags ~orig:(main_sub1, env1) ~modif:(main_sub2, env2) flags
  in
  let pre, env1, env2 =
    Comp.compare_subs ~postconds:posts ~hyps:hyps
      ~original:(main_sub1, env1) ~modified:(main_sub2, env2)
  in
  Format.printf "\nComparing\n\n%s\nand\n\n%s\n%!"
    (Sub.to_string main_sub1) (Sub.to_string main_sub2);
  (pre, env1, env2)

let should_compare (f : flags) : bool =
  f.compare || ((not @@ String.is_empty f.file1) && (not @@ String.is_empty f.file2))

let main (flags : flags) (proj : project) : unit =
  let ctx = Env.mk_ctx () in
  let var_gen = Env.mk_var_gen () in
  let solver = Z3.Solver.mk_simple_solver ctx in
  update_default_num_unroll flags.num_unroll;
  let pre, env1, env2 =
    if should_compare flags then
      compare_projs ctx var_gen proj flags
    else
      analyze_proj ctx var_gen proj flags
  in
  let result = Pre.check ~print_constr:flags.print_constr solver ctx pre  in
  let () = match flags.gdb_filename with
    | None -> ()
    | Some f -> Output.output_gdb solver result env2 ~func:flags.func ~filename:f in
  let () = match flags.bildb_output with
    | None -> ()
    | Some f -> Output.output_bildb solver result env2 f in
  Output.print_result solver result pre ~print_path:flags.print_path
    ~orig:env1 ~modif:env2

module Analysis = struct

  type t =
    | Single
    | Comparative

  let single () =
    printf "Single!\n%!"

  let comparative () =
    printf "Compare!\n%!"

  let run () =
    printf "Running analysis\n%!"

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

  let find_null_deref = Cmd.flag "find-null-deref"
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
      $ find_null_deref
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

  let invalid_file_count_msg count =
    Format.sprintf "CBAT can only analyze one binary for a single analysis or \
                    two binaries for a comparative analysis. Number of \
                    binaries provided: %d." count

  (* Ensures the user inputted a function for analysis. *)
  let check_func (func : string option) : string =
    match func with
    | Some f -> f
    | None -> Format.printf "%s\n%!" missing_func_msg; exit 1

  (* Determines whether CBAT should perform a single or comparative analysis. *)
  let analysis_type (files : string list) : Analysis.t =
    match List.length files with
    | 1 -> Single
    | 2 -> Comparative
    | n -> Format.printf "%s\n%!" (invalid_file_count_msg n); exit 1

  let callback
      func
      precond
      postcond
      find_null_deref
      compare_func_calls
      compare_final_reg_values
      loop_unroll
      print_paths
      inline
      gdb_filename
      bildb_output
      use_constant_chaosing
      mem_offset
      print_constr
      files
      _
    =
    (* Check the user has provided the proper arguments. *)
    let func = check_func func in
    let analysis = analysis_type files in
    begin
      match analysis with
      | Single -> Analysis.single_analysis ()
      | Comparative -> Analysis.comparative_analysis ()
    end;
    Ok ()

end

let () =
  Cmd.declare Cli.name Cli.grammar Cli.callback ~doc:Cli.doc

(*********)


let () = when_ready (fun {get=(!!)} ->
    let flags =
      {
        compare = !!compare;
        file1 = !!file1;
        file2 = !!file2;
        func = !!func;
        check_calls = !!check_calls;
        inline = !!inline;
        pre_cond = !!pre_cond;
        post_cond = !!post_cond;
        num_unroll = !!num_unroll;
        output_vars = !!output_vars;
        gdb_filename = !!gdb_filename;
        bildb_output = !!bildb_output;
        print_path = !!print_path;
        use_fun_input_regs = !!use_fun_input_regs;
        mem_offset = !!mem_offset;
        check_null_deref = !!check_null_deref;
        print_constr = !!print_constr
      }
    in
    Project.register_pass' @@
    main flags
  )

let () = manpage [
    `S "DESCRIPTION";
    `P "Computes the weakest precondition of a subroutine given a postcondition."
  ]
end
