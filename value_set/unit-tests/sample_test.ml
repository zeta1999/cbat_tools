(***************************************************************************)
(*                                                                         *)
(*  Copyright (C) 2018 The Charles Stark Draper Laboratory, Inc.           *)
(*                                                                         *)
(*  This file is provided under the license found in the LICENSE file in   *)
(*  the top-level directory of this project.                               *)
(*                                                                         *)
(*  This work is funded in part by ONR/NAWC Contract N6833518C0107.  Its   *)
(*  content does not necessarily reflect the position or policy of the US  *)
(*  Government and no official endorsement should be inferred.             *)
(*                                                                         *)
(***************************************************************************)

include Bap.Std
open OUnit2

(* The last argument of every test is a `ctx` argument. *)
let sample_test _ =
  let msg = "Hello world" in
  assert_bool msg (0 = 1)

(* Multiple tests can be mapped over test data. *)
let more_tests =

  (* Some data to test over. *)
  let data = [0; 1; 2; 3;] in

  (* For test results, it can be useful to have a unique test name. *)
  let test_name n = Printf.sprintf "Testing %d = 0" n in

  (* If the test fails, we want a useful message. *)
  let msg n = Printf.sprintf "%d does not equal 0" n in

  (* Here's an actual test function. The last argument is `ctx`. *)
  let is_zero n _ = 
    let msg' = msg n in
    assert_bool msg' (n = 0) in

  (* Map the test over the data, and flatten it to return it. *)
  let tests = List.map (fun n -> (test_name n)>::(is_zero n)) data in
  List.flatten [tests]

(* Note how single tests have two colons, 
 * and test families have three colons. *)
let all_tests =
  "sample tests">:::[
    "my sample">::sample_test;
    "more samples">:::more_tests;
  ]

(* These tests are loaded and executed by the 
 * main test declaration in `test.ml`. *)
