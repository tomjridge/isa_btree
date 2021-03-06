(** Exhaustively test the B-tree functionality, using a "correct"
   in-memory store. In this case, we use a "Tree store".

At the moment this takes constants from a config file, but perhaps we
   should test over a set of configs as well (just use the test code,
   parameterized by a config).

A previous version of the tests was fine-grained (each little step was
   tested). This just tests the big step.


We take 'r = tree. Then insert has type r -> k -> v -> (r option,'t)m

Here, we know that insert will always mutate, so we always get a Some.

We can also take ('a,t) m = 'a

*)

let _ = 
  Isa_export_wrapper.enable_isa_checks();
  Tjr_lib.Test.enable();
  ()

let with_logger f = 
    Logger.logger := Some (Tjr_lib.Log.mk_log_ops());
    Logger.at_exit ~print:true;
    Logger.log_lazy (fun _ -> "Logger initialized");
    f();
    Logger.at_exit ~print:false
    
let _ = 
  match List.tl (Array.to_list (Sys.argv)) with

  | ["exhaustive_deprecated"] -> begin
      with_logger (fun () -> 
          Printf.printf "%s: tests begin\n%!" __MODULE__;
          Test_exhaustive.config |> List.iter (fun pre_config -> 
              Test_exhaustive.test_exhaustive ~pre_config);
          Printf.printf "%s: tests OK\n%!" __MODULE__);
    end

  | ["test_exhaustive_2"] -> with_logger (fun () -> 
      Printf.printf "%s: tests begin\n%!" __MODULE__;
      Test_exhaustive_2.config |> List.iter (fun pre_config -> 
          Test_exhaustive_2.test_exhaustive ~pre_config);
      Printf.printf "%s: tests OK\n%!" __MODULE__)

  | ["test_leaf_impl"] -> 
    Leaf_node_frame_impls.Internal_leaf_impl.test_leaf_impl()

  | ["test_node_impl"] -> 
    with_logger (fun () -> Leaf_node_frame_impls.Internal_node_impl.test_node_impl())

  | ["test_delete"] -> 
    Test_delete.test()

  | ["test_insert_many"] -> 
    with_logger (fun () -> 
        List.iter Test_insert_all.test_insert_many Constants.all_constants)

  | ["test_insert_all"] -> 
    with_logger (fun () -> 
        List.iter Test_insert_all.test_insert_all Constants.all_constants)

  | ["test_seq_insert"] -> 
      with_logger (fun () -> Test_sequential_insert.test_seq_insert ())

  | ["test_polymap"] -> begin
      let open Test_spec in
      let rec loop n m = 
        n <= 0 |> function
        | true -> ()
        | false -> 
          spec_map_ops.add n n m |> fun m -> 
          loop (n-1) m
      in
      loop (int_of_float 1e7) spec_map_ops.empty
    end



(*  | ["no_asserts"] -> begin
      disable_isa_checks();
      disable_tests();  (* disable test flag *)
      run_tests()
    end*)
