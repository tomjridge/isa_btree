let tests = [
  (fun () -> Test_bytestore.main());

  (fun() -> Test_in_mem.(  (* ---------------------------------------- *)
       test Batteries.(0 -- 10 |> List.of_enum);
       (* test Batteries.(0 -- 100 |> List.of_enum); *)
       test_insert ()));



(*
let main () = (  
    (* read stdin and convert to an int list range *)
    let _ = Printf.printf "test: reading input from stdin\n" in
    let js = Yojson.Safe.from_channel Pervasives.stdin in
    let _ = Printf.printf "test: read %s\n" (Yojson.Safe.to_string js) in
    let range = range_t_of_yojson js |> function Ok x -> x in
    test range
)
*)



  (fun () -> Test_ii.(  (* ---------------------------------------- *)
    print_string "Test_ii"; 
    main ()))

]

(* FIXME also main2 *)



let _ = (
  match Array.to_list Sys.argv |> List.tl with
  | [] -> tests |> List.iter (fun f -> f ())

  (* run a particular test *)
  | [n] -> n|>int_of_string|> List.nth tests |> fun f -> f()
)
