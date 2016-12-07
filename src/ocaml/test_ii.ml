(* test int int map backed by a file *)

open Int_int_store

let (s,r) = S_int_int.existing_file_to_new_store "/tmp/filestore.b1"

let (s',r') = T.Insert.insert 1 2 r s

let main () = 
  let (s,r) = (ref s,ref r) in
  let xs = ref (Batteries.(0 -- 1000 |> List.of_enum)) in
  while (!xs <> []) do
    let x = List.hd !xs in
    let (s',r') = T.Insert.insert x (2*x) !r !s in
    s:=s';r:=r';xs:=List.tl !xs
  done;
  S_int_int.ST.sync !s;
  ()

let _ = print_endline "test_ii"; main ()




(* 

2016-12-06 no cache:

$ ocaml $ time ./test_ii.native
test_ii

real	1m35.895s
user	1m35.068s
sys	0m0.900s

LRU read cache is much the same


*)
