(* test int int map backed by a file *)

open Int_int_store

let (s,r) = S_int_int.existing_file_to_new_store "/tmp/filestore.b1"

let (s',r') = T.Insert.insert 1 2 r s

let main () = 
  let (s,r) = (ref s,ref r) in
  let xs = ref (Batteries.(1 -- 1000 |> List.of_enum)) in
  while (!xs <> []) do
    let x = List.hd !xs in
    let (s',r') = T.Insert.insert x (2*x) !r !s in
    s:=s';r:=r';xs:=List.tl !xs
  done;
  S_int_int.ST.sync !s;
  ()

let main_2 () = 
  let s0 = ref (r,s,Map_int.empty) in
  let xs = ref (Batteries.(1 -- 1000 |> List.of_enum)) in
  while (!xs <> []) do
    let x = List.hd !xs in
    let s0' = Int_int_cached.Insert.insert x (2*x) !s0 in
    s0:=s0';xs:=List.tl !xs
  done;
  s0:=Int_int_cached.sync !s0;
  ()


let _ = print_endline "test_ii"; main_2 ()




(* 

2016-12-06 no cache:

$ ocaml $ time ./test_ii.native
test_ii

real	1m35.895s
user	1m35.068s
sys	0m0.900s

LRU read cache is much the same

--

2016-12-08 with reasonable splitting:

timings with reasonable splitting:
$ ocaml $ time ./test_ii.native
test_ii

real	0m22.850s
user	0m22.796s
sys	0m0.072s

size of store: 12288 bytes = 3 blocks as expected

--

2016-12-09 with high-level cache and insert_many

$ ocaml $ time ./test_ii.native
test_ii

real	0m0.096s
user	0m0.092s
sys	0m0.004s



*)
