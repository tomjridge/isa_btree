(* test int int map backed by a file *)

open Btree_util
open Ext_int_int_store
open Int_int_filestore

let default_filename = "/tmp/store"


module Btree = Int_int_store.Btree_simple.Btree

module RM = Btree.Raw_map
module Sem = Btree_api.Sem

let run = Btree_api.State_monad.run

(* let ((s',r'),_) = MWE.insert 1 2 |> run (s,r) *)

module ST = Ext_int_int_store.ST
module FS = Int_int_filestore

let test_int_int_filestore range = 
  Printf.printf "%s, test_int_int_filestore, int map backed by recycling filestore, %d elts: " 
    __MODULE__ (List.length range);
  flush_all();
  let (s,r) = FS.from_file default_filename true true in
  let sr = ref (s,r) in
  let run = Sem.run_ref sr in
  let xs = ref range in
  while (!xs <> []) do
    print_string ".";
    let x = List.hd !xs in
    run (RM.insert x (2*x));
    xs:=List.tl !xs;
  done;
  print_newline ();
  (* FIXME check res? *)
  let (s,r) = !sr in
  let s = ref s in
  Sem.run_ref s (ST.sync ());
  Unix.close ((!s).fs.fd);
  ()

(* using int_int_cached ---------------------------------------- *)

let test_int_int_cached range = 
  Printf.printf "%s, test_int_int_cached, int map backed by recycling filestore and api cache, %d elts: " 
    __MODULE__ (List.length range);
  flush_all();
  let (s,r) = FS.from_file default_filename true true in
  let s0 = ref (r,s,Map_int.empty) in
  let run = Sem.run_ref s0 in
  let xs = ref range in
  while (!xs <> []) do
    print_string ".";
    let x = List.hd !xs in
    run (Int_int_cached.Insert.insert x (2*x));
    xs:=List.tl !xs
  done;
  print_newline ();
  (* FIXME should we check res in following? *)
  run (Int_int_cached.sync ());
  Unix.close ((!s0) |> (fun (x,y,z) -> y.fs.fd));
  ()



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
