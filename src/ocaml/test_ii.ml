(* test int int map backed by a file *)

open B1_filestore

let (s,r) = S.create "/tmp/filestore.b1"

let (s',r') = T.Insert.insert 1 2 r s

let main () = 
  let (s,r) = (ref s,ref r) in
  let xs = ref (Batteries.(0 -- 10 |> List.of_enum)) in
  while (!xs <> []) do
    let x = List.hd !xs in
    let (s',r') = T.Insert.insert x (2*x) !r !s in
    s:=s';r:=r';xs:=List.tl !xs
  done

let _ = print_endline "test_ii"; main ()


