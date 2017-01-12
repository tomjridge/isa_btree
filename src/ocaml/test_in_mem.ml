(* in-mem testing ---------------------------------------- *)

let failwith x = failwith ("test_in_mem: "^x)

(* we concentrate on relatively small parameters *)


(* setup ---------------------------------------- *)

open Btree

module Map_int = Map.Make(
  struct type t = int let compare: t -> t -> int = Pervasives.compare end)

module C : CONSTANTS = struct
  let max_leaf_size = 5
  let max_node_keys = 5
  let min_leaf_size = 2
  let min_node_keys = 2
end


module KV (* : KEY_VALUE_TYPES *) = struct 
  type key = int[@@deriving yojson]
  type value_t = int[@@deriving yojson]
  let key_ord k1 k2 = Pervasives.compare k1 k2
  let equal_value = (=)
end

module PR = struct 
  type page_ref = int[@@deriving yojson]
end

module FT = struct

  open KV
  open PR

  type pframe =  
      Node_frame of (key list * page_ref list) |
      Leaf_frame of (key * value_t) list[@@deriving yojson]

  type page = pframe[@@deriving yojson]

  let frame_to_page : pframe -> page = fun x -> x
  let page_to_frame : page -> pframe = fun x -> x

end

module ST' = struct

  open FT
  open PR

  type page = FT.page

  type store = {free:int; m:page Map_int.t}

  (* for yojson *)
  type store' = {free':int; m':(int * page) list}[@@deriving yojson]

  let store_to_' s = {free'=s.free; m'=s.m|>Map_int.bindings}

  type store_error = unit

  let dest_Store : store -> page_ref -> page = (fun s r -> Map_int.find r s.m)

  let page_ref_to_page r s = (s,Our.Util.Ok(Map_int.find r s.m))

  let alloc p s = (
    let f = s.free in
    ({free=(f+1);m=Map_int.add f p s.m}),Our.Util.Ok(f))

  let free :
    page_ref list -> store -> store * (unit, store_error) Our.Util.rresult = (
    fun ps s -> (s,Our.Util.Ok(())))


  (* for empty store, we want an empty leaf at page 0 *)
  (*
  let empty_store () = (
    {free=1;m=Map_int.empty |> Map_int.add 0 (Leaf_frame[])},
    0)
  *)  
end

module ST (* : STORE *) = struct
  include PR
  include ST'
end

module S (* : Btree.S *) = struct

  module C = C

  module KV = KV

  module ST = ST

  module FT = FT


end

module BT = Btree.Make(S)

open BT.M


(* state type for testing ---------------------------------------- *)
module Test_state = struct 
    type t = {t:Tree.tree;s:Store.store;r:Store.page_ref }

    (* we want to ignore the store and page_ref *)
    let compare (x:t) (y:t) = (Pervasives.compare (x.t) (y.t))
end


(* for maintaing a set of states *)
module Test_state_set = Set.Make(Test_state)


type action = Insert of int | Delete of int


(* we have a set of states s that we have already generated; 
   we have a set of states todo that we need to process; 
   for each todo, we apply all possible actions; 
   any new states that result are stored in "todo"; *)

(* if we hit an exception, we want to know what the input tree was,
   and what the command was *)

(* FIXME remove *)
let (init_store, init_r) = (
  let open ST in
  let open FT in
  ({free=1;m=Map_int.empty |> Map_int.add 0 (Leaf_frame[])}, 0)
)

(* save so we know what the last action was *)
let action = ref (Insert 0) 

type range_t = int list[@@deriving yojson]



(* explore all possible states for the given range *)

let test range = (
  let s = ref Test_state.(Test_state_set.(singleton {t=Tree.Leaf[];s=init_store;r=init_r })) in
  let todo = ref (!s) in
  (* next states from a given tree *)
  let step t = (
    (range|>List.map (fun x -> action:=Insert x; 
                       BT.Insert.insert x x (t.Test_state.r) (t.Test_state.s))) @
    (range|>List.map (fun x -> action:=Delete x; 
                       BT.Delete.delete x (t.Test_state.r) (t.Test_state.s)))
  ) |> List.map (fun (s,r) -> Test_state.{t=(Frame.r_to_t s r) ;s;r}) |> Test_state_set.of_list
  in
  let _ = 
    (* FIXME this may be faster if we store todo as a list and check
       for membership when computing next state of the head of todo;
       use rev_append *)
    Printf.printf "test: starting while\n";
    while (not(Test_state_set.is_empty !todo)) do
      let nexts : Test_state_set.t list = !todo|>Test_state_set.elements|>List.map step in
      let next = List.fold_left (fun a b -> Test_state_set.union a b) Test_state_set.empty nexts in
      let new_ = Test_state_set.diff next !s in
      s:=Test_state_set.union !s new_;
      todo:=new_;
      print_string "."; flush_all ();
      ()
    done
  in
  Printf.printf "Tests passed; num states explored: %d\n" (Test_state_set.cardinal !s))


let main () = (  
    (* read stdin and convert to an int list range *)
    let _ = Printf.printf "test: reading input from stdin\n" in
    let js = Yojson.Safe.from_channel Pervasives.stdin in
    let _ = Printf.printf "test: read %s\n" (Yojson.Safe.to_string js) in
    let range = range_t_of_yojson js |> function Ok x -> x in
    test range
)

let test_insert () = (
  let r0 = ref init_r in
  let s0 = ref init_store in
  try (
  let xs = ref (Batteries.(1 -- 1000000 |> List.of_enum)) in
    while (!xs <> []) do
      let x = List.hd !xs in
      let (s0',r0') = BT.Insert.insert x (2*x) !r0 !s0 in
      s0:=s0';r0:=r0';xs:=List.tl !xs
    done;
  ) with _ -> (
      print_endline "Failure...";
      !s0|>ST'.store_to_'|>ST'.store'_to_yojson|>Yojson.Safe.to_string|>print_endline;
      ()
    );
    ()
)

let big () = 
  let range = Batteries.(0 -- 100 |> List.of_enum) in
  test range

let _ = 
  if 1 < Array.length Sys.argv then
    match Sys.argv.(1) with
    | "test" -> main() 
    | "big" -> big()
    | "insert" -> test_insert()
  else ()
                                                                         
