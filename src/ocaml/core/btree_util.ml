(* general util stuff ---------------------------------------- *)

module Set_int = Set.Make(struct type t = int let compare: t -> t -> int = Pervasives.compare end)

module Map_int = Map.Make(struct type t = int let compare: t -> t -> int = Pervasives.compare end)


let dest_Ok x = Our.Util.(
  match x with
  | Ok y -> y
  | _ -> failwith "dest_Ok")



(* various marshalling stuff ---------------------------------------- *)

(* basic mappings; various implementations in ext_convs *)
type ('a,'b) conv = {
  m: 'a -> 'b;
  u: 'b -> 'a
}


let (%) f g = fun x -> f(g(x))


let conv_compose (f:('b,'c) conv) (g:('a,'b)conv) = {
  m = f.m % g.m;
  u = g.u % f.u;
}

let _ = conv_compose

(* Marshal to/from byte list *)
module M_byte_list = struct

  module Byte = struct type t = char end

  type m_t = Byte.t list

  type 'a cnv = ('a,m_t) conv

  module X = struct
   
    let i' : int32 cnv = Int32.{
        m = (fun i0 -> 
            let arr = Array.make 4 (Char.chr 0) in
            for j = 0 to 3 do 
              let off = j in
              let c = (shift_right i0 (8*j)) |> logand (of_int 255) in
              arr.(off) <- (c|>to_int|>Char.chr)
            done;
            [arr.(0);arr.(1);arr.(2);arr.(3)]);
        u = (fun bs -> 
            assert (List.length bs = 4);
            let arr = Array.of_list bs in
            let i = ref (Int32.of_int 0) in
            for j = 0 to 3 do
              let off = j in
              let c = shift_left (arr.(off)|>Char.code|>Int32.of_int) off in
              i:=(logor !i c)
            done;
            !i)
      }

    
    let i32 : int32 cnv = {
      m = (fun x -> 
          Test.test (fun _ -> assert (x|>i'.m|>i'.u = x));
          x|>i'.m);
      u = (fun x -> 
          Test.test (fun _ -> assert (x|>i'.u|>i'.m = x));
          x|>i'.u)
    }
          

    let i32s : int32 list cnv = {
      m = (fun is ->
          is|>List.map i32.m|>List.concat);
      u = (fun bs ->
          bs|>BatList.ntake 4|>List.map i32.u)
    }


  end

end


(* marshall to/from bytes, via M_byte_list *)
module M_bytes = struct

  type m_t = bytes (* marshall target type *)
  (* for marshalling, we marshall to int32 rather than bytes;
       slightly less efficient, but good enough *)

  type 'a cnv = ('a,m_t) conv

  let bs_to_bytes : (char list,bytes) conv = {
    m = (fun cs -> cs|>BatString.implode|>Bytes.of_string);
    u = (fun bs -> bs|>Bytes.to_string|>BatString.explode)
  }

  module X = struct

    let i32s : int32 list cnv = conv_compose bs_to_bytes M_byte_list.X.i32s 

  end

end


(* marshal to in32 list *)
module M_int32s = struct

  type m_t = int32 list (* marshall target type *)
  (* for marshalling, we marshall to int32 rather than bytes;
       slightly less efficient, but good enough *)


  type 'a cnv = ('a,m_t) conv


  (* where we know that the 'a fits in one i_t; FIXME used? *)
      (*
  type 'a conv1 = {
    m1: 'a -> i_t;
    u1: i_t -> 'a
  } *)

  module X = struct 

    let i : int cnv = {
      m = (fun x -> [Int32.of_int x]);
      u = (function [i] -> Int32.to_int i)
    }

    let s : string cnv = {
      m = (fun s -> 
          s|> BatString.explode|>BatList.ntake 4
          (* list of [a;b;c;d] chars *)
          |> List.map M_byte_list.X.i32.u);
      u = (fun is -> 
          is|>List.map M_byte_list.X.i32.m
          |>List.concat
          |>BatString.implode
        )     
    }


  end

end



(* import from Our ---------------------------------------- *)

include Our.Util
