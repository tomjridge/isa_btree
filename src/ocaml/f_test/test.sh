#!/usr/bin/env ocaml

(* #!/usr/bin/env OCAMLRUNPARAM=b ocaml - doesn't work for some reason - causes a hang  *)

#use "topfind";;
#require "bos.setup";;
#require "ppx_deriving";;
#require "ppx_deriving_yojson";;
#require "batteries";;
#load "btree.cma";;

let _ = print_endline "test.sh; you may want export OCAMLRUNPARAM=b"

let range = Batteries.(0 -- 8 |> List.of_enum)

let _ = Test.test range

;;

