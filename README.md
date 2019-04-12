# isa_btree: Isabelle formalization of B-tree correctness

## Description

This repository contains Isabelle definitions of the main B-tree operations, together with an OCaml version of the definitions wrapped in an OCaml library.

## Main directories

* docs: documentation, including ocamldoc and Isabelle-generated html (likely out of date)
* src: the Isabelle sources
* ocaml: the OCaml wrapper around the Isabelle-generated code. The main OCaml code can be found in `ocaml/isa_export_wrapper.ml`.

## Documentation

See the docs directory. A pdf rendering of the ocamldoc for the isa_export_wrapper.ml file can be found in [here](docs/isa_export_wrapper.pdf).

## Dependencies (for OCaml code)

| Dependency                  | Comment                                           |
| -------------------         | ------------------------------------------------- |
| num                         | isa exported code uses Big_int                    |
| yojson, ppx_deriving_yojson |                                                   |
| tjr_fs_shared               | shared lib                                        |
|                             |                                                   |

