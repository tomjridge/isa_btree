# isa_btree: Isabelle formalization of B-tree correctness

## Description

This repository contains Isabelle definitions of the main B-tree operations, together with an OCaml version of the definitions wrapped in an OCaml library.

## Quick links

* The tjr_btree OCaml library can be found at <https://github.com/tomjridge/tjr_btree>
* The online ocamldoc documentation can be found [here](http://tomjridge.github.io/isa_btree/ocamldoc). The main module is Isa_export_wrapper. See also the docs directory. A pdf rendering (likely out-of-date) of the ocamldoc for the Isa_export_wrapper module can be found in [here](docs/isa_export_wrapper.pdf).


## Main directories

* docs: documentation, including ocamldoc and Isabelle-generated html (likely out of date)
* src: the Isabelle sources
* ocaml: the OCaml wrapper around the Isabelle-generated code. The main OCaml code can be found in `ocaml/isa_export_wrapper.ml`.


## Dependencies (for OCaml code)

| Dependency                  | Comment                                           |
| -------------------         | ------------------------------------------------- |
| num                         | isa exported code uses Big_int                    |
| yojson, ppx_deriving_yojson |                                                   |
| tjr_fs_shared               | shared lib                                        |
|                             |                                                   |



## Compile-time configuration

Profiling is controlled by ppx_optcomp, a config file
"/tmp/optcomp_config.ml", and file "profilers.ml". By default,
profiling is disabled (?). To enable, you have to edit this config
file.
