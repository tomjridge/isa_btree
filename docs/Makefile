all: tmp.pdf


# NOTE --latex-engine will soon become --pdf-engine
#    --latex-engine=lualatex 
#
# graphics=true ensures that we use pandoc's graphics setup (which
# scales images nicely)
tmp.pdf: mk_latex.native isa_btree.md FORCE
	./mk_latex.native >tmp.md_with_latex
	pandoc --from=markdown+raw_tex --to=latex \
    --template=pandoc_latex_template.modified \
    --metadata=title:'Isabelle/HOL formalization of the B-tree datastructure' \
    --metadata=author:'Tom Ridge' \
    --metadata=date:'2017-12-05' \
    --number-sections \
    -V graphics=true \
    -V toc=true \
	  --standalone tmp.md_with_latex > tmp.tex
	lualatex tmp.tex

mk_latex.native: mk_latex.ml
	ocamlfind ocamlopt -package omacro -linkpkg -thread -o mk_latex.native mk_latex.ml

clean:
	rm -f tmp.*

FORCE:
