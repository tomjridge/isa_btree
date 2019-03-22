SHELL:=bash

# run isabelle to export code ------------------------------------------

all:
	$(MAKE) build

# to complete export of code, make sure Isabelle processes the theory
# Export_code to the end
run_isabelle: 
	SRC=$$PWD isabelle jedit d_find_ins_del/Export_code.thy 

build:
	cd `realpath .` && SRC=$$PWD isabelle build -o quick_and_dirty=true -D .


# docs -----------------------------------------------------------------

# NOTE following just builds some text documentation/index. 

tweak_comments=/tmp/l/bin/tweak_comments.native

index.txt: FORCE
	(for f in */*.thy; do echo "$$f ========================================"; $(tweak_comments) $$f; grep "\------\\|ignore_definition" $$f; echo; done)>$@


html_doc: FORCE
	-cd `realpath .` && SRC=$$PWD isabelle build -o browser_info -v -D .  # currently fails to produce anything... FIXME why?

# html likely in dir like ~/.isabelle/Isabelle2018/browser_info/Unsorted/isa_btree ?


pdf_doc: FORCE
	isabelle document -o pdf -n document -t '' -d output/document 2>&1
	echo # NOTE output in output/document.pdf


tjr_list_files:
	find . -maxdepth 2 \( -name "*.thy" \) -a -not -path "*/old*" -not -name "tmp.md" | sort | munge_find_to_tree.py 

FORCE:
