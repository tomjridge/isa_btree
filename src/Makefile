SHELL:=bash

index.txt: FORCE
	(for f in */*.thy; do echo "$$f ========================================"; tweak_comments.native $$f; grep "\------" $$f; echo; done)>$@


doc: FORCE
	-isabelle build -o browser_info -v -D .  # fails, see NOTE 1
	isabelle document -o pdf -n document -t '' output/document 2>&1
	echo # NOTE output in output/document.pdf

# NOTE 1 - this fails because of splitarray command not found (but it
# should be... it is in the path, but perhaps subshells aren't
# inheriting the right env), so next line is manually invoking
# isabelle document
#
# Also html likely in dir like ~/.isabelle/Isabelle2015/browser_info/Unsorted/isa_btree

FORCE:
