SHELL:=bash

index.txt: FORCE
	(for f in */*.thy; do echo "$$f ========================================"; grep "\------" $$f; echo; done)>$@


FORCE:
