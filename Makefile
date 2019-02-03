DUNE:=dune

build:
	$(DUNE) build @install

install:
	$(DUNE) install

uninstall:
	$(DUNE) uninstall

clean:
	$(DUNE) clean

doc: FORCE
	$(DUNE) build @doc

doc_install: doc
	rm -rf docs/ocamldoc/*
	cp -R _build/default/_doc/_html/* docs/ocamldoc

FORCE:
