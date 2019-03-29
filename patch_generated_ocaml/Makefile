SHELL:=/bin/bash

ORIG:=orig/isa_export.ml

PATCH:=isa_export.patch

# manually patched - just edit isa_export.ml in place
PATCHED:=patched/isa_export.ml

GENERATED_PATCHED:=patched/isa_export.ml

# * Generated code
#
# After isa export, there should be a file /tmp/isa_export.ml
#
# - Copy to ORIG
# - Try to apply patch: make generated_patched
# - If this fails, manually patch ORIG, output to PATCHED and remake patch; then make generated_patched again
#
# https://forums.anandtech.com/threads/best-practices-for-creating-patch-with-diff.2264468/

all: 
	echo "Need to make a particular target"
	false

patch: $(PATCH)

generated_patched: $(GENERATED_PATCHED)
	ocamlc -c -w -8-20 $(GENERATED_PATCHED) # check builds
	cp $(GENERATED_PATCHED) ../ocaml 

$(PATCH): $(ORIG) FORCE
	diff -u3 -p $(ORIG) $(PATCHED) >$@ 
# this fails if there are changes?

$(GENERATED_PATCHED): $(ORIG) FORCE
	-patch -i $(PATCH) $(ORIG) -o $@ 

FORCE:


# insert_with_mutation -------------------------------------------------

# There should be a file /tmp/insert_with_mutation.ml. Copy this file
# into this directory, then apply patch. Patch is minimal, so
# hopefully no need to regenerate often.

# diff -u3 -p insert_with_mutation.ml.orig insert_with_mutation.ml >insert_with_mutation.patch

insert_with_mutation.ml: /tmp/insert_with_mutation.ml FORCE
	cp $< $@.orig
	patch -i insert_with_mutation.patch $@.orig -o $@
	ocamlfind ocamlc -package tjr_monad -c -w -8 $@
	cp $@ ../ocaml
