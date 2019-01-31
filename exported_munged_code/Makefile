SHELL:=/bin/bash

ORIG:=isa_export.ml.orig

PATCH:=isa_export.patch

# manually patched
PATCHED:=isa_export.ml.patched

GENERATED_PATCHED:=isa_export.ml

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

$(PATCH): $(ORIG) $(PATCHED)
	diff -u3 -p $(ORIG) $(PATCHED) >$@ 
# this fails if there are changes?

$(GENERATED_PATCHED): $(ORIG) FORCE
	-patch -i $(PATCH) $(ORIG) -o $@ 

FORCE:


# insert_with_mutation -------------------------------------------------

# There should be a file /tmp/insert_with_mutation.ml. Copy this file
# into this directory, then apply patch. Patch is minimal, so
# hopefully no need to regenerate often.

insert_with_mutation.ml: /tmp/insert_with_mutation.ml
	cp $< $@.orig
	patch -i insert_with_mutation.patch $@.orig -o $@
	ocamlc -c -w -8 $@
