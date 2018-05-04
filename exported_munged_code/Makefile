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
# - If this fails, manually patch ORIG, output to PATCHED and remake patch
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

$(GENERATED_PATCHED): $(ORIG) 
	-patch -i $(PATCH) $(ORIG) -o $@ 

FORCE:
