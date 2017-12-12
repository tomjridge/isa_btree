SHELL:=bash

all: $(wildcard *.svg)
	for f in *.svg; do \
rsvg-convert -f pdf -o $${f/.svg/.pdf} $$f; \
rsvg-convert -f ps -o $${f/.svg/.ps} $$f; \
done
	touch all

clean: 
	for f in *.svg; do \
rm -f $${f/.svg/.pdf} $${f/.svg/.ps}; \
done
	rm -f all
