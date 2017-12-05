SHELL:=bash

all: 
	for f in *.svg; do \
rsvg-convert -f pdf -o $${f/.svg/.pdf} $$f; \
rsvg-convert -f ps -o $${f/.svg/.ps} $$f; \
done


clean: 
	for f in *.svg; do \
rm -f $${f/.svg/.pdf} $${f/.svg/.ps}; \
done
