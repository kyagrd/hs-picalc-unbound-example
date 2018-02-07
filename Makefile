.PHONY: all pdf force hs

LHS2TEX=lhs2TeX

force: pdf
	pdflatex main

pdf: main.pdf

main.pdf: main.tex mylhs2tex.sty biblio.bib \
	PiCalc.tex IdSubLTS.tex OpenLTS.tex OpenBisim.tex \
       	abstract.tex intro.tex related.tex
	latexmk -pdf main

mylhs2tex.sty: mylhs2tex.lhs
	$(LHS2TEX) --poly -o $@ $<

intro.tex: intro.lhs exampleFigure.lhs
	$(LHS2TEX) --poly -o $@ $<

PiCalc.tex: PiCalc.lhs mylhs2tex.sty
	$(LHS2TEX) --poly -o $@ $<

IdSubLTS.tex: IdSubLTS.lhs mylhs2tex.sty
	$(LHS2TEX) --poly -o $@ $<

OpenLTS.tex: OpenLTS.lhs FigOpenLTS.tex mylhs2tex.sty
	$(LHS2TEX) --poly -o $@ $<

FigOpenLTS.tex: OpenLTS.lhs mylhs2tex.sty
	$(LHS2TEX) --poly -l figureOpenLTS=True -o $@ $<

OpenBisim.tex: OpenBisim.lhs discuss.lhs mylhs2tex.sty
	$(LHS2TEX) --poly -o $@ $<
