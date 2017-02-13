all: Makefile.coq
	make -f Makefile.coq

Makefile.coq:
	coq_makefile -f _CoqProject -o Makefile.coq

clean:
	make -f Makefile.coq clean

paper.vo: paper.v
	make -f Makefile.coq paper.vo

paper.tex: paper.vo
	"coqdoc" -interpolate -utf8 -latex -R . Top paper.v -o paper.tex
