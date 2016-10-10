all: Makefile.coq
	make -f Makefile.coq

Makefile.coq:
	coq_makefile -f _CoqProject -o Makefile.coq
