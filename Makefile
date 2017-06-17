all: Makefile.coq
	make -f Makefile.coq

Makefile.coq:
	coq_makefile -f _CoqProject -o Makefile.coq

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

clean:
	make -f Makefile.coq clean

doc:
	"coqdoc" -interpolate -utf8 -html -R . ReflParam templateCoqMisc.v paramDirect.v
