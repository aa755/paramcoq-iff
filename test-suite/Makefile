tests: nat.vlog vec.vlog vecSRevAuto.vlog

all: Makefile.coq
	make -f Makefile.coq

Makefile.coq:
	coq_makefile -f _CoqProject -o Makefile.coq

clean:
	make -f Makefile.coq clean

%.vlog: %.v
	script -c "make -f Makefile.coq $(addsuffix o,$<)" $(addsuffix log,$<)

