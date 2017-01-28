tests: nat.vlog Makefile.coq #vec.vlog vecSRevAuto.vlog

all: Makefile.coq
	make -f Makefile.coq

Makefile.coq:
	coq_makefile -f _CoqProject -o Makefile.coq

clean:
	make -f Makefile.coq clean

%.vlog: %.v ../../paramDirect.v
	script -c "make -f Makefile.coq $(addsuffix o,$<)" $(addsuffix log,$<)

