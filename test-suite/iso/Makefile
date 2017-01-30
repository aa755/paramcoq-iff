tests: nat.vlog Makefile.coq vec.vlog IWTS.vlog list.vlog indFunArg.vlog multIndices2.vlog multIndices3.vlog multIndices2NonDep.vlog #vecSRevAuto.vlog

all: Makefile.coq
	make -f Makefile.coq

Makefile.coq:
	coq_makefile -f _CoqProject -o Makefile.coq

clean:
	make -f Makefile.coq clean
	rm *.vlog

%.vlog: %.v ../../paramDirect.v
	script -c "make -f Makefile.coq $(addsuffix o,$<)" $(addsuffix log,$<)

