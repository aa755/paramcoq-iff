TEST=nat  vec  vecSRevAuto  IWTS  indFunArg boolConj
TESTVO:=$(TEST:=.vo)
TESTVLOG:=$(TEST:=.vlog)

testlogs: $(TESTVLOG)
tests: $(TESTVO)

errors:
	grep "Error" *.vlog

all: Makefile.coq
	make -f Makefile.coq

Makefile.coq:
	coq_makefile -f _CoqProject -o Makefile.coq

clean:
	make -f Makefile.coq clean
	rm *.vlog

%.vlog: %.v ../paramDirect.v
	script -c "make -f Makefile.coq $(addsuffix o,$<)" $(addsuffix log,$<)

