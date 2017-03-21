TEST=nat  vec  vecSRevAuto  IWTS  indFunArg boolConj exists IWP
TESTVO:=$(TEST:=.vo)
TESTVLOG:=$(TEST:=.vlog)

testlogs: $(TESTVLOG)
tests: $(TESTVO)

testlogsParallel:
	$(MAKE) nat.vlog; $(MAKE) -j5 testlogs

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

