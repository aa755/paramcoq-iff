TEST=nat vec IWTS  list  indFunArg  multIndices2  multIndices3 multIndices4  multIndices2NonDep  alphaEquivariant bool eqs exists sigs squiggle4 squiggle4Thm squiggle4Impl natAbs #vecSRevAuto 
TESTVO:=$(TEST:=.vo)
TESTVLOG:=$(TEST:=.vlog)

testlogs: $(TESTVLOG)
tests: $(TESTVO)

# if not found, grep returns and error exit code
errors:
	grep "Error" *.vlog

all: Makefile.coq
	make -f Makefile.coq

Makefile.coq:
	coq_makefile -f _CoqProject -o Makefile.coq

clean:
	make -f Makefile.coq clean
	rm *.vlog

%.vlog: %.v ../../paramDirect.v
	script -c "make -f Makefile.coq $(addsuffix o,$<)" $(addsuffix log,$<)


%.vo: %.v ../../paramDirect.v
	make -f Makefile.coq $(addsuffix o,$<)
