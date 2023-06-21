all: Makefile.coq
	@+$(MAKE) -f Makefile.coq all

clean: Makefile.coq
	@+$(MAKE) -f Makefile.coq cleanall
	@rm -f Makefile.coq Makefile.coq.conf

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

force _CoqProject Makefile: ;

%: Makefile.coq force/Users/basla/Course Files/Thesis/final-software
	@+$(MAKE) -f Makefile.coq $@

.PHONY: all clean force