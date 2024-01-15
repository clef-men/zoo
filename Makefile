.PHONY : all
all :

.PHONY : depend
depend :
	@ opam install . --deps-only --verbose

Makefile.coq : _CoqProject
	@ coq_makefile -f $< -o $@

ifeq (,$(filter depend,$(MAKECMDGOALS)))
-include Makefile.coq
endif

.PHONY : clean
clean ::
	@ rm -f Makefile.coq Makefile.coq.conf
