targets_nocoq := depend ocaml2zoo

.PHONY : all
all :

.PHONY : phony
phony :

.PHONY : depend
depend :
	@ opam install . --deps-only --verbose

Makefile.coq : _CoqProject
	@ coq_makefile -f $< -o $@

ifeq (,$(filter $(targets_nocoq),$(MAKECMDGOALS)))
-include Makefile.coq
endif

.PHONY : ocaml2zoo
ocaml2zoo :
	@ $(MAKE) -f Makefile.ocaml2zoo

build-% : phony
	@ ./make_package.sh $*
install-% : phony
	@ ./make_package.sh $* install

.PHONY : clean
clean ::
	@ rm -f Makefile.coq Makefile.coq.conf
	@ $(MAKE) -f Makefile.ocaml2zoo $@
