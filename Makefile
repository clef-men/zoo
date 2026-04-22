targets_norocq :=

.PHONY : all
all :

.PHONY : phony
phony :

.PHONY : clean
clean ::

.PHONY : doc
doc :
	@ rm -rf html
	@ COQDOCEXTRAFLAGS="--external https://plv.mpi-sws.org/coqdoc/stdpp/ stdpp --external https://plv.mpi-sws.org/coqdoc/iris/ iris" $(MAKE) gallinahtml

include Makefile.ocaml

include Makefile.theories
