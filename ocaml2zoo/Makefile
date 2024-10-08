.PHONY : all
all : build

.PHONY : build
build :
	@ dune build

.PHONY : install
install :
	@ dune install

.PHONY : depend
depend :
	@ opam install . --deps-only --yes

.PHONY : test
test : build
	@ ./tests/run.sh

.PHONY : top
top :
	@ dune utop .

.PHONY : clean
clean :
	@ dune clean
	@ rm -f tests/*.{cm[it],v}
