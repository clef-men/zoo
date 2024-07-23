.PHONY : all
all : build

.PHONY : build
build :
	@ opam exec -- dune build

.PHONY : test
test : build
	@ ./tests/run.sh

.PHONY : top
top :
	@ opam exec -- dune utop .

.PHONY : clean
clean :
	@ opam exec -- dune clean
	@ rm -f zoo.cmi zoo.cmti
	@ rm -f tests/*.{cmi,cmt,v}
