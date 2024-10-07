opam_exec := opam exec --switch=. --set-switch --
dune := $(opam_exec) dune

.PHONY : all
all : build

.PHONY : build
build :
	@ $(dune) build

.PHONY : test
test : build
	@ ./tests/run.sh

.PHONY : top
top :
	@ $(dune) utop .

.PHONY : clean
clean :
	@ $(dune) clean
	@ rm -f tests/*.{cm[it],v}
