.PHONY : all
all : build

.PHONY : build
build :
	@ dune build

.PHONY : install
install :
	@ dune install

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
