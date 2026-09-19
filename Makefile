.PHONY : all
all : theories

.PHONY : lib
lib :
	@ dune build @lib/check @lib/all

.PHONY : bench
bench :
	@ dune build bench

.PHONY : ocaml2zoo
ocaml2zoo :
	@ ocaml2zoo . theories

.PHONY : plugin
plugin :
	@ dune build plugin

.PHONY : theories
theories :
	@ dune build theories --display=short

.PHONY : rocq-zoo
rocq-zoo :
	@ dune build theories/zoo --display=short
	@ dune install rocq-zoo

.PHONY : install
install :
	@ dune install

.PHONY : doc
doc :
	@ dune build @theories/doc

.PHONY : clean
clean :
	@ dune clean
