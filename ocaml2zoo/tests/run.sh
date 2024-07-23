#! /usr/bin/env bash

set -eou pipefail

for test in tests/*.ml ; do
	test=${test%.*}

	opam exec -- ocamlopt -stop-after typing -bin-annot zoo.mli $test.ml
	./bin/ocaml2zoo.exe $test.cmt

	if diff ${test}__types.v ${test}__types.exp > /dev/null \
	&& diff ${test}__code.v ${test}__code.exp > /dev/null
	then
		echo "test successful: \"$(basename $test)\""
	else
		echo "test failed: \"$(basename $test)\""
		exit 1
	fi
done
