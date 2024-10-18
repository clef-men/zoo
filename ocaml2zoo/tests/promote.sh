#! /usr/bin/env bash

set -eou pipefail

if [[ 0 < $# ]] ; then
	tests="$@"
	tests="${tests/#/tests/}"
	tests="${tests/%/.ml}"
else
  tests="$(ls tests/*.ml)"
fi

for test in $tests ; do
	if [ ! -f "$test" ] ; then
		echo "error: test does not exist: \"$test\""
		exit 1
	fi

	test="${test%.*}"

	ocamlopt -stop-after typing -bin-annot zoo.mli "$test.ml"
	./bin/ocaml2zoo.exe "$test.cmt"

	cp "${test}__types.v" "${test}__types.exp"
	cp "${test}__code.v" "${test}__code.exp"
done
