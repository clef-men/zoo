#!/bin/bash
set -euo pipefail
IFS=$'\n\t'

if command -v gnutar >/dev/null ; then
  # On MacOS, run "sudo port install gnutar" to obtain gnutar.
  TAR=gnutar
else
  TAR=tar
fi

ARCHIVE=store

rm -rf $ARCHIVE $ARCHIVE.tar.gz

mkdir $ARCHIVE

make clean

cp -r \
   Makefile \
   README.md \
   coq-store.opam \
   _CoqProject \
   theories \
   $ARCHIVE

cd $ARCHIVE

$TAR cvfz $ARCHIVE.tar.gz \
     --exclude-vcs-ignores \
     --exclude-vcs \
     --owner=0 --group=0 \
     $ARCHIVE

rm -rf $ARCHIVE
