#!/usr/bin/env bash

PS4='$ '
set -ex

# in case we're run from out of git repo
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
pushd "$DIR" 1>/dev/null

# now change to the git root
ROOT_DIR="$(git rev-parse --show-toplevel)"
pushd "$ROOT_DIR" 1>/dev/null

if test ! -d .git
then
    echo 'Error: .git directory does not exist.'
    echo 'This script only works on a git clone of the HoTT repository.'
    exit 1
fi

echo '$ git submodule sync + init'
git submodule sync
git submodule update --init --recursive

echo '$ checking out coq'
git clone --depth=1 -b ${COQ_VERSION} https://github.com/coq/coq.git coq-HoTT

pushd coq-HoTT

[ -e .opam ] || opam init -j ${NJOBS} --compiler=system -n -y
eval $(opam config env)
opam config var root
opam install -j ${NJOBS} -y camlp5 ocamlfind
opam list
echo '$ ./configure '"$@"
./configure "$@"
echo '$ make states tools coqlight plugins grammar/compat5.cmo grammar/grammar.cma'
make states tools coqlight plugins grammar/compat5.cmo grammar/grammar.cma
echo '$ sudo make install-binaries + rsync plugins theories'
touch bin/coqtop.byte bin/coqchk stm/{proof,tac,query}workertop.cma
sudo make install-binaries install-devfiles
sudo rsync -a plugins theories /usr/local/lib/coq/

popd

popd 1>/dev/null
popd 1>/dev/null
