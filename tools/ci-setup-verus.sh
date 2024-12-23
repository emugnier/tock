#!/bin/bash

set -e

git clone \
  --depth 1 \
  --recurse-submodules --shallow-submodules \
  https://github.com/verus-lang/verus
cd verus/source
git fetch --depth 1 origin bc5b90fb1c0119334513d4c37f06988633a7a10a
git checkout bc5b90f
git submodule update --init --recursive --remote
# trigger toolchain installation
rustc --version
echo "Verus is at $PWD"
echo "Verus is at git revision: $(git rev-parse HEAD)"
