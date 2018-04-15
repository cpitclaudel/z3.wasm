#!/usr/bin/env bash
rm -rf dist/ html/z3*w.*
mkdir dist
cp html/* dist/
cp README.dist.rst dist/README.rst
cp build/z3/z3smt2w.js build/z3/z3smt2w.wasm build/z3/z3w.js build/z3/z3w.wasm dist/
tar --create --gzip --file z3.wasm.tar.gz --transform 's|^dist|z3.wasm|' dist
