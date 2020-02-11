#!/usr/bin/env bash

# Copyright (c) 2017 Clément Pit-Claudel
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in all
# copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE

# Notes:
#
# * If you see an error like this, upgrade to a more recent Ubuntu box:
#
#       /vagrant/build/emsdk-portable/clang/e1.37.36_64bit/llc:
#       /usr/lib/x86_64-linux-gnu/libstdc++.so.6: version `GLIBCXX_3.4.20' not
#       found (required by /vagrant/build/emsdk-portable/clang/e1.37.36_64bit/llc)
#
# * This script is only know to work on Ubuntu. You can run it locally, but in
#   that case DO NOT set VAGRANT=true.

: "${VAGRANT:=false}"

if [ "$VAGRANT" = true ]; then
    : "${BASEDIR:=/vagrant/}"
else
    : "${BASEDIR:=$(pwd)/}"
fi

export OPTLEVEL=3
export BUILDDIR="${BASEDIR}build/"
export Z3_ROOT="${BUILDDIR}z3/"
export Z3_RELEASE="4.7.1"
export EMSCRIPTEN_TEMPDIR="/tmp/emscripten/"
export EMSCRIPT_RELEASE="1.39.7"
export EMSDK_ROOT="${BUILDDIR}emscripten-$EMSCRIPT_RELEASE/"

function say() {
    printf "\033[1;32m%s\033[0m\n" "$1"
}

say ""
say '*********************************'
say '***  Installing dependencies  ***'
say '*********************************'

export DEBIAN_FRONTEND=noninteractive

say '* apt-get update'; {
    sudo apt-get -y -q update
}

if [ "$VAGRANT" = true ]; then
    say '* apt-get install (VBox extensions)'; {
        sudo apt-get -y -q install virtualbox-guest-dkms virtualbox-guest-utils
    }
fi

say '* apt-get install (Dependencies)'; {
    sudo apt-get -y -q install git build-essential lzip python2.7 cmake autoconf libtool
}

if [ "$VAGRANT" = true ]; then
    [ ! -f /usr/bin/python   ] && sudo ln -s /usr/bin/python2.7 /usr/bin/python
    [ ! -f /usr/bin/python2  ] && sudo ln -s /usr/bin/python2.7 /usr/bin/python2
    [ ! -f /usr/local/bin/ld ] && sudo ln -s "$(which gold)" /usr/local/bin/ld
    # https://stackoverflow.com/questions/25197570/llvm-clang-compile-error-with-memory-exhausted
fi

say ""
say '*******************'
say '*** Downloading ***'
say '*******************'

rm -rf "$BUILDDIR"
mkdir "$BUILDDIR"


say '* wget emscripten'; {
    git clone --depth 1 https://github.com/emscripten-core/emsdk.git "$EMSDK_ROOT"
}

say '* git clone z3'; {
    git clone --depth 1 --branch z3-$Z3_RELEASE --quiet https://github.com/Z3Prover/z3.git "$Z3_ROOT"
}

say ""
say '****************'
say '*** Building ***'
say '****************'


cd "$EMSDK_ROOT"

# Build in release mode to not run out of memory
# https://github.com/kripken/emscripten/issues/4667

say '* Emscripten: setup'; {
    ./emsdk update
    ./emsdk install $EMSCRIPT_RELEASE --build=Release
    ./emsdk activate $EMSCRIPT_RELEASE

    # Use incoming because of https://github.com/kripken/emscripten/pull/5239
    # ./emsdk install emscripten-incoming-32bit --build=Release
    # ./emsdk activate emscripten-incoming-32bit

    # Needed by emcc
    sed -i "s/NODE_JS *= *'\(.*\)'/NODE_JS=['\1','--stack_size=8192']/" ~/.emscripten

    # Regenerate emsdk_set_env.sh
    ./emsdk construct_env ""
}

# Don't source emsdk_env directly, as it produces output that can't be logged
# without creating a subshell (which would break `source`)
source "${EMSDK_ROOT}emsdk_set_env.sh"

# emcc fails in all sorts of weird ways without this
ulimit -s unlimited

say '* Emscripten: stdlib (very slow!)'; {
    mkdir -p "$EMSCRIPTEN_TEMPDIR"
    cd "$EMSCRIPTEN_TEMPDIR"
    printf '#include<stdio.h>\nint main() { return 0; }\n' > minimal.c
    emcc minimal.c
}

cd "$Z3_ROOT"

Z3_CONFIGURE_OPTS=(--staticlib --staticbin --noomp --x86)

say '* Z3: configure (slow!)'; {
    emconfigure python scripts/mk_make.py "${Z3_CONFIGURE_OPTS[@]}"
}

say '* Z3: make standalone (very slow!)'; {
    emmake make -C build -j6
}

# Shared options
EMCC_OPTIONS=(
    -s INVOKE_RUN=0 # Don't call main automatically
    -O${OPTLEVEL}

    # Don't pollute the global namespace
    -s MODULARIZE=1
    -s EXPORT_NAME="'Z3'"

    # Catch errors early
    -s STRICT=1 -s ERROR_ON_UNDEFINED_SYMBOLS=1

    # Avoid various aborts
    # -s OUTLINING_LIMIT=10000 # Avoid “excessive recursion” errors at asm.js parsing time
    #                          # (But beware: excessively low values cause stack overflows in the program itself)
    -s DISABLE_EXCEPTION_CATCHING=0 # Let program catch exceptions
    -s ABORTING_MALLOC=0 -s ALLOW_MEMORY_GROWTH=1 # Allow dynamic memory resizing
)

# Options for standalone, full Z3 builds
EMCC_Z3_OPTIONS=(
    ${EMCC_OPTIONS[@]}

    -s EXPORTED_FUNCTIONS='["_main"]'
    -s 'EXTRA_EXPORTED_RUNTIME_METHODS=["FS"]'

    # Enable this to exit fully after main completes
    # https://github.com/kripken/emscripten/commit/f585dcbc2d929ef8b8bc6813e0710ec3215ac0b1
    # -s NO_EXIT_RUNTIME=0

    # Add this to make it possible to run the test suite (it's
    # normally included by default, but “-s STRICT=1” disables it)
    -l "nodefs.js"
)

# Options for the small SMT2 client
EMCC_Z3_SMT2_OPTIONS=(
    ${EMCC_OPTIONS[@]}
    -s EXPORTED_FUNCTIONS='["_smt2Init", "_smt2SetParam", "_smt2Ask", "_smt2Destroy"]'
    -s EXTRA_EXPORTED_RUNTIME_METHODS='["ccall", "cwrap", "allocateUTF8", "writeAsciiToMemory"]'
    -fPIC -I src/api/
)

EMCC_WASM_OPTIONS=(
    -s WASM=1
    # Async compilation causes Firefox to infloop, repeatedly printing “still
    # waiting on run dependencies: dependency: wasm-instantiate”. We'll run
    # in a WebWorker anyway, so it wouldn't buy us much.
    -s WASM_ASYNC_COMPILATION=0)

EMCC_Z3_JS_INPUTS=("${Z3_ROOT}build/z3.bc")
EMCC_Z3_SMT2_JS_INPUTS=("${BASEDIR}z3smt2.c" "${Z3_ROOT}build/libz3.a")

cd "$Z3_ROOT"

say '* Z3: Linking (slow!)'; {
    cp "${Z3_ROOT}build/z3" "${Z3_ROOT}build/z3.bc"
    # emcc "${EMCC_Z3_OPTIONS[@]}" "${EMCC_Z3_JS_INPUTS[@]}" -o z3.js
    emcc "${EMCC_Z3_OPTIONS[@]}" "${EMCC_WASM_OPTIONS[@]}" "${EMCC_Z3_JS_INPUTS[@]}" -o z3w.js
}

say '* Z3 smt2 client: Linking (slow!)'; {
    # emcc "${EMCC_Z3_SMT2_OPTIONS[@]}" "${EMCC_Z3_SMT2_JS_INPUTS[@]}" -o z3smt2.js
    emcc "${EMCC_Z3_SMT2_OPTIONS[@]}" "${EMCC_WASM_OPTIONS[@]}" "${EMCC_Z3_SMT2_JS_INPUTS[@]}" -o z3smt2w.js
}

say ""
say '*********************************'
say '***       Build complete      ***'
say '*********************************'
