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

# Note:
# I you see an error like this:
#
#    /vagrant/z3-wasm/emsdk-portable/clang/e1.37.36_64bit/llc:
#    /usr/lib/x86_64-linux-gnu/libstdc++.so.6: version `GLIBCXX_3.4.20' not
#    found (required by /vagrant/z3-wasm/emsdk-portable/clang/e1.37.36_64bit/llc)
#
# Then upgrade to a more recent Ubuntu box

: "${BASEDIR:=/vagrant}"
export LOGFILE="$BASEDIR/provision.log"
export DEBIAN_FRONTEND=noninteractive

export JS_ROOT="$BASEDIR/z3-wasm/"
export Z3_ROOT="${JS_ROOT}z3/"
export EMSDK_ROOT="${JS_ROOT}emsdk-portable/"
export Z3_SMT2_ROOT="${JS_ROOT}z3-smt2/"

export OPTLEVEL=3

function say() {
    date >> "$LOGFILE"
    echo "$1" | tee -a "$LOGFILE"
}

echo "" > "$LOGFILE"
say "* Starting; see ${LOGFILE} for details."

say ""
say '*********************************'
say '***  Installing dependencies  ***'
say '*********************************'

say '* apt-get update'; {
    sudo apt-get -y -q update
} >> "$LOGFILE" 2>&1
say '* apt-get install (VBox extensions)'; {
    sudo apt-get -y -q install virtualbox-guest-dkms virtualbox-guest-utils
} >> "$LOGFILE" 2>&1
say '* apt-get install (Dependencies)'; {
    sudo apt-get -y -q install git build-essential lzip python2.7 cmake autoconf libtool
    sudo ln -s /usr/bin/python2.7 /usr/bin/python
    sudo ln -s /usr/bin/python2.7 /usr/bin/python2
} >> "$LOGFILE" 2>&1

say ""
say '*******************'
say '*** Downloading ***'
say '*******************'

rm -rf "$JS_ROOT"
mkdir "$JS_ROOT"

say '* wget emscripten'; {
    wget --quiet -O /tmp/emsdk-portable.tar.gz https://s3.amazonaws.com/mozilla-games/emscripten/releases/emsdk-portable.tar.gz
    tar -xf /tmp/emsdk-portable.tar.gz -C "$JS_ROOT"
} >> "$LOGFILE" 2>&1

say '* git clone z3'; {
    git clone --depth 1 --quiet https://github.com/Z3Prover/z3.git "$Z3_ROOT"
} >> "$LOGFILE" 2>&1

say ""
say '****************'
say '*** Building ***'
say '****************'

cd "$EMSDK_ROOT"

# Use gold to minimize memory usage, and build release mode to not run out of memory
# https://github.com/kripken/emscripten/issues/4667
# https://stackoverflow.com/questions/25197570/llvm-clang-compile-error-with-memory-exhausted
sudo ln -s "$(which gold)" /usr/local/bin/ld

say '* emscripten (slow!)'; {
    ./emsdk update
    ./emsdk install latest --build=Release
    ./emsdk activate latest

    # Use incoming because of https://github.com/kripken/emscripten/pull/5239
    # ./emsdk install emscripten-incoming-32bit --build=Release
    # ./emsdk activate emscripten-incoming-32bit

    # Needed by emcc
    sed -i "s/NODE_JS *= *'\(.*\)'/NODE_JS=['\1','--stack_size=8192']/" ~/.emscripten
    source "${EMSDK_ROOT}/emsdk_env.sh"

    # Work around https://github.com/kripken/emscripten/pull/5967
    sed -i 's/python %s/%s/g' "$EMSCRIPTEN/tools/shared.py"
} >> "$LOGFILE" 2>&1

cd "$Z3_ROOT"

Z3_CONFIGURE_OPTS=(--staticlib --staticbin --noomp --x86)

say '* Z3: configure'; {
    emconfigure python scripts/mk_make.py "${Z3_CONFIGURE_OPTS[@]}"
} >> "$LOGFILE" 2>&1

say '* Z3: make standalone (slow!)'; {
    emmake make -C build -j4
} >> "$LOGFILE" 2>&1

# Shared options
EMCC_OPTIONS=(
    -s INVOKE_RUN=0 # Don't call main automatically

    # Don't pollute the global namespace
    -s MODULARIZE=1
    -s EXPORT_NAME="'Z3'"

    # Catch errors early
    -s STRICT=1 -s ERROR_ON_UNDEFINED_SYMBOLS=1

    # Avoid various aborts
    # 200000: 16.70s, 14.92s, 15883 lines in __ZN19iz3translation_full14translate_mainE5ast_rb
    #  50000: 16.48s, 18.74s, 5559 lines in __ZN16fpa2bv_converter5roundEP4sortR7obj_refI4expr11ast_managerES6_S6_S6_S6_
    #  10000: 15.29s, 17.05s, no warnings
    -s OUTLINING_LIMIT=10000 # Avoid “excessive recursion” errors at js parsing time
    #                        # (But beware: excessively low values cause stack overflows in the program itself)
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
    -O${OPTLEVEL} -fPIC -I src/api/
)

EMCC_WASM_OPTIONS=(
    -s WASM=1
    # Async compilation causes Firefox to infloop, repeatedly printing “still
    # waiting on run dependencies: dependency: wasm-instantiate”. We'll run
    # in a WebWorker anyway, so it wouldn't buy us much.
    -s BINARYEN_ASYNC_COMPILATION=0)

EMCC_Z3_JS_INPUTS=("${Z3_ROOT}/build/z3.bc")
EMCC_Z3_SMT2_JS_INPUTS=("${BASEDIR}/z3smt2.c" "${Z3_ROOT}/build/libz3.a")

ulimit -s unlimited

say '* Z3: Linking'; {
    cp "${Z3_ROOT}/build/z3" "${Z3_ROOT}/build/z3.bc"
    # emcc "${EMCC_Z3_OPTIONS[@]}" "${EMCC_Z3_JS_INPUTS[@]}" -o z3.js
    emcc "${EMCC_Z3_OPTIONS[@]}" "${EMCC_WASM_OPTIONS[@]}" "${EMCC_Z3_JS_INPUTS[@]}" -o z3w.js
} >> "$LOGFILE" 2>&1

mkdir "$Z3_SMT2_ROOT"
cd "$Z3_SMT2_ROOT"

say '* Z3 smt2 client: Linking'; {
    # emcc "${EMCC_Z3_SMT2_OPTIONS[@]}" "${EMCC_Z3_SMT2_JS_INPUTS[@]}" -o z3smt2.js
    emcc "${EMCC_Z3_SMT2_OPTIONS[@]}" "${EMCC_WASM_OPTIONS[@]}" "${EMCC_Z3_SMT2_JS_INPUTS[@]}" -o z3smt2w.js
} >> "$LOGFILE" 2>&1

say ""
say '*********************************'
say '***       Setup complete      ***'
say '*********************************'
