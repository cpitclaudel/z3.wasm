#!/usr/bin/env bash

# Copyright (c) 2016 Clément Pit-Claudel
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

: "${BASEDIR:=/vagrant}"
export LOGFILE="$BASEDIR/provision.log"
export DEBIAN_FRONTEND=noninteractive

export JS_ROOT="$BASEDIR/cvc4-js/"
export CVC4_ROOT="${JS_ROOT}CVC4/"
export EMSDK_ROOT="${JS_ROOT}emsdk-portable/"
export ANTLRC_ROOT="${JS_ROOT}libantlr3c-3.2/"
export LIBGMP_ROOT="${JS_ROOT}gmp-6.1.2/"
export CLN_ROOT="${JS_ROOT}cln-1.3.4/"
export INCLUDE_ROOT="${JS_ROOT}include/"

export OPTLEVEL=3

echo "" > "$LOGFILE"
echo "* Starting; see ${LOGFILE} for details."

echo ""
echo '*********************************'
echo '***  Installing dependencies  ***'
echo '*********************************'

echo '* apt-get update'; {
    sudo add-apt-repository -y ppa:ubuntu-elisp/ppa
    sudo apt-get -y -q update
} >> "$LOGFILE" 2>&1
echo '* apt-get install (VBox extensions)'; {
    sudo apt-get -y -q install virtualbox-guest-dkms virtualbox-guest-utils
} >> "$LOGFILE" 2>&1
echo '* apt-get install (Dependencies)'; {
    sudo apt-get -y -q install git build-essential lunzip antlr3.2 python2.7 cmake autoconf libtool libboost-dev
    sudo ln -s /usr/bin/python2.7 /usr/bin/python
} >> "$LOGFILE" 2>&1

echo ""
echo '*******************'
echo '*** Downloading ***'
echo '*******************'

mkdir "$JS_ROOT"

echo '* wget emscripten'; {
    wget --quiet -O /tmp/emsdk-portable.tar.gz https://s3.amazonaws.com/mozilla-games/emscripten/releases/emsdk-portable.tar.gz
    tar -xf /tmp/emsdk-portable.tar.gz -C "$JS_ROOT"
} >> "$LOGFILE" 2>&1

echo '* wget ANTLR C runtime'; {
    wget --quiet -O /tmp/libantlr3c-3.2.tar.gz http://www.antlr3.org/download/C/libantlr3c-3.2.tar.gz
    tar -xf /tmp/libantlr3c-3.2.tar.gz -C "$JS_ROOT"
} >> "$LOGFILE" 2>&1

echo '* wget libGMP'; {
    wget --quiet -O /tmp/gmp-6.1.2.tar.lz https://gmplib.org/download/gmp/gmp-6.1.2.tar.lz
    tar -xf /tmp/gmp-6.1.2.tar.lz -C "$JS_ROOT"
} >> "$LOGFILE" 2>&1

echo '* wget CLN'; {
    wget --quiet -O /tmp/cln-1.3.4.tar.bz2 https://ginac.de/CLN/cln-1.3.4.tar.bz2
    tar -xf /tmp/cln-1.3.4.tar.bz2 -C "$JS_ROOT"
} >> "$LOGFILE" 2>&1

echo '* git clone cvc4'; {
    git clone --depth 1 --quiet https://github.com/CVC4/CVC4.git "$CVC4_ROOT"
} >> "$LOGFILE" 2>&1

echo ""
echo '****************'
echo '*** Building ***'
echo '****************'

cd "$EMSDK_ROOT"

# Use gold to minimize memory usage, and build release mode to not run out of memory
# https://github.com/kripken/emscripten/issues/4667
# https://stackoverflow.com/questions/25197570/llvm-clang-compile-error-with-memory-exhausted
sudo ln -s "$(which gold)" /usr/local/bin/ld

echo '* emscripten (slow!)'; {
    ./emsdk update
    ./emsdk install latest --build=Release
    ./emsdk activate latest

    # See https://github.com/kripken/emscripten/pull/5239/
    ./emsdk install emscripten-incoming-32bit --build=Release
    ./emsdk activate emscripten-incoming-32bit

    # Needed by emcc
    sed -i "s/NODE_JS *= *'\(.*\)'/NODE_JS=['\1','--stack_size=8192']/" ~/.emscripten
    source ./emsdk_env.sh
} >> "$LOGFILE" 2>&1

cd "$LIBGMP_ROOT"

echo '* libgmp: configure'; {
    emconfigure ./configure --with-pic --disable-assembly --disable-fft --disable-shared
} >> "$LOGFILE" 2>&1

echo '* libgmp: make'; {
    emmake make -j4
} >> "$LOGFILE" 2>&1

cd "$CLN_ROOT"

echo '* CLN: configure'; {
    # FIXME --with-gmp="${LIBGMP_ROOT}" needs a folder with lib/ and include/
    emconfigure ./configure --without-gmp --enable-static --disable-shared
} >> "$LOGFILE" 2>&1

echo '* CLN: make'; {
    emmake make -j4
} >> "$LOGFILE" 2>&1

cd "$ANTLRC_ROOT"

echo '* ANTLR C runtime: configure'; {
    emconfigure ./configure --with-pic --disable-abiflags --disable-antlrdebug --disable-64bit --disable-shared
} >> "$LOGFILE" 2>&1

echo '* ANTLR C runtime: make'; {
    emmake make -j4
} >> "$LOGFILE" 2>&1

cd "$CVC4_ROOT"

# "Move" boost to a separate folder where it can live on its own, to prevent
# cmake from assuming `-l/usr/include` (which confuses emscripten, since it
# causes other system libraries to be selected in preference to emscripten ones)
# http://vclf.blogspot.com/2014/08/emscripten-linking-to-boost-libraries.html
mkdir -p "${INCLUDE_ROOT}"
ln -s /usr/include/boost/ "${INCLUDE_ROOT}"

CVC4_CONFIGURE_OPTS=(--with-antlr-dir="${ANTLRC_ROOT}" --with-boost="${INCLUDE_ROOT}"
                     --enable-static --enable-static-binary --enable-static-boost
                     --disable-maintainer-mode --disable-doxygen-doc
                     --disable-tracing --disable-assertions
                     --disable-debug-symbols --disable-unit-testing
                     --disable-thread-support --enable-language-bindings=
                     # --disable-statistics --disable-replay  --disable-proof  --disable-dumping
                     --with-build=production)

CVC4_CONFIGURE_ENV=(ANTLR="$(which antlr3.2)"
                    CPPFLAGS="-I${LIBGMP_ROOT} -I${ANTLRC_ROOT}"
                    LDFLAGS="-L${LIBGMP_ROOT}.libs -L${ANTLRC_ROOT}.libs")

echo '* CVC4: configure'; {
    env "${CVC4_CONFIGURE_ENV[@]}" emconfigure ./configure --config-cache "${CVC4_CONFIGURE_OPTS[@]}"
} >> "$LOGFILE" 2>&1

echo '* CVC4: make (slow!)'; {
    emmake make -j4
} >> "$LOGFILE" 2>&1


BUILD_DIR=$(grep -P "CURRENT_BUILD = .*" builds/current | sed 's/CURRENT_BUILD = //')

EMCC_OPTIONS=(-s INVOKE_RUN=0 # Don't call main automatically
              -s NO_EXIT_RUNTIME=1 # Don't exit fully, otherwise main() can only be called once

              # Generate a single file (this way the generated code doesn't need asynchronous loading)
              # Doesn't work for WASM
              # --memory-init-file 0

              -s STRICT=1 -s ERROR_ON_UNDEFINED_SYMBOLS=1 # Catch errors early

              # Don't pollute the global namespace
              -s EXPORTED_FUNCTIONS='["_main"]' -s MODULARIZE=1
              -s 'EXTRA_EXPORTED_RUNTIME_METHODS=["FS"]'

              # Avoid various aborts
              -s OUTLINING_LIMIT=200000 # Avoid “excessive recursion” errors at js parsing time
              # (But beware: too low values cause stack overflows in the program itself)
              -s DISABLE_EXCEPTION_CATCHING=0 # Let CVC4 catch exceptions
              -s ABORTING_MALLOC=0 -s ALLOW_MEMORY_GROWTH=1 # Allow dynamic memory resizing

              # This makes it possible to run the test suite (it's normally
              # included by default, but “-s STRICT=1” disables it)
              -l "nodefs.js")

EMCC_WASM_OPTIONS=(-s WASM=1
                   # No need for async compilation: it's broken (see notes) and
                   # we'll run in a WebWorker anyway
                   -s BINARYEN_ASYNC_COMPILATION=0)

EMCC_JS_INPUTS=(cvc4.bc
                ../gmp-6.1.2/.libs/libgmp.a
                ../libantlr3c-3.2/.libs/libantlr3c.a)

ulimit -s unlimited

echo '* CVC4: Linking javascript'; {
    cp "builds/${BUILD_DIR}/src/main/cvc4" cvc4.bc
    emcc "${EMCC_OPTIONS[@]}" -s EXPORT_NAME="'CVC4'" -O${OPTLEVEL} "${EMCC_JS_INPUTS[@]}" -o cvc4.js
    emcc "${EMCC_OPTIONS[@]}" -s EXPORT_NAME="'CVC4'" -O${OPTLEVEL} "${EMCC_JS_INPUTS[@]}" "${EMCC_WASM_OPTIONS[@]}" -o cvc4-wasm.js
} >> "$LOGFILE" 2>&1


# emcc "${EMCC_OPTIONS[@]}" -s EXPORT_NAME="'CVC4'" -O${OPTLEVEL} "${EMCC_JS_INPUTS[@]}" -o cvc4.js

echo ""
echo '*********************************'
echo '***       Setup complete      ***'
echo '*********************************'

echo ""
echo "Log into the VM using ‘vagrant ssh’."
