// Copyright (c) 2018 Clément Pit-Claudel
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in all
// copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE

#include<z3.h>
#include<stdlib.h>

void smt2HandleError(Z3_context c, Z3_error_code e) {
  // Silently ignore errors (let the client deal with them; they are mentioned
  // in the output returned by Z3_eval_smtlib2_string).
}

// Create a fresh SMT2 context
Z3_context smt2Init() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_set_error_handler(ctx, smt2HandleError);
    Z3_del_config(cfg);
    return ctx;
}

// Globally set `option` to `value`.
void smt2SetParam(const char* option, const char* value) {
  Z3_global_param_set(option, value);
}

// Send `query` to `ctx` and fetch the response as a string.
const char* smt2Ask(Z3_context ctx, const char* query) {
  return Z3_eval_smtlib2_string(ctx, query);
}

// Release the resources used by `ctx`.
void smt2Destroy(Z3_context ctx) {
  Z3_del_context(ctx);
}

int main() {
  Z3_context ctx = smt2Init();

  smt2SetParam("smtlib2_compliant", "true");
  smt2SetParam("model", "true");

  printf("%s", smt2Ask(ctx, "(declare-fun x () Int)"));
  printf("%s", smt2Ask(ctx, "(declare-fun y () Int)"));
  printf("%s", smt2Ask(ctx, "(declare-fun z () Int)"));
  printf("%s", smt2Ask(ctx, "(assert (>= (* 2 x) (+ y z)))"));
  printf("%s", smt2Ask(ctx, "(declare-fun f (Int) Int)"));
  printf("%s", smt2Ask(ctx, "(declare-fun g (Int Int) Int)"));
  printf("%s", smt2Ask(ctx, "(assert (< (f x) (g x x)))"));
  printf("%s", smt2Ask(ctx, "(assert (> (f y) (g x x)))"));
  printf("%s", smt2Ask(ctx, "(check-sat)"));
  printf("%s", smt2Ask(ctx, "(get-model)"));
  printf("%s", smt2Ask(ctx, "(push)"));
  printf("%s", smt2Ask(ctx, "(assert (= x y))"));
  printf("%s", smt2Ask(ctx, "(check-sat)"));
  printf("%s", smt2Ask(ctx, "(get-model)"));
  printf("%s", smt2Ask(ctx, "(check-sat)"));
  printf("%s", smt2Ask(ctx, "(pop)"));
  printf("%s", smt2Ask(ctx, "(exit)"));

  smt2Destroy(ctx);

  return 0;
}
