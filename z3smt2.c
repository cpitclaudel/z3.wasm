#include<z3.h>
#include<stdlib.h>

void smt2HandleError(Z3_context c, Z3_error_code e) {
  // Silently ignore errors (let the client deal with them; they are mentioned
  // in the output returned by Z3_eval_smtlib2_string).
}

Z3_context smt2Init() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_set_error_handler(ctx, smt2HandleError);
    Z3_del_config(cfg);
    return ctx;
}

void smt2SetParam(const char* option, const char* value) {
  Z3_global_param_set(option, value);
}

const char* smt2Ask(Z3_context ctx, const char* query) {
  return Z3_eval_smtlib2_string(ctx, query);
}

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
