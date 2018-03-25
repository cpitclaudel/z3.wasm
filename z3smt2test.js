process.chdir("./z3-js/z3/"); // To find the WASM file
var Z3Factory = require('./z3-js/z3/z3smt2w.js');
var z3smt2 = Z3Factory();

var smt2API = {
    init: z3smt2.cwrap('smt2Init', 'number', []),
    setParam: z3smt2.cwrap('smt2SetParam', null, ['string', 'string']),
    ask: z3smt2.cwrap('smt2Ask', 'string', ['number', 'string']),
    destroy: z3smt2.cwrap('smt2Destroy', null, ['number']) };

var ctx = smt2API.init();

smt2API.setParam("model", "true");
smt2API.setParam("auto_config", "false");
smt2API.setParam("smt.random_seed", "0");
smt2API.setParam("smt.case_split", "3");
smt2API.setParam("smt.relevancy", "2");
smt2API.setParam("smt.mbqi", "false");

// var fs = require("fs");
// var query = fs.readFileSync("input.smt2", {encoding: "utf-8"});
// console.log(query);
// console.log("result", smt2API.ask(ctx, query));
console.log(smt2API.ask(ctx, "(declare-fun x () Int)"));
console.log(smt2API.ask(ctx, "(declare-fun y () Int)"));
console.log(smt2API.ask(ctx, "(declare-fun z () Int)"));
console.log(smt2API.ask(ctx, "(assert (>= (* 2 x) (+ y z)))"));
console.log(smt2API.ask(ctx, "(declare-fun f (Int) Int)"));
console.log(smt2API.ask(ctx, "(declare-fun g (Int Int) Int)"));
console.log(smt2API.ask(ctx, "(assert (< (f x) (g x x)))"));
console.log(smt2API.ask(ctx, "(assert (> (f y) (g x x)))"));
console.log(smt2API.ask(ctx, "(check-sat)"));
console.log(smt2API.ask(ctx, "(get-model)"));
console.log(smt2API.ask(ctx, "(push)"));
console.log(smt2API.ask(ctx, "(assert (= x y))"));
console.log(smt2API.ask(ctx, "(check-sat)"));
console.log(smt2API.ask(ctx, "(get-model)"));
console.log(smt2API.ask(ctx, "(check-sat)"));
console.log(smt2API.ask(ctx, "(pop)"));
console.log(smt2API.ask(ctx, "(exit)"));

console.log(smt2API.destroy(ctx));
