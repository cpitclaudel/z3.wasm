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

process.chdir("./z3-wasm/z3/"); // To find the WASM file
var Z3Factory = require('./z3-wasm/z3/z3smt2w.js');
var z3smt2 = Z3Factory();

var smt2API = {
    init: z3smt2.cwrap('smt2Init', 'number', []),
    setParam: z3smt2.cwrap('smt2SetParam', null, ['string', 'string']),
    ask: z3smt2.cwrap('smt2Ask', 'string', ['number', 'string']),
    destroy: z3smt2.cwrap('smt2Destroy', null, ['number']) };

var ctx = smt2API.init();

smt2API.setParam("model", "true");
smt2API.setParam("auto_config", "false");
smt2API.setParam("smtlib2_compliant", "false");

function say(msg) {
    process.stdout.write(msg || "");
}

// var fs = require("fs");
// var query = fs.readFileSync("input.smt2", {encoding: "utf-8"});
// say(query);
// say("result", smt2API.ask(ctx, query));
say(smt2API.ask(ctx, "(declare-fun x () Int)"));
say(smt2API.ask(ctx, "(declare-fun y () Int)"));
say(smt2API.ask(ctx, "(declare-fun z () Int)"));
say(smt2API.ask(ctx, "(assert (>= (* 2 x) (+ y z)))"));
say(smt2API.ask(ctx, "(declare-fun f (Int) Int)"));
say(smt2API.ask(ctx, "(declare-fun g (Int Int) Int)"));
say(smt2API.ask(ctx, "(assert (< (f x) (g x x)))"));
say(smt2API.ask(ctx, "(assert (> (f y) (g x x)))"));
say(smt2API.ask(ctx, "(check-sat)"));
say(smt2API.ask(ctx, "(get-model)"));
say(smt2API.ask(ctx, "(push)"));
say(smt2API.ask(ctx, "(assert (= x y))"));
say(smt2API.ask(ctx, "(check-sat)"));
say(smt2API.ask(ctx, "(get-model)"));
say(smt2API.ask(ctx, "(check-sat)"));
say(smt2API.ask(ctx, "(pop)"));
say(smt2API.ask(ctx, "(exit)"));

smt2API.destroy(ctx);
