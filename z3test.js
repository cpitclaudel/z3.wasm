process.chdir("./z3-js/z3/"); // To find the WASM file
var Z3Factory = require("./z3-js/z3/z3w.js");
var z3 = Z3Factory();

var FS = z3["FS"];

FS.mkdir("/nodefs");
FS.mount(FS.filesystems["NODEFS"], { root: "../../" }, "/nodefs");

z3.callMain(process.argv.splice(2));
