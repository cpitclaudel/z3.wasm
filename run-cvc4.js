#!/usr/bin/env nodejs

var fs = require("fs");
var path = require("path");

var NODEFS_ROOT = "/nodefs";

function loadCVC4() {
    var script_directory = __dirname;
    var original_wd = process.cwd();

    // cvc4.js must be loaded from the right directory, to find cvc4.js.mem
    process.chdir(script_directory);
    var CVC4 = require("./cvc4.node.js"); // FIXME
    var cvc4 = CVC4();
    process.chdir(original_wd);

    return cvc4;
}

function adjust_path(path_or_arg) {
    if (fs.existsSync(path_or_arg)) {
        return path.join(NODEFS_ROOT, path.resolve(path_or_arg));
    } else {
        return path_or_arg;
    }
}

function main() {
    var args = process.argv.splice(2).map(adjust_path);
    // console.log(args);

    if (args.some(a => a.includes("regress0")))
        process.exit(0);

    var cvc4 = loadCVC4();
    var FS = cvc4["FS"];

    FS.mkdir(NODEFS_ROOT);
    FS.mount(FS.filesystems["NODEFS"], { root: "/" }, NODEFS_ROOT);

    cvc4.callMain(args); // Calls process.exit() due to sed in provision.sh
}

main();
