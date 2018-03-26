/* exported makeZ3Demo */
function makeZ3Demo(window, queries, responses, ace) {
    var editor;
    var worker;
    var verification_start;

    var console = window.console;
    var document = window.document;
    var command_line_args = document.getElementById("command-line-args");
    var run_button = document.getElementById("run");
    var stdout_textbox = document.getElementById("stdout");

    function postZ3Message(query, payload) {
        console.info("[Window] → Z3 (" + query + "):", payload);
        worker.postMessage({ kind: query, payload: payload });
    }

    function clear(node) {
        while (node.hasChildNodes()) {
            node.removeChild(node.lastChild);
        }
    }

    function disableButton(message) {
        run_button.disabled = true;
        run_button.value = message;
    }

    function enableButton() {
        run_button.disabled = false;
        run_button.value = "Run Z3!";
    }

    function verifyCurrentInput(_event) {
        var input = editor.getValue();
        var args = command_line_args.value.split(/ +/);
        clear(stdout_textbox);
        disableButton("Running…");
        verification_start = window.performance.now();
        postZ3Message(queries.VERIFY, { args: args, input: input });
    }

    function logOutput(message, cssClass) {
        var span_node = window.document.createElement("span");
        span_node.className = cssClass;
        span_node.appendChild(window.document.createTextNode(message + "\n"));
        stdout_textbox.appendChild(span_node);
    }

    function onZ3Message(event) {
        console.info("Z3 → [Window]:", event);
        var kind = event.data.kind;
        var payload = event.data.payload;
        switch (kind) {
        case responses.PROGRESS:
            disableButton(payload);
            break;
        case responses.READY:
            enableButton();
            break;
        case responses.STDOUT:
            logOutput(payload, "stdout-msg");
            break;
        case responses.STDERR:
            logOutput(payload, "stderr-msg")
            break;
        case responses.VERIFICATION_COMPLETE:
            enableButton();
            var elapsed = Math.round(window.performance.now() - verification_start);
            logOutput ("-- Verification complete (" + elapsed + "ms)", "info-msg");
            break;
        }
    }

    function setupZ3Worker() {
        worker = new window.Worker("worker.js");
        worker.onmessage = onZ3Message;
    }

    function setupAceEditor() {
        editor = ace.edit("editor");
        editor.setTheme("ace/theme/monokai");
        editor.getSession().setMode("ace/mode/lisp");
        editor.setOptions({ fontFamily: "Ubuntu Mono, monospace", fontSize: "1rem" });
    }

    function init() {
        setupAceEditor();
        setupZ3Worker();
        clear(stdout_textbox);
        run_button.onclick = verifyCurrentInput;
    }

    return { init: init };
}
