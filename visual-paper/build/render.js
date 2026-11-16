// Renders every formula of tmp/math.json with KaTeX and prints the result as JSON.
// Runs with Node (`node render.js`) or with macOS JavaScriptCore (`jsc render.js`), from build/.
var readText, emit;
if (typeof require === "function" && typeof process !== "undefined") {
  var fs = require("fs"), path = require("path");
  var katex = require(path.join(__dirname, "..", "vendor", "katex", "katex.min.js"));
  readText = function (f) { return fs.readFileSync(path.join(__dirname, f), "utf8"); };
  emit = function (s) { process.stdout.write(s + "\n"); };
} else {
  var self = this;
  load("../vendor/katex/katex.min.js");
  readText = readFile;
  emit = print;
}
var items = JSON.parse(readText("tmp/math.json"));
var macros = JSON.parse(readText("tmp/macros.json"));
function copy(o) { var r = {}; for (var k in o) r[k] = o[k]; return r; }
var out = items.map(function (it) {
  var opts = { displayMode: it[1], macros: copy(macros), throwOnError: true, strict: false,
               output: "html", trust: false };
  try {
    return { ok: true, html: katex.renderToString(it[0], opts) };
  } catch (e) {
    opts.throwOnError = false; opts.macros = copy(macros);
    var html;
    try { html = katex.renderToString(it[0], opts); } catch (e2) { html = "<code>" + it[0] + "</code>"; }
    return { ok: false, err: String(e), html: html };
  }
});
emit(JSON.stringify(out));
