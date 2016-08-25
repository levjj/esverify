var fs = require("fs");

require('browserify')(
  ["node_modules/JS_WALA/normalizer/lib/normalizer.js"],
  {standalone: "JS_WALA"}
).bundle((err, buf) => {
  let rewritten = String(buf).replace(
    /(if\(typeof Object\.defineProperty \!== 'undefined'\))/,
    "if([].flatmap) return;\n$1");
  fs.writeFileSync("jswala.js", rewritten);
});
