#!/usr/bin/env node

var fs = require('fs');
var esverify = require("../esverify.js");

function error(msg) {
  console.error(msg);
  process.exit(1);
}

if (process.argv.length != 3) {
  error("Usage: esverify [file.js|-]");
}

var opts = { logMessages: true };
function run(err, js) {
  if (err) error('Error: ' + e.message);
  esverify.verify(js.toString(), opts)
    .then(msgs => msgs.forEach(msg => msg.status != "verified" && error("failed")));
}

var fname = process.argv[2];
if (fname !== '-') {
  opts.filename = fname;
  fs.readFile(fname, run);
} else {
  var content = '';
  process.stdin.resume();
  process.stdin.on('data', chunk => content += chunk);
  process.stdin.on('error', e => error('Error: ' + e.message));
  process.stdin.on('end', () => run(null, content));
}
