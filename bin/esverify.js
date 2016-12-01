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

function run(err, js) {
  if (err) error('Error: ' + e.message);
  var p = Promise.resolve();
  var vcs = esverify.verify(js.toString());
  vcs.forEach(vc => {
    p = p.then(() => vc.solve())
         .then(() => console.log(vc.description, '\n', vc.result()));
  });
  p.then(() => process.exit(0));
  p.catch(e => error('Error: ' + e));
}

var fname = process.argv[2];
if (fname !== '-') {
  fs.readFile(fname, run);
} else {
  var content = '';
  process.stdin.resume();
  process.stdin.on('data', chunk => content += chunk);
  process.stdin.on('error', e => error('Error: ' + e.message));
  process.stdin.on('end', () => run(null, content));
}
