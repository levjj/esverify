#!/usr/bin/env node

var fs = require('fs');
var minimist = require('minimist2');
var esverify = require('../build/main/index.js');

function error (msg) {
  console.error(msg);
  process.exit(1);
}

function usage (err) {
  console.log('Usage: esverify [OPTIONS] FILE\n');
  console.log('Options:');
  console.log('  --z3path PATH           Path to local z3 executable');
  console.log('                          (default path is "z3")');
  console.log('  -r, --remote            Invokes z3 remotely via HTTP request');
  console.log('  --z3url URL             URL to remote z3 web server');
  console.log('  --noqi                  Disables quantifier instantiations');
  console.log('  -t, --timeout SECS      Sets timeout in seconds for z3');
  console.log('                          (default timeout is 10s, 0 disables timeout)');
  console.log('  -f, --logformat FORMAT  Format can be either "simple", "colored" or "html"');
  console.log('                          (default format is "colored")');
  console.log('  -q, --quiet             Suppresses output');
  console.log('  -v, --verbose           Prints SMT input, output and test code');
  console.log('  --logsmt PATH           Path for logging SMT input in verbose mode');
  console.log('                          (default path is "/tmp/vc.smt")');
  console.log('  -h, --help              Prints this help text and exit');
  console.log('  --version               Prints version information');
  process.exit(err ? 1 : 0);
}

var opts = minimist(process.argv.slice(2), {
  boolean: ['noqi', 'remote', 'quiet', 'verbose', 'help', 'version'],
  string: ['logformat', 'z3path', 'z3url', 'logsmt', 'timeout'],
  alias: {r: 'remote', f: 'logformat', q: 'quiet', t: 'timeout', v: 'verbose', h: 'help' },
  unknown: function(opt) { return opt[0] == '-' && opt != '-' ? usage(true) : true; }
});
if (opts.version) {
  console.log(require('../package.json').version);
  process.exit(0);
}
if (opts._.length != 1 || opts.help) usage(!opts.help);
opts.qi = !opts['noqi'];
if (opts.hasOwnProperty('timeout')) {
  opts.timeout = parseInt(opts.timeout, 10);
  if (!Number.isInteger(opts.timeout) || opts.timeout < 0) usage(true);
}
opts.filename = opts._[0];

function run (err, js) {
  if (err) error('Error: ' + err.message);
  esverify.verify(js.toString(), opts)
    .then(msgs => msgs.some(msg => msg.status != 'verified') && error('failed'));
}

if (opts.filename !== '-') {
  fs.readFile(opts.filename, run);
} else {
  var content = '';
  process.stdin.resume();
  process.stdin.on('data', chunk => content += chunk);
  process.stdin.on('error', e => error('Error: ' + e.message));
  process.stdin.on('end', () => run(null, content));
}
