/* Runs C programs with the CInterp interpreter off the main thread. */
importScripts('cinterp.js');

function norm(s) {
  return s.replace(/\r/g, '').replace(/[ \t]+$/gm, '').replace(/\s+$/, '');
}

self.onmessage = function (ev) {
  var msg = ev.data;
  if (msg.type === 'run') {
    var t0 = Date.now();
    var r = CInterp.run(msg.code, msg.input || '', {});
    r.ms = Date.now() - t0;
    self.postMessage({ type: 'run-result', id: msg.id, result: r });
    return;
  }
  if (msg.type === 'judge') {
    var tests = msg.tests;
    var results = [];
    for (var i = 0; i < tests.length; i++) {
      var t0j = Date.now();
      var r2 = CInterp.run(msg.code, tests[i].input, {});
      var ms = Date.now() - t0j;
      var verdict;
      if (r2.status === 'CE') {
        self.postMessage({ type: 'judge-done', id: msg.id, compileError: r2.error, warnings: r2.warnings, results: [] });
        return;
      }
      if (r2.status === 'TLE') verdict = 'TLE';
      else if (r2.status === 'RE') verdict = 'RE';
      else if (norm(r2.stdout) !== norm(tests[i].output)) verdict = 'WA';
      else if (msg.leakCheck && r2.leaks.length) verdict = 'LEAK';
      else verdict = 'AC';
      var item = { i: i, verdict: verdict, ms: ms, stdout: r2.stdout, error: r2.error, leaks: r2.leaks, exitCode: r2.exitCode };
      results.push(item);
      self.postMessage({ type: 'judge-progress', id: msg.id, item: item, warnings: i === 0 ? r2.warnings : null });
    }
    self.postMessage({ type: 'judge-done', id: msg.id, results: results });
  }
};
