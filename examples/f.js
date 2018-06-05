let x = 0;

function f() { ensures(pure()); x++; }       // not actually pure
function g() { ensures(pure()); return x + 1; }
function h1() { /*empty*/ }
function h2a() { h1(); }
function h2b() { ensures(pure()); h1(); }    // inlining h1 shows purity
function h3a() { ensures(pure()); h2a(); }   // not verified because inlining restricted to one level
function h3b() { ensures(pure()); h2b(); }   // verified because h2b marked as pure`,
