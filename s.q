// hypertree server

\p 12346

\l t.q
\l x.q
\l a.q
\l d.q
\l e.q

/ connect to client
.js.K:0Ni
.z.po:{[w]`.js.K set w;neg[.js.K](`.js.ini;.js.obj[]);}
.z.pc:{[w]`.js.K set 0Ni}
.z.ps:{.js.snd .js.exe x}

/ utilities
.js.snd:{neg[.js.K](`.js.exe;x)}
.js.obj:{{x!get each x}`$'"AFGHIJLNOPQRSTUVWXYZ"}
.js.ret:{(x;.js.obj[])}
.js.upd:{if[not null .js.K;Z set();P[1]:.ht.P 1;.js.snd .js.set()]}

/ define Z
.js.set();
