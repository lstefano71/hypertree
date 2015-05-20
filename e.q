// js events

.js.row:{[d]if[Y;if[count G;if[0=count W 0;if[0<count n:.js.cnv[G;Q]d`row;if[count[get Z]>r:Z[`n_]?n;`P set .ht.row[not Z[`o_]r;P;G]n;:.js.set d]]]]]}
.js.col:{[d]if[X;if[count G;`P set .ht.P;(Z,`W`G)set'.ht.col[get Z;W;G;Q]d`col;:.js.set d]]}
.js.cell:{[d]if[X;if[count G;`P set .ht.P;(Z,`W`G)set'.ht.cell[get Z;W;G;Q]. d`col`row;:.js.set d]]}
.js.sorts:{[d]`S set d[`cols]!d`sorts;$[0=count S;.js.set d;[Z set .ht.sort[get Z;G;key S]get S;.js.ret d]]}
.js.groups:{[d]`F`G set'.js.sym d`visible`groups;`P set .ht.vpaths[P]G;Z set();.js.set d}
.js.get:{[d]`R set`start`end!"j"$d`start`end;.js.ret d}

/ event utilities
.js.cnv:{raze@[flip enlist z;i;{y$string x};upper q i:where"s"<>q:y count[z]#x]}
.js.exe:{.js[x`fn]x}
.js.val:{$[x in key[`.],raze{` sv'(`,x),/:1_key` sv`,x}each key`;get x;()]}
.js.set:{Z set .ht.cons[.js.val Z;T;P;A;S;(G;F);L]W;`Z set Z;.js.ret x}
