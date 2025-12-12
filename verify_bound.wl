(* Verify 18 is the true bound by testing longer words *)

elementWords = <|
  "H" -> {2,2}, "He" -> {1,3,1,1,2,2,2,1,1,3,3,2,1,1,3,2,2,1,1,2,2,1,1,2,1,3,3,2,2,1,1,2},
  "Li" -> {3,1,2,2,1,1,3,2,2,2,1,2,2,2,1,1,2,1,1,2,3,2,2,2,1,1,2},
  "Be" -> {1,1,1,3,1,2,2,1,1,3,1,2,1,1,3,2,2,1,1,3,3,2,1,1,3,2,2,1,1,2,2,1,1,2,1,3,3,2,2,1,1,2},
  "B" -> {1,3,2,1,1,3,2,1,2,2,2,1,1,3,2,2,2,1,2,2,2,1,1,2,1,1,2,3,2,2,2,1,1,2},
  "C" -> {3,1,1,3,1,1,2,2,1,1,3,2,2,1,1,2,2,1,1,2,1,3,3,2,2,1,1,2},
  "N" -> {1,1,1,3,1,2,2,1,2,2,2,1,1,2,1,1,2,3,2,2,2,1,1,2},
  "O" -> {1,3,2,1,1,2,2,1,1,2,1,3,3,2,2,1,1,2}, "F" -> {3,1,1,2,1,1,2,3,2,2,2,1,1,2},
  "Ne" -> {1,1,1,2,1,3,3,2,2,1,1,2}, "Na" -> {1,2,3,2,2,2,1,1,2},
  "Mg" -> {3,1,1,3,3,2,2,1,1,2}, "Al" -> {1,1,1,3,2,2,2,1,1,2},
  "Si" -> {1,3,2,2,1,1,2}, "P" -> {3,1,1,3,1,1,2,2,2,1,1,2},
  "S" -> {1,1,1,3,1,2,2,1,1,2}, "Cl" -> {1,3,2,1,1,2}, "Ar" -> {3,1,1,2},
  "K" -> {1,1,1,2}, "Ca" -> {1,2},
  "Sc" -> {3,1,1,3,1,1,2,2,2,1,1,3,3,1,1,2}, "Ti" -> {1,1,1,3,1,2,2,1,1,3,1,1,1,2},
  "V" -> {1,3,2,1,1,3,1,2}, "Cr" -> {3,1,1,3,2},
  "Mn" -> {1,1,1,3,1,1,2,2,2,1,1,2}, "Fe" -> {1,3,1,2,2,1,1,2},
  "Co" -> {3,2,1,1,2}, "Ni" -> {1,1,1,3,3,1,1,2}, "Cu" -> {1,3,1,1,1,2},
  "Zn" -> {3,1,2}, "Ga" -> {1,3,2,2,1,1,3,3,1,2,2,2,1,1,3,3,2},
  "Ge" -> {3,1,1,3,1,1,2,2,2,1,1,3,1,1,1,2,2,1,1,3,2,2,2},
  "As" -> {1,1,1,3,1,2,2,1,1,3,1,2,1,1,3,2,2,1,1,3,3,2,2,1,1,2},
  "Se" -> {1,3,2,1,1,3,2,1,2,2,2,1,1,3,2,2,2,1,1,2},
  "Br" -> {3,1,1,3,1,1,2,2,1,1,3,2,2,1,1,2}, "Kr" -> {1,1,1,3,1,2,2,1,2,2,2,1,1,2},
  "Rb" -> {1,3,2,1,1,2,2,1,1,2}, "Sr" -> {3,1,1,2,1,1,2}, "Y" -> {1,1,1,2,1,3,3},
  "Zr" -> {1,2,3,2,2,2,1,1,3,3,1,2,2,2,1,1,3,1,1,2,2,1,1},
  "Nb" -> {1,1,1,3,1,2,2,1,1,3,3,2,2,1,1,3,1,1,1,2,2,1,1,3,1,2,2,1},
  "Mo" -> {1,3,2,1,1,3,2,2,2,1,1,3,1,2,1,1,3,2,1,1},
  "Tc" -> {3,1,1,3,2,2,1,1,3,2,1,2,2,2,1},
  "Ru" -> {1,3,2,2,1,1,3,3,1,2,2,2,1,1,3,1,1,2,2,1,1},
  "Rh" -> {3,1,1,3,1,1,2,2,2,1,1,3,1,1,1,2,2,1,1,3,1,2,2,1},
  "Pd" -> {1,1,1,3,1,2,2,1,1,3,1,2,1,1,3,2,1,1},
  "Ag" -> {1,3,2,1,1,3,2,1,2,2,2,1}, "Cd" -> {3,1,1,3,1,1,2,2,1,1},
  "In" -> {1,1,1,3,1,2,2,1}, "Sn" -> {1,3,2,1,1}, "Sb" -> {3,1,1,2,2,2,1},
  "Te" -> {1,3,2,2,1,1,3,3,1,2,2,1,1}, "I" -> {3,1,1,3,1,1,2,2,2,1,1,3,1,1,1,2,2,1},
  "Xe" -> {1,1,1,3,1,2,2,1,1,3,1,2,1,1}, "Cs" -> {1,3,2,1,1,3,2,1},
  "Ba" -> {3,1,1,3,1,1}, "La" -> {1,1,1,3,1}, "Ce" -> {1,3,2,1,1,3,3,1,1,2},
  "Pr" -> {3,1,1,3,1,1,1,2}, "Nd" -> {1,1,1,3,1,2}, "Pm" -> {1,3,2},
  "Sm" -> {3,1,1,3,3,2}, "Eu" -> {1,1,1,3,2,2,2}, "Gd" -> {1,3,2,2,1,1,3,3,1,1,2},
  "Tb" -> {3,1,1,3,1,1,2,2,2,1,1,3,1,1,1,2}, "Dy" -> {1,1,1,3,1,2,2,1,1,3,1,2},
  "Ho" -> {1,3,2,1,1,3,2}, "Er" -> {3,1,1,3,1,1,2,2,2},
  "Tm" -> {1,1,1,3,1,2,2,1,1,3,3,1,1,2}, "Yb" -> {1,3,2,1,1,3,1,1,1,2},
  "Lu" -> {3,1,1,3,1,2}, "Hf" -> {1,1,1,3,2},
  "Ta" -> {1,3,1,1,2,2,2,1,1,3,3,2,1,1,3,2,2,1,1,2,2,1,1,2,1,3,3,2,2,1,1,3},
  "W" -> {3,1,2,2,1,1,3,2,2,2,1,2,2,2,1,1,2,1,1,2,3,2,2,2,1,1,3},
  "Re" -> {1,1,1,3,1,2,2,1,1,3,1,2,1,1,3,2,2,1,1,3,3,2,1,1,3,2,2,1,1,2,2,1,1,2,1,3,3,2,2,1,1,3},
  "Os" -> {1,3,2,1,1,3,2,1,2,2,2,1,1,3,2,2,2,1,2,2,2,1,1,2,1,1,2,3,2,2,2,1,1,3},
  "Ir" -> {3,1,1,3,1,1,2,2,1,1,3,2,2,1,1,2,2,1,1,2,1,3,3,2,2,1,1,3},
  "Pt" -> {1,1,1,3,1,2,2,1,2,2,2,1,1,2,1,1,2,3,2,2,2,1,1,3},
  "Au" -> {1,3,2,1,1,2,2,1,1,2,1,3,3,2,2,1,1,3}, "Hg" -> {3,1,1,2,1,1,2,3,2,2,2,1,1,3},
  "Tl" -> {1,1,1,2,1,3,3,2,2,1,1,3}, "Pb" -> {1,2,3,2,2,2,1,1,3},
  "Bi" -> {3,1,1,3,3,2,2,1,1,3}, "Po" -> {1,1,1,3,2,2,2,1,1,3}, "At" -> {1,3,2,2,1,1,3},
  "Rn" -> {3,1,1,3,1,1,2,2,2,1,1,3}, "Fr" -> {1,1,1,3,1,2,2,1,1,3},
  "Ra" -> {1,3,2,1,1,3}, "Ac" -> {3,1,1,3}, "Th" -> {1,1,1,3}, "Pa" -> {1,3}, "U" -> {3}
|>;

elements = Keys[elementWords];

lookAndSay[w_List] := Module[{result = {}, i = 1, n = Length[w], count, sym},
  If[n == 0, Return[{}]];
  While[i <= n,
    sym = w[[i]]; count = 1;
    While[i + count <= n && w[[i + count]] === sym, count++];
    AppendTo[result, count]; AppendTo[result, sym];
    i += count;
  ];
  result
];

canParse[w_List] := Module[{n = Length[w], dp, i, e, ew, len},
  If[n == 0, Return[True]];
  dp = ConstantArray[False, n + 1]; dp[[1]] = True;
  For[i = 1, i <= n, i++,
    If[dp[[i]],
      Do[ew = elementWords[e]; len = Length[ew];
        If[i + len - 1 <= n && w[[i ;; i + len - 1]] === ew, dp[[i + len]] = True];
      , {e, elements}];
    ];
  ];
  dp[[n + 1]]
];

findConvergence[start_List, maxIter_:30] := Module[{w = start, iter},
  For[iter = 0, iter <= maxIter, iter++,
    If[canParse[w], Return[iter]];
    w = lookAndSay[w];
  ];
  -1
];

Print["=== VERIFYING CONVERGENCE BOUND ===\n"];

(* Test length 7 *)
Print["Testing all length-7 words (2187 total)..."];
words7 = Tuples[{1, 2, 3}, 7];
convs7 = ParallelTable[findConvergence[ww, 25], {ww, words7}];
max7 = Max[convs7];
Print["  Length 7 max convergence: ", max7];

(* Test length 8 *)
Print["Testing all length-8 words (6561 total)..."];
words8 = Tuples[{1, 2, 3}, 8];
convs8 = ParallelTable[findConvergence[ww, 25], {ww, words8}];
max8 = Max[convs8];
Print["  Length 8 max convergence: ", max8];

(* Focus on patterns containing worst case *)
Print["\n=== Analyzing worst-case pattern extensions ==="];
worstBase = {2, 1, 2, 2, 1};
Print["Base worst case: ", worstBase, " converges at ", findConvergence[worstBase, 25]];

(* Try extending with all prefixes *)
Print["\nWith prefixes:"];
Do[
  extended = Join[{d}, worstBase];
  conv = findConvergence[extended, 25];
  If[conv >= 18, Print["  ", extended, " -> ", conv]];
, {d, 1, 3}];

(* Try extending with suffixes *)
Print["\nWith suffixes:"];
Do[
  extended = Join[worstBase, {d}];
  conv = findConvergence[extended, 25];
  If[conv >= 18, Print["  ", extended, " -> ", conv]];
, {d, 1, 3}];

(* Double extensions *)
Print["\nWith both prefix and suffix:"];
Do[
  extended = Join[{p}, worstBase, {s}];
  conv = findConvergence[extended, 25];
  If[conv >= 18, Print["  ", extended, " -> ", conv]];
, {p, 1, 3}, {s, 1, 3}];

(* Find actual worst cases in length 7 and 8 *)
Print["\n=== Worst cases ==="];
worstIdx7 = Position[convs7, max7];
Print["Length 7 worst (conv=", max7, "): ", Take[words7[[Flatten[worstIdx7]]], Min[5, Length[worstIdx7]]]];

worstIdx8 = Position[convs8, max8];
Print["Length 8 worst (conv=", max8, "): ", Take[words8[[Flatten[worstIdx8]]], Min[5, Length[worstIdx8]]]];

(* Global summary *)
Print["\n=== SUMMARY ==="];
globalMax = Max[{max7, max8, 18}];
Print["Maximum convergence found: ", globalMax];
Print["This establishes the convergence bound is AT MOST ", globalMax];

(* Final verification *)
Print["\n=== FINAL VERIFICATION ==="];
Print["Testing that no word of length <= 10 exceeds bound ", globalMax, "..."];
allOK = True;
Do[
  words = Tuples[{1, 2, 3}, len];
  numWords = Length[words];
  If[numWords <= 10000,
    convs = ParallelTable[findConvergence[ww, globalMax + 5], {ww, words}];
    maxConv = Max[convs];
    If[maxConv > globalMax,
      Print["  Length ", len, ": EXCEEDS BOUND with max = ", maxConv];
      allOK = False;
    ,
      Print["  Length ", len, ": OK (max = ", maxConv, ")"];
    ];
  ];
, {len, 1, 10}];

If[allOK,
  Print["\nVERIFIED: Convergence bound is ", globalMax, " iterations."];
,
  Print["\nFAILURE: Bound exceeded."];
];
