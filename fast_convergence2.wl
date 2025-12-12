(* Fast Convergence Analysis - Fixed *)

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
wordList = Values[elementWords];

lookAndSay[w_List] := Module[{result = {}, i = 1, n = Length[w], count, sym},
  If[n == 0, Return[{}]];
  While[i <= n,
    sym = w[[i]];
    count = 1;
    While[i + count <= n && w[[i + count]] === sym, count++];
    AppendTo[result, count];
    AppendTo[result, sym];
    i += count;
  ];
  result
];

(* DP parser *)
canParse[w_List] := Module[{n = Length[w], dp, i, e, ew, len},
  If[n == 0, Return[True]];
  dp = ConstantArray[False, n + 1];
  dp[[1]] = True;
  For[i = 1, i <= n, i++,
    If[dp[[i]],
      Do[
        ew = elementWords[e];
        len = Length[ew];
        If[i + len - 1 <= n && w[[i ;; i + len - 1]] === ew,
          dp[[i + len]] = True;
        ];
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

Print["=== CONVERGENCE ANALYSIS ===\n"];

(* Test single digits *)
Print["Single digits:"];
Do[
  conv = findConvergence[{d}, 30];
  Print["  {", d, "} converges at iteration ", conv];
, {d, 1, 3}];

(* Trace {1} *)
Print["\nDetailed trace of {1}:"];
w = {1};
For[i = 0, i <= 12, i++,
  p = canParse[w];
  Print["  Iteration ", i, ": length=", Length[w], ", parses=", p,
        If[Length[w] <= 15, ", word=" <> ToString[w], ""]];
  If[p, Break[]];
  w = lookAndSay[w];
];

(* Test all short words *)
Print["\n=== Maximum convergence by starting length ==="];
Do[
  words = Tuples[{1, 2, 3}, len];
  convs = Table[findConvergence[ww, 30], {ww, words}];
  maxC = Max[convs];
  worstList = Select[Transpose[{words, convs}], #[[2]] == maxC &][[All, 1]];
  Print["Length ", len, ": max convergence = ", maxC];
  Print["  Worst cases: ", Take[worstList, Min[3, Length[worstList]]]];
, {len, 1, 5}];

(* Find THE worst case overall *)
Print["\n=== Searching for global maximum convergence ==="];
globalMax = 0;
globalWorst = {};
Do[
  words = Tuples[{1, 2, 3}, len];
  Do[
    conv = findConvergence[ww, 30];
    If[conv > globalMax,
       globalMax = conv;
       globalWorst = {ww}];
    If[conv == globalMax && !MemberQ[globalWorst, ww],
       AppendTo[globalWorst, ww]];
  , {ww, words}];
  Print["After length ", len, ": global max = ", globalMax];
, {len, 1, 6}];

Print["\nGlobal maximum convergence: ", globalMax];
Print["Worst starting words: ", Take[globalWorst, Min[10, Length[globalWorst]]]];

(* Trace the worst case *)
If[Length[globalWorst] > 0,
  Print["\n=== Detailed trace of worst case ==="];
  w = globalWorst[[1]];
  Print["Starting word: ", w];
  For[i = 0, i <= globalMax + 2, i++,
    p = canParse[w];
    Print["  Iter ", i, ": len=", Length[w], ", parses=", p];
    If[p, Break[]];
    w = lookAndSay[w];
  ];
];

Print["\n=== Element verification ==="];
allOK = True;
Do[
  w = elementWords[e];
  For[iter = 0, iter <= 10, iter++,
    If[!canParse[w],
      Print["FAILURE: ", e, " fails at iteration ", iter];
      allOK = False;
      Break[];
    ];
    w = lookAndSay[w];
  ];
, {e, elements}];
If[allOK, Print["All 92 elements remain parseable for 10 iterations."]];

Print["\n=== COMPLETE ==="];
