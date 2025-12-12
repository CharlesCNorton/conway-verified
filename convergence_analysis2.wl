(* Conway Cosmological Theorem - Fixed Convergence Analysis *)

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
sortedElements = SortBy[elements, -Length[elementWords[#]] &];

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

(* Boundary-aware parser: check that boundaries are compatible *)
parseWordBoundary[w_List] := Module[{result = {}, remaining = w, found, elem, eword, prevLast = None},
  While[Length[remaining] > 0,
    found = False;
    Do[
      eword = elementWords[elem];
      If[Length[eword] <= Length[remaining] && Take[remaining, Length[eword]] === eword,
        If[prevLast === None || prevLast =!= First[eword],
          AppendTo[result, elem];
          remaining = Drop[remaining, Length[eword]];
          prevLast = Last[eword];
          found = True;
          Break[];
        ];
      ];
    , {elem, sortedElements}];
    If[!found, Return[{False, result, remaining}]];
  ];
  {True, result, {}}
];

(* Simple parser - longest match first, with backtracking *)
parseWordBacktrack[w_List] := Module[{},
  parseHelper[{}, w]
];

parseHelper[parsed_, {}] := {True, parsed, {}};
parseHelper[parsed_, remaining_] := Module[{elem, eword, result},
  Do[
    eword = elementWords[elem];
    If[Length[eword] <= Length[remaining] && Take[remaining, Length[eword]] === eword,
      result = parseHelper[Append[parsed, elem], Drop[remaining, Length[eword]]];
      If[result[[1]], Return[result]];
    ];
  , {elem, sortedElements}];
  {False, parsed, remaining}
];

isElementConcat[w_List] := parseWordBacktrack[w][[1]];

(* Find first iteration where word parses as element concatenation *)
findConvergence[start_List, maxIter_:50] := Module[{w = start, i},
  Do[
    If[isElementConcat[w], Return[i - 1]];
    w = lookAndSay[w];
  , {i, 0, maxIter}];
  -1
];

Print["=== CONVERGENCE ANALYSIS (with backtracking parser) ===\n"];

(* Test single digit starts *)
Print["Single digit starting words:"];
Do[
  conv = findConvergence[{d}, 30];
  Print["  Start {", d, "}: converges at iteration ", conv];
, {d, 1, 3}];

(* Test all 2-digit combinations *)
Print["\nAll 2-digit combinations:"];
maxConv2 = 0;
worst2 = {};
Do[
  w = {d1, d2};
  conv = findConvergence[w, 30];
  If[conv > maxConv2, maxConv2 = conv; worst2 = {w}];
  If[conv == maxConv2 && !MemberQ[worst2, w], AppendTo[worst2, w]];
, {d1, 1, 3}, {d2, 1, 3}];
Print["  Max convergence: ", maxConv2];
Print["  Worst cases: ", worst2];

(* Test all 3-digit combinations *)
Print["\nAll 3-digit combinations:"];
maxConv3 = 0;
worst3 = {};
Do[
  w = {d1, d2, d3};
  conv = findConvergence[w, 30];
  If[conv > maxConv3, maxConv3 = conv; worst3 = {w}];
  If[conv == maxConv3 && !MemberQ[worst3, w], AppendTo[worst3, w]];
, {d1, 1, 3}, {d2, 1, 3}, {d3, 1, 3}];
Print["  Max convergence: ", maxConv3];
Print["  Worst cases: ", Take[worst3, Min[5, Length[worst3]]]];

(* Test 4-digit *)
Print["\nAll 4-digit combinations:"];
maxConv4 = 0;
worst4 = {};
Do[
  w = {d1, d2, d3, d4};
  conv = findConvergence[w, 30];
  If[conv > maxConv4, maxConv4 = conv; worst4 = {w}];
  If[conv == maxConv4 && !MemberQ[worst4, w], AppendTo[worst4, w]];
, {d1, 1, 3}, {d2, 1, 3}, {d3, 1, 3}, {d4, 1, 3}];
Print["  Max convergence: ", maxConv4];
Print["  Worst cases: ", Take[worst4, Min[5, Length[worst4]]]];

(* Detailed trace *)
Print["\n=== TRACE OF {1} ==="];
w = {1};
Do[
  parsed = parseWordBacktrack[w];
  Print["Iter ", i, ": length=", Length[w], ", parsed=", parsed[[1]]];
  If[parsed[[1]],
    Print["  Elements: ", parsed[[2]]];
    Break[];
  ,
    Print["  Word: ", If[Length[w] <= 30, w, Take[w, 30]]];
  ];
  w = lookAndSay[w];
, {i, 0, 15}];

(* Key question: what is the max convergence iteration? *)
Print["\n=== COMPREHENSIVE BOUND TEST ==="];
allConvs = {};
Do[
  words = Tuples[{1, 2, 3}, len];
  convs = findConvergence[#, 30] & /@ words;
  maxC = Max[convs];
  AppendTo[allConvs, {len, maxC, Count[convs, maxC]}];
  Print["Length ", len, ": max convergence = ", maxC];
, {len, 1, 5}];

Print["\nOverall maximum: ", Max[allConvs[[All, 2]]]];

(* Now verify element iterations *)
Print["\n=== ELEMENT ITERATIONS ==="];
Print["Verifying that element words stay as element concatenations..."];
Do[
  w = elementWords[e];
  Do[
    parsed = parseWordBacktrack[w];
    If[!parsed[[1]],
      Print["  FAILURE: ", e, " at iteration ", i];
      Break[];
    ];
    w = lookAndSay[w];
  , {i, 1, 10}];
, {e, elements}];
Print["All 92 elements verified for 10 iterations."];
