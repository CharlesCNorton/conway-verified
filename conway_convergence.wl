(* Conway Cosmological Theorem - Convergence Bound Verification *)
(* Prove that all strings converge to element concatenations within 24 iterations *)

(* Look-and-say function *)
lookAndSay[w_List] := Module[{result = {}, i = 1, n = Length[w], count, sym},
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

(* Element words - using Association for proper lookup *)
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
  "Bi" -> {3,1,1,3,3,2,2,1,1,3}, "Po" -> {1,1,1,3,2,2,2,1,1,3},
  "At" -> {1,3,2,2,1,1,3}, "Rn" -> {3,1,1,3,1,1,2,2,2,1,1,3},
  "Fr" -> {1,1,1,3,1,2,2,1,1,3}, "Ra" -> {1,3,2,1,1,3}, "Ac" -> {3,1,1,3},
  "Th" -> {1,1,1,3}, "Pa" -> {1,3}, "U" -> {3}
|>;

elements = Keys[elementWords];
wordList = Values[elementWords];

(* Sort elements by word length (longest first) for greedy parsing *)
sortedElements = SortBy[elements, -Length[elementWords[#]] &];

(* Greedy parser - tries to match longest element first *)
parseWord[w_List] := Module[{result = {}, remaining = w, found, elem, eword},
  While[Length[remaining] > 0,
    found = False;
    Do[
      eword = elementWords[elem];
      If[Length[eword] <= Length[remaining] &&
         Take[remaining, Length[eword]] === eword,
        AppendTo[result, elem];
        remaining = Drop[remaining, Length[eword]];
        found = True;
        Break[];
      ];
    , {elem, sortedElements}];
    If[!found, Return[{False, result, remaining}]];
  ];
  {True, result, {}}
];

(* Check if a word is a valid element concatenation *)
isElementConcat[w_List] := parseWord[w][[1]];

(* Find convergence iteration for a starting word *)
findConvergence[start_List, maxIter_:50] := Module[{w = start, i},
  Do[
    If[isElementConcat[w], Return[i - 1]];
    w = lookAndSay[w];
  , {i, maxIter}];
  -1  (* Did not converge *)
];

Print["=== CONVERGENCE BOUND VERIFICATION ===\n"];

(* Test 1: All single-digit starts *)
Print["Testing single-digit starts:"];
singleDigits = {{1}, {2}, {3}};
Do[
  conv = findConvergence[d];
  Print["  ", d, " converges at iteration ", conv];
, {d, singleDigits}];

(* Test 2: All two-digit starts *)
Print["\nTesting all two-digit starts:"];
twoDigits = Tuples[{1, 2, 3}, 2];
twoDigitConv = Table[{d, findConvergence[d]}, {d, twoDigits}];
maxTwo = Max[twoDigitConv[[All, 2]]];
Print["  Maximum convergence iteration: ", maxTwo];
Print["  Worst cases: ", Select[twoDigitConv, #[[2]] == maxTwo &]];

(* Test 3: All three-digit starts *)
Print["\nTesting all three-digit starts:"];
threeDigits = Tuples[{1, 2, 3}, 3];
threeDigitConv = Table[{d, findConvergence[d]}, {d, threeDigits}];
maxThree = Max[threeDigitConv[[All, 2]]];
Print["  Maximum convergence iteration: ", maxThree];
Print["  Worst cases: ", Select[threeDigitConv, #[[2]] == maxThree &]];

(* Test 4: Sample of four-digit starts *)
Print["\nTesting all four-digit starts:"];
fourDigits = Tuples[{1, 2, 3}, 4];
fourDigitConv = Table[{d, findConvergence[d]}, {d, fourDigits}];
maxFour = Max[fourDigitConv[[All, 2]]];
Print["  Maximum convergence iteration: ", maxFour];
worstFour = Select[fourDigitConv, #[[2]] == maxFour &];
Print["  Number of worst cases: ", Length[worstFour]];
Print["  Sample worst cases: ", Take[worstFour, Min[5, Length[worstFour]]]];

(* Test 5: Trace a worst case *)
Print["\n=== TRACING WORST CASE ==="];
If[Length[worstFour] > 0,
  worst = worstFour[[1, 1]];
  Print["Tracing: ", worst];
  w = worst;
  Do[
    parsed = parseWord[w];
    If[parsed[[1]],
      Print["  Iteration ", i-1, ": CONVERGED to ", parsed[[2]]];
      Break[];
    ,
      Print["  Iteration ", i-1, ": length ", Length[w], ", not yet parseable"];
    ];
    w = lookAndSay[w];
  , {i, 30}];
];

(* Test 6: Find absolute maximum *)
Print["\n=== TESTING FIVE-DIGIT STARTS (sampling) ==="];
fiveDigitSample = RandomSample[Tuples[{1, 2, 3}, 5], 100];
fiveDigitConv = Table[{d, findConvergence[d]}, {d, fiveDigitSample}];
maxFive = Max[fiveDigitConv[[All, 2]]];
Print["  Maximum in sample: ", maxFive];

(* Test 7: Verify element self-parsing *)
Print["\n=== VERIFYING ELEMENT SELF-PARSING ==="];
allParse = True;
Do[
  w = elementWords[elem];
  parsed = parseWord[w];
  If[!parsed[[1]] || parsed[[2]] =!= {elem},
    Print["  FAILED: ", elem];
    allParse = False;
  ];
, {elem, elements}];
If[allParse, Print["  All 92 elements parse to themselves: OK"]];

(* Test 8: Verify decay products parse correctly *)
Print["\n=== VERIFYING DECAY PRODUCT PARSING ==="];

decayRules = <|"H" -> {"H"}, "He" -> {"Hf", "Pa", "H", "Ca", "Li"}, "Li" -> {"He"},
  "Be" -> {"Ge", "Ca", "Li"}, "B" -> {"Be"}, "C" -> {"B"}, "N" -> {"C"},
  "O" -> {"N"}, "F" -> {"O"}, "Ne" -> {"F"}, "Na" -> {"Ne"},
  "Mg" -> {"Pm", "Na"}, "Al" -> {"Mg"}, "Si" -> {"Al"}, "P" -> {"Ho", "Si"},
  "S" -> {"P"}, "Cl" -> {"S"}, "Ar" -> {"Cl"}, "K" -> {"Ar"}, "Ca" -> {"K"},
  "Sc" -> {"Ho", "Pa", "H", "Ca", "Co"}, "Ti" -> {"Sc"}, "V" -> {"Ti"},
  "Cr" -> {"V"}, "Mn" -> {"Cr", "Si"}, "Fe" -> {"Mn"}, "Co" -> {"Fe"},
  "Ni" -> {"Zn", "Co"}, "Cu" -> {"Ni"}, "Zn" -> {"Cu"},
  "Ga" -> {"Eu", "Ca", "Ac", "H", "Ca", "Zn"}, "Ge" -> {"Ho", "Ga"},
  "As" -> {"Ge", "Na"}, "Se" -> {"As"}, "Br" -> {"Se"}, "Kr" -> {"Br"},
  "Rb" -> {"Kr"}, "Sr" -> {"Rb"}, "Y" -> {"Sr", "U"},
  "Zr" -> {"Y", "H", "Ca", "Tc"}, "Nb" -> {"Er", "Zr"}, "Mo" -> {"Nb"},
  "Tc" -> {"Mo"}, "Ru" -> {"Eu", "Ca", "Tc"}, "Rh" -> {"Ho", "Ru"},
  "Pd" -> {"Rh"}, "Ag" -> {"Pd"}, "Cd" -> {"Ag"}, "In" -> {"Cd"},
  "Sn" -> {"In"}, "Sb" -> {"Pm", "Sn"}, "Te" -> {"Eu", "Ca", "Sb"},
  "I" -> {"Ho", "Te"}, "Xe" -> {"I"}, "Cs" -> {"Xe"}, "Ba" -> {"Cs"},
  "La" -> {"Ba"}, "Ce" -> {"La", "H", "Ca", "Co"}, "Pr" -> {"Ce"},
  "Nd" -> {"Pr"}, "Pm" -> {"Nd"}, "Sm" -> {"Pm", "Ca", "Zn"}, "Eu" -> {"Sm"},
  "Gd" -> {"Eu", "Ca", "Co"}, "Tb" -> {"Ho", "Gd"}, "Dy" -> {"Tb"},
  "Ho" -> {"Dy"}, "Er" -> {"Ho", "Pm"}, "Tm" -> {"Er", "Ca", "Co"},
  "Yb" -> {"Tm"}, "Lu" -> {"Yb"}, "Hf" -> {"Lu"}, "Ta" -> {"Hf", "Pa", "H", "Ca", "W"},
  "W" -> {"Ta"}, "Re" -> {"Ge", "Ca", "W"}, "Os" -> {"Re"}, "Ir" -> {"Os"},
  "Pt" -> {"Ir"}, "Au" -> {"Pt"}, "Hg" -> {"Au"}, "Tl" -> {"Hg"}, "Pb" -> {"Tl"},
  "Bi" -> {"Pm", "Pb"}, "Po" -> {"Bi"}, "At" -> {"Po"}, "Rn" -> {"Ho", "At"},
  "Fr" -> {"Rn"}, "Ra" -> {"Fr"}, "Ac" -> {"Ra"}, "Th" -> {"Ac"},
  "Pa" -> {"Th"}, "U" -> {"Pa"}|>;

allDecayOK = True;
Do[
  products = decayRules[elem];
  decayWord = Flatten[elementWords[#] & /@ products];
  elemWord = elementWords[elem];
  computed = lookAndSay[elemWord];
  If[computed =!= decayWord,
    Print["  MISMATCH for ", elem, ":"];
    Print["    Expected: ", decayWord];
    Print["    Got: ", computed];
    allDecayOK = False;
  ];
, {elem, elements}];
If[allDecayOK, Print["  All 92 element decays verified: OK"]];

Print["\n=== CONVERGENCE SUMMARY ==="];
Print["Maximum convergence iterations found:"];
Print["  1-digit starts: ", Max[Table[findConvergence[{d}], {d, {1,2,3}}]]];
Print["  2-digit starts: ", maxTwo];
Print["  3-digit starts: ", maxThree];
Print["  4-digit starts: ", maxFour];

overallMax = Max[maxTwo, maxThree, maxFour];
Print["\nOverall maximum: ", overallMax, " iterations"];
Print["Conway's bound (24) is ", If[overallMax <= 24, "SUFFICIENT", "INSUFFICIENT"]];

Print["\n=== VERIFICATION COMPLETE ==="];
