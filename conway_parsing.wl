(* Conway Cosmological Theorem - Unique Parsing Analysis *)
(* Verify that element words form a uniquely decodable code *)

(* Element words from Coq formalization *)
(* S1=1, S2=2, S3=3 *)

elementWords = {
  "H" -> {2,2},
  "He" -> {1,3,1,1,2,2,2,1,1,3,3,2,1,1,3,2,2,1,1,2,2,1,1,2,1,3,3,2,2,1,1,2},
  "Li" -> {3,1,2,2,1,1,3,2,2,2,1,2,2,2,1,1,2,1,1,2,3,2,2,2,1,1,2},
  "Be" -> {1,1,1,3,1,2,2,1,1,3,1,2,1,1,3,2,2,1,1,3,3,2,1,1,3,2,2,1,1,2,2,1,1,2,1,3,3,2,2,1,1,2},
  "B" -> {1,3,2,1,1,3,2,1,2,2,2,1,1,3,2,2,2,1,2,2,2,1,1,2,1,1,2,3,2,2,2,1,1,2},
  "C" -> {3,1,1,3,1,1,2,2,1,1,3,2,2,1,1,2,2,1,1,2,1,3,3,2,2,1,1,2},
  "N" -> {1,1,1,3,1,2,2,1,2,2,2,1,1,2,1,1,2,3,2,2,2,1,1,2},
  "O" -> {1,3,2,1,1,2,2,1,1,2,1,3,3,2,2,1,1,2},
  "F" -> {3,1,1,2,1,1,2,3,2,2,2,1,1,2},
  "Ne" -> {1,1,1,2,1,3,3,2,2,1,1,2},
  "Na" -> {1,2,3,2,2,2,1,1,2},
  "Mg" -> {3,1,1,3,3,2,2,1,1,2},
  "Al" -> {1,1,1,3,2,2,2,1,1,2},
  "Si" -> {1,3,2,2,1,1,2},
  "P" -> {3,1,1,3,1,1,2,2,2,1,1,2},
  "S" -> {1,1,1,3,1,2,2,1,1,2},
  "Cl" -> {1,3,2,1,1,2},
  "Ar" -> {3,1,1,2},
  "K" -> {1,1,1,2},
  "Ca" -> {1,2},
  "Sc" -> {3,1,1,3,1,1,2,2,2,1,1,3,3,1,1,2},
  "Ti" -> {1,1,1,3,1,2,2,1,1,3,1,1,1,2},
  "V" -> {1,3,2,1,1,3,1,2},
  "Cr" -> {3,1,1,3,2},
  "Mn" -> {1,1,1,3,1,1,2,2,2,1,1,2},
  "Fe" -> {1,3,1,2,2,1,1,2},
  "Co" -> {3,2,1,1,2},
  "Ni" -> {1,1,1,3,3,1,1,2},
  "Cu" -> {1,3,1,1,1,2},
  "Zn" -> {3,1,2},
  "Ga" -> {1,3,2,2,1,1,3,3,1,2,2,2,1,1,3,3,2},
  "Ge" -> {3,1,1,3,1,1,2,2,2,1,1,3,1,1,1,2,2,1,1,3,2,2,2},
  "As" -> {1,1,1,3,1,2,2,1,1,3,1,2,1,1,3,2,2,1,1,3,3,2,2,1,1,2},
  "Se" -> {1,3,2,1,1,3,2,1,2,2,2,1,1,3,2,2,2,1,1,2},
  "Br" -> {3,1,1,3,1,1,2,2,1,1,3,2,2,1,1,2},
  "Kr" -> {1,1,1,3,1,2,2,1,2,2,2,1,1,2},
  "Rb" -> {1,3,2,1,1,2,2,1,1,2},
  "Sr" -> {3,1,1,2,1,1,2},
  "Y" -> {1,1,1,2,1,3,3},
  "Zr" -> {1,2,3,2,2,2,1,1,3,3,1,2,2,2,1,1,3,1,1,2,2,1,1},
  "Nb" -> {1,1,1,3,1,2,2,1,1,3,3,2,2,1,1,3,1,1,1,2,2,1,1,3,1,2,2,1},
  "Mo" -> {1,3,2,1,1,3,2,2,2,1,1,3,1,2,1,1,3,2,1,1},
  "Tc" -> {3,1,1,3,2,2,1,1,3,2,1,2,2,2,1},
  "Ru" -> {1,3,2,2,1,1,3,3,1,2,2,2,1,1,3,1,1,2,2,1,1},
  "Rh" -> {3,1,1,3,1,1,2,2,2,1,1,3,1,1,1,2,2,1,1,3,1,2,2,1},
  "Pd" -> {1,1,1,3,1,2,2,1,1,3,1,2,1,1,3,2,1,1},
  "Ag" -> {1,3,2,1,1,3,2,1,2,2,2,1},
  "Cd" -> {3,1,1,3,1,1,2,2,1,1},
  "In" -> {1,1,1,3,1,2,2,1},
  "Sn" -> {1,3,2,1,1},
  "Sb" -> {3,1,1,2,2,2,1},
  "Te" -> {1,3,2,2,1,1,3,3,1,2,2,1,1},
  "I" -> {3,1,1,3,1,1,2,2,2,1,1,3,1,1,1,2,2,1},
  "Xe" -> {1,1,1,3,1,2,2,1,1,3,1,2,1,1},
  "Cs" -> {1,3,2,1,1,3,2,1},
  "Ba" -> {3,1,1,3,1,1},
  "La" -> {1,1,1,3,1},
  "Ce" -> {1,3,2,1,1,3,3,1,1,2},
  "Pr" -> {3,1,1,3,1,1,1,2},
  "Nd" -> {1,1,1,3,1,2},
  "Pm" -> {1,3,2},
  "Sm" -> {3,1,1,3,3,2},
  "Eu" -> {1,1,1,3,2,2,2},
  "Gd" -> {1,3,2,2,1,1,3,3,1,1,2},
  "Tb" -> {3,1,1,3,1,1,2,2,2,1,1,3,1,1,1,2},
  "Dy" -> {1,1,1,3,1,2,2,1,1,3,1,2},
  "Ho" -> {1,3,2,1,1,3,2},
  "Er" -> {3,1,1,3,1,1,2,2,2},
  "Tm" -> {1,1,1,3,1,2,2,1,1,3,3,1,1,2},
  "Yb" -> {1,3,2,1,1,3,1,1,1,2},
  "Lu" -> {3,1,1,3,1,2},
  "Hf" -> {1,1,1,3,2},
  "Ta" -> {1,3,1,1,2,2,2,1,1,3,3,2,1,1,3,2,2,1,1,2,2,1,1,2,1,3,3,2,2,1,1,3},
  "W" -> {3,1,2,2,1,1,3,2,2,2,1,2,2,2,1,1,2,1,1,2,3,2,2,2,1,1,3},
  "Re" -> {1,1,1,3,1,2,2,1,1,3,1,2,1,1,3,2,2,1,1,3,3,2,1,1,3,2,2,1,1,2,2,1,1,2,1,3,3,2,2,1,1,3},
  "Os" -> {1,3,2,1,1,3,2,1,2,2,2,1,1,3,2,2,2,1,2,2,2,1,1,2,1,1,2,3,2,2,2,1,1,3},
  "Ir" -> {3,1,1,3,1,1,2,2,1,1,3,2,2,1,1,2,2,1,1,2,1,3,3,2,2,1,1,3},
  "Pt" -> {1,1,1,3,1,2,2,1,2,2,2,1,1,2,1,1,2,3,2,2,2,1,1,3},
  "Au" -> {1,3,2,1,1,2,2,1,1,2,1,3,3,2,2,1,1,3},
  "Hg" -> {3,1,1,2,1,1,2,3,2,2,2,1,1,3},
  "Tl" -> {1,1,1,2,1,3,3,2,2,1,1,3},
  "Pb" -> {1,2,3,2,2,2,1,1,3},
  "Bi" -> {3,1,1,3,3,2,2,1,1,3},
  "Po" -> {1,1,1,3,2,2,2,1,1,3},
  "At" -> {1,3,2,2,1,1,3},
  "Rn" -> {3,1,1,3,1,1,2,2,2,1,1,3},
  "Fr" -> {1,1,1,3,1,2,2,1,1,3},
  "Ra" -> {1,3,2,1,1,3},
  "Ac" -> {3,1,1,3},
  "Th" -> {1,1,1,3},
  "Pa" -> {1,3},
  "U" -> {3}
};

elements = Keys[elementWords];
words = Values[elementWords];

Print["=== UNIQUE PARSING ANALYSIS ===\n"];
Print["Total elements: ", Length[elements]];

(* Check 1: Prefix-freeness *)
Print["\n=== CHECK 1: PREFIX-FREENESS ==="];

prefixPairs = {};
Do[
  w1 = elementWords[[elem1]];
  Do[
    w2 = elementWords[[elem2]];
    If[elem1 =!= elem2 && Length[w1] <= Length[w2],
      If[Take[w2, Length[w1]] === w1,
        AppendTo[prefixPairs, {elem1, elem2}];
      ];
    ];
  , {elem2, elements}];
, {elem1, elements}];

If[Length[prefixPairs] == 0,
  Print["Element words are PREFIX-FREE: No element word is a prefix of another."];
  Print["This guarantees unique left-to-right parsing!"];
,
  Print["WARNING: Found ", Length[prefixPairs], " prefix relationships:"];
  Do[Print["  ", p[[1]], " is a prefix of ", p[[2]]], {p, prefixPairs}];
];

(* Check 2: All words start differently at position 1 or 2 *)
Print["\n=== CHECK 2: INITIAL SYMBOL DISTRIBUTION ==="];

firstSymbols = GroupBy[Transpose[{elements, First /@ words}], Last -> First];
Print["Elements by first symbol:"];
Do[
  Print["  ", k, ": ", Length[firstSymbols[k]], " elements"];
, {k, Sort[Keys[firstSymbols]]}];

(* Check 3: Verify all words have correct structure (pairs) *)
Print["\n=== CHECK 3: WORD STRUCTURE ==="];

allEven = And @@ (EvenQ[Length[#]] & /@ words);
Print["All words have even length (pairs): ", allEven];

(* Check 4: No word is a suffix of another *)
Print["\n=== CHECK 4: SUFFIX-FREENESS ==="];

suffixPairs = {};
Do[
  w1 = elementWords[[elem1]];
  Do[
    w2 = elementWords[[elem2]];
    If[elem1 =!= elem2 && Length[w1] <= Length[w2],
      If[Take[w2, -Length[w1]] === w1,
        AppendTo[suffixPairs, {elem1, elem2}];
      ];
    ];
  , {elem2, elements}];
, {elem1, elements}];

If[Length[suffixPairs] == 0,
  Print["Element words are SUFFIX-FREE: No element word is a suffix of another."];
,
  Print["Found ", Length[suffixPairs], " suffix relationships:"];
  Do[Print["  ", p[[1]], " is a suffix of ", p[[2]]], {p, Take[suffixPairs, Min[10, Length[suffixPairs]]]}];
];

(* Check 5: Boundary conditions - last symbol distribution *)
Print["\n=== CHECK 5: BOUNDARY SYMBOL ANALYSIS ==="];

lastSymbols = GroupBy[Transpose[{elements, Last /@ words}], Last -> First];
Print["Elements by last symbol:"];
Do[
  Print["  ", k, ": ", Length[lastSymbols[k]], " elements"];
, {k, Sort[Keys[lastSymbols]]}];

(* The key for non-interaction: elements ending in 1 won't interact with elements starting with 1, etc. *)
Print["\n=== CHECK 6: BOUNDARY COMPATIBILITY MATRIX ==="];

(* For each pair (last symbol of e1, first symbol of e2), check if they differ *)
boundaryMatrix = Table[
  {Last[elementWords[[e1]]], First[elementWords[[e2]]]}
, {e1, elements}, {e2, elements}];

sameCount = Count[Flatten[boundaryMatrix, 1], {x_, x_}];
diffCount = Count[Flatten[boundaryMatrix, 1], {x_, y_} /; x =!= y];
Print["Boundary pairs where last(e1) = first(e2): ", sameCount];
Print["Boundary pairs where last(e1) != first(e2): ", diffCount];

(* Check 7: Test parsing of some concatenations *)
Print["\n=== CHECK 7: PARSING TEST ==="];

(* Simple greedy parser *)
parseWord[w_, wordList_] := Module[{result = {}, remaining = w, found},
  While[Length[remaining] > 0,
    found = False;
    Do[
      If[Length[wordList[[elem]]] <= Length[remaining] &&
         Take[remaining, Length[wordList[[elem]]]] === wordList[[elem]],
        AppendTo[result, elem];
        remaining = Drop[remaining, Length[wordList[[elem]]]];
        found = True;
        Break[];
      ];
    , {elem, elements}];
    If[Not[found],
      Return[{"PARSE_FAILED", remaining}];
    ];
  ];
  result
];

(* Test with some known element concatenations *)
testCases = {
  Join[elementWords["H"], elementWords["H"]],  (* H.H *)
  Join[elementWords["U"], elementWords["Pa"]], (* U.Pa *)
  Join[elementWords["Ca"], elementWords["K"]], (* Ca.K *)
  elementWords["He"]  (* He alone *)
};

Print["Test parsing results:"];
Do[
  result = parseWord[test, elementWords];
  Print["  ", test, " -> ", result];
, {test, testCases}];

(* Check 8: Verify decay products parse correctly *)
Print["\n=== CHECK 8: DECAY PRODUCT PARSING ==="];

decayRules = {"H" -> {"H"}, "He" -> {"Hf", "Pa", "H", "Ca", "Li"}, "Li" -> {"He"},
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
  "Pa" -> {"Th"}, "U" -> {"Pa"}};

(* For each element, the decay products concatenated should parse back to those products *)
allDecayParseOK = True;
Do[
  products = elem /. decayRules;
  concatenated = Flatten[elementWords[[#]] & /@ products];
  parsed = parseWord[concatenated, elementWords];
  If[parsed =!= products,
    Print["MISMATCH for ", elem, ": expected ", products, ", got ", parsed];
    allDecayParseOK = False;
  ];
, {elem, elements}];

If[allDecayParseOK,
  Print["All 92 element decays parse correctly back to their products!"];
];

Print["\n=== UNIQUE PARSING ANALYSIS COMPLETE ==="];
