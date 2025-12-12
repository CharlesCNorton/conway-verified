(* Conway Cosmological Theorem - Comprehensive Convergence Analysis *)
(* Goal: Determine exact convergence bounds for arbitrary words *)

(* Element words from Coq formalization *)
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

(* Look-and-say function *)
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

(* Sort elements by word length descending for greedy parsing *)
sortedElements = SortBy[elements, -Length[elementWords[#]] &];

(* Greedy parser with boundary checking *)
parseWord[w_List] := Module[{result = {}, remaining = w, found, elem, eword},
  While[Length[remaining] > 0,
    found = False;
    Do[
      eword = elementWords[elem];
      If[Length[eword] <= Length[remaining] && Take[remaining, Length[eword]] === eword,
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

isElementConcat[w_List] := parseWord[w][[1]];

(* Find convergence iteration *)
findConvergence[start_List, maxIter_:50] := Module[{w = start, i},
  Do[
    If[isElementConcat[w], Return[i - 1]];
    w = lookAndSay[w];
  , {i, maxIter}];
  -1
];

Print["=== COMPREHENSIVE CONVERGENCE ANALYSIS ===\n"];

(* Test all words up to length 6 *)
Print["Testing all words of length 1-6 over {1,2,3}..."];

maxConv = 0;
worstCases = {};

Do[
  words = Tuples[{1, 2, 3}, len];
  convs = Table[{w, findConvergence[w, 30]}, {w, words}];
  maxInLen = Max[convs[[All, 2]]];
  worst = Select[convs, #[[2]] == maxInLen &];
  Print["  Length ", len, ": max convergence = ", maxInLen, " (", Length[worst], " cases)"];
  If[maxInLen > maxConv,
    maxConv = maxInLen;
    worstCases = worst;
  ];
, {len, 1, 6}];

Print["\nOverall maximum convergence: ", maxConv];
Print["Worst case examples: ", Take[worstCases, Min[5, Length[worstCases]]]];

(* Trace one worst case in detail *)
Print["\n=== DETAILED TRACE OF WORST CASE ==="];
If[Length[worstCases] > 0,
  worst = worstCases[[1, 1]];
  Print["Starting word: ", worst];
  w = worst;
  Do[
    parsed = parseWord[w];
    If[parsed[[1]],
      Print["  Iteration ", i, ": CONVERGED -> ", parsed[[2]]];
      Break[];
    ,
      Print["  Iteration ", i, ": length ", Length[w], ", first 20 symbols: ", Take[w, Min[20, Length[w]]]];
    ];
    w = lookAndSay[w];
  , {i, 0, 30}];
];

(* Verify prefix-free property *)
Print["\n=== PREFIX-FREE VERIFICATION ==="];
prefixPairs = {};
Do[
  w1 = elementWords[e1];
  Do[
    w2 = elementWords[e2];
    If[e1 =!= e2 && Length[w1] < Length[w2] && Take[w2, Length[w1]] === w1,
      AppendTo[prefixPairs, {e1, e2}];
    ];
  , {e2, elements}];
, {e1, elements}];

If[Length[prefixPairs] == 0,
  Print["Element words are PREFIX-FREE: No word is a prefix of another."];
,
  Print["PREFIX VIOLATIONS: ", prefixPairs];
];

(* Verify suffix-free property *)
Print["\n=== SUFFIX-FREE VERIFICATION ==="];
suffixPairs = {};
Do[
  w1 = elementWords[e1];
  Do[
    w2 = elementWords[e2];
    If[e1 =!= e2 && Length[w1] < Length[w2] && Take[w2, -Length[w1]] === w1,
      AppendTo[suffixPairs, {e1, e2}];
    ];
  , {e2, elements}];
, {e1, elements}];

Print["Suffix pairs found: ", Length[suffixPairs]];
If[Length[suffixPairs] > 0,
  Print["Examples: ", Take[suffixPairs, Min[10, Length[suffixPairs]]]];
];

(* Verify unique decodability via Sardinas-Patterson *)
Print["\n=== SARDINAS-PATTERSON UNIQUE DECODABILITY TEST ==="];

sardinasPatterson[codewords_] := Module[{S, Snew, dangling, w1, w2, d},
  dangling[a_, b_] := If[Length[a] < Length[b] && Take[b, Length[a]] === a,
    {Drop[b, Length[a]]}, {}];
  S = {};
  Do[
    Do[
      S = Union[S, dangling[w1, w2]];
    , {w2, codewords}];
  , {w1, codewords}];

  Do[
    If[MemberQ[S, {}] || MemberQ[codewords, Alternatives @@ S],
      Return["NOT UNIQUELY DECODABLE"]
    ];
    Snew = S;
    Do[
      Do[
        Snew = Union[Snew, dangling[w1, d], dangling[d, w1]];
      , {d, S}];
    , {w1, codewords}];
    If[Snew === S, Return["UNIQUELY DECODABLE"]];
    S = Snew;
  , {100}];
  "UNDETERMINED"
];

udResult = sardinasPatterson[wordList];
Print["Sardinas-Patterson result: ", udResult];

(* Verify boundary non-interaction for all decay products *)
Print["\n=== DECAY BOUNDARY VERIFICATION ==="];

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

boundaryViolations = {};
Do[
  prods = decayRules[e];
  Do[
    e1 = prods[[i]];
    e2 = prods[[i + 1]];
    last1 = Last[elementWords[e1]];
    first2 = First[elementWords[e2]];
    If[last1 === first2,
      AppendTo[boundaryViolations, {e, e1, e2, last1}];
    ];
  , {i, Length[prods] - 1}];
, {e, elements}];

If[Length[boundaryViolations] == 0,
  Print["All decay product boundaries are non-interacting!"];
,
  Print["BOUNDARY VIOLATIONS: ", boundaryViolations];
];

(* Verify audioactive equals decay concatenation *)
Print["\n=== AUDIOACTIVE = DECAY CONCATENATION VERIFICATION ==="];
allMatch = True;
Do[
  w = elementWords[e];
  computed = lookAndSay[w];
  expected = Flatten[elementWords[#] & /@ decayRules[e]];
  If[computed =!= expected,
    Print["MISMATCH for ", e];
    allMatch = False;
  ];
, {e, elements}];
If[allMatch, Print["All 92 elements verified: lookAndSay[word] = concat[decay products]"]];

Print["\n=== ANALYSIS COMPLETE ==="];
