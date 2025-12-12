elementWords = <|
  "H" -> {2,2}, "He" -> {1,3,1,1,2,2,2,1,1,3,3,2,1,1,3,2,2,1,1,2,2,1,1,2,1,3,3,2,2,1,1,2},
  "Li" -> {3,1,2,2,1,1,3,2,2,2,1,2,2,2,1,1,2,1,1,2,3,2,2,2,1,1,2},
  "Ca" -> {1,2}, "Pa" -> {1,3}, "U" -> {3}, "Zn" -> {3,1,2}, "Pm" -> {1,3,2},
  "Th" -> {1,1,1,3}, "K" -> {1,1,1,2}, "Ar" -> {3,1,1,2}, "Hf" -> {1,1,1,3,2},
  "La" -> {1,1,1,3,1}, "Nd" -> {1,1,1,3,1,2}, "Ac" -> {3,1,1,3}, "Cr" -> {3,1,1,3,2},
  "Lu" -> {3,1,1,3,1,2}, "Ba" -> {3,1,1,3,1,1}, "Sm" -> {3,1,1,3,3,2},
  "Co" -> {3,2,1,1,2}, "Fe" -> {1,3,1,2,2,1,1,2}, "Ho" -> {1,3,2,1,1,3,2}
|>;

elements = Keys[elementWords];

Print["Checking boundary matches..."];
Print["Format: last(e1) vs first(e2)"];
matches = {};
Do[
  w1 = elementWords[e1];
  last1 = Last[w1];
  Do[
    w2 = elementWords[e2];
    first2 = First[w2];
    If[last1 === first2,
      AppendTo[matches, {e1, e2, last1}];
    ];
  , {e2, elements}];
, {e1, elements}];

If[Length[matches] > 0,
  Print["MATCHES FOUND:"];
  Do[Print["  last(", m[[1]], ")=", m[[3]], " = first(", m[[2]], ")"], {m, matches}];
,
  Print["No matches found."];
];
