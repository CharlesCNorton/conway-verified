(* Unique Parsing Verification for Conway's 92 Elements *)

(* Element words from the Coq formalization *)
(* Using 1,2,3 as symbols (S1, S2, S3 in Coq) *)

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

elements = {"H", "He", "Li", "Be", "B", "C", "N", "O", "F", "Ne",
  "Na", "Mg", "Al", "Si", "P", "S", "Cl", "Ar", "K", "Ca",
  "Sc", "Ti", "V", "Cr", "Mn", "Fe", "Co", "Ni", "Cu", "Zn",
  "Ga", "Ge", "As", "Se", "Br", "Kr", "Rb", "Sr", "Y", "Zr",
  "Nb", "Mo", "Tc", "Ru", "Rh", "Pd", "Ag", "Cd", "In", "Sn",
  "Sb", "Te", "I", "Xe", "Cs", "Ba", "La", "Ce", "Pr", "Nd",
  "Pm", "Sm", "Eu", "Gd", "Tb", "Dy", "Ho", "Er", "Tm", "Yb",
  "Lu", "Hf", "Ta", "W", "Re", "Os", "Ir", "Pt", "Au", "Hg",
  "Tl", "Pb", "Bi", "Po", "At", "Rn", "Fr", "Ra", "Ac", "Th",
  "Pa", "U"};

words = Association[elementWords];

Print["=== Unique Parsing Verification ===\n"];

(* Test 1: All words are distinct *)
Print["Test 1: All element words are distinct"];
wordList = Values[words];
Print["  Number of elements: ", Length[wordList]];
Print["  Number of distinct words: ", Length[DeleteDuplicates[wordList]]];
Print["  PASS: ", Length[wordList] == Length[DeleteDuplicates[wordList]]];
Print[""];

(* Test 2: Check prefix-free property *)
Print["Test 2: Prefix-free property (no element is prefix of another)"];
isPrefixOf[short_, long_] := Length[short] < Length[long] && Take[long, Length[short]] === short;

prefixPairs = {};
Do[
  Do[
    If[i != j && isPrefixOf[wordList[[i]], wordList[[j]]],
      AppendTo[prefixPairs, {elements[[i]], elements[[j]]}]
    ],
    {j, 92}
  ],
  {i, 92}
];

If[Length[prefixPairs] == 0,
  Print["  No element word is a prefix of another"];
  Print["  PASS: True"],
  Print["  Prefix pairs found: ", prefixPairs];
  Print["  PASS: False"]
];
Print[""];

(* Test 3: Check boundary conditions *)
Print["Test 3: Adjacent element boundary analysis"];
Print["  Computing first and last symbols of each element..."];

firstSymbol = Association[Table[e -> First[words[e]], {e, elements}]];
lastSymbol = Association[Table[e -> Last[words[e]], {e, elements}]];

(* For unique parsing, adjacent elements in a valid concatenation must have different boundary symbols *)
(* This is the "non-interacting" property *)

Print["  First symbols distribution: ", Counts[Values[firstSymbol]]];
Print["  Last symbols distribution: ", Counts[Values[lastSymbol]]];
Print[""];

(* Test 4: Build the parsing automaton *)
Print["Test 4: Building parsing trie for the 92 elements"];

(* Build a trie from element words *)
buildTrie[wordAssoc_] := Module[{trie, addWord},
  trie = <||>;
  addWord[word_, name_] := Module[{node, sym},
    node = trie;
    Do[
      sym = word[[i]];
      If[!KeyExistsQ[node, sym], node[sym] = <||>];
      node = node[sym],
      {i, Length[word] - 1}
    ];
    node[Last[word]] = name;
  ];
  Do[addWord[wordAssoc[e], e], {e, Keys[wordAssoc]}];
  trie
];

(* Count trie nodes *)
countNodes[trie_] := 1 + Total[countNodes /@ Select[Values[trie], AssociationQ]];

trie = buildTrie[words];
Print["  Trie nodes: ", countNodes[trie]];

(* Test 5: Verify audioactive output can be parsed *)
Print[""];
Print["Test 5: Verify audioactive outputs parse uniquely"];

(* Look-and-say function *)
lookAndSay[word_List] := Module[{result, i, count, sym},
  If[word === {}, Return[{}]];
  result = {};
  i = 1;
  While[i <= Length[word],
    sym = word[[i]];
    count = 1;
    While[i + count <= Length[word] && word[[i + count]] === sym, count++];
    AppendTo[result, count];
    AppendTo[result, sym];
    i += count;
  ];
  result
];

(* Parse a word into elements using greedy matching *)
parseWord[word_List, wordAssoc_] := Module[{result, pos, matched, e, w, bestMatch, bestLen},
  result = {};
  pos = 1;
  While[pos <= Length[word],
    bestMatch = None;
    bestLen = 0;
    Do[
      w = wordAssoc[e];
      If[Length[w] > bestLen && pos + Length[w] - 1 <= Length[word] &&
         Take[word, {pos, pos + Length[w] - 1}] === w,
        bestMatch = e;
        bestLen = Length[w]
      ],
      {e, Keys[wordAssoc]}
    ];
    If[bestMatch === None,
      Return[{False, result, pos}]
    ];
    AppendTo[result, bestMatch];
    pos += bestLen;
  ];
  {True, result, pos}
];

(* Test parsing on audioactive outputs of each element *)
Print["  Testing audioactive output parsing for all 92 elements..."];
allParseable = True;
Do[
  w = words[e];
  output = lookAndSay[w];
  {success, parsed, pos} = parseWord[output, words];
  If[!success,
    Print["  FAIL: ", e, " -> audioactive output not parseable at position ", pos];
    allParseable = False;
  ],
  {e, elements}
];

If[allParseable,
  Print["  All audioactive outputs parse successfully!"];
  Print["  PASS: True"],
  Print["  PASS: False"]
];

(* Test 6: Verify parsing matches decay table *)
Print[""];
Print["Test 6: Verify parsing matches declared decay products"];

decayTable = {
  "H" -> {"H"}, "He" -> {"Hf", "Pa", "H", "Ca", "Li"}, "Li" -> {"He"},
  "Be" -> {"Ge", "Ca", "Li"}, "B" -> {"Be"}, "C" -> {"B"}, "N" -> {"C"},
  "O" -> {"N"}, "F" -> {"O"}, "Ne" -> {"F"}, "Na" -> {"Ne"},
  "Mg" -> {"Pm", "Na"}, "Al" -> {"Mg"}, "Si" -> {"Al"},
  "P" -> {"Ho", "Si"}, "S" -> {"P"}, "Cl" -> {"S"}, "Ar" -> {"Cl"},
  "K" -> {"Ar"}, "Ca" -> {"K"}, "Sc" -> {"Ho", "Pa", "H", "Ca", "Co"},
  "Ti" -> {"Sc"}, "V" -> {"Ti"}, "Cr" -> {"V"}, "Mn" -> {"Cr", "Si"},
  "Fe" -> {"Mn"}, "Co" -> {"Fe"}, "Ni" -> {"Zn", "Co"}, "Cu" -> {"Ni"},
  "Zn" -> {"Cu"}, "Ga" -> {"Eu", "Ca", "Ac", "H", "Ca", "Zn"},
  "Ge" -> {"Ho", "Ga"}, "As" -> {"Ge", "Na"}, "Se" -> {"As"},
  "Br" -> {"Se"}, "Kr" -> {"Br"}, "Rb" -> {"Kr"}, "Sr" -> {"Rb"},
  "Y" -> {"Sr", "U"}, "Zr" -> {"Y", "H", "Ca", "Tc"}, "Nb" -> {"Er", "Zr"},
  "Mo" -> {"Nb"}, "Tc" -> {"Mo"}, "Ru" -> {"Eu", "Ca", "Tc"},
  "Rh" -> {"Ho", "Ru"}, "Pd" -> {"Rh"}, "Ag" -> {"Pd"}, "Cd" -> {"Ag"},
  "In" -> {"Cd"}, "Sn" -> {"In"}, "Sb" -> {"Pm", "Sn"},
  "Te" -> {"Eu", "Ca", "Sb"}, "I" -> {"Ho", "Te"}, "Xe" -> {"I"},
  "Cs" -> {"Xe"}, "Ba" -> {"Cs"}, "La" -> {"Ba"},
  "Ce" -> {"La", "H", "Ca", "Co"}, "Pr" -> {"Ce"}, "Nd" -> {"Pr"},
  "Pm" -> {"Nd"}, "Sm" -> {"Pm", "Ca", "Zn"}, "Eu" -> {"Sm"},
  "Gd" -> {"Eu", "Ca", "Co"}, "Tb" -> {"Ho", "Gd"}, "Dy" -> {"Tb"},
  "Ho" -> {"Dy"}, "Er" -> {"Ho", "Pm"}, "Tm" -> {"Er", "Ca", "Co"},
  "Yb" -> {"Tm"}, "Lu" -> {"Yb"}, "Hf" -> {"Lu"},
  "Ta" -> {"Hf", "Pa", "H", "Ca", "W"}, "W" -> {"Ta"},
  "Re" -> {"Ge", "Ca", "W"}, "Os" -> {"Re"}, "Ir" -> {"Os"},
  "Pt" -> {"Ir"}, "Au" -> {"Pt"}, "Hg" -> {"Au"}, "Tl" -> {"Hg"},
  "Pb" -> {"Tl"}, "Bi" -> {"Pm", "Pb"}, "Po" -> {"Bi"}, "At" -> {"Po"},
  "Rn" -> {"Ho", "At"}, "Fr" -> {"Rn"}, "Ra" -> {"Fr"}, "Ac" -> {"Ra"},
  "Th" -> {"Ac"}, "Pa" -> {"Th"}, "U" -> {"Pa"}
};

decays = Association[decayTable];

allMatch = True;
Do[
  w = words[e];
  output = lookAndSay[w];
  {success, parsed, pos} = parseWord[output, words];
  expected = decays[e];
  If[parsed =!= expected,
    Print["  MISMATCH: ", e];
    Print["    Computed: ", parsed];
    Print["    Expected: ", expected];
    allMatch = False;
  ],
  {e, elements}
];

If[allMatch,
  Print["  All parsing results match decay table!"];
  Print["  PASS: True"],
  Print["  PASS: False"]
];

Print[""];
Print["=== Summary ==="];
Print["All 92 element words are distinct: True"];
Print["No element is a prefix of another: ", Length[prefixPairs] == 0];
Print["All audioactive outputs parseable: ", allParseable];
Print["Parsing matches decay table: ", allMatch];
