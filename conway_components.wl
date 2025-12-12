(* Conway Cosmological Theorem - Component Analysis *)
(* Investigating the strongly connected components *)

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

elementIndex = AssociationThread[elements -> Range[92]];

decayRules = {
  "H" -> {"H"}, "He" -> {"Hf", "Pa", "H", "Ca", "Li"}, "Li" -> {"He"},
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
  "Pa" -> {"Th"}, "U" -> {"Pa"}
};

(* Build decay matrix *)
decayMatrix = Table[0, {92}, {92}];
Do[
  elem = elements[[i]];
  products = elem /. decayRules;
  Do[j = elementIndex[prod]; decayMatrix[[i, j]] += 1, {prod, products}];
, {i, 92}];

(* Build directed graph *)
edges = Flatten[Table[
  elem = elements[[i]];
  products = elem /. decayRules;
  DirectedEdge[i, elementIndex[#]] & /@ products
, {i, 92}], 1];

g = Graph[Range[92], edges, VertexLabels -> Table[i -> elements[[i]], {i, 92}]];

Print["=== STRONGLY CONNECTED COMPONENTS ===\n"];

sccs = ConnectedComponents[g];
Print["Number of strongly connected components: ", Length[sccs]];

Do[
  Print["\nComponent ", c, " (", Length[sccs[[c]]], " elements):"];
  Print["  Elements: ", elements[[#]] & /@ Sort[sccs[[c]]]];
, {c, Length[sccs]}];

(* Check weak connectivity *)
Print["\n=== WEAK CONNECTIVITY ==="];
weakComps = WeaklyConnectedComponents[g];
Print["Number of weakly connected components: ", Length[weakComps]];

(* Analyze the decay DAG structure *)
Print["\n=== CONDENSATION GRAPH (SCC DAG) ==="];

(* Which component does each element belong to? *)
componentOf = Association[];
Do[
  Do[componentOf[v] = c, {v, sccs[[c]]}];
, {c, Length[sccs]}];

(* Edges between components *)
interComponentEdges = DeleteDuplicates[Select[
  {componentOf[#[[1]]], componentOf[#[[2]]]} & /@ edges,
  #[[1]] != #[[2]] &
]];

Print["Edges between components: ", interComponentEdges];

(* Check: which component contains H (the fixed point)? *)
hComponent = componentOf[1];
Print["\nHydrogen is in component: ", hComponent];
Print["Component with H has elements: ", elements[[#]] & /@ sccs[[hComponent]]];

(* Analyze reachability *)
Print["\n=== REACHABILITY ANALYSIS ==="];

(* Can we reach H from every element? *)
reachH = Table[
  Length[FindPath[g, i, 1, Infinity, 1]] > 0
, {i, 92}];

reachableFromAll = And @@ reachH;
Print["H is reachable from all elements: ", reachableFromAll];

unreachable = Select[Range[92], Not[reachH[[#]]] &];
If[Length[unreachable] > 0,
  Print["Elements that cannot reach H: ", elements[[#]] & /@ unreachable];
];

(* What is the longest path to H? *)
Print["\n=== PATH LENGTHS TO H ==="];

pathLengths = Table[
  paths = FindPath[g, i, 1, Infinity, All];
  If[Length[paths] > 0,
    Min[Length /@ paths] - 1,  (* -1 because path length = edges *)
    Infinity
  ]
, {i, 92}];

finitePathLengths = Select[Transpose[{elements, pathLengths}], #[[2]] < Infinity &];
maxPath = Max[Select[pathLengths, # < Infinity &]];
Print["Maximum path length to H: ", maxPath];
Print["Elements with maximum path length:"];
Print["  ", Select[finitePathLengths, #[[2]] == maxPath &][[All, 1]]];

(* Distribution of path lengths *)
Print["\nPath length distribution:"];
lengthDist = Tally[Select[pathLengths, # < Infinity &]];
Do[Print["  Length ", d[[1]], ": ", d[[2]], " elements"], {d, Sort[lengthDist]}];

(* Extract Conway's degree-71 polynomial *)
Print["\n=== CONWAY'S DEGREE-71 POLYNOMIAL ==="];

M = SparseArray[decayMatrix];
charPoly = CharacteristicPolynomial[M, x];
factors = FactorList[charPoly];

degree71Factor = Select[factors, Exponent[#[[1]], x] == 71 &];
If[Length[degree71Factor] > 0,
  conwayPoly = degree71Factor[[1, 1]];
  Print["Conway's polynomial (degree 71):"];
  coeffs = CoefficientList[conwayPoly, x];
  Print["Coefficients (constant to leading):"];
  Print[coeffs];

  (* Verify against known Conway polynomial *)
  (* The polynomial is: x^71 - x^69 - 2x^68 - x^67 + 2x^66 + 2x^65 + x^64 - x^63 - ... *)
  Print["\nFirst few terms: ",
    Sum[coeffs[[i+1]] x^i, {i, 0, Min[10, Length[coeffs]-1]}] + " ... + x^71"];
];

(* Other factors *)
Print["\n=== OTHER FACTORS ==="];
otherFactors = Select[factors, Exponent[#[[1]], x] != 71 && Exponent[#[[1]], x] > 0 &];
Do[
  Print["Degree ", Exponent[f[[1]], x], " factor: ", f[[1]], " (multiplicity ", f[[2]], ")"];
, {f, otherFactors}];

Print["\n=== ANALYSIS COMPLETE ==="];
