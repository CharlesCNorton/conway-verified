(* Conway Cosmological Theorem - Nilpotent Subspace Analysis *)
(* Understanding the 18 zero eigenvalues *)

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

decayMatrix = Table[0, {92}, {92}];
Do[elem = elements[[i]]; products = elem /. decayRules;
  Do[j = elementIndex[prod]; decayMatrix[[i, j]] += 1, {prod, products}], {i, 92}];

M = SparseArray[decayMatrix];

Print["=== ZERO EIGENVALUE ANALYSIS ===\n"];

(* Compute null space *)
nullSpace = NullSpace[M];
Print["Dimension of null space: ", Length[nullSpace]];

(* Compute generalized eigenspace for eigenvalue 0 *)
(* The algebraic multiplicity is 18, let's find the generalized null space *)

Print["\n=== NILPOTENT INDEX ==="];
(* Find the smallest k such that dim(ker(M^k)) = 18 *)
Do[
  kerDim = Length[NullSpace[MatrixPower[M, k]]];
  Print["dim(ker(M^", k, ")) = ", kerDim];
  If[kerDim == 18, Print["Nilpotent index reached at k = ", k]; Break[]];
, {k, 1, 20}];

(* Jordan form analysis *)
Print["\n=== JORDAN STRUCTURE ==="];

(* Count Jordan blocks for eigenvalue 0 *)
(* Using the formula: number of k×k blocks = rank(M^{k-1}) - 2*rank(M^k) + rank(M^{k+1}) *)
ranks = Table[MatrixRank[MatrixPower[M, k]], {k, 0, 10}];
Print["Ranks of M^k:"];
Do[Print["  rank(M^", k-1, ") = ", ranks[[k]]], {k, 1, Length[ranks]}];

Print["\nJordan block analysis for eigenvalue 0:"];
Do[
  (* Number of blocks of size >= k *)
  blocksGEk = ranks[[k]] - ranks[[k+1]];
  Print["  Jordan blocks of size >= ", k, ": ", blocksGEk];
, {k, 1, 5}];

(* Which elements are involved in the nilpotent part? *)
Print["\n=== STRUCTURAL ANALYSIS ==="];

(* Elements with no predecessors (sources) *)
columnSums = Total[decayMatrix];
sources = Select[Range[92], columnSums[[#]] == 0 &];
Print["Elements with no predecessors (pure sources): ", Length[sources]];
If[Length[sources] > 0, Print["  ", elements[[#]] & /@ sources]];

(* Elements that decay to a single other element (simple chains) *)
rowSums = Total /@ decayMatrix;
simpleElements = Select[Range[92], rowSums[[#]] == 1 &];
Print["\nElements with single decay product: ", Length[simpleElements]];

(* Find long chains (elements that form linear sequences) *)
Print["\n=== CHAIN ANALYSIS ==="];

(* Find elements where M[i,j] = 1 and element j has exactly one predecessor *)
chains = {};
Do[
  If[rowSums[[i]] == 1,
    j = First[Select[Range[92], decayMatrix[[i, #]] == 1 &]];
    If[columnSums[[j]] == 1,  (* j has exactly one predecessor *)
      AppendTo[chains, {elements[[i]], elements[[j]]}];
    ];
  ];
, {i, 92}];

Print["Simple chain links (A -> B where B has only A as predecessor):"];
Print["  ", Length[chains], " such links"];

(* Trace chains *)
Print["\n=== MAXIMAL CHAINS ==="];

(* Build chain graph *)
chainSuccessor = Association[];
Do[
  If[rowSums[[i]] == 1,
    j = First[Select[Range[92], decayMatrix[[i, #]] == 1 &]];
    chainSuccessor[i] = j;
  ];
, {i, 92}];

(* Find chain starts (elements with no chain predecessor) *)
chainTargets = Values[chainSuccessor];
chainStarts = Select[Keys[chainSuccessor], Not[MemberQ[chainTargets, #]] &];

Print["Chain starting points: ", elements[[#]] & /@ chainStarts];

(* Trace each maximal chain *)
Do[
  chain = {start};
  current = start;
  While[KeyExistsQ[chainSuccessor, current],
    current = chainSuccessor[current];
    AppendTo[chain, current];
  ];
  If[Length[chain] >= 3,
    Print["  ", elements[[#]] & /@ chain, " (length ", Length[chain], ")"];
  ];
, {start, chainStarts}];

(* Understanding the structure of Conway's 92 elements *)
Print["\n=== SUMMARY ==="];
Print["The 18 zero eigenvalues correspond to the structural deficit"];
Print["between the 92 elements and the 74 independent generators."];
Print["This reflects the existence of long chains in the decay structure."];

Print["\n=== ANALYSIS COMPLETE ==="];
