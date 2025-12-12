(* Conway Cosmological Theorem - Decay Matrix Analysis *)
(* Step 1: Build the 92x92 decay matrix *)

(* Element list in order (indices 1-92) *)
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

(* Create index lookup *)
elementIndex = AssociationThread[elements -> Range[92]];

(* Decay rules from Coq formalization *)
decayRules = {
  "H" -> {"H"},
  "He" -> {"Hf", "Pa", "H", "Ca", "Li"},
  "Li" -> {"He"},
  "Be" -> {"Ge", "Ca", "Li"},
  "B" -> {"Be"},
  "C" -> {"B"},
  "N" -> {"C"},
  "O" -> {"N"},
  "F" -> {"O"},
  "Ne" -> {"F"},
  "Na" -> {"Ne"},
  "Mg" -> {"Pm", "Na"},
  "Al" -> {"Mg"},
  "Si" -> {"Al"},
  "P" -> {"Ho", "Si"},
  "S" -> {"P"},
  "Cl" -> {"S"},
  "Ar" -> {"Cl"},
  "K" -> {"Ar"},
  "Ca" -> {"K"},
  "Sc" -> {"Ho", "Pa", "H", "Ca", "Co"},
  "Ti" -> {"Sc"},
  "V" -> {"Ti"},
  "Cr" -> {"V"},
  "Mn" -> {"Cr", "Si"},
  "Fe" -> {"Mn"},
  "Co" -> {"Fe"},
  "Ni" -> {"Zn", "Co"},
  "Cu" -> {"Ni"},
  "Zn" -> {"Cu"},
  "Ga" -> {"Eu", "Ca", "Ac", "H", "Ca", "Zn"},
  "Ge" -> {"Ho", "Ga"},
  "As" -> {"Ge", "Na"},
  "Se" -> {"As"},
  "Br" -> {"Se"},
  "Kr" -> {"Br"},
  "Rb" -> {"Kr"},
  "Sr" -> {"Rb"},
  "Y" -> {"Sr", "U"},
  "Zr" -> {"Y", "H", "Ca", "Tc"},
  "Nb" -> {"Er", "Zr"},
  "Mo" -> {"Nb"},
  "Tc" -> {"Mo"},
  "Ru" -> {"Eu", "Ca", "Tc"},
  "Rh" -> {"Ho", "Ru"},
  "Pd" -> {"Rh"},
  "Ag" -> {"Pd"},
  "Cd" -> {"Ag"},
  "In" -> {"Cd"},
  "Sn" -> {"In"},
  "Sb" -> {"Pm", "Sn"},
  "Te" -> {"Eu", "Ca", "Sb"},
  "I" -> {"Ho", "Te"},
  "Xe" -> {"I"},
  "Cs" -> {"Xe"},
  "Ba" -> {"Cs"},
  "La" -> {"Ba"},
  "Ce" -> {"La", "H", "Ca", "Co"},
  "Pr" -> {"Ce"},
  "Nd" -> {"Pr"},
  "Pm" -> {"Nd"},
  "Sm" -> {"Pm", "Ca", "Zn"},
  "Eu" -> {"Sm"},
  "Gd" -> {"Eu", "Ca", "Co"},
  "Tb" -> {"Ho", "Gd"},
  "Dy" -> {"Tb"},
  "Ho" -> {"Dy"},
  "Er" -> {"Ho", "Pm"},
  "Tm" -> {"Er", "Ca", "Co"},
  "Yb" -> {"Tm"},
  "Lu" -> {"Yb"},
  "Hf" -> {"Lu"},
  "Ta" -> {"Hf", "Pa", "H", "Ca", "W"},
  "W" -> {"Ta"},
  "Re" -> {"Ge", "Ca", "W"},
  "Os" -> {"Re"},
  "Ir" -> {"Os"},
  "Pt" -> {"Ir"},
  "Au" -> {"Pt"},
  "Hg" -> {"Au"},
  "Tl" -> {"Hg"},
  "Pb" -> {"Tl"},
  "Bi" -> {"Pm", "Pb"},
  "Po" -> {"Bi"},
  "At" -> {"Po"},
  "Rn" -> {"Ho", "At"},
  "Fr" -> {"Rn"},
  "Ra" -> {"Fr"},
  "Ac" -> {"Ra"},
  "Th" -> {"Ac"},
  "Pa" -> {"Th"},
  "U" -> {"Pa"}
};

(* Build the 92x92 decay matrix M where M[i,j] = count of element j in decay of element i *)
decayMatrix = Table[0, {92}, {92}];

Do[
  elem = elements[[i]];
  products = elem /. decayRules;
  Do[
    j = elementIndex[prod];
    decayMatrix[[i, j]] += 1;
  , {prod, products}];
, {i, 92}];

(* Convert to sparse matrix for efficiency *)
M = SparseArray[decayMatrix];

Print["=== STEP 1: DECAY MATRIX BUILT ==="];
Print["Matrix dimensions: ", Dimensions[M]];
Print["Non-zero entries: ", Length[ArrayRules[M]] - 1];
Print["Matrix is valid: ", Total[decayMatrix, 2] == Total[Length /@ (elements /. decayRules)]];

(* Verify some known decays *)
Print["\nVerification samples:"];
Print["H -> H: M[1,1] = ", M[[1,1]]];
Print["He -> {Hf,Pa,H,Ca,Li}: row 2 sum = ", Total[M[[2]]]];
Print["U -> Pa: M[92,91] = ", M[[92,91]]];

(* Step 2: Compute characteristic polynomial *)
Print["\n=== STEP 2: CHARACTERISTIC POLYNOMIAL ==="];

(* Use the transpose for the standard convention: columns are "from", rows are "to" *)
(* Actually, our M[i,j] = element j appears in decay of element i *)
(* So M^T has M^T[j,i] = element j appears in decay of element i *)
(* This means M (not transposed) is the right matrix for iteration *)

charPoly = CharacteristicPolynomial[M, x];
Print["Characteristic polynomial computed."];
Print["Degree: ", Exponent[charPoly, x]];

(* Factor the characteristic polynomial *)
Print["\nFactoring characteristic polynomial..."];
factored = Factor[charPoly];
factors = FactorList[charPoly];
Print["Number of irreducible factors: ", Length[factors]];

(* Find degrees of factors *)
factorDegrees = Sort[Exponent[#[[1]], x] & /@ factors];
Print["Factor degrees: ", factorDegrees];

(* Check for degree-71 factor (Conway's polynomial) *)
degree71Factor = Select[factors, Exponent[#[[1]], x] == 71 &];
If[Length[degree71Factor] > 0,
  Print["\n*** CONWAY'S DEGREE-71 POLYNOMIAL FOUND ***"];
  conwayPoly = degree71Factor[[1, 1]];
  Print["Leading coefficient: ", Coefficient[conwayPoly, x, 71]];
  Print["Constant term: ", conwayPoly /. x -> 0];
,
  Print["WARNING: No degree-71 factor found!"];
  Print["Actual factorization: ", factored];
];

(* Step 3: Compute eigenvalues *)
Print["\n=== STEP 3: EIGENVALUES ==="];

eigenvals = Eigenvalues[N[M, 50]];  (* 50 digits precision *)
sortedEigs = Sort[eigenvals, Abs[#1] > Abs[#2] &];

Print["Largest eigenvalue (Conway's constant): "];
lambda = sortedEigs[[1]];
Print["  \[Lambda] = ", N[lambda, 30]];
Print["  |\[Lambda]| = ", N[Abs[lambda], 30]];

(* Known value of Conway's constant *)
knownLambda = 1.303577269034296391803118960624313209753624589988464608528635824320111312684671`30;
Print["\nKnown Conway's constant: ", knownLambda];
Print["Difference: ", N[Abs[lambda - knownLambda], 20]];

(* Check if lambda is a root of the degree-71 polynomial *)
If[Length[degree71Factor] > 0,
  residual = Abs[conwayPoly /. x -> lambda];
  Print["\nResidual of \[Lambda] in degree-71 polynomial: ", N[residual, 10]];
];

(* List top 10 eigenvalues by magnitude *)
Print["\nTop 10 eigenvalues by magnitude:"];
Do[
  Print["  ", i, ": ", N[sortedEigs[[i]], 15], " (|.| = ", N[Abs[sortedEigs[[i]]], 10], ")"];
, {i, 10}];

(* Step 4: Verify matrix properties *)
Print["\n=== STEP 4: MATRIX PROPERTIES ==="];

(* Row sums = number of decay products *)
rowSums = Total /@ decayMatrix;
Print["Row sums (decay product counts):"];
Print["  Min: ", Min[rowSums], ", Max: ", Max[rowSums], ", Mean: ", N[Mean[rowSums], 4]];

(* Check irreducibility via graph connectivity *)
adjMatrix = Sign[decayMatrix];  (* Binary adjacency *)
g = AdjacencyGraph[adjMatrix];
Print["Decay graph connected: ", ConnectedGraphQ[g]];
Print["Strongly connected components: ", Length[ConnectedComponents[g]]];

(* Find fixed point (H) *)
fixedPoints = Select[Range[92], decayMatrix[[#, #]] == 1 && Total[decayMatrix[[#]]] == 1 &];
Print["Fixed points: ", elements[[#]] & /@ fixedPoints];

Print["\n=== COMPUTATION COMPLETE ==="];
