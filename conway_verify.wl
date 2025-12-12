(* Conway Cosmological Theorem - Polynomial Verification *)
(* Verify our computed polynomial against known results *)

(* Our computed coefficients (from constant to x^71) *)
computedCoeffs = {-6, 3, -6, 12, -4, 7, -7, 1, 0, 5, -2, -4, -12, 2, 7, 12, -7, -10, -4, 3, 9, -7, 0, -8, 14, -3, 9, 2, -3, -10, -2, -6, 1, 10, -3, 1, 7, -7, 7, -12, -5, 8, 6, 10, -8, -8, -7, -3, 9, 1, 6, 6, -2, -3, -10, -2, 3, 5, 2, -1, -1, -1, -1, -1, 1, 2, 2, -1, -2, -1, 0, 1};

Print["=== CONWAY'S POLYNOMIAL VERIFICATION ===\n"];
Print["Number of coefficients: ", Length[computedCoeffs]];
Print["Leading coefficient: ", Last[computedCoeffs]];
Print["Constant term: ", First[computedCoeffs]];

(* Reconstruct the polynomial *)
conwayPoly = Sum[computedCoeffs[[i]] x^(i-1), {i, Length[computedCoeffs]}];

(* Known Conway polynomial from literature *)
(* Standard form: x^71 - x^69 - 2x^68 - x^67 + 2x^66 + 2x^65 + x^64 - x^63 - ... *)
(* Reference: Conway's original paper and Johnston 2010 *)

(* Johnston's form (from https://njohnston.ca/2010/10/a-derivation-of-conways-degree-71-look-and-say-polynomial/) *)
johnstonCoeffs = {
  1,   (* x^71 *)
  0,   (* x^70 *)
  -1,  (* x^69 *)
  -2,  (* x^68 *)
  -1,  (* x^67 *)
  2,   (* x^66 *)
  2,   (* x^65 *)
  1,   (* x^64 *)
  -1,  (* x^63 *)
  -1,  (* x^62 *)
  -1,  (* x^61 *)
  -1,  (* x^60 *)
  -1,  (* x^59 *)
  2,   (* x^58 *)
  5,   (* x^57 *)
  3,   (* x^56 *)
  -2,  (* x^55 *)
  -10, (* x^54 *)
  -3,  (* x^53 *)
  -2,  (* x^52 *)
  6,   (* x^51 *)
  6,   (* x^50 *)
  1,   (* x^49 *)
  9,   (* x^48 *)
  -3,  (* x^47 *)
  -7,  (* x^46 *)
  -8,  (* x^45 *)
  -8,  (* x^44 *)
  10,  (* x^43 *)
  6,   (* x^42 *)
  8,   (* x^41 *)
  -5,  (* x^40 *)
  -12, (* x^39 *)
  7,   (* x^38 *)
  -7,  (* x^37 *)
  7,   (* x^36 *)
  1,   (* x^35 *)
  -3,  (* x^34 *)
  10,  (* x^33 *)
  1,   (* x^32 *)
  -6,  (* x^31 *)
  -2,  (* x^30 *)
  -10, (* x^29 *)
  -3,  (* x^28 *)
  2,   (* x^27 *)
  9,   (* x^26 *)
  -3,  (* x^25 *)
  14,  (* x^24 *)
  -8,  (* x^23 *)
  0,   (* x^22 *)
  -7,  (* x^21 *)
  9,   (* x^20 *)
  3,   (* x^19 *)
  -4,  (* x^18 *)
  -10, (* x^17 *)
  -7,  (* x^16 *)
  12,  (* x^15 *)
  7,   (* x^14 *)
  2,   (* x^13 *)
  -12, (* x^12 *)
  -4,  (* x^11 *)
  -2,  (* x^10 *)
  5,   (* x^9 *)
  0,   (* x^8 *)
  1,   (* x^7 *)
  -7,  (* x^6 *)
  7,   (* x^5 *)
  -4,  (* x^4 *)
  12,  (* x^3 *)
  -6,  (* x^2 *)
  3,   (* x^1 *)
  -6   (* x^0 *)
};

johnstonPoly = Sum[johnstonCoeffs[[i]] x^(71-i+1), {i, Length[johnstonCoeffs]}];

Print["\n=== COMPARISON WITH JOHNSTON'S POLYNOMIAL ==="];
Print["Johnston coefficients length: ", Length[johnstonCoeffs]];

(* Compare *)
diff = Expand[conwayPoly - johnstonPoly];
Print["Difference (should be 0): ", diff];
Print["Polynomials match: ", diff === 0];

(* Verify roots *)
Print["\n=== ROOT ANALYSIS ==="];

roots = x /. NSolve[conwayPoly == 0, x, WorkingPrecision -> 50];
realRoots = Select[roots, Abs[Im[#]] < 10^-40 &];
complexRoots = Select[roots, Abs[Im[#]] >= 10^-40 &];

Print["Total roots: ", Length[roots]];
Print["Real roots: ", Length[realRoots]];
Print["Complex roots (conjugate pairs): ", Length[complexRoots]/2];

(* Dominant root *)
sortedByMag = SortBy[roots, -Abs[#] &];
lambda = sortedByMag[[1]];
Print["\nDominant eigenvalue (Conway's constant):"];
Print["  \[Lambda] = ", N[lambda, 40]];

(* Conway's constant to 50 digits (from OEIS A014715) *)
knownLambda = SetPrecision[1.303577269034296391803118960624313209753, 50];
Print["  Known: ", knownLambda];
Print["  |Error|: ", Abs[lambda - knownLambda]];

(* Verify it's a root *)
Print["  P(\[Lambda]) = ", N[conwayPoly /. x -> lambda, 10]];

(* Second largest magnitude *)
Print["\nSecond largest |eigenvalue|: ", N[Abs[sortedByMag[[2]]], 20]];
Print["  Value: ", N[sortedByMag[[2]], 20]];

(* Spectral gap *)
Print["\nSpectral gap (\[Lambda]_1 / |\[Lambda]_2|): ", N[Abs[lambda] / Abs[sortedByMag[[2]]], 10]];

(* Distribution of eigenvalue magnitudes *)
Print["\n=== EIGENVALUE MAGNITUDE DISTRIBUTION ==="];
mags = Sort[Abs /@ roots, Greater];
Print["Magnitudes (top 10): ", N[Take[mags, 10], 8]];

(* Count by magnitude ranges *)
Print["\nCount by magnitude:"];
Print["  |z| > 1.2: ", Length[Select[mags, # > 1.2 &]]];
Print["  1.0 < |z| <= 1.2: ", Length[Select[mags, 1.0 < # <= 1.2 &]]];
Print["  0.5 < |z| <= 1.0: ", Length[Select[mags, 0.5 < # <= 1.0 &]]];
Print["  |z| <= 0.5: ", Length[Select[mags, # <= 0.5 &]]];

(* Verify polynomial factorization structure *)
Print["\n=== FULL CHARACTERISTIC POLYNOMIAL STRUCTURE ==="];

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
fullCharPoly = CharacteristicPolynomial[M, x];
factors = FactorList[fullCharPoly];

Print["Full factorization:"];
Do[
  deg = Exponent[f[[1]], x];
  Print["  ", f[[1]], "  (degree ", deg, ", multiplicity ", f[[2]], ")"];
, {f, factors}];

Print["\nDegree verification: ",
  Total[(Exponent[#[[1]], x] * #[[2]]) & /@ factors], " = 92"];

Print["\n=== VERIFICATION COMPLETE ==="];
