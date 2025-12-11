(* Conway Cosmological Theorem - Decay Matrix Construction *)
(* Build the 92x92 transition matrix for element decay *)

(* Element names in order (H=1 through U=92) *)
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

(* Decay table from Coq formalization - element_decays_to *)
decayTable = {
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

decayAssoc = Association[decayTable];

(* Build the 92x92 decay matrix *)
(* M[i,j] = number of times element j appears in decay of element i *)
buildDecayMatrix[] := Module[{M, i, j, products},
  M = ConstantArray[0, {92, 92}];
  Do[
    products = decayAssoc[elements[[i]]];
    Do[
      j = elementIndex[p];
      M[[i, j]] += 1,
      {p, products}
    ],
    {i, 92}
  ];
  M
];

M = buildDecayMatrix[];

Print["Decay Matrix M constructed (92x92)"];
Print["Non-zero entries: ", Total[Flatten[M] /. 0 -> Nothing // Length]];
Print["Row sums (total decay products per element): "];
Print[Total[M, {2}] // Short];

(* Verify matrix properties *)
Print["\nMatrix properties:"];
Print["Dimensions: ", Dimensions[M]];
Print["Is sparse: ", Total[Flatten[M] /. n_?Positive -> 1] / 92^2 // N];

(* Compute characteristic polynomial *)
Print["\nComputing characteristic polynomial..."];
charPoly = CharacteristicPolynomial[M, x];
Print["Degree: ", Exponent[charPoly, x]];

(* Factor the characteristic polynomial *)
Print["\nFactoring characteristic polynomial..."];
factored = Factor[charPoly];
Print["Factored form: ", factored // Short];

(* Find the irreducible factors and their degrees *)
factors = FactorList[charPoly];
Print["\nIrreducible factors:"];
Do[
  Print["  Degree ", Exponent[f[[1]], x], " with multiplicity ", f[[2]]],
  {f, factors}
];

(* Compute eigenvalues numerically *)
Print["\nComputing eigenvalues..."];
eigenvals = Eigenvalues[N[M, 50]];
Print["Largest eigenvalue (Conway's constant): ", Max[Abs[eigenvals]]];
Print["Expected value: 1.303577269034296391803527480068..."];

(* Sort eigenvalues by magnitude *)
sortedEigs = SortBy[eigenvals, -Abs[#] &];
Print["\nTop 10 eigenvalues by magnitude:"];
Do[Print["  ", i, ": ", sortedEigs[[i]] // N], {i, Min[10, Length[sortedEigs]]}];

(* Save results *)
Export["decay_matrix.mx", M];
Export["char_poly.mx", charPoly];

Print["\nMatrix and polynomial saved."];
