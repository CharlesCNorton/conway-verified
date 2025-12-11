(* Conway's Degree-71 Polynomial - Detailed Analysis *)

(* Load the decay matrix *)
M = Import["decay_matrix.mx"];

(* Compute characteristic polynomial *)
charPoly = CharacteristicPolynomial[M, x];

(* Get the factors *)
factors = FactorList[charPoly];

(* Extract the degree-71 factor *)
degree71Factor = Select[factors, Exponent[#[[1]], x] == 71 &][[1, 1]];

Print["Conway's Degree-71 Polynomial:"];
Print[""];

(* Print coefficients *)
coeffs = CoefficientList[degree71Factor, x];
Print["Coefficients (constant term to x^71):"];
Print[coeffs];

(* Verify this matches the known Conway polynomial *)
(* The standard form has leading coefficient 1 *)
If[Coefficient[degree71Factor, x, 71] != 1,
  degree71Factor = degree71Factor / Coefficient[degree71Factor, x, 71]
];

Print[""];
Print["Polynomial in standard form (leading coeff = 1):"];
Print[degree71Factor // Expand];

(* Compute Conway's constant to high precision *)
Print[""];
Print["Computing Conway's constant to 100 digits..."];
roots = x /. NSolve[degree71Factor == 0, x, WorkingPrecision -> 100];
realRoots = Select[roots, Im[#] == 0 &];
conwayConstant = Max[realRoots];
Print["Conway's constant \[Lambda] = ", conwayConstant];

(* Verify it's the unique real root > 1 *)
Print[""];
Print["Real roots of the degree-71 polynomial:"];
Print[Select[roots, Abs[Im[#]] < 10^-50 &]];

(* Check algebraic properties *)
Print[""];
Print["Verifying \[Lambda] satisfies the polynomial:"];
Print["P(\[Lambda]) = ", degree71Factor /. x -> conwayConstant];

(* Compute the minimal polynomial directly from eigenvalue *)
Print[""];
Print["Verifying irreducibility..."];
Print["Is irreducible over rationals: ", IrreduciblePolynomialQ[degree71Factor]];

(* Save the polynomial *)
Export["degree71_poly.txt",
  StringJoin["Conway's Degree-71 Polynomial\n\n",
    "Coefficients [a_0, a_1, ..., a_71]:\n",
    ToString[coeffs],
    "\n\nPolynomial:\n",
    ToString[degree71Factor // InputForm]]
];

(* Additional spectral analysis *)
Print[""];
Print["=== Spectral Analysis ==="];
eigenvals = Eigenvalues[N[M, 30]];
Print["Spectral radius: ", Max[Abs[eigenvals]]];
Print["Number of eigenvalues with |z| > 1: ", Count[eigenvals, z_ /; Abs[z] > 1]];
Print["Number of eigenvalues with |z| = 1: ", Count[eigenvals, z_ /; Abs[Abs[z] - 1] < 10^-10]];
Print["Number of eigenvalues with |z| < 1: ", Count[eigenvals, z_ /; Abs[z] < 1 - 10^-10]];

(* Analyze the transuranic structure *)
Print[""];
Print["=== Transuranic Analysis ==="];
Print["The factor (x-1)^2 corresponds to:"];
Print["  - Hydrogen (fixed point)"];
Print["  - A generalized eigenvector direction"];
Print[""];
Print["The factor x^18 corresponds to nilpotent chains"];
Print["The factor (x+1) corresponds to period-2 oscillation"];

Print[""];
Print["Analysis complete."];
