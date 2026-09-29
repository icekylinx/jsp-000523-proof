import JSP523.MainTheorem

/-!
# JSP-000523 submission verification

Theorem 1 of `paper/proof.pdf` gives the finite rank-three bound, the eventual
exact formula for each fixed rank at least four, and the coefficient-one
forcing asymptotic for every fixed rank at least three. The first declaration
below identifies the least forcing threshold with the avoiding maximum plus one.

Run `lake env lean verification/Submission.lean` after `lake build JSP523`.
-/

#print axioms JSP523.forcing_threshold_exact
#print axioms JSP523.coefficient_one_forcing_density
#print axioms JSP523.eventually_fixed_rank_at_least_four_forcing_exact
#print axioms JSP523.jsp_000523_main_theorem
