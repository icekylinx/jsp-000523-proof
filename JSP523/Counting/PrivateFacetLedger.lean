import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Rank-five private-facet ledger: arithmetic core

§IV.A.2, equation (IV.A.3), of the all-rank manuscript obtains
`|L| ≤ 1/2 |∂L| + |L_root|` by assigning two
private facets to every unrooted edge.  The following lemma isolates the exact
arithmetic conversion to a shadow-surplus deficit.
-/

namespace JSP523

/-- Twice the edge bound implies the corresponding surplus upper bound. -/
theorem private_facet_surplus
    (m shadow rooted : ℝ)
    (h : 2 * m ≤ shadow + 2 * rooted) :
    m - shadow ≤ -m + 2 * rooted := by
  linarith

/-- If the rooted error is at most `ε`, the surplus is at most `-m + 2ε`. -/
theorem private_facet_surplus_with_error
    (m shadow rooted ε : ℝ)
    (h : 2 * m ≤ shadow + 2 * rooted)
    (hroot : rooted ≤ ε) :
    m - shadow ≤ -m + 2 * ε := by
  have h₁ := private_facet_surplus m shadow rooted h
  linarith

end JSP523
