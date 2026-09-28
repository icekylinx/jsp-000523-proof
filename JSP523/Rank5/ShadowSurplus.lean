import JSP523.Rank5.PrivateFacetAssembly
import Lean.Elab.Tactic.Omega

/-!
# Integral form of the actual four-shadow surplus deficit

The finite private-facet inequality also gives a signed surplus statement
without division or a cast to the reals.  This is the exact discrete form
used before the later asymptotic ledger.
-/

namespace JSP523.Rank5

section ShadowSurplus

variable {α : Type*} [DecidableEq α]

/-- The actual four-shadow has nonpositive surplus up to the rooted error,
    conditional on the same explicit rank-five structural inputs as the
    private-facet assembly theorem. -/
theorem actual_four_shadow_integral_surplus
    {all rooted unrooted : Family α}
    (z : Edge α → α)
    (hdecomp : all.card = rooted.card + unrooted.card)
    (hsub : unrooted ⊆ all)
    (hEcard : ∀ E ∈ unrooted, E.card = 5)
    (hnoroot : ∀ E ∈ unrooted,
      ¬ ∃ v ∈ E, ∀ S : Edge α,
        S ⊆ E → S.card = 3 → v ∈ S → z S = v)
    (hshared : ∀ E ∈ unrooted, ∀ a ∈ E,
      (∃ F ∈ all, F ≠ E ∧ E.erase a ⊆ F) →
      CoherentDeletedFace E z a) :
    (all.card : ℤ) - ((fourShadow all).card : ℤ) ≤
      -(all.card : ℤ) + 2 * (rooted.card : ℤ) := by
  have h := actual_four_shadow_bound_of_rootless_coherence
    z hdecomp hsub hEcard hnoroot hshared
  omega

end ShadowSurplus

end JSP523.Rank5
