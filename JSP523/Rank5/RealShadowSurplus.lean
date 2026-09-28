import JSP523.Rank5.ShadowSurplus
import JSP523.Counting.PrivateFacetLedger

/-!
# The actual rank-five shadow bound in the real surplus ledger

This module transfers the finite natural-number shadow theorem to the real
surplus interface used by the later error estimates.  All combinatorial
structural inputs remain visible at the theorem boundary.
-/

namespace JSP523.Rank5

section RealShadowSurplus

variable {α : Type*} [DecidableEq α]

/-- Direct real form of the actual four-shadow cardinal bound. -/
theorem actual_four_shadow_real_bound
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
    (2 : ℝ) * (all.card : ℝ) ≤
      ((fourShadow all).card : ℝ) + 2 * (rooted.card : ℝ) := by
  have hnat := actual_four_shadow_bound_of_rootless_coherence
    z hdecomp hsub hEcard hnoroot hshared
  have hcast : ((2 * all.card : ℕ) : ℝ) ≤
      (((fourShadow all).card + 2 * rooted.card : ℕ) : ℝ) :=
    Nat.cast_le.mpr hnat
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using hcast

/-- The finite shadow count supplies the real signed deficit with the
    actual four-shadow and actual rooted subfamily substituted. -/
theorem actual_four_shadow_real_surplus
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
    (all.card : ℝ) - ((fourShadow all).card : ℝ) ≤
      -(all.card : ℝ) + 2 * (rooted.card : ℝ) := by
  exact JSP523.private_facet_surplus _ _ _
    (actual_four_shadow_real_bound z hdecomp hsub hEcard hnoroot hshared)

/-- A separate real error bound on the rooted subfamily may be inserted
    without changing any of the finite combinatorial hypotheses. -/
theorem actual_four_shadow_real_surplus_with_error
    {all rooted unrooted : Family α}
    (z : Edge α → α) (ε : ℝ)
    (hdecomp : all.card = rooted.card + unrooted.card)
    (hsub : unrooted ⊆ all)
    (hEcard : ∀ E ∈ unrooted, E.card = 5)
    (hnoroot : ∀ E ∈ unrooted,
      ¬ ∃ v ∈ E, ∀ S : Edge α,
        S ⊆ E → S.card = 3 → v ∈ S → z S = v)
    (hshared : ∀ E ∈ unrooted, ∀ a ∈ E,
      (∃ F ∈ all, F ≠ E ∧ E.erase a ⊆ F) →
      CoherentDeletedFace E z a)
    (hroot : (rooted.card : ℝ) ≤ ε) :
    (all.card : ℝ) - ((fourShadow all).card : ℝ) ≤
      -(all.card : ℝ) + 2 * ε := by
  exact JSP523.private_facet_surplus_with_error _ _ _ ε
    (actual_four_shadow_real_bound z hdecomp hsub hEcard hnoroot hshared)
    hroot

end RealShadowSurplus

end JSP523.Rank5
