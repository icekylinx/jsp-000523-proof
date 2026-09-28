import JSP523.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset

/-!
# The original forcing threshold and the maximum avoiding size

The JSP-000523 question is often phrased as a least edge count that forces
four edges, whereas the mathematical manuscripts use the largest admissible
family.  This file proves the exact finite relationship between those two
conventions for every finite ground set and rank.
-/

namespace JSP523

variable {α : Type*} [DecidableEq α]

/-- The four-edge configuration occurs in `F`. -/
def ContainsForbiddenQuad (F : Family α) : Prop :=
  ∃ A B C D : Edge α,
    A ∈ F ∧ B ∈ F ∧ C ∈ F ∧ D ∈ F ∧
      ForbiddenQuad A B C D

theorem admissible_iff_no_forbidden (F : Family α) :
    Admissible F ↔ ¬ ContainsForbiddenQuad F := by
  constructor
  · intro h ⟨A, B, C, D, hA, hB, hC, hD, hQuad⟩
    exact h hA hB hC hD hQuad
  · intro h A B C D hA hB hC hD hQuad
    exact h ⟨A, B, C, D, hA, hB, hC, hD, hQuad⟩

/-- All admissible `r`-uniform families supported on `V`. -/
noncomputable def admissibleFamilies (V : Edge α) (r : ℕ) :
    Finset (Family α) := by
  classical
  exact (V.powersetCard r).powerset.filter Admissible

theorem mem_admissibleFamilies {V : Edge α} {r : ℕ}
    {F : Family α} :
    F ∈ admissibleFamilies V r ↔
      F ⊆ V.powersetCard r ∧ Admissible F := by
  classical
  simp [admissibleFamilies]

/-- The manuscripts' convention: the maximum number of edges avoiding
the repeated-union configuration. -/
noncomputable def maxAvoidingCard (V : Edge α) (r : ℕ) : ℕ :=
  (admissibleFamilies V r).sup Finset.card

theorem maxAvoidingCard_upper
    {V : Edge α} {r : ℕ} {F : Family α}
    (hSupport : F ⊆ V.powersetCard r)
    (hAdmissible : Admissible F) :
    F.card ≤ maxAvoidingCard V r := by
  exact Finset.le_sup
    (mem_admissibleFamilies.mpr ⟨hSupport, hAdmissible⟩)

theorem maxAvoidingCard_attained (V : Edge α) (r : ℕ) :
    ∃ F : Family α,
      F ⊆ V.powersetCard r ∧ Admissible F ∧
        F.card = maxAvoidingCard V r := by
  have hEmpty : (∅ : Family α) ∈ admissibleFamilies V r := by
    apply mem_admissibleFamilies.mpr
    constructor
    · simp
    · intro A B C D hA
      simp at hA
  obtain ⟨F, hF, hEq⟩ :=
    Finset.exists_mem_eq_sup (admissibleFamilies V r)
      ⟨∅, hEmpty⟩ Finset.card
  exact ⟨F, (mem_admissibleFamilies.mp hF).1,
    (mem_admissibleFamilies.mp hF).2, hEq.symm⟩

/-- The official forcing-threshold convention on the fixed vertex set
`V`: every supported family with at least `k` edges has the configuration. -/
def IsForcingThreshold (V : Edge α) (r k : ℕ) : Prop :=
  ∀ F : Family α,
    F ⊆ V.powersetCard r → k ≤ F.card → ContainsForbiddenQuad F

theorem forcing_threshold_iff_gt_max
    (V : Edge α) (r k : ℕ) :
    IsForcingThreshold V r k ↔ maxAvoidingCard V r < k := by
  constructor
  · intro h
    obtain ⟨F, hSupport, hAdmissible, hCard⟩ :=
      maxAvoidingCard_attained V r
    by_contra hNot
    have hk : k ≤ F.card := by omega
    have hForbidden := h F hSupport hk
    exact (admissible_iff_no_forbidden F).mp hAdmissible hForbidden
  · intro hk F hSupport hCard
    by_contra hNo
    have hAdmissible : Admissible F :=
      (admissible_iff_no_forbidden F).mpr hNo
    have hUpper := maxAvoidingCard_upper hSupport hAdmissible
    omega

/-- The least forcing threshold is exactly one more than the maximum
avoiding size. -/
theorem forcing_threshold_exact (V : Edge α) (r : ℕ) :
    IsForcingThreshold V r (maxAvoidingCard V r + 1) ∧
      ∀ k, IsForcingThreshold V r k →
        maxAvoidingCard V r + 1 ≤ k := by
  constructor
  · exact (forcing_threshold_iff_gt_max V r _).mpr (by omega)
  · intro k h
    have hk := (forcing_threshold_iff_gt_max V r k).mp h
    omega

end JSP523
