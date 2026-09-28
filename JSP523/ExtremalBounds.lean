import JSP523.ExtremalScope
import JSP523.LowerConstruction
import JSP523.Coarse.AllRank
import Mathlib.Data.Fintype.Card

/-!
# Finite extremal bounds in every rank

The star-plus-matching construction in §I of `paper/proof.pdf` is realized
with a matching of the required size, and then passed to the finite extremal
function. The same construction supplies the lower bounds used in Parts II–IV.
Theorem I.1 supplies the coarse upper bound at every rank at least three.
-/

namespace JSP523

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- The exact construction lower bound on a nonempty finite vertex type. -/
theorem maxAvoidingCard_lower_all_rank (c : α) (r : ℕ) (hr : 0 < r) :
    ((Finset.univ.erase c : Edge α).card).choose (r - 1) +
      (Finset.univ.erase c : Edge α).card / r ≤
        maxAvoidingCard (Finset.univ : Edge α) r := by
  obtain ⟨H, hUniform, hAdmissible, hCard⟩ :=
    exists_star_plus_matching_exact c r hr
  have hSupport : H ⊆ (Finset.univ : Edge α).powersetCard r := by
    intro E hE
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ E, hUniform hE⟩
  rw [← hCard]
  exact maxAvoidingCard_upper hSupport hAdmissible

/-- The lower bound in the manuscript's `n`-vertex notation, including the
matching term even at rank three. -/
theorem maxAvoidingCard_fin_lower_all_rank
    (n r : ℕ) (hn : 0 < n) (hr : 0 < r) :
    (n - 1).choose (r - 1) + (n - 1) / r ≤
      maxAvoidingCard (Finset.univ : Edge (Fin n)) r := by
  let c : Fin n := ⟨0, hn⟩
  simpa [c] using maxAvoidingCard_lower_all_rank c r hr

/-- The finite coarse upper bound of Theorem I.1, transferred from each
admissible family to the extremal function. -/
theorem maxAvoidingCard_coarse_all_rank (r : ℕ) (hr : 3 ≤ r) :
    r.factorial * maxAvoidingCard (Finset.univ : Edge α) r ≤
      3 * r ^ r * (Fintype.card α) ^ (r - 1) := by
  obtain ⟨H, hSupport, hAdmissible, hCard⟩ :=
    maxAvoidingCard_attained (Finset.univ : Edge α) r
  have hUniform : Uniform r H := by
    intro E hE
    exact (Finset.mem_powersetCard.mp (hSupport hE)).2
  simpa only [hCard] using
    Coarse.coarse_bound_all_rank H r hr hUniform hAdmissible

/-- The finite all-rank sandwich obtained from the common construction and
the self-contained coarse bound in §I.1. -/
theorem maxAvoidingCard_all_rank_sandwich
    (c : α) (r : ℕ) (hr : 3 ≤ r) :
    ((Finset.univ.erase c : Edge α).card).choose (r - 1) +
        (Finset.univ.erase c : Edge α).card / r ≤
          maxAvoidingCard (Finset.univ : Edge α) r ∧
      r.factorial * maxAvoidingCard (Finset.univ : Edge α) r ≤
        3 * r ^ r * (Fintype.card α) ^ (r - 1) := by
  exact ⟨maxAvoidingCard_lower_all_rank c r (by omega),
    maxAvoidingCard_coarse_all_rank r hr⟩

/-- The least forcing threshold has the construction lower bound and the
finite coarse upper bound in every rank at least three. -/
theorem forcing_threshold_bounds_all_rank
    (c : α) (r : ℕ) (hr : 3 ≤ r) :
    IsForcingThreshold (Finset.univ : Edge α) r
        (maxAvoidingCard (Finset.univ : Edge α) r + 1) ∧
      (∀ k, IsForcingThreshold (Finset.univ : Edge α) r k →
        maxAvoidingCard (Finset.univ : Edge α) r + 1 ≤ k) ∧
      ((Finset.univ.erase c : Edge α).card).choose (r - 1) +
        (Finset.univ.erase c : Edge α).card / r + 1 ≤
          maxAvoidingCard (Finset.univ : Edge α) r + 1 ∧
      r.factorial * (maxAvoidingCard (Finset.univ : Edge α) r + 1) ≤
        3 * r ^ r * (Fintype.card α) ^ (r - 1) + r.factorial := by
  obtain ⟨hIs, hLeast⟩ :=
    forcing_threshold_exact (Finset.univ : Edge α) r
  obtain ⟨hLower, hUpper⟩ :=
    maxAvoidingCard_all_rank_sandwich c r hr
  refine ⟨hIs, hLeast, by omega, ?_⟩
  calc
    r.factorial * (maxAvoidingCard (Finset.univ : Edge α) r + 1) =
        r.factorial * maxAvoidingCard (Finset.univ : Edge α) r +
          r.factorial := by simp [mul_add]
    _ ≤ 3 * r ^ r * (Fintype.card α) ^ (r - 1) + r.factorial :=
      Nat.add_le_add_right hUpper r.factorial

end JSP523
