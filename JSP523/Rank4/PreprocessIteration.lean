import JSP523.Rank4.PreprocessHighCodegree

/-!
# Finite iteration bookkeeping for regularization

The one-step regularizer can be iterated without losing track of its
actual deletion sets: the total loss is at most the sum of the successive
losses.  This is the finite composition step used when the degree factor is
reduced repeatedly.
-/

namespace JSP523.Rank4

variable {α : Type*} [DecidableEq α]

/-- Iterate a deterministic finite cleanup map. -/
def iterateFiniteCleanup (clean : Family α → Family α) : ℕ → Family α → Family α
  | 0, H => H
  | n + 1, H => clean (iterateFiniteCleanup clean n H)

omit [DecidableEq α] in
/-- Every step of an iterated cleanup is a subfamily of its input. -/
theorem iterate_finite_cleanup_mono
    (clean : Family α → Family α)
    (hClean : ∀ H, clean H ⊆ H) :
    ∀ n H, iterateFiniteCleanup clean n H ⊆ H := by
  intro n
  induction n with
  | zero => intro H; simp [iterateFiniteCleanup]
  | succ n ih =>
      intro H
      exact (hClean (iterateFiniteCleanup clean n H)).trans (ih H)

/-- Exact finite layer accounting: deleting successively nested subfamilies
costs at most the sum of the sizes of the actual stepwise deletion sets. -/
theorem iterate_finite_cleanup_loss_le_sum
    (clean : Family α → Family α)
    (hClean : ∀ H, clean H ⊆ H) (H : Family α) (N : ℕ) :
    (H \ iterateFiniteCleanup clean N H).card ≤
      ∑ i ∈ Finset.range N,
        (iterateFiniteCleanup clean i H \ iterateFiniteCleanup clean (i + 1) H).card := by
  induction N with
  | zero => simp [iterateFiniteCleanup]
  | succ N ih =>
      let A := iterateFiniteCleanup clean N H
      let B := iterateFiniteCleanup clean (N + 1) H
      have hBA : B ⊆ A := by
        dsimp [A, B, iterateFiniteCleanup]
        exact hClean _
      have hLayer : H \ B ⊆ (H \ A) ∪ (A \ B) := by
        intro E hE
        by_cases hEA : E ∈ A
        · exact Finset.mem_union.mpr (Or.inr
            (Finset.mem_sdiff.mpr ⟨hEA, (Finset.mem_sdiff.mp hE).2⟩))
        · exact Finset.mem_union.mpr (Or.inl
            (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hE).1, hEA⟩))
      have hCard : (H \ B).card ≤ (H \ A).card + (A \ B).card := by
        calc
          (H \ B).card ≤ ((H \ A) ∪ (A \ B)).card := Finset.card_le_card hLayer
          _ ≤ (H \ A).card + (A \ B).card := Finset.card_union_le _ _
      rw [Finset.sum_range_succ]
      simpa [A, B, iterateFiniteCleanup] using
        hCard.trans (Nat.add_le_add_right ih _)

/-- If every round has a specified deletion budget, the total iterated loss
is bounded by the sum of those budgets. -/
theorem iterate_finite_cleanup_loss_le_budgets
    (clean : Family α → Family α)
    (hClean : ∀ H, clean H ⊆ H) (H : Family α) (N : ℕ)
    (budget : ℕ → ℕ)
    (hStep : ∀ i ∈ Finset.range N,
      (iterateFiniteCleanup clean i H \
        iterateFiniteCleanup clean (i + 1) H).card ≤ budget i) :
    (H \ iterateFiniteCleanup clean N H).card ≤
      ∑ i ∈ Finset.range N, budget i := by
  calc
    _ ≤ ∑ i ∈ Finset.range N,
        (iterateFiniteCleanup clean i H \
          iterateFiniteCleanup clean (i + 1) H).card :=
            iterate_finite_cleanup_loss_le_sum clean hClean H N
    _ ≤ ∑ i ∈ Finset.range N, budget i := by
      apply Finset.sum_le_sum
      intro i hi
      exact hStep i hi

end JSP523.Rank4
