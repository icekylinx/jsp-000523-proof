import JSP523.Rank4.GlobalActualUniformization

namespace JSP523.Rank4

/-- The two equality forms themselves imply the exact count. The small
missing-star hypothesis follows from the form, not from stability. -/
theorem rank_four_global_equality_form_implies_card
    {n : ℕ} (H : Family (Fin (n + 1))) (v : Fin (n + 1))
    (hn : 1000 ≤ n) (hAdm : Admissible H) (hUniform : Uniform 4 H)
    (hForm : RankFourNearStarEqualityFamily H (Finset.univ.erase v) v) :
    H.card = n.choose 3 + n / 4 := by
  have hSupport : ∀ E ∈ H, E ⊆ insert v (Finset.univ.erase v) := by
    intro E _
    simp
  have hW : (Finset.univ.erase v : Edge (Fin (n + 1))).card = n := by simp
  have hMissing : (missingStarTriples H (Finset.univ.erase v) v).card ≤ 1 := by
    rcases hForm with h | h
    · omega
    · omega
  have hq : 10000 * (missingStarTriples H (Finset.univ.erase v) v).card ≤
      (Finset.univ.erase v : Edge (Fin (n + 1))).card ^ 3 := by
    rw [hW]
    exact (Nat.mul_le_mul_left 10000 hMissing).trans
      ((by norm_num : 10000 * 1 ≤ 1000 ^ 3).trans (Nat.pow_le_pow_left hn 3))
  have h := (rank_four_near_star_equality_iff hAdm hUniform hSupport
    (by simp) (by simpa only [hW] using hn) hq).mpr hForm
  simpa only [hW] using h

end JSP523.Rank4
