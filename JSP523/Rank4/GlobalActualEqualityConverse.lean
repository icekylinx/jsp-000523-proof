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
  have hCube : 10000 ≤ n ^ 3 := by
    have h := Nat.pow_le_pow_left hn 3
    norm_num at h
    omega
  have hq : 10000 * (missingStarTriples H (Finset.univ.erase v) v).card ≤
      (Finset.univ.erase v : Edge (Fin (n + 1))).card ^ 3 := by
    rw [hW]
    nlinarith
  have h := (rank_four_near_star_equality_iff hAdm hUniform hSupport
    (by simp) (by simpa only [hW] using hn) hq).mpr hForm
  simpa only [hW] using h

end JSP523.Rank4
