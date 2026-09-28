import JSP523.Rank3.ReceiverGlobalCapacity
import JSP523.Rank3.ReceiverOrdinaryCapacity

/-!
# Large reciprocal targets have ordinary capacity

The reciprocal map is the symmetric difference of a double receiver's two
actual cores. If that target has at least three cores, §II.5 bounds the
original receiver by two unless it is the triangle exception.
-/

namespace JSP523.Rank3

variable {α : Type*} [DecidableEq α]

theorem ordinary_double_pair_large_reciprocal_le_two
    {H : Family α} {V : Edge α} {z v : α}
    (hH : Admissible H) (hzV : z ∈ V) (hvV : v ∈ V)
    (hzv : z ≠ v)
    (hcard : (commonLink H V ({z, v} : Edge α)).card = 2)
    (hlarge : 3 ≤
      (commonLink H V (reciprocalCellMap H V ({z, v} : Edge α))).card)
    (hordinary : ¬ triangleExceptionalReceiverCell H V ({z, v} : Edge α)) :
    actualCellChargeTotal H V z v ≤ 2 := by
  obtain ⟨x, y, u, hxy, hxu, hyu, hyV, huV, hcases⟩ :=
    double_receiver_has_reciprocal_cell hH hzV hvV hzv hcard
  rcases hcases with ⟨hp, hr, _, _⟩ | ⟨hp, hr, _, _⟩
  · have hne : ({x, y} : Edge α) ≠ ({x, u} : Edge α) := by
      intro he
      have hyMem : y ∈ ({x, u} : Edge α) := by rw [← he]; simp
      rcases Finset.mem_insert.mp hyMem with hyx | hyu'
      · exact hxy hyx.symm
      · exact hyu (Finset.mem_singleton.mp hyu')
    have hmap := reciprocalCellMap_eq_pair_symmDiff H V
      ({z, v} : Edge α) hcard hp hr hne
    have hmap' : reciprocalCellMap H V ({z, v} : Edge α) =
        ({y, u} : Edge α) := by
      rw [hmap]
      simpa only [Finset.pair_comm] using
        (pair_symmDiff_shared_right hyu (Ne.symm hxy) (Ne.symm hxu))
    have hlarge' : 3 ≤ (commonLink H V ({y, u} : Edge α)).card := by
      rw [← hmap']
      exact hlarge
    exact ordinary_double_book_large_reciprocal_le_two hH
      hzV hvV hyV huV hzv hxy hxu hyu hp hr hcard hlarge' hordinary
  · have hne : ({x, y} : Edge α) ≠ ({y, u} : Edge α) := by
      intro he
      have hxMem : x ∈ ({y, u} : Edge α) := by rw [← he]; simp
      rcases Finset.mem_insert.mp hxMem with hxy' | hxu'
      · exact hxy hxy'
      · exact hxu (Finset.mem_singleton.mp hxu')
    have hmap := reciprocalCellMap_eq_pair_symmDiff H V
      ({z, v} : Edge α) hcard hp hr hne
    have hmap' : reciprocalCellMap H V ({z, v} : Edge α) =
        ({x, u} : Edge α) := by
      rw [hmap]
      simpa only [Finset.pair_comm] using
        (pair_symmDiff_shared_right hxu hxy (Ne.symm hyu))
    have hlarge' : 3 ≤ (commonLink H V ({x, u} : Edge α)).card := by
      rw [← hmap']
      exact hlarge
    have hxV : x ∈ V :=
      (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hp).1).1 (by simp)
    have hp' : ({y, x} : Edge α) ∈ commonLink H V ({z, v} : Edge α) := by
      simpa only [Finset.pair_comm] using hp
    exact ordinary_double_book_large_reciprocal_le_two hH
      hzV hvV hxV huV hzv (Ne.symm hxy) hyu hxu hp' hr hcard
      hlarge' hordinary

/-- Unordered-cell version for the regular/nonregular partition of all
double receivers. -/
theorem ordinary_double_cell_large_reciprocal_le_two
    {H : Family α} {V q : Edge α}
    (hH : Admissible H)
    (hq : q ∈ doubleLinkCells H V)
    (hlarge : 3 ≤ (commonLink H V (reciprocalCellMap H V q)).card)
    (hordinary : ¬ triangleExceptionalReceiverCell H V q) :
    actualCellChargeForPair H V q ≤ 2 := by
  classical
  have hqUsed := (Finset.mem_filter.mp hq).1
  have hqCard := (Finset.mem_filter.mp hq).2
  have hq2 : q.card = 2 :=
    (Finset.mem_powersetCard.mp (usedCells_subset H V hqUsed)).2
  let e := corePairRep q hq2
  have he := corePairRep_spec q hq2
  have hsub := (Finset.mem_powersetCard.mp (usedCells_subset H V hqUsed)).1
  have hsub' : ({e.1, e.2} : Edge α) ⊆ V := by
    rw [← he.2]
    exact hsub
  have heV : e.1 ∈ V ∧ e.2 ∈ V :=
    ⟨hsub' (by simp), hsub' (by simp)⟩
  have hcard' : (commonLink H V ({e.1, e.2} : Edge α)).card = 2 := by
    rw [← he.2]
    exact hqCard
  have hlarge' : 3 ≤
      (commonLink H V (reciprocalCellMap H V ({e.1, e.2} : Edge α))).card := by
    rw [← he.2]
    exact hlarge
  have hordinary' : ¬ triangleExceptionalReceiverCell H V
      ({e.1, e.2} : Edge α) := by
    rw [← he.2]
    exact hordinary
  have hpoint := ordinary_double_pair_large_reciprocal_le_two
    hH heV.1 heV.2 he.1 hcard' hlarge' hordinary'
  simpa [actualCellChargeForPair, hq2, e] using hpoint

end JSP523.Rank3
