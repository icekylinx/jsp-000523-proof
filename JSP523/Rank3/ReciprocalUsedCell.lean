import JSP523.Rank3.ReceiverGlobalCapacity

namespace JSP523.Rank3

section ReciprocalUsedCell

variable {α : Type*} [DecidableEq α]

theorem reciprocal_cell_map_mem_used_cells_of_double
    {H : Family α} {V q : Edge α} (hH : Admissible H)
    (hq : q ∈ doubleLinkCells H V) :
    reciprocalCellMap H V q ∈ usedCells H V := by
  classical
  have hqUsed := (Finset.mem_filter.mp hq).1
  have hqCard := (Finset.mem_filter.mp hq).2
  have hq2 : q.card = 2 :=
    (Finset.mem_powersetCard.mp (used_cells_subset H V hqUsed)).2
  let e := corePairRep q hq2
  have he := core_pair_rep_spec q hq2
  have hqCardRep :
      (commonLink H V ({e.1, e.2} : Edge α)).card = 2 := by
    rw [← he.2]
    exact hqCard
  have hsub := (Finset.mem_powersetCard.mp (used_cells_subset H V hqUsed)).1
  have hsub' : ({e.1, e.2} : Edge α) ⊆ V := by rw [← he.2]; exact hsub
  have heV : e.1 ∈ V ∧ e.2 ∈ V :=
    ⟨hsub' (by simp), hsub' (by simp)⟩
  obtain ⟨x, y, u, hxy, hxu, hyu, hyV, huV, hcases⟩ :=
    double_receiver_has_reciprocal_cell hH heV.1 heV.2 he.1 hqCardRep
  have hxV : x ∈ V := by
    rcases hcases with ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩
    · have hpV := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp h₁).1).1
      exact hpV (by simp)
    · have hpV := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp h₁).1).1
      exact hpV (by simp)
  have htarget : reciprocalCellMap H V q = ({y, u} : Edge α) ∨
      reciprocalCellMap H V q = ({x, u} : Edge α) := by
    rcases hcases with ⟨h₁, h₂, h₃, h₄⟩ | ⟨h₁, h₂, h₃, h₄⟩
    · have hne : ({x, y} : Edge α) ≠ ({x, u} : Edge α) := by
        intro hh
        have hyMem : y ∈ ({x, u} : Edge α) := by rw [← hh]; simp
        rcases Finset.mem_insert.mp hyMem with hyx | hyu'
        · exact hxy hyx.symm
        · exact hyu (Finset.mem_singleton.mp hyu')
      have hmap := reciprocal_cell_map_eq_pair_symm_diff H V
        ({e.1, e.2} : Edge α) hqCardRep h₁ h₂ hne
      left
      rw [he.2, hmap]
      simpa only [Finset.pair_comm] using
        (pair_symm_diff_shared_right hyu (Ne.symm hxy) (Ne.symm hxu))
    · have hne : ({x, y} : Edge α) ≠ ({y, u} : Edge α) := by
        intro hh
        have hxMem : x ∈ ({y, u} : Edge α) := by rw [← hh]; simp
        rcases Finset.mem_insert.mp hxMem with hxy' | hxu'
        · exact hxy hxy'
        · exact hxu (Finset.mem_singleton.mp hxu')
      have hmap := reciprocal_cell_map_eq_pair_symm_diff H V
        ({e.1, e.2} : Edge α) hqCardRep h₁ h₂ hne
      right
      rw [he.2, hmap]
      simpa only [Finset.pair_comm] using
        (pair_symm_diff_shared_right hxu hxy (Ne.symm hyu))
  have hcard := reciprocal_cell_map_card_ge_two_of_double hH hq
  have hcommon : (commonLink H V (reciprocalCellMap H V q)).Nonempty := by
    exact Finset.card_pos.mp (lt_of_lt_of_le (by decide : 0 < 2) hcard)
  apply (mem_used_cells_iff_common_link_nonempty H V _).mpr
  refine ⟨?_, hcommon⟩
  rcases htarget with htarget | htarget
  · rw [htarget]
    apply Finset.mem_powersetCard.mpr
    constructor
    · intro a ha
      rcases Finset.mem_insert.mp ha with hay | hau
      · exact hay ▸ hyV
      · exact (Finset.mem_singleton.mp hau) ▸ huV
    · simp [hyu]
  · rw [htarget]
    apply Finset.mem_powersetCard.mpr
    constructor
    · intro a ha
      rcases Finset.mem_insert.mp ha with hax | hau
      · exact hax ▸ hxV
      · exact (Finset.mem_singleton.mp hau) ▸ huV
    · simp [hxu]

end ReciprocalUsedCell

end JSP523.Rank3
