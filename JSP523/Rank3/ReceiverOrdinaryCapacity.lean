import JSP523.Rank3.ReceiverCapacityExtended

/-!
# Ordinary double receivers with a large reciprocal cell

For a two-core receiver, a reciprocal cell of multiplicity at least three
is either a star, whose actual charge is at most two, or the manuscript's
exceptional triangle. This file packages the pointwise implication used in
the global capacity sum of §II.5.
-/

namespace JSP523.Rank3

variable {α : Type*} [DecidableEq α]

/-- A large reciprocal cell gives ordinary capacity two unless it is the
triangle exception. The two displayed source cores are the actual members
of the receiver's common link. -/
theorem ordinary_double_book_large_reciprocal_le_two
    {H : Family α} {V : Edge α} {z v x y u : α}
    (hH : Admissible H)
    (hzV : z ∈ V) (hvV : v ∈ V)
    (hyV : y ∈ V) (huV : u ∈ V)
    (hzv : z ≠ v) (hxy : x ≠ y) (hxu : x ≠ u) (hyu : y ≠ u)
    (h₁ : ({x, y} : Edge α) ∈ commonLink H V ({z, v} : Edge α))
    (h₂ : ({x, u} : Edge α) ∈ commonLink H V ({z, v} : Edge α))
    (hcard : (commonLink H V ({z, v} : Edge α)).card = 2)
    (hlarge : 3 ≤ (commonLink H V ({y, u} : Edge α)).card)
    (hordinary : ¬ triangleExceptionalReceiverCell H V ({z, v} : Edge α)) :
    actualCellChargeTotal H V z v ≤ 2 := by
  by_cases hcenter : ∃ a : α,
      ∀ p ∈ commonLink H V ({y, u} : Edge α), a ∈ p
  · obtain ⟨a, ha⟩ := hcenter
    have h₁or := (mem_commonLink_pair_iff_oriented H V hzv _).mp h₁
    have h₂or := (mem_commonLink_pair_iff_oriented H V hzv _).mp h₂
    have h₁rev : ({x, y} : Edge α) ∈
        commonLink H V ({v, z} : Edge α) := by
      simpa only [Finset.pair_comm] using h₁
    have h₂rev : ({x, u} : Edge α) ∈
        commonLink H V ({v, z} : Edge α) := by
      simpa only [Finset.pair_comm] using h₂
    have h₁revOr := (mem_commonLink_pair_iff_oriented H V (Ne.symm hzv) _).mp h₁rev
    have h₂revOr := (mem_commonLink_pair_iff_oriented H V (Ne.symm hzv) _).mp h₂rev
    have hpv := reciprocal_pair_in_commonLink H V hvV hxy hxu hyu h₁or h₂or
    have hpz := reciprocal_pair_in_commonLink H V hzV hxy hxu hyu h₁revOr h₂revOr
    have hav : a ∈ ({x, v} : Edge α) := by
      apply ha
      simpa only [Finset.pair_comm] using hpv
    have haz : a ∈ ({x, z} : Edge α) := by
      apply ha
      simpa only [Finset.pair_comm] using hpz
    have hax : a = x := by
      have hv : a = x ∨ a = v := by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hav
      have hz : a = x ∨ a = z := by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using haz
      rcases hv with h | h
      · exact h
      · rcases hz with h' | h'
        · exact h'
        · exact False.elim (hzv (h'.symm.trans h))
    have hxCenter : ∀ p ∈ commonLink H V ({y, u} : Edge α), x ∈ p := by
      intro p hp
      rw [← hax]
      exact ha p hp
    exact double_receiver_star_capacity_le_two hH hzV hvV hzv hxy hxu hyu
      h₁ h₂ hcard hxCenter hlarge
  · exact False.elim (hordinary
      (double_receiver_triangle_exception_of_no_center
        hH hzV hvV hyV huV hzv hxy hxu hyu h₁ h₂ hcard hlarge hcenter))

end JSP523.Rank3
