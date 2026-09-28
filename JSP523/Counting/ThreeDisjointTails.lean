import JSP523.Counting.LinearTriple

/-!
# Three disjoint tails avoid a pair

The rank-four shared-budget argument uses three pairwise disjoint parent
tails.  A two-element set can meet at most two of them.  This elementary
finite statement is separated out for use in other ranks.
-/

namespace JSP523

variable {α : Type*} [DecidableEq α]

theorem three_disjoint_tails_one_avoids_pair
    {P R S T : Edge α}
    (hPcard : P.card = 2)
    (hRS : Disjoint R S) (hRT : Disjoint R T)
    (hST : Disjoint S T) :
    Disjoint P R ∨ Disjoint P S ∨ Disjoint P T := by
  classical
  by_contra hNone
  have hPR : (P ∩ R).Nonempty := by
    by_contra hEmpty
    have hEq : P ∩ R = ∅ := Finset.not_nonempty_iff_eq_empty.mp hEmpty
    exact hNone (Or.inl (Finset.disjoint_iff_inter_eq_empty.mpr hEq))
  have hPS : (P ∩ S).Nonempty := by
    by_contra hEmpty
    have hEq : P ∩ S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hEmpty
    exact hNone (Or.inr (Or.inl (Finset.disjoint_iff_inter_eq_empty.mpr hEq)))
  have hPT : (P ∩ T).Nonempty := by
    by_contra hEmpty
    have hEq : P ∩ T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hEmpty
    exact hNone (Or.inr (Or.inr (Finset.disjoint_iff_inter_eq_empty.mpr hEq)))
  obtain ⟨x, hx⟩ := hPR
  obtain ⟨y, hy⟩ := hPS
  obtain ⟨z, hz⟩ := hPT
  have hxP : x ∈ P := (Finset.mem_inter.mp hx).1
  have hyP : y ∈ P := (Finset.mem_inter.mp hy).1
  have hzP : z ∈ P := (Finset.mem_inter.mp hz).1
  have hxy : x ≠ y := by
    intro hEq
    exact (Finset.disjoint_left.mp hRS)
      (Finset.mem_inter.mp hx).2 (hEq ▸ (Finset.mem_inter.mp hy).2)
  have hxz : x ≠ z := by
    intro hEq
    exact (Finset.disjoint_left.mp hRT)
      (Finset.mem_inter.mp hx).2 (hEq ▸ (Finset.mem_inter.mp hz).2)
  have hyz : y ≠ z := by
    intro hEq
    exact (Finset.disjoint_left.mp hST)
      (Finset.mem_inter.mp hy).2 (hEq ▸ (Finset.mem_inter.mp hz).2)
  have hsub : ({x, y, z} : Edge α) ⊆ P := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl
    · exact hxP
    · exact hyP
    · exact hzP
  have hCard := Finset.card_le_card hsub
  have hThree : ({x, y, z} : Edge α).card = 3 := by
    simp [hxy, hxz, hyz]
  omega

end JSP523
