import JSP523.Rank4.PreprocessReciprocalDeletion
import JSP523.Rank4.PreprocessLabelExceptions
import JSP523.Rank4.LocalDirtyPairGraph
import JSP523.Rank3.PairGraphClassification

/-! # Distinct-witness reciprocal tail fibers from admissibility -/

namespace JSP523.Rank4

variable {α : Type*} [DecidableEq α]

private theorem pair_disjoint_of_not_mem
    (P : Edge α) (a b : α) (ha : a ∉ P) (hb : b ∉ P) :
    Disjoint ({a, b} : Edge α) P := by
  apply Finset.disjoint_left.mpr
  intro x hx hxP
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact ha hxP
  · exact hb hxP

private theorem physical_pairs_disjoint
    (a b r s : α)
    (hab : a ≠ b) (har : a ≠ r) (hbs : b ≠ s) (hrs : r ≠ s) :
    Disjoint ({a, s} : Edge α) ({b, r} : Edge α) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl
  · rcases hy with h | h
    · exact hab h
    · exact har h
  · rcases hy with h | h
    · exact hbs h.symm
    · exact hrs h.symm

/-- Two distinct-witness reciprocal tails cannot be disjoint: their
fixed opposite cross-pairs would produce a forbidden two-versus-two trade. -/
theorem reciprocal_witness_tail_fiber_intersecting
    (D : FiniteCompletionCliqueData α) (a b r s : α) :
    ∀ P ∈ reciprocalWitnessTailFiber D a b r s,
      ∀ Q ∈ reciprocalWitnessTailFiber D a b r s,
        ¬ Disjoint P Q := by
  classical
  intro P hP Q hQ hDisj
  have hPparts := Finset.mem_filter.mp hP
  have hQparts := Finset.mem_filter.mp hQ
  obtain ⟨hab, har, has, hbr, hbs, hrs,
    _, hBRP, hASP⟩ := hPparts.2
  obtain ⟨_, _, _, _, _, _, _, hBRQ, hASQ⟩ := hQparts.2
  have hPcard := (Finset.mem_powersetCard.mp hPparts.1).2
  have hPNon : ({a, s} : Edge α).Nonempty := by simp
  have hPhysNe : ({a, s} : Edge α) ≠ ({b, r} : Edge α) := by
    intro h
    have : a ∈ ({b, r} : Edge α) := h ▸ (by simp : a ∈ ({a, s} : Edge α))
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h
    · exact hab h
    · exact har h
  have hTailNe : P ≠ Q := by
    intro h
    have hPos : P.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨z, hz⟩ := hPos
    exact (Finset.disjoint_left.mp hDisj) hz (h ▸ hz)
  have hASBR := physical_pairs_disjoint a b r s hab har hbs hrs
  have hASP' := hASP
  have hBRP' := hBRP
  have hASQ' := hASQ
  have hBRQ' := hBRQ
  change a ∉ P ∧ s ∉ P ∧ a ∈ D.ground ∧ s ∈ D.ground ∧
    a ≠ s ∧ insert a (insert s P) ∈ D.K at hASP'
  change b ∉ P ∧ r ∉ P ∧ b ∈ D.ground ∧ r ∈ D.ground ∧
    b ≠ r ∧ insert b (insert r P) ∈ D.K at hBRP'
  change a ∉ Q ∧ s ∉ Q ∧ a ∈ D.ground ∧ s ∈ D.ground ∧
    a ≠ s ∧ insert a (insert s Q) ∈ D.K at hASQ'
  change b ∉ Q ∧ r ∉ Q ∧ b ∈ D.ground ∧ r ∈ D.ground ∧
    b ≠ r ∧ insert b (insert r Q) ∈ D.K at hBRQ'
  have hAS_P : ({a, s} : Edge α) ∪ P ∈ D.K := by
    simpa [Finset.union_comm, Finset.insert_comm] using hASP'.2.2.2.2.2
  have hBR_P : ({b, r} : Edge α) ∪ P ∈ D.K := by
    simpa [Finset.union_comm, Finset.insert_comm] using hBRP'.2.2.2.2.2
  have hAS_Q : ({a, s} : Edge α) ∪ Q ∈ D.K := by
    simpa [Finset.union_comm, Finset.insert_comm] using hASQ'.2.2.2.2.2
  have hBR_Q : ({b, r} : Edge α) ∪ Q ∈ D.K := by
    simpa [Finset.union_comm, Finset.insert_comm] using hBRQ'.2.2.2.2.2
  exact disjoint_pair_cycle_forbidden hPNon hPhysNe hTailNe hASBR
    (pair_disjoint_of_not_mem P a s hASP'.1 hASP'.2.1)
    (pair_disjoint_of_not_mem Q a s hASQ'.1 hASQ'.2.1)
    (pair_disjoint_of_not_mem P b r hBRP'.1 hBRP'.2.1)
    (pair_disjoint_of_not_mem Q b r hBRQ'.1 hBRQ'.2.1)
    hDisj hAS_P hBR_Q hAS_Q hBR_P D.admissible

/-- If all reciprocal tails share a vertex, their target edges all
contain the same actual triple facet. -/
theorem reciprocal_witness_tail_fiber_card_le_of_center
    (D : FiniteCompletionCliqueData α) (a b r s z : α) (Dcap : ℕ)
    (h_center : ∀ P ∈ reciprocalWitnessTailFiber D a b r s, z ∈ P)
    (h_facet : ∀ T : Edge α, T.card = 3 →
      (D.K.filter fun E => T ⊆ E).card ≤ Dcap) :
    (reciprocalWitnessTailFiber D a b r s).card ≤ Dcap := by
  classical
  let F := reciprocalWitnessTailFiber D a b r s
  by_cases hEmpty : F.Nonempty
  · obtain ⟨P₀, hP₀⟩ := hEmpty
    obtain ⟨_, _, _, _, _, _, hAB₀, _, _⟩ :=
      (Finset.mem_filter.mp hP₀).2
    have hAB₀' := hAB₀
    change a ∉ P₀ ∧ b ∉ P₀ ∧ a ∈ D.ground ∧ b ∈ D.ground ∧
      a ≠ b ∧ insert a (insert b P₀) ∈ D.K at hAB₀'
    have hza : z ≠ a := by
      intro h
      exact hAB₀'.1 (h ▸ h_center P₀ hP₀)
    have hzb : z ≠ b := by
      intro h
      exact hAB₀'.2.1 (h ▸ h_center P₀ hP₀)
    let T : Edge α := {a, b, z}
    have hTcard : T.card = 3 := by
      have hset : T = insert z ({a, b} : Edge α) := by
        ext x
        simp only [T, Finset.mem_insert, Finset.mem_singleton]
        tauto
      rw [hset, Finset.card_insert_of_notMem]
      · rw [Finset.card_pair hAB₀'.2.2.2.2.1]
      · simp [hza, hzb]
    have hMaps : ∀ P ∈ F,
        insert a (insert b P) ∈ D.K.filter (fun E => T ⊆ E) := by
      intro P hP
      obtain ⟨_, _, _, _, _, _, hAB, _, _⟩ :=
        (Finset.mem_filter.mp hP).2
      have hAB' := hAB
      change a ∉ P ∧ b ∉ P ∧ a ∈ D.ground ∧ b ∈ D.ground ∧
        a ≠ b ∧ insert a (insert b P) ∈ D.K at hAB'
      apply Finset.mem_filter.mpr
      refine ⟨hAB'.2.2.2.2.2, ?_⟩
      intro x hx
      simp only [T, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · simp
      · simp
      · simp [h_center P hP]
    have hInj : (F : Set (Edge α)).InjOn
        (fun P => insert a (insert b P)) := by
      intro P hP Q hQ hEq
      obtain ⟨_, _, _, _, _, _, hABP, _, _⟩ :=
        (Finset.mem_filter.mp hP).2
      obtain ⟨_, _, _, _, _, _, hABQ, _, _⟩ :=
        (Finset.mem_filter.mp hQ).2
      change a ∉ P ∧ b ∉ P ∧ a ∈ D.ground ∧ b ∈ D.ground ∧
        a ≠ b ∧ insert a (insert b P) ∈ D.K at hABP
      change a ∉ Q ∧ b ∉ Q ∧ a ∈ D.ground ∧ b ∈ D.ground ∧
        a ≠ b ∧ insert a (insert b Q) ∈ D.K at hABQ
      have haP : a ∉ insert b P := by
        simp [hABP.2.2.2.2.1, hABP.1]
      have haQ : a ∉ insert b Q := by
        simp [hABQ.2.2.2.2.1, hABQ.1]
      have hErase := congrArg (fun E : Edge α => (E.erase a).erase b) hEq
      simpa [Finset.erase_insert haP, Finset.erase_insert haQ,
        Finset.erase_insert hABP.2.1,
        Finset.erase_insert hABQ.2.1] using hErase
    exact (Finset.card_le_card_of_injOn
      (fun P => insert a (insert b P)) hMaps hInj).trans
        (h_facet T hTcard)
  · have hF : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hEmpty
    change F.card ≤ Dcap
    simp [hF]

/-- The manuscript's distinct-witness tail cap follows from admissibility
and the actual triple-degree bound, with no separate fiber premise. -/
theorem reciprocal_witness_tail_fiber_card_le_max_facet_three
    (D : FiniteCompletionCliqueData α) (Dcap : ℕ)
    (h_facet : ∀ T : Edge α, T.card = 3 →
      (D.K.filter fun E => T ⊆ E).card ≤ Dcap)
    (a b r s : α) :
    (reciprocalWitnessTailFiber D a b r s).card ≤
      max Dcap 3 := by
  classical
  let F := reciprocalWitnessTailFiber D a b r s
  have hPair : ∀ P ∈ F, P.card = 2 := by
    intro P hP
    exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hP).1).2
  have hMeet : ∀ P ∈ F, ∀ Q ∈ F, ¬ Disjoint P Q :=
    reciprocal_witness_tail_fiber_intersecting D a b r s
  rcases JSP523.Rank3.intersecting_pair_graph_star_or_small
      F hPair hMeet with ⟨z, hz⟩ | hSmall
  · exact (reciprocal_witness_tail_fiber_card_le_of_center
      D a b r s z Dcap hz h_facet).trans (Nat.le_max_left _ _)
  · exact hSmall.trans (Nat.le_max_right _ _)

end JSP523.Rank4
