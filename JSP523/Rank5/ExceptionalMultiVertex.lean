import JSP523.Rank5.ExceptionalVertexIncidence
import JSP523.Counting.StarDecomposition
import JSP523.Coarse.GroundBound

/-!
# Outside edges with several exceptional vertices

This is the injective-facet count for the `b₂+⋯+b_{r-1}` term in
§IV.2.2 of `paper/proof.pdf`. We delete one ordinary
vertex from each such edge. Unique ordinary completion makes the map
injective, and the resulting facet contains at least two bad vertices.
-/

namespace JSP523

variable {α : Type*} [DecidableEq α]

/-- Actual outside edges with at least two bad singleton vertices and at
least one ordinary vertex. -/
def outsideSeveralBadWithOrdinary
    (H : Family α) (W : Edge α) (v : α) (r : ℕ) : Family α :=
  let D := badSingletonVertices H W v r
  let U := W \ D
  (outsideFamily H W).filter fun E =>
    2 ≤ (E ∩ D).card ∧ (E ∩ U).Nonempty

/-- The exact finite `J` bound for outside edges meeting the exceptional
set at least twice but not lying wholly inside it. -/
theorem outside_several_bad_with_ordinary_card_le_j
    (H : Family α) (W : Edge α) (v : α) (r : ℕ)
    (hAdm : Admissible H) (hUniform : Uniform r H)
    (hr : 3 ≤ r) (hvW : v ∉ W) :
    let D := badSingletonVertices H W v r
    (outsideSeveralBadWithOrdinary H W v r).card ≤
      D.card.choose 2 * (W.card - 2).choose (r - 3) := by
  classical
  let D := badSingletonVertices H W v r
  let U := W \ D
  let B := outsideSeveralBadWithOrdinary H W v r
  let T := (W.powersetCard (r - 1)).filter fun P => 2 ≤ (P ∩ D).card
  have hB (E : Edge α) (hE : E ∈ B) :
      E ∈ H ∧ E ⊆ W ∧ 2 ≤ (E ∩ D).card ∧ (E ∩ U).Nonempty := by
    obtain ⟨hOut, hBad, hOrd⟩ := Finset.mem_filter.mp hE
    obtain ⟨hEH, hEW⟩ := Finset.mem_filter.mp hOut
    exact ⟨hEH, hEW, hBad, hOrd⟩
  let y : ↥B → α := fun e =>
    Classical.choose (hB e.1 e.2).2.2.2
  have hy (e : ↥B) : y e ∈ e.1 ∩ U :=
    Classical.choose_spec (hB e.1 e.2).2.2.2
  let f : ↥B → Edge α := fun e => e.1.erase (y e)
  have hMap : ∀ e ∈ B.attach, f e ∈ T := by
    intro e _he
    obtain ⟨hEH, hEW, hBad, _hOrd⟩ := hB e.1 e.2
    have hyE : y e ∈ e.1 := (Finset.mem_inter.mp (hy e)).1
    have hyU : y e ∈ U := (Finset.mem_inter.mp (hy e)).2
    have hyNotD : y e ∉ D := (Finset.mem_sdiff.mp hyU).2
    have hSub : f e ⊆ W := by
      intro z hz
      exact hEW (Finset.mem_of_mem_erase hz)
    have hCard : (f e).card = r - 1 := by
      dsimp [f]
      rw [Finset.card_erase_of_mem hyE]
      have hSize := hUniform hEH
      omega
    have hInter : (f e ∩ D) = e.1 ∩ D := by
      ext z
      simp only [f, Finset.mem_inter]
      constructor
      · rintro ⟨hz, hzD⟩
        exact ⟨Finset.mem_of_mem_erase hz, hzD⟩
      · rintro ⟨hzE, hzD⟩
        have hzy : z ≠ y e := by
          intro hEq
          exact hyNotD (hEq ▸ hzD)
        exact ⟨Finset.mem_erase.mpr ⟨hzy, hzE⟩, hzD⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powersetCard.mpr ⟨hSub, hCard⟩,
        hInter ▸ hBad⟩
  have hInj : Set.InjOn f (↑B.attach : Set ↥B) := by
    intro e _he g _hg hEq
    have he := hB e.1 e.2
    have hg := hB g.1 g.2
    have hye : y e ∈ e.1 := (Finset.mem_inter.mp (hy e)).1
    have hyg : y g ∈ g.1 := (Finset.mem_inter.mp (hy g)).1
    have hyeU : y e ∈ U := (Finset.mem_inter.mp (hy e)).2
    have hygU : y g ∈ U := (Finset.mem_inter.mp (hy g)).2
    have hP : f e ⊆ W := by
      intro z hz
      exact he.2.1 (Finset.mem_of_mem_erase hz)
    have hPcard : (f e).card = r - 1 := by
      dsimp [f]
      rw [Finset.card_erase_of_mem hye]
      have hSize := hUniform he.1
      omega
    by_cases hyEq : y e = y g
    · apply Subtype.ext
      have hE : e.1 = insert (y e) (f e) :=
        (Finset.insert_erase hye).symm
      have hG : g.1 = insert (y g) (f g) :=
        (Finset.insert_erase hyg).symm
      rw [hE, hG, hyEq, hEq]
    · have hEdgeE : insert (y e) (f e) ∈ H := by
        simpa [f, Finset.insert_erase hye] using he.1
      have hEdgeG : insert (y g) (f e) ∈ H := by
        have hG : insert (y g) (f g) ∈ H := by
          simpa [f, Finset.insert_erase hyg] using hg.1
        simpa [hEq] using hG
      exact False.elim
        (ordinary_vertices_unique_facet_completion hAdm hUniform hP
          hPcard hr hvW hyeU hygU hyEq hEdgeE hEdgeG)
  have hCard : B.card ≤ T.card := by
    have hCard' := Finset.card_le_card_of_injOn f hMap hInj
    simpa using hCard'
  have hTSub : T ⊆ W.powersetCard (r - 1) := Finset.filter_subset _ _
  have hDSub : D ⊆ W := Finset.filter_subset _ _
  have hTCount : T.card ≤ ∑ P ∈ T, (P ∩ D).card.choose 2 := by
    calc
      T.card = ∑ _P ∈ T, 1 := by simp
      _ ≤ ∑ P ∈ T, (P ∩ D).card.choose 2 := by
        apply Finset.sum_le_sum
        intro P hPT
        have hTwo : 2 ≤ (P ∩ D).card := (Finset.mem_filter.mp hPT).2
        exact Nat.choose_pos hTwo
  have hJ := sum_pair_multiplicity_le_universe_budget hTSub hDSub
    (by omega : 2 ≤ r - 1)
  exact hCard.trans (hTCount.trans (by simpa [Nat.sub_sub] using hJ))

/-- The all-exceptional outside layer `b_r` obeys the coarse Part I bound
on the exceptional ground set itself, as used after (IV.2.9). -/
theorem outside_all_bad_coarse_bound
    (H : Family α) (W : Edge α) (v : α) (r : ℕ)
    (hr : 5 ≤ r) (hUniform : Uniform r H) (hAdm : Admissible H) :
    let D := badSingletonVertices H W v r
    r.factorial * (outsideFamily H D).card ≤
      3 * r ^ r * D.card ^ (r - 1) := by
  let D := badSingletonVertices H W v r
  let B := outsideFamily H D
  have hBH : B ⊆ H := Finset.filter_subset _ _
  have hBU : Uniform r B := by
    intro E hE
    exact hUniform (hBH hE)
  have hBW : ∀ E ∈ B, E ⊆ D := by
    intro E hE
    exact (Finset.mem_filter.mp hE).2
  exact Coarse.coarse_bound_on_ground_set B D r (by omega)
    hBU (admissible_mono hBH hAdm) hBW

end JSP523
