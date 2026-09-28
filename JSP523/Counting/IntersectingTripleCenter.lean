import JSP523.Counting.LinearTriple
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Large intersecting triple systems have a center

This is the nine-pair covering argument in the first section of the new
rank-four preprocessing proof.  It is stated independently of rank, so the
same finite lemma can be used for common triple systems elsewhere.
-/

namespace JSP523

section IntersectingTripleCenter

variable {α : Type*} [DecidableEq α]

/-- The number of triples of `H` containing a specified pair. -/
def triplePairDegree (H : Family α) (P : Edge α) : ℕ :=
  (H.filter fun E => P ⊆ E).card

/-- If an intersecting triple family has no common point, nine pairs cover
all its triples.  Consequently a pair-degree cap `D` gives `|H| ≤ 9D`. -/
theorem intersecting_triples_card_le_nine_mul_pairDegree
    {H : Family α} {D : ℕ}
    (hU : Uniform 3 H)
    (hI : PairwiseIntersecting H)
    (hN : NoGlobalCenter H)
    (hD : ∀ P : Edge α, P.card = 2 → triplePairDegree H P ≤ D) :
    H.card ≤ 9 * D := by
  classical
  by_cases hEmpty : H.Nonempty
  · obtain ⟨T, hT⟩ := hEmpty
    let S : α → Edge α := fun x => Classical.choose (hN x)
    have hS (x : α) : S x ∈ H ∧ x ∉ S x :=
      Classical.choose_spec (hN x)
    let pairs : Family α :=
      T.biUnion fun x => (S x).image fun y => ({x, y} : Edge α)
    have hpairs : pairs.card ≤ 9 := by
      have hpart : ∀ x ∈ T,
          ((S x).image fun y => ({x, y} : Edge α)).card ≤ 3 := by
        intro x hx
        exact (Finset.card_image_le).trans (hU (hS x).1).le
      calc
        pairs.card ≤ T.card * 3 :=
          Finset.card_biUnion_le_card_mul T _ 3 hpart
        _ = 9 := by rw [hU hT]
    have hcover : ∀ E ∈ H, ∃ P ∈ pairs, P.card = 2 ∧ P ⊆ E := by
      intro E hE
      have hET : (E ∩ T).Nonempty := by
        by_cases hEq : E = T
        · subst E
          have hTcard : T.card = 3 := hU hT
          simpa using (Finset.card_pos.mp (by omega : 0 < T.card))
        · exact hI hE hT hEq
      obtain ⟨x, hxET⟩ := hET
      have hxE : x ∈ E := (Finset.mem_inter.mp hxET).1
      have hxT : x ∈ T := (Finset.mem_inter.mp hxET).2
      have hES : E ≠ S x := by
        intro hEq
        exact (hS x).2 (hEq ▸ hxE)
      obtain ⟨y, hyES⟩ := hI hE (hS x).1 hES
      have hyE : y ∈ E := (Finset.mem_inter.mp hyES).1
      have hyS : y ∈ S x := (Finset.mem_inter.mp hyES).2
      have hxy : x ≠ y := by
        intro hEq
        exact (hS x).2 (hEq ▸ hyS)
      refine ⟨{x, y}, ?_, Finset.card_pair hxy, ?_⟩
      · exact Finset.mem_biUnion.mpr
          ⟨x, hxT, Finset.mem_image.mpr ⟨y, hyS, rfl⟩⟩
      · intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact hxE
        · exact hyE
    have hpairsCard : ∀ P ∈ pairs, P.card = 2 := by
      intro P hP
      obtain ⟨x, hxT, hx⟩ := Finset.mem_biUnion.mp hP
      obtain ⟨y, hyS, rfl⟩ := Finset.mem_image.mp hx
      apply Finset.card_pair
      intro hxy
      exact (hS x).2 (hxy ▸ hyS)
    let f : Edge α → Edge α := fun E =>
      if h : E ∈ H then Classical.choose (hcover E h) else ∅
    have hf (E : Edge α) (hE : E ∈ H) :
        f E ∈ pairs ∧ (f E).card = 2 ∧ f E ⊆ E := by
      simpa [f, hE] using Classical.choose_spec (hcover E hE)
    have hmap : ∀ E ∈ H, f E ∈ pairs := fun E hE => (hf E hE).1
    have hfiber : ∀ P ∈ pairs,
        {E ∈ H | f E = P}.card ≤ D := by
      intro P hP
      have hsub : {E ∈ H | f E = P} ⊆
          H.filter (fun E => P ⊆ E) := by
        intro E hE
        have hEf := Finset.mem_filter.mp hE
        apply Finset.mem_filter.mpr
        refine ⟨hEf.1, ?_⟩
        rw [← hEf.2]
        exact (hf E hEf.1).2.2
      exact (Finset.card_le_card hsub).trans (hD P (hpairsCard P hP))
    have hcard := Finset.card_le_mul_card_image_of_maps_to hmap D hfiber
    exact hcard.trans (Nat.mul_le_mul_left D hpairs) |>.trans_eq (by omega)
  · simp [Finset.not_nonempty_iff_eq_empty.mp hEmpty]

/-- The large-cell form used when weak common cells have been deleted. -/
theorem intersecting_triples_large_has_center
    {H : Family α} {D : ℕ}
    (hU : Uniform 3 H)
    (hI : PairwiseIntersecting H)
    (hD : ∀ P : Edge α, P.card = 2 → triplePairDegree H P ≤ D)
    (hLarge : 9 * D < H.card) :
    ∃ x : α, ∀ ⦃E : Edge α⦄, E ∈ H → x ∈ E := by
  classical
  by_contra hNoCenter
  have hN : NoGlobalCenter H := by
    intro x
    by_contra hx
    apply hNoCenter
    refine ⟨x, ?_⟩
    intro E hE
    by_contra hxE
    exact hx ⟨E, hE, hxE⟩
  have hSmall := intersecting_triples_card_le_nine_mul_pairDegree
    hU hI hN hD
  omega

end IntersectingTripleCenter

end JSP523
