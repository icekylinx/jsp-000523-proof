import JSP523.Counting.LinearTriple
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite covers of intersecting uniform families

This formalizes the three cover assertions of Lemma IV.1.1 in
`paper/proof.pdf`.
The pair cover is given as an explicit finite family of pairs, with the
manuscript's `k²` bound.
-/

namespace JSP523

variable {α : Type*} [DecidableEq α]

/-- The members of an intersecting family are covered by the vertex stars
through any fixed member. -/
theorem intersecting_vertex_cover
    {T : Family α} {A : Edge α} {k : ℕ}
    (hU : Uniform k T) (hI : PairwiseIntersecting T)
    (hA : A ∈ T) (hk : 1 ≤ k) :
    ∀ C ∈ T, ∃ x ∈ A, x ∈ C := by
  intro C hC
  by_cases hCA : C = A
  · have hApos : A.Nonempty := Finset.card_pos.mp (by rw [hU hA]; omega)
    obtain ⟨x, hx⟩ := hApos
    exact ⟨x, hx, hCA ▸ hx⟩
  · obtain ⟨x, hx⟩ := hI hC hA hCA
    exact ⟨x, (Finset.mem_inter.mp hx).2, (Finset.mem_inter.mp hx).1⟩

/-- If an intersecting family has no global center, it has a cover by at
most `k²` pair stars.  Every recorded center really is a two-element set. -/
theorem intersecting_pair_cover
    {T : Family α} {A : Edge α} {k : ℕ}
    (hU : Uniform k T) (hI : PairwiseIntersecting T)
    (hN : NoGlobalCenter T) (hA : A ∈ T) (hk : 1 ≤ k) :
    ∃ P : Family α, P.card ≤ k * k ∧
      (∀ Q ∈ P, Q.card = 2) ∧
      (∀ C ∈ T, ∃ Q ∈ P, Q ⊆ C) := by
  classical
  let B : α → Edge α := fun x => Classical.choose (hN x)
  have hB (x : α) : B x ∈ T ∧ x ∉ B x := Classical.choose_spec (hN x)
  let P : Family α := A.biUnion fun x =>
    (B x).image fun y => ({x, y} : Edge α)
  refine ⟨P, ?_, ?_, ?_⟩
  · have hEach : ∀ x ∈ A,
        ((B x).image fun y => ({x, y} : Edge α)).card ≤ k := by
      intro x hx
      exact (Finset.card_image_le).trans (le_of_eq (hU (hB x).1))
    have hCard := Finset.card_biUnion_le_card_mul A
      (fun x => (B x).image fun y => ({x, y} : Edge α)) k hEach
    simpa only [P, hU hA] using hCard
  · intro Q hQ
    obtain ⟨x, _hx, hxQ⟩ := Finset.mem_biUnion.mp hQ
    obtain ⟨y, hyB, rfl⟩ := Finset.mem_image.mp hxQ
    exact Finset.card_pair (Ne.symm (fun hxy => (hB x).2 (hxy ▸ hyB)))
  · intro C hC
    obtain ⟨x, hxA, hxC⟩ := intersecting_vertex_cover hU hI hA hk C hC
    have hCB : C ≠ B x := by
      intro hEq
      exact (hB x).2 (hEq ▸ hxC)
    obtain ⟨y, hy⟩ := hI hC (hB x).1 hCB
    have hyC := (Finset.mem_inter.mp hy).1
    have hyB := (Finset.mem_inter.mp hy).2
    refine ⟨{x, y}, ?_, ?_⟩
    · exact Finset.mem_biUnion.mpr
        ⟨x, hxA, Finset.mem_image.mpr ⟨y, hyB, rfl⟩⟩
    · intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hxC
      · exact (Finset.mem_singleton.mp hz) ▸ hyC

/-- A fixed pair in the total intersection is a one-pair cover. -/
theorem intersecting_common_pair_cover
    {T : Family α} {x y : α} (hxy : x ≠ y)
    (hx : ∀ C ∈ T, x ∈ C) (hy : ∀ C ∈ T, y ∈ C) :
    ∃ P : Family α, P.card = 1 ∧
      (∀ Q ∈ P, Q.card = 2) ∧
      (∀ C ∈ T, ∃ Q ∈ P, Q ⊆ C) := by
  refine ⟨{{x, y}}, by simp, ?_, ?_⟩
  · intro Q hQ
    have hQeq : Q = ({x, y} : Edge α) := Finset.mem_singleton.mp hQ
    rw [hQeq]
    exact Finset.card_pair hxy
  · intro C hC
    refine ⟨{x, y}, by simp, ?_⟩
    simp [Finset.insert_subset_iff, hx C hC, hy C hC]

/-- The first codegree estimate behind (IV.1.2): a fixed member gives at
most `k` vertex stars, each of capacity `D`. -/
theorem intersecting_card_le_vertex_cap
    {T : Family α} {A : Edge α} {k D : ℕ}
    (hU : Uniform k T) (hI : PairwiseIntersecting T)
    (hA : A ∈ T) (hk : 1 ≤ k)
    (hCap : ∀ x : α, (T.filter fun C => x ∈ C).card ≤ D) :
    T.card ≤ k * D := by
  classical
  have hSub : T ⊆ A.biUnion (fun x => T.filter fun C => x ∈ C) := by
    intro C hC
    obtain ⟨x, hxA, hxC⟩ := intersecting_vertex_cover hU hI hA hk C hC
    exact Finset.mem_biUnion.mpr
      ⟨x, hxA, Finset.mem_filter.mpr ⟨hC, hxC⟩⟩
  have hUnion := Finset.card_biUnion_le_card_mul A
    (fun x => T.filter fun C => x ∈ C) D (by
      intro x _hx
      exact hCap x)
  exact (Finset.card_le_card hSub).trans (by simpa [hU hA] using hUnion)

/-- The pair-star form of the codegree estimate behind (IV.1.3).
The explicit cover from Lemma IV.1.1 gives at most `k²` fibers. -/
theorem intersecting_card_le_pair_cap
    {T : Family α} {A : Edge α} {k D : ℕ}
    (hU : Uniform k T) (hI : PairwiseIntersecting T)
    (hN : NoGlobalCenter T) (hA : A ∈ T) (hk : 1 ≤ k)
    (hCap : ∀ Q : Edge α, Q.card = 2 →
      (T.filter fun C => Q ⊆ C).card ≤ D) :
    T.card ≤ k * k * D := by
  classical
  obtain ⟨P, hPcard, hPtwo, hCover⟩ :=
    intersecting_pair_cover hU hI hN hA hk
  have hSub : T ⊆ P.biUnion (fun Q => T.filter fun C => Q ⊆ C) := by
    intro C hC
    obtain ⟨Q, hQ, hQC⟩ := hCover C hC
    exact Finset.mem_biUnion.mpr
      ⟨Q, hQ, Finset.mem_filter.mpr ⟨hC, hQC⟩⟩
  have hUnion := Finset.card_biUnion_le_card_mul P
    (fun Q => T.filter fun C => Q ⊆ C) D (by
      intro Q hQ
      exact hCap Q (hPtwo Q hQ))
  exact (Finset.card_le_card hSub).trans
    (hUnion.trans (by simpa only [mul_assoc] using Nat.mul_le_mul_right D hPcard))

/-- If a common pair lies in every member, one pair fiber suffices. -/
theorem intersecting_card_le_common_pair_cap
    {T : Family α} {x y : α} {D : ℕ}
    (hxy : x ≠ y)
    (hx : ∀ C ∈ T, x ∈ C) (hy : ∀ C ∈ T, y ∈ C)
    (hCap : ∀ Q : Edge α, Q.card = 2 →
      (T.filter fun C => Q ⊆ C).card ≤ D) :
    T.card ≤ D := by
  let Q : Edge α := {x, y}
  have hQcard : Q.card = 2 := Finset.card_pair hxy
  have hSub : T ⊆ T.filter fun C => Q ⊆ C := by
    intro C hC
    exact Finset.mem_filter.mpr ⟨hC, by
      simp [Q, Finset.insert_subset_iff, hx C hC, hy C hC]⟩
  exact (Finset.card_le_card hSub).trans (hCap Q hQcard)

end JSP523
