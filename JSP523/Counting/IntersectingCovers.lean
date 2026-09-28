import JSP523.Counting.LinearTriple
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Intersecting covers in arbitrary uniformity

This formalizes the covering statements of Lemma IV.1.1 in
`paper/proof.pdf`, §IV.1. For an intersecting `k`-uniform family without
a common vertex, choose one member `A` and, for each `x ∈ A`, a member
avoiding `x`. Their intersections with a third member produce at most
`k²` pairs that cover the family. The module also proves the vertex-star
and two-common-vertex cases of the lemma, together with the finite
pair-codegree consequences used in (IV.1.3).
-/

namespace JSP523

variable {α : Type*} [DecidableEq α]

/-- First assertion of Lemma IV.1.1: any fixed member supplies at most
`k` vertex stars covering a nonempty intersecting `k`-uniform family. -/
theorem intersecting_vertex_cover
    {H : Family α} {k : ℕ}
    (hNonempty : H.Nonempty)
    (hU : Uniform k H)
    (hI : PairwiseIntersecting H)
    (hk : 0 < k) :
    ∃ A ∈ H, A.card = k ∧
      ∀ E ∈ H, ∃ x ∈ A, x ∈ E := by
  obtain ⟨A, hA⟩ := hNonempty
  refine ⟨A, hA, hU hA, ?_⟩
  intro E hE
  have hEA : (E ∩ A).Nonempty := by
    by_cases hEq : E = A
    · subst E
      have hAcard : A.card = k := hU hA
      simpa using Finset.card_pos.mp (by omega : 0 < A.card)
    · exact hI hE hA hEq
  obtain ⟨x, hx⟩ := hEA
  exact ⟨x, (Finset.mem_inter.mp hx).2, (Finset.mem_inter.mp hx).1⟩

/-- The finite vertex-codegree consequence of the first assertion of
Lemma IV.1.1: if each vertex belongs to at most `D` members, then
`|H| ≤ k D`. This is the covering count behind (IV.1.2). -/
theorem intersecting_card_le_vertex_degree
    {H : Family α} {k D : ℕ}
    (hU : Uniform k H)
    (hI : PairwiseIntersecting H)
    (hk : 0 < k)
    (hD : ∀ x : α, (H.filter fun E => x ∈ E).card ≤ D) :
    H.card ≤ k * D := by
  classical
  by_cases hEmpty : H.Nonempty
  · obtain ⟨A, hA, hAcard, hCover⟩ :=
      intersecting_vertex_cover hEmpty hU hI hk
    have hSub : H ⊆ A.biUnion (fun x => H.filter fun E => x ∈ E) := by
      intro E hE
      obtain ⟨x, hxA, hxE⟩ := hCover E hE
      exact Finset.mem_biUnion.mpr
        ⟨x, hxA, Finset.mem_filter.mpr ⟨hE, hxE⟩⟩
    calc
      H.card ≤ (A.biUnion (fun x => H.filter fun E => x ∈ E)).card :=
        Finset.card_le_card hSub
      _ ≤ A.card * D :=
        Finset.card_biUnion_le_card_mul A _ D (fun x _ => hD x)
      _ = k * D := by rw [hAcard]
  · simp [Finset.not_nonempty_iff_eq_empty.mp hEmpty]

/-- Lemma IV.1.1: at most `k²` pair stars cover a nonempty intersecting
`k`-uniform family with empty total intersection. The hypothesis `2 ≤ k`
is the range in which the pair-star conclusion is used in §IV.1. -/
theorem intersecting_pair_cover
    {H : Family α} {k : ℕ}
    (hNonempty : H.Nonempty)
    (hU : Uniform k H)
    (hI : PairwiseIntersecting H)
    (hN : NoGlobalCenter H)
    (hk : 2 ≤ k) :
    ∃ P : Family α, P.card ≤ k * k ∧
      (∀ Q ∈ P, Q.card = 2) ∧
      ∀ E ∈ H, ∃ Q ∈ P, Q ⊆ E := by
  classical
  obtain ⟨A, hA⟩ := hNonempty
  let B : α → Edge α := fun x => Classical.choose (hN x)
  have hB (x : α) : B x ∈ H ∧ x ∉ B x :=
    Classical.choose_spec (hN x)
  let P : Family α :=
    A.biUnion fun x => (B x).image fun y => ({x, y} : Edge α)
  have hPcard : P.card ≤ k * k := by
    have hPart : ∀ x ∈ A,
        ((B x).image fun y => ({x, y} : Edge α)).card ≤ k := by
      intro x hx
      exact (Finset.card_image_le).trans (hU (hB x).1).le
    calc
      P.card ≤ A.card * k :=
        Finset.card_biUnion_le_card_mul A _ k hPart
      _ = k * k := by rw [hU hA]
  have hPsize : ∀ Q ∈ P, Q.card = 2 := by
    intro Q hQ
    obtain ⟨x, hxA, hx⟩ := Finset.mem_biUnion.mp hQ
    obtain ⟨y, hyB, rfl⟩ := Finset.mem_image.mp hx
    apply Finset.card_pair
    intro hxy
    exact (hB x).2 (hxy ▸ hyB)
  have hCover : ∀ E ∈ H, ∃ Q ∈ P, Q ⊆ E := by
    intro E hE
    have hEA : (E ∩ A).Nonempty := by
      by_cases hEq : E = A
      · subst E
        have hAcard : A.card = k := hU hA
        simpa using Finset.card_pos.mp (by omega : 0 < A.card)
      · exact hI hE hA hEq
    obtain ⟨x, hxEA⟩ := hEA
    have hxE : x ∈ E := (Finset.mem_inter.mp hxEA).1
    have hxA : x ∈ A := (Finset.mem_inter.mp hxEA).2
    have hEB : E ≠ B x := by
      intro hEq
      exact (hB x).2 (hEq ▸ hxE)
    obtain ⟨y, hyEB⟩ := hI hE (hB x).1 hEB
    have hyE : y ∈ E := (Finset.mem_inter.mp hyEB).1
    have hyB : y ∈ B x := (Finset.mem_inter.mp hyEB).2
    refine ⟨{x, y}, ?_, ?_⟩
    · exact Finset.mem_biUnion.mpr
        ⟨x, hxA, Finset.mem_image.mpr ⟨y, hyB, rfl⟩⟩
    · intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hxE
      · exact hyE
  exact ⟨P, hPcard, hPsize, hCover⟩

/-- Final assertion of Lemma IV.1.1: two common vertices give a single
pair star covering the family. -/
theorem intersecting_one_pair_cover_of_two_centers
    {H : Family α} {x y : α}
    (hxy : x ≠ y)
    (hCenters : ∀ E ∈ H, x ∈ E ∧ y ∈ E) :
    ({x, y} : Edge α).card = 2 ∧
      ∀ E ∈ H, ({x, y} : Edge α) ⊆ E := by
  constructor
  · exact Finset.card_pair hxy
  · intro E hE z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact (hCenters E hE).1
    · exact (Finset.mem_singleton.mp hz) ▸ (hCenters E hE).2

/-- The pair-codegree form of (IV.1.3): if each pair belongs to at most
`D` members, the pair-star cover gives `|H| ≤ k² D`. -/
theorem intersecting_card_le_pair_degree
    {H : Family α} {k D : ℕ}
    (hU : Uniform k H)
    (hI : PairwiseIntersecting H)
    (hN : NoGlobalCenter H)
    (hk : 2 ≤ k)
    (hD : ∀ Q : Edge α, Q.card = 2 →
      (H.filter fun E => Q ⊆ E).card ≤ D) :
    H.card ≤ k * k * D := by
  classical
  by_cases hEmpty : H.Nonempty
  · obtain ⟨P, hPcard, hPsize, hCover⟩ :=
      intersecting_pair_cover hEmpty hU hI hN hk
    let f : Edge α → Edge α := fun E =>
      if h : E ∈ H then Classical.choose (hCover E h) else ∅
    have hf (E : Edge α) (hE : E ∈ H) :
        f E ∈ P ∧ f E ⊆ E := by
      simpa [f, hE] using Classical.choose_spec (hCover E hE)
    have hMap : ∀ E ∈ H, f E ∈ P := fun E hE => (hf E hE).1
    have hFiber : ∀ Q ∈ P, {E ∈ H | f E = Q}.card ≤ D := by
      intro Q hQ
      have hSub : {E ∈ H | f E = Q} ⊆
          H.filter (fun E => Q ⊆ E) := by
        intro E hE
        have hEf := Finset.mem_filter.mp hE
        apply Finset.mem_filter.mpr
        refine ⟨hEf.1, ?_⟩
        rw [← hEf.2]
        exact (hf E hEf.1).2
      exact (Finset.card_le_card hSub).trans (hD Q (hPsize Q hQ))
    have hCount := Finset.card_le_mul_card_image_of_maps_to hMap D hFiber
    calc
      H.card ≤ D * P.card := hCount
      _ ≤ D * (k * k) := Nat.mul_le_mul_left D hPcard
      _ = k * k * D := Nat.mul_comm D (k * k)
  · simp [Finset.not_nonempty_iff_eq_empty.mp hEmpty]

/-- The second case of (IV.1.3): if two vertices belong to every member,
the codegree of their pair bounds the whole family. -/
theorem intersecting_card_le_pair_degree_of_two_centers
    {H : Family α} {D : ℕ} {x y : α}
    (hxy : x ≠ y)
    (hCenters : ∀ E ∈ H, x ∈ E ∧ y ∈ E)
    (hD : ∀ Q : Edge α, Q.card = 2 →
      (H.filter fun E => Q ⊆ E).card ≤ D) :
    H.card ≤ D := by
  have hCover := (intersecting_one_pair_cover_of_two_centers
    hxy hCenters).2
  have hSub : H ⊆ H.filter (fun E => ({x, y} : Edge α) ⊆ E) := by
    intro E hE
    exact Finset.mem_filter.mpr ⟨hE, hCover E hE⟩
  exact (Finset.card_le_card hSub).trans
    (hD {x, y} (Finset.card_pair hxy))

end JSP523
