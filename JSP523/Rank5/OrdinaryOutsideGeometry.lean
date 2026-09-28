import JSP523.Counting.BadSetIncidence

/-!
# Ordinary outside edges cannot differ in one vertex

This is the distance-one exclusion repeatedly used in the tail-packing
argument of §IV.2.1 in `paper/proof.pdf`. The proof is the
actual unique-completion consequence of (IV.2.2), with no abstract
distance assumption.
-/

namespace JSP523

variable {α : Type*} [DecidableEq α]

theorem ordinary_outside_edges_difference_at_least_two
    {H : Family α} {W E F : Edge α} {v : α} {r : ℕ}
    (hAdm : Admissible H) (hUniform : Uniform r H)
    (hr : 3 ≤ r) (hvW : v ∉ W)
    (hE : E ∈ H) (hF : F ∈ H)
    (hEU : E ⊆ W \ badSingletonVertices H W v r)
    (hFU : F ⊆ W \ badSingletonVertices H W v r)
    (hEF : E ≠ F) :
    2 ≤ (E \ F).card := by
  have hEcard := hUniform hE
  have hFcard := hUniform hF
  have hDiffE := Finset.card_sdiff_add_card_inter E F
  have hDiffF := Finset.card_sdiff_add_card_inter F E
  have hPos : 0 < (E \ F).card := by
    by_contra hZero
    have hEmpty : E \ F = ∅ := Finset.card_eq_zero.mp (by omega)
    have hSub : E ⊆ F := Finset.sdiff_eq_empty_iff_subset.mp hEmpty
    exact hEF (Finset.eq_of_subset_of_card_le hSub (by omega))
  by_contra hNot
  have hOne : (E \ F).card = 1 := by omega
  have hOtherOne : (F \ E).card = 1 := by
    rw [Finset.inter_comm] at hDiffF
    omega
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hOne
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hOtherOne
  let P := E ∩ F
  have hxDiff : x ∈ E \ F := by rw [hx]; simp
  have hyDiff : y ∈ F \ E := by rw [hy]; simp
  have hxE : x ∈ E := (Finset.mem_sdiff.mp hxDiff).1
  have hyF : y ∈ F := (Finset.mem_sdiff.mp hyDiff).1
  have hxU : x ∈ W \ badSingletonVertices H W v r := hEU hxE
  have hyU : y ∈ W \ badSingletonVertices H W v r := hFU hyF
  have hxy : x ≠ y := by
    intro hxy
    exact (Finset.mem_sdiff.mp hxDiff).2 (hxy ▸ hyF)
  have hPsub : P ⊆ W := by
    intro z hz
    exact (Finset.mem_sdiff.mp (hEU (Finset.mem_inter.mp hz).1)).1
  have hPcard : P.card = r - 1 := by
    dsimp [P]
    omega
  have hEdgeX : insert x P ∈ H := by
    have hRepr : insert x P = E := by
      ext z
      have hEq : E \ F = {x} := hx
      change z ∈ insert x (E ∩ F) ↔ z ∈ E
      simp only [Finset.mem_insert, Finset.mem_inter]
      constructor
      · rintro (rfl | ⟨hzE, _⟩)
        · exact hxE
        · exact hzE
      · intro hzE
        by_cases hzF : z ∈ F
        · exact Or.inr ⟨hzE, hzF⟩
        · have hzDiff : z ∈ E \ F := Finset.mem_sdiff.mpr ⟨hzE, hzF⟩
          rw [hEq] at hzDiff
          exact Or.inl (Finset.mem_singleton.mp hzDiff)
    exact hRepr ▸ hE
  have hEdgeY : insert y P ∈ H := by
    have hRepr : insert y P = F := by
      ext z
      have hEq : F \ E = {y} := hy
      change z ∈ insert y (E ∩ F) ↔ z ∈ F
      simp only [Finset.mem_insert, Finset.mem_inter]
      constructor
      · rintro (rfl | ⟨_, hzF⟩)
        · exact hyF
        · exact hzF
      · intro hzF
        by_cases hzE : z ∈ E
        · exact Or.inr ⟨hzE, hzF⟩
        · have hzDiff : z ∈ F \ E := Finset.mem_sdiff.mpr ⟨hzF, hzE⟩
          rw [hEq] at hzDiff
          exact Or.inl (Finset.mem_singleton.mp hzDiff)
    exact hRepr ▸ hF
  exact ordinary_vertices_unique_facet_completion hAdm hUniform hPsub
    hPcard hr hvW hxU hyU hxy hEdgeX hEdgeY

/-- Removing any common fixed root from two ordinary outside edges
preserves their difference, hence their tails still have distance at least
two. This is the geometric input for the two-bad-pair tail count. -/
theorem ordinary_outside_tails_difference_at_least_two
    {H : Family α} {W E F R : Edge α} {v : α} {r : ℕ}
    (hAdm : Admissible H) (hUniform : Uniform r H)
    (hr : 3 ≤ r) (hvW : v ∉ W)
    (hE : E ∈ H) (hF : F ∈ H)
    (hEU : E ⊆ W \ badSingletonVertices H W v r)
    (hFU : F ⊆ W \ badSingletonVertices H W v r)
    (hEF : E ≠ F) (hRF : R ⊆ F) :
    2 ≤ ((E \ R) \ (F \ R)).card := by
  have hDiff : (E \ R) \ (F \ R) = E \ F := by
    ext x
    simp only [Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨hxE, hxNotR⟩, hxNot⟩
      refine ⟨hxE, ?_⟩
      intro hxF
      exact hxNot ⟨hxF, hxNotR⟩
    · rintro ⟨hxE, hxNotF⟩
      refine ⟨⟨hxE, ?_⟩, ?_⟩
      · intro hxR
        exact hxNotF (hRF hxR)
      · rintro ⟨hxF, _⟩
        exact hxNotF hxF
  rw [hDiff]
  exact ordinary_outside_edges_difference_at_least_two
    hAdm hUniform hr hvW hE hF hEU hFU hEF

end JSP523
