import JSP523.Rank5.OrdinaryOutsideGeometry

/-!
# Separation of outside edges with a unique bad pair

The ordinary outside geometry excludes distance one. The overlap trade
then excludes distance two when both edges contain the same unique bad
pair.
-/

namespace JSP523

variable {α : Type*} [DecidableEq α]

/-- Distinct actual outside edges that contain the same unique bad pair
cannot differ in fewer than three vertices. The bad pairs and ordinary
outside set are the concrete families from §IV.2.1. -/
theorem unique_bad_pair_outside_edges_difference_at_least_three
    {H : Family α} {W P E F : Edge α} {v : α} {r : ℕ}
    (hAdm : Admissible H) (hUniform : Uniform r H)
    (hr : 3 ≤ r) (hvW : v ∉ W)
    (hE : E ∈ H) (hF : F ∈ H) (hEF : E ≠ F)
    (hEoutside : E ⊆ W \ badSingletonVertices H W v r)
    (hFoutside : F ⊆ W \ badSingletonVertices H W v r)
    (hPbad : P ∈ badMissingSets H W v r 2
      ((W.card - r - 2).choose (r - 3)))
    (hPE : P ⊆ E) (hPF : P ⊆ F)
    (hUniqueE : ∀ Q ∈ badMissingSets H W v r 2
        ((W.card - r - 2).choose (r - 3)), Q ⊆ E → Q = P)
    (hUniqueF : ∀ Q ∈ badMissingSets H W v r 2
        ((W.card - r - 2).choose (r - 3)), Q ⊆ F → Q = P) :
    3 ≤ (E \ F).card := by
  have hDistanceOne := ordinary_outside_edges_difference_at_least_two
    hAdm hUniform hr hvW hE hF hEoutside hFoutside hEF
  by_contra hNotThree
  have hDiffEF : (E \ F).card = 2 := by omega
  have hDiffFE : (F \ E).card = 2 := by
    have hEcard := hUniform hE
    have hFcard := hUniform hF
    have hESplit := Finset.card_sdiff_add_card_inter E F
    have hFSplit := Finset.card_sdiff_add_card_inter F E
    rw [Finset.inter_comm] at hFSplit
    omega
  have hPcard : P.card = 2 :=
    (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hPbad).1).2
  have hPnonempty : P.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨p, hpP⟩ := hPnonempty
  have hShared : (E ∩ F).Nonempty := by
    refine ⟨p, Finset.mem_inter.mpr ⟨hPE hpP, hPF hpP⟩⟩
  have hTrade := overlapping_edges_have_bad_missing_set
    hAdm hE hF
    (hEoutside.trans (Finset.sdiff_subset : W \ badSingletonVertices H W v r ⊆ W))
    (hFoutside.trans (Finset.sdiff_subset : W \ badSingletonVertices H W v r ⊆ W))
    (hUniform hE) (hUniform hF) hEF hShared hvW
  have hBad :
      E \ F ∈ badMissingSets H W v r 2
        ((W.card - r - 2).choose (r - 3)) ∨
      F \ E ∈ badMissingSets H W v r 2
        ((W.card - r - 2).choose (r - 3)) := by
    simpa [hDiffEF, hDiffFE, Nat.sub_sub] using hTrade
  rcases hBad with hBadE | hBadF
  · have hRootEq := hUniqueE (E \ F) hBadE Finset.sdiff_subset
    have hpRoot : p ∈ E \ F := by rw [hRootEq]; exact hpP
    exact (Finset.mem_sdiff.mp hpRoot).2 (hPF hpP)
  · have hRootEq := hUniqueF (F \ E) hBadF Finset.sdiff_subset
    have hpRoot : p ∈ F \ E := by rw [hRootEq]; exact hpP
    exact (Finset.mem_sdiff.mp hpRoot).2 (hPE hpP)

end JSP523
