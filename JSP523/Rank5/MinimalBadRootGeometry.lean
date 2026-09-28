import JSP523.Counting.BadSetIncidence

/-!
# Minimal bad roots force distant outside edges

In §IV.2.1 of `jsp-000523-proof/paper/proof.md`, edges carrying a minimal
bad `k`-set are grouped by that root. If neither edge contains a smaller
bad set, their remaining tails have distance at least `k`. The theorem
below proves the actual edge-level statement directly from (IV.2.2).
-/

namespace JSP523

variable {α : Type*} [DecidableEq α]

/-- No bad subset of an outside edge has positive size below `k`. -/
def NoSmallerBadSubset
    (H : Family α) (W : Edge α) (v : α) (r k : ℕ)
    (E : Edge α) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j < k →
    ∀ Q : Edge α, Q ⊆ E → Q.card = j →
      Q ∉ badMissingSets H W v r j
        ((W.card - r - j).choose (r - 1 - j))

/-- Distinct outside edges containing the same nonempty root of size
`k ≤ r-2` have difference at least `k` when all smaller bad roots are
absent. This is the actual geometric distance input for the `k ≥ 3`
packing strata in (IV.2.5). -/
theorem minimal_bad_root_edges_distance
    {H : Family α} {W E F P : Edge α} {v : α} {r k : ℕ}
    (hAdm : Admissible H) (hUniform : Uniform r H)
    (hE : E ∈ H) (hF : F ∈ H)
    (hEW : E ⊆ W) (hFW : F ⊆ W) (hvW : v ∉ W)
    (hEF : E ≠ F)
    (hP : P ⊆ E ∩ F) (hPcard : P.card = k)
    (hkPos : 1 ≤ k) (hkBound : k ≤ r - 2)
    (hNoE : NoSmallerBadSubset H W v r k E)
    (hNoF : NoSmallerBadSubset H W v r k F) :
    k ≤ (E \ F).card := by
  have hEcard := hUniform hE
  have hFcard := hUniform hF
  have hDiffE := Finset.card_sdiff_add_card_inter E F
  have hDiffF := Finset.card_sdiff_add_card_inter F E
  let j := (E \ F).card
  have hjPos : 1 ≤ j := by
    by_contra hNot
    have hEmpty : E \ F = ∅ := Finset.card_eq_zero.mp (by omega)
    have hSub : E ⊆ F := Finset.sdiff_eq_empty_iff_subset.mp hEmpty
    exact hEF (Finset.eq_of_subset_of_card_le hSub (by omega))
  have hPnon : P.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x, hxP⟩ := hPnon
  have hShared : (E ∩ F).Nonempty := ⟨x, hP hxP⟩
  by_contra hNot
  have hjSmall : j < k := by omega
  have hjBound : j ≤ r - 2 := by omega
  have hSame : (F \ E).card = j := by
    rw [Finset.inter_comm] at hDiffF
    dsimp [j]
    omega
  have hBad := overlapping_edges_have_bad_missing_set hAdm hE hF
    hEW hFW hEcard hFcard hEF hShared hvW
  change E \ F ∈ badMissingSets H W v r j
      ((W.card - r - j).choose (r - 1 - j)) ∨
    F \ E ∈ badMissingSets H W v r j
      ((W.card - r - j).choose (r - 1 - j)) at hBad
  rcases hBad with hBadE | hBadF
  · exact (hNoE j hjPos hjSmall (E \ F) Finset.sdiff_subset rfl) hBadE
  · exact (hNoF j hjPos hjSmall (F \ E) Finset.sdiff_subset hSame) hBadF

/-- The corresponding tail-distance formulation after deleting the
common minimal bad root. -/
theorem minimal_bad_root_tails_distance
    {H : Family α} {W E F P : Edge α} {v : α} {r k : ℕ}
    (hAdm : Admissible H) (hUniform : Uniform r H)
    (hE : E ∈ H) (hF : F ∈ H)
    (hEW : E ⊆ W) (hFW : F ⊆ W) (hvW : v ∉ W)
    (hEF : E ≠ F)
    (hP : P ⊆ E ∩ F) (hPcard : P.card = k)
    (hkPos : 1 ≤ k) (hkBound : k ≤ r - 2)
    (hNoE : NoSmallerBadSubset H W v r k E)
    (hNoF : NoSmallerBadSubset H W v r k F) :
    k ≤ ((E \ P) \ (F \ P)).card := by
  have hPF : P ⊆ F := hP.trans Finset.inter_subset_right
  have hDiff : (E \ P) \ (F \ P) = E \ F := by
    ext x
    simp only [Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨hxE, hxNotP⟩, hxNotTail⟩
      refine ⟨hxE, ?_⟩
      intro hxF
      exact hxNotTail ⟨hxF, hxNotP⟩
    · rintro ⟨hxE, hxNotF⟩
      refine ⟨⟨hxE, ?_⟩, ?_⟩
      · intro hxP
        exact hxNotF (hPF hxP)
      · rintro ⟨hxF, _⟩
        exact hxNotF hxF
  rw [hDiff]
  exact minimal_bad_root_edges_distance hAdm hUniform hE hF hEW hFW
    hvW hEF hP hPcard hkPos hkBound hNoE hNoF

end JSP523
