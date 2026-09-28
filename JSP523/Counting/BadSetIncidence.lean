import JSP523.Counting.OverlapTrade
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Incidence bound for high-multiplicity missing sets

This formalizes the finite double count behind (IV.2.3) of
`jsp-000523-proof/paper/proof.md`.
For a uniform family of missing star facets, the sum of its `k`-set
multiplicities is exactly `choose(t,k)` times its size.  Any set of `k`-sets
whose multiplicities are at least half a threshold has the corresponding
Markov bound.
-/

namespace JSP523

variable {α : Type*} [DecidableEq α]

/-- The multiplicity of a set `P` among actual members of `M`. -/
def setMultiplicity (M : Family α) (P : Edge α) : ℕ :=
  (M.filter fun S => P ⊆ S).card

/-- Exact incidence count between a `t`-uniform family `M` and all its
`k`-subsets, with the ambient ground set explicit. -/
theorem sum_setMultiplicity_eq
    {M : Family α} {W : Edge α} {t k : ℕ}
    (hU : Uniform t M) (hW : ∀ S ∈ M, S ⊆ W) :
    (∑ P ∈ W.powersetCard k, setMultiplicity M P) =
      M.card * t.choose k := by
  classical
  simp only [setMultiplicity, Finset.card_filter]
  rw [Finset.sum_comm]
  have hInner : ∀ S ∈ M,
      (∑ P ∈ W.powersetCard k, if P ⊆ S then (1 : ℕ) else 0) =
        t.choose k := by
    intro S hS
    have hFilter :
        (W.powersetCard k).filter (fun P => P ⊆ S) = S.powersetCard k := by
      ext P
      simp only [Finset.mem_filter, Finset.mem_powersetCard]
      constructor
      · rintro ⟨⟨_hPW, hPcard⟩, hPS⟩
        exact ⟨hPS, hPcard⟩
      · rintro ⟨hPS, hPcard⟩
        exact ⟨⟨hPS.trans (hW S hS), hPcard⟩, hPS⟩
    rw [← Finset.card_filter, hFilter, Finset.card_powersetCard, hU hS]
  calc
    (∑ S ∈ M, ∑ P ∈ W.powersetCard k,
      if P ⊆ S then (1 : ℕ) else 0)
        = ∑ _S ∈ M, t.choose k := by
            apply Finset.sum_congr rfl
            intro S hS
            exact hInner S hS
    _ = M.card * t.choose k := by simp [Finset.sum_const]

/-- Finite form of (IV.2.3): if each recorded `k`-set has missing-facet
multiplicity at least `Λ/2`, then its number is at most
`2 * choose(t,k) * |M| / Λ` (without division in the Lean statement). -/
theorem bad_set_incidence_bound
    {M : Family α} {W : Edge α} {t k Λ : ℕ}
    (hU : Uniform t M) (hW : ∀ S ∈ M, S ⊆ W)
    {Bad : Family α} (hBad : Bad ⊆ W.powersetCard k)
    (hThreshold : ∀ P ∈ Bad, Λ ≤ 2 * setMultiplicity M P) :
    Λ * Bad.card ≤ 2 * t.choose k * M.card := by
  classical
  have hEach : ∀ P ∈ Bad, Λ ≤ 2 * setMultiplicity M P := hThreshold
  have hLower : Λ * Bad.card ≤
      ∑ P ∈ Bad, 2 * setMultiplicity M P := by
    calc
      Λ * Bad.card = ∑ _P ∈ Bad, Λ := by
        simp [Finset.sum_const, mul_comm]
      _ ≤ ∑ P ∈ Bad, 2 * setMultiplicity M P :=
        Finset.sum_le_sum hEach
  have hUpper : (∑ P ∈ Bad, 2 * setMultiplicity M P) ≤
      ∑ P ∈ W.powersetCard k, 2 * setMultiplicity M P :=
    Finset.sum_le_sum_of_subset hBad
  have hIdentity := sum_setMultiplicity_eq hU hW (k := k)
  calc
    Λ * Bad.card ≤ ∑ P ∈ Bad, 2 * setMultiplicity M P := hLower
    _ ≤ ∑ P ∈ W.powersetCard k, 2 * setMultiplicity M P := hUpper
    _ = 2 * t.choose k * M.card := by
      rw [← Finset.mul_sum, hIdentity]
      ac_rfl

/-- The missing star facets are uniform and lie in the outside ground set. -/
theorem missingStarFacets_uniform
    (H : Family α) (W : Edge α) (v : α) (r : ℕ) :
    Uniform (r - 1) (missingStarFacets H W v r) := by
  intro S hS
  exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hS).1).2

theorem missingStarFacets_subset_ground
    (H : Family α) (W : Edge α) (v : α) (r : ℕ) :
    ∀ S ∈ missingStarFacets H W v r, S ⊆ W := by
  intro S hS
  exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hS).1).1

/-- Direct missing-star specialization of (IV.2.3). -/
theorem missing_star_bad_set_bound
    (H : Family α) (W : Edge α) (v : α) (r k Λ : ℕ)
    {Bad : Family α} (hBad : Bad ⊆ W.powersetCard k)
    (hThreshold : ∀ P ∈ Bad,
      Λ ≤ 2 * setMultiplicity (missingStarFacets H W v r) P) :
    Λ * Bad.card ≤
      2 * (r - 1).choose k * (missingStarFacets H W v r).card := by
  exact bad_set_incidence_bound
    (missingStarFacets_uniform H W v r)
    (missingStarFacets_subset_ground H W v r)
    hBad hThreshold

/-- The actual bad `k`-sets of §IV.2, with the integer-safe convention
`Λ ≤ 2μ_k(P)` for multiplicity at least half the threshold. -/
def badMissingSets (H : Family α) (W : Edge α) (v : α)
    (r k Λ : ℕ) : Family α :=
  (W.powersetCard k).filter fun P =>
    Λ ≤ 2 * setMultiplicity (missingStarFacets H W v r) P

/-- Equation (IV.2.3) for the manuscript's actual bad-set family. -/
theorem badMissingSets_card_bound
    (H : Family α) (W : Edge α) (v : α) (r k Λ : ℕ) :
    Λ * (badMissingSets H W v r k Λ).card ≤
      2 * (r - 1).choose k * (missingStarFacets H W v r).card := by
  apply missing_star_bad_set_bound H W v r k Λ
    (Finset.filter_subset _ _)
  intro P hP
  exact (Finset.mem_filter.mp hP).2

/-- The strong overlap count (IV.2.2) places at least one of the two
difference roots in the corresponding actual bad-set family. -/
theorem overlapping_edges_have_bad_missing_set
    {H : Family α} {W E F : Edge α} {v : α} {r : ℕ}
    (hH : Admissible H)
    (hE : E ∈ H) (hF : F ∈ H)
    (hEsub : E ⊆ W) (hFsub : F ⊆ W)
    (hEcard : E.card = r) (hFcard : F.card = r)
    (hEF : E ≠ F) (hShared : (E ∩ F).Nonempty)
    (hvW : v ∉ W) :
    let k := (E \ F).card
    let Λ := (W.card - r - k).choose (r - 1 - k)
    E \ F ∈ badMissingSets H W v r k Λ ∨
      F \ E ∈ badMissingSets H W v r k Λ := by
  classical
  let k := (E \ F).card
  let Λ := (W.card - r - k).choose (r - 1 - k)
  have hDiffE : E \ F ⊆ W :=
    (Finset.sdiff_subset).trans hEsub
  have hDiffF : F \ E ⊆ W :=
    (Finset.sdiff_subset).trans hFsub
  have hDiff := Finset.card_sdiff_add_card_inter E F
  have hDiff' := Finset.card_sdiff_add_card_inter F E
  have hSameCard : (F \ E).card = k := by
    dsimp [k]
    rw [Finset.inter_comm] at hDiff'
    omega
  have hBad := overlap_has_bad_difference
    hH hE hF hEsub hFsub hEcard hFcard hEF hShared hvW
  change Λ ≤ 2 * setMultiplicity (missingStarFacets H W v r) (E \ F) ∨
    Λ ≤ 2 * setMultiplicity (missingStarFacets H W v r) (F \ E) at hBad
  change E \ F ∈ badMissingSets H W v r k Λ ∨
    F \ E ∈ badMissingSets H W v r k Λ
  rcases hBad with hBadE | hBadF
  · exact Or.inl (Finset.mem_filter.mpr
      ⟨Finset.mem_powersetCard.mpr ⟨hDiffE, rfl⟩, hBadE⟩)
  · exact Or.inr (Finset.mem_filter.mpr
      ⟨Finset.mem_powersetCard.mpr ⟨hDiffF, hSameCard⟩, hBadF⟩)

/-- The bad singleton vertices `D` and ordinary set `U = W \ D` of §IV.2. -/
def badSingletonVertices (H : Family α) (W : Edge α) (v : α)
    (r : ℕ) : Edge α :=
  W.filter fun x =>
    ({x} : Edge α) ∈ badMissingSets H W v r 1
      ((W.card - r - 1).choose (r - 2))

/-- Exact finite singleton consequence of (IV.2.3), underlying (IV.2.4).
The manuscript's asymptotic form follows by estimating the binomial
threshold for fixed rank and large `|W|`. -/
theorem badSingletonVertices_card_bound
    (H : Family α) (W : Edge α) (v : α) (r : ℕ) :
    let Λ := (W.card - r - 1).choose (r - 2)
    Λ * (badSingletonVertices H W v r).card ≤
      2 * (r - 1) * (missingStarFacets H W v r).card := by
  classical
  let Λ := (W.card - r - 1).choose (r - 2)
  let D := badSingletonVertices H W v r
  let Bad := badMissingSets H W v r 1 Λ
  have hMap : ∀ x ∈ D, ({x} : Edge α) ∈ Bad := by
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  have hInj : Set.InjOn (fun x : α => ({x} : Edge α)) (↑D : Set α) := by
    intro x _hx y _hy hEq
    exact Finset.singleton_injective hEq
  have hDle : D.card ≤ Bad.card :=
    Finset.card_le_card_of_injOn (fun x : α => ({x} : Edge α)) hMap hInj
  have hBad := badMissingSets_card_bound H W v r 1 Λ
  rw [Nat.choose_one_right] at hBad
  change Λ * D.card ≤ 2 * (r - 1) *
    (missingStarFacets H W v r).card
  exact (Nat.mul_le_mul_left Λ hDle).trans hBad

/-- Unique completion in `U`: two outside edges cannot complete the same
facet with two distinct ordinary vertices. This is the assertion after
(IV.2.4), stated with the facet and its two completions explicit. -/
theorem ordinary_vertices_unique_facet_completion
    {H : Family α} {W P : Edge α} {v x y : α} {r : ℕ}
    (hH : Admissible H) (hU : Uniform r H)
    (hP : P ⊆ W) (hPcard : P.card = r - 1) (hr : 3 ≤ r)
    (hvW : v ∉ W)
    (hxU : x ∈ W \ badSingletonVertices H W v r)
    (hyU : y ∈ W \ badSingletonVertices H W v r)
    (hxy : x ≠ y)
    (hEdgeX : insert x P ∈ H) (hEdgeY : insert y P ∈ H) :
    False := by
  have hxP : x ∉ P := by
    intro hx
    have hCard := hU hEdgeX
    rw [Finset.insert_eq_of_mem hx, hPcard] at hCard
    omega
  have hyP : y ∉ P := by
    intro hy
    have hCard := hU hEdgeY
    rw [Finset.insert_eq_of_mem hy, hPcard] at hCard
    omega
  have hxW := (Finset.mem_sdiff.mp hxU).1
  have hyW := (Finset.mem_sdiff.mp hyU).1
  have hEsub : insert x P ⊆ W := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hzP
    · exact hxW
    · exact hP hzP
  have hFsub : insert y P ⊆ W := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hzP
    · exact hyW
    · exact hP hzP
  have hEF : insert x P ≠ insert y P := by
    intro hEq
    have hxF : x ∈ insert y P := hEq ▸ Finset.mem_insert_self x P
    rcases Finset.mem_insert.mp hxF with hEqXY | hxP'
    · exact hxy hEqXY
    · exact hxP hxP'
  have hPnon : P.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨z, hzP⟩ := hPnon
  have hShared : ((insert x P) ∩ (insert y P)).Nonempty :=
    ⟨z, Finset.mem_inter.mpr
      ⟨Finset.mem_insert_of_mem hzP, Finset.mem_insert_of_mem hzP⟩⟩
  have hDiffE : insert x P \ insert y P = ({x} : Edge α) :=
    Finset.insert_sdiff_insert' hxy hxP
  have hDiffF : insert y P \ insert x P = ({y} : Edge α) :=
    Finset.insert_sdiff_insert' hxy.symm hyP
  have hBad := overlapping_edges_have_bad_missing_set
    hH hEdgeX hEdgeY hEsub hFsub
    (hU hEdgeX) (hU hEdgeY) hEF hShared hvW
  have hBad' :
      ({x} : Edge α) ∈ badMissingSets H W v r 1
        ((W.card - r - 1).choose (r - 2)) ∨
      ({y} : Edge α) ∈ badMissingSets H W v r 1
        ((W.card - r - 1).choose (r - 2)) := by
    simpa [hDiffE, hDiffF, Nat.sub_sub] using hBad
  rcases hBad' with hBadX | hBadY
  · exact (Finset.mem_sdiff.mp hxU).2
      (Finset.mem_filter.mpr ⟨hxW, hBadX⟩)
  · exact (Finset.mem_sdiff.mp hyU).2
      (Finset.mem_filter.mpr ⟨hyW, hBadY⟩)

/-- An outside edge has no bad subset in any size relevant to intersections
of at least two vertices. -/
def BadFreeOutsideEdge (H : Family α) (W : Edge α) (v : α)
    (r : ℕ) (E : Edge α) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k ≤ r - 2 →
    ∀ P : Edge α, P ⊆ E → P.card = k →
      P ∉ badMissingSets H W v r k
        ((W.card - r - k).choose (r - 1 - k))

/-- The end of the cleaning argument for (IV.2.5): after all small bad
subsets have been removed, distinct retained outside edges meet at most
once. This statement isolates the exact combinatorial endpoint; the
quantitative cost of deleting dirty edges is a separate obligation. -/
theorem bad_free_outside_family_linear
    {H B : Family α} {W : Edge α} {v : α} {r : ℕ}
    (hH : Admissible H) (hBH : B ⊆ H)
    (hU : Uniform r B) (hW : ∀ E ∈ B, E ⊆ W)
    (hvW : v ∉ W)
    (hClean : ∀ E ∈ B, BadFreeOutsideEdge H W v r E) :
    LinearFamily B := by
  intro E F hE hF hEF
  by_contra hNot
  have hTwo : 2 ≤ (E ∩ F).card := by omega
  have hShared : (E ∩ F).Nonempty := Finset.card_pos.mp (by omega)
  have hEcard := hU hE
  have hFcard := hU hF
  have hDiff := Finset.card_sdiff_add_card_inter E F
  have hDiff' := Finset.card_sdiff_add_card_inter F E
  let k := (E \ F).card
  have hkPos : 1 ≤ k := by
    by_contra hZero
    have hEmpty : E \ F = ∅ := Finset.card_eq_zero.mp (by omega)
    have hSub : E ⊆ F := Finset.sdiff_eq_empty_iff_subset.mp hEmpty
    exact hEF (Finset.eq_of_subset_of_card_le hSub (by omega))
  have hkBound : k ≤ r - 2 := by dsimp [k]; omega
  have hSameCard : (F \ E).card = k := by
    dsimp [k]
    rw [Finset.inter_comm] at hDiff'
    omega
  have hBad := overlapping_edges_have_bad_missing_set
    hH (hBH hE) (hBH hF) (hW E hE) (hW F hF)
    hEcard hFcard hEF hShared hvW
  change E \ F ∈ badMissingSets H W v r k
      ((W.card - r - k).choose (r - 1 - k)) ∨
    F \ E ∈ badMissingSets H W v r k
      ((W.card - r - k).choose (r - 1 - k)) at hBad
  rcases hBad with hBadE | hBadF
  · exact (hClean E hE k hkPos hkBound (E \ F)
      Finset.sdiff_subset rfl) hBadE
  · exact (hClean F hF k hkPos hkBound (F \ E)
      Finset.sdiff_subset hSameCard) hBadF

end JSP523
