import JSP523.Counting.LinearNearStar

/-!
# Overlap trades and missing star facets at arbitrary rank

This is the finite trade and exact binomial deficit estimate (IV.2.2) in
`paper/proof.pdf`.
The proof works at every rank for which the stated overlap exists.
-/

namespace JSP523

variable {α : Type*} [DecidableEq α]

private theorem fresh_union_sdiff
    {C A X : Edge α} (hAC : A ⊆ C) (hXC : Disjoint X C) :
    (A ∪ X) \ C = X := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_union]
  constructor
  · rintro ⟨hxA | hxX, hxNotC⟩
    · exact False.elim (hxNotC (hAC hxA))
    · exact hxX
  · intro hxX
    exact ⟨Or.inr hxX, (Finset.disjoint_left.mp hXC) hxX⟩

/-- Distinct rank-`r` edges that overlap force at least one of two opposite
star extensions to be missing.  The size of `X` is irrelevant to the
forbidden-switch statement; the manuscript later chooses it so both star
extensions have size `r`. -/
theorem overlap_trade_force_missing_star
    {H : Family α} {E F X : Edge α} {v : α} {r : ℕ}
    (hH : Admissible H)
    (hE : E ∈ H) (hF : F ∈ H)
    (hEcard : E.card = r) (hFcard : F.card = r)
    (hEF : E ≠ F) (hShared : (E ∩ F).Nonempty)
    (hv : v ∉ E ∪ F)
    (hX : Disjoint X (E ∪ F)) (hvX : v ∉ X) :
    insert v ((E \ F) ∪ X) ∉ H ∨
      insert v ((F \ E) ∪ X) ∉ H := by
  let Y := E \ F
  let Z := F \ E
  let P := E ∩ F
  let Q := insert v X
  have hY : Y.Nonempty := by
    by_contra hEmpty
    have hEq : E \ F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hEmpty
    have hSub : E ⊆ F := Finset.sdiff_eq_empty_iff_subset.mp hEq
    exact hEF (Finset.eq_of_subset_of_card_le hSub (by omega))
  have hZ : Z.Nonempty := by
    by_contra hEmpty
    have hEq : F \ E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hEmpty
    have hSub : F ⊆ E := Finset.sdiff_eq_empty_iff_subset.mp hEq
    exact hEF (Finset.eq_of_subset_of_card_le hSub (by omega)).symm
  have hQ : Q.Nonempty := ⟨v, Finset.mem_insert_self v X⟩
  have hYZ : Disjoint Y Z := by
    apply Finset.disjoint_left.mpr
    intro x hxY hxZ
    exact (Finset.mem_sdiff.mp hxY).2 (Finset.mem_sdiff.mp hxZ).1
  have hPY : Disjoint P Y := by
    apply Finset.disjoint_left.mpr
    intro x hxP hxY
    exact (Finset.mem_sdiff.mp hxY).2 (Finset.mem_inter.mp hxP).2
  have hPZ : Disjoint P Z := by
    apply Finset.disjoint_left.mpr
    intro x hxP hxZ
    exact (Finset.mem_sdiff.mp hxZ).2 (Finset.mem_inter.mp hxP).1
  have hQY : Disjoint Q Y := by
    apply Finset.disjoint_left.mpr
    intro x hxQ hxY
    rcases Finset.mem_insert.mp hxQ with rfl | hxX
    · exact hv (Finset.mem_union_left F (Finset.mem_sdiff.mp hxY).1)
    · exact (Finset.disjoint_left.mp hX) hxX
        (Finset.mem_union_left F (Finset.mem_sdiff.mp hxY).1)
  have hQZ : Disjoint Q Z := by
    apply Finset.disjoint_left.mpr
    intro x hxQ hxZ
    rcases Finset.mem_insert.mp hxQ with rfl | hxX
    · exact hv (Finset.mem_union_right E (Finset.mem_sdiff.mp hxZ).1)
    · exact (Finset.disjoint_left.mp hX) hxX
        (Finset.mem_union_right E (Finset.mem_sdiff.mp hxZ).1)
  have hPQ : Disjoint P Q := by
    apply Finset.disjoint_left.mpr
    intro x hxP hxQ
    rcases Finset.mem_insert.mp hxQ with rfl | hxX
    · exact hv (Finset.mem_union_left F (Finset.mem_inter.mp hxP).1)
    · exact (Finset.disjoint_left.mp hX) hxX
        (Finset.mem_union_left F (Finset.mem_inter.mp hxP).1)
  have hSwitch : ForbiddenQuad (Y ∪ P) (Z ∪ Q) (Y ∪ Q) (Z ∪ P) :=
    prefix_switch_forbidden hY hZ hShared hQ hYZ hPY hPZ hQY hQZ hPQ
  have hEP : Y ∪ P = E := Finset.sdiff_union_inter E F
  have hFP : Z ∪ P = F := by
    simpa only [Finset.inter_comm] using Finset.sdiff_union_inter F E
  have hStarE : Y ∪ Q = insert v ((E \ F) ∪ X) := by
    ext x
    simp only [Y, Q, Finset.mem_union, Finset.mem_insert]
    tauto
  have hStarF : Z ∪ Q = insert v ((F \ E) ∪ X) := by
    ext x
    simp only [Z, Q, Finset.mem_union, Finset.mem_insert]
    tauto
  by_contra hBoth
  have hFirst : insert v ((E \ F) ∪ X) ∈ H := by
    by_contra hNo
    exact hBoth (Or.inl hNo)
  have hSecond : insert v ((F \ E) ∪ X) ∈ H := by
    by_contra hNo
    exact hBoth (Or.inr hNo)
  have hA : Y ∪ P ∈ H := hEP ▸ hE
  have hB : Z ∪ Q ∈ H := hStarF.symm ▸ hSecond
  have hC : Y ∪ Q ∈ H := hStarE.symm ▸ hFirst
  have hD : Z ∪ P ∈ H := hFP ▸ hF
  exact hH hA hB hC hD hSwitch

/-- Every fresh set `X` of the manuscript's required size produces a
different missing star facet.  This is the pointwise-to-counting part of
equation (IV.2.2), with the available
ground set written explicitly. -/
theorem overlap_trade_missing_star_count_and_root_sum
    {H : Family α} {W E F : Edge α} {v : α} {r : ℕ}
    (hH : Admissible H)
    (hE : E ∈ H) (hF : F ∈ H)
    (hEsub : E ⊆ W) (hFsub : F ⊆ W)
    (hEcard : E.card = r) (hFcard : F.card = r)
    (hEF : E ≠ F) (hShared : (E ∩ F).Nonempty)
    (hvW : v ∉ W) :
    ((W \ (E ∪ F)).card).choose (r - 1 - (E \ F).card) ≤
      (missingStarFacets H W v r).card ∧
    ((W \ (E ∪ F)).card).choose (r - 1 - (E \ F).card) ≤
      ((missingStarFacets H W v r).filter
        fun S => E \ F ⊆ S).card +
      ((missingStarFacets H W v r).filter
        fun S => F \ E ⊆ S).card := by
  classical
  let C := E ∪ F
  let Y := E \ F
  let Z := F \ E
  let Ω := W \ C
  let k := Y.card
  let Xset := Ω.powersetCard (r - 1 - k)
  have hPpos : 0 < (E ∩ F).card := Finset.card_pos.mpr hShared
  have hYeq : Y.card + (E ∩ F).card = r := by
    simpa only [Y, hEcard] using Finset.card_sdiff_add_card_inter E F
  have hZeq : Z.card + (E ∩ F).card = r := by
    simpa only [Z, Finset.inter_comm, hFcard] using
      Finset.card_sdiff_add_card_inter F E
  have hk : k ≤ r - 1 := by dsimp [k]; omega
  have hZcard : Z.card = k := by dsimp [k] at *; omega
  have hYsub : Y ⊆ C := by
    intro x hx
    exact Finset.mem_union_left F (Finset.mem_sdiff.mp hx).1
  have hZsub : Z ⊆ C := by
    intro x hx
    exact Finset.mem_union_right E (Finset.mem_sdiff.mp hx).1
  have hYsubW : Y ⊆ W := hYsub.trans (Finset.union_subset hEsub hFsub)
  have hZsubW : Z ⊆ W := hZsub.trans (Finset.union_subset hEsub hFsub)
  have hXdata (X : Edge α) (hX : X ∈ Xset) :
      X ⊆ W ∧ X.card = r - 1 - k ∧ Disjoint X C ∧ v ∉ X := by
    have hPow := Finset.mem_powersetCard.mp hX
    have hSubΩ : X ⊆ Ω := hPow.1
    have hSubW : X ⊆ W := by
      intro x hx
      exact (Finset.mem_sdiff.mp (hSubΩ hx)).1
    have hDisj : Disjoint X C := by
      apply Finset.disjoint_left.mpr
      intro x hxX hxC
      exact (Finset.mem_sdiff.mp (hSubΩ hxX)).2 hxC
    exact ⟨hSubW, hPow.2, hDisj,
      fun hvX => hvW (hSubW hvX)⟩
  have hUnionData (A X : Edge α)
      (hAsubC : A ⊆ C) (hAsubW : A ⊆ W)
      (hAcard : A.card = k)
      (hX : X ∈ Xset) :
      A ∪ X ⊆ W ∧ (A ∪ X).card = r - 1 := by
    obtain ⟨hXsubW, hXcard, hXdisj, _⟩ := hXdata X hX
    have hAX : Disjoint A X := by
      apply Finset.disjoint_left.mpr
      intro x hxA hxX
      exact (Finset.disjoint_left.mp hXdisj) hxX (hAsubC hxA)
    refine ⟨Finset.union_subset hAsubW hXsubW, ?_⟩
    rw [Finset.card_union_of_disjoint hAX, hAcard, hXcard]
    omega
  let f : Edge α → Edge α := fun X =>
    if insert v (Y ∪ X) ∈ H then Z ∪ X else Y ∪ X
  have hmap : ∀ X ∈ Xset, f X ∈ missingStarFacets H W v r := by
    intro X hX
    obtain ⟨_, _, hXdisj, hvX⟩ := hXdata X hX
    have hOutside : v ∉ E ∪ F := by
      intro hvEF
      exact hvW ((Finset.union_subset hEsub hFsub) hvEF)
    have hSwitch := overlap_trade_force_missing_star
      hH hE hF hEcard hFcard hEF hShared hOutside hXdisj hvX
    by_cases hFirst : insert v (Y ∪ X) ∈ H
    · have hSecond : insert v (Z ∪ X) ∉ H := by
        rcases hSwitch with hNoFirst | hNoSecond
        · exact False.elim (hNoFirst hFirst)
        · exact hNoSecond
      have hPow : Z ∪ X ∈ W.powersetCard (r - 1) :=
        Finset.mem_powersetCard.mpr
          (hUnionData Z X hZsub hZsubW hZcard hX)
      exact Finset.mem_filter.mpr ⟨by simpa [f, hFirst] using hPow,
        by simpa [f, hFirst] using hSecond⟩
    · have hPow : Y ∪ X ∈ W.powersetCard (r - 1) :=
        Finset.mem_powersetCard.mpr
          (hUnionData Y X hYsub hYsubW rfl hX)
      exact Finset.mem_filter.mpr ⟨by simpa [f, hFirst] using hPow,
        by simp [f, hFirst]⟩
  have hRecover (X : Edge α) (hX : X ∈ Xset) : f X \ C = X := by
    have hDisj := (hXdata X hX).2.2.1
    by_cases hFirst : insert v (Y ∪ X) ∈ H
    · simpa [f, hFirst] using fresh_union_sdiff hZsub hDisj
    · simpa [f, hFirst] using fresh_union_sdiff hYsub hDisj
  have hinj : Set.InjOn f (↑Xset : Set (Edge α)) := by
    intro X hX X' hX' hEq
    calc
      X = f X \ C := (hRecover X hX).symm
      _ = f X' \ C := by rw [hEq]
      _ = X' := hRecover X' hX'
  have hcard := Finset.card_le_card_of_injOn f hmap hinj
  let M := missingStarFacets H W v r
  let MY := M.filter fun S => Y ⊆ S
  let MZ := M.filter fun S => Z ⊆ S
  have hRootMap : ∀ X ∈ Xset, f X ∈ MY ∪ MZ := by
    intro X hX
    have hMissing : f X ∈ M := hmap X hX
    by_cases hFirst : insert v (Y ∪ X) ∈ H
    · apply Finset.mem_union_right
      exact Finset.mem_filter.mpr ⟨hMissing, by simp [f, hFirst]⟩
    · apply Finset.mem_union_left
      exact Finset.mem_filter.mpr ⟨hMissing, by simp [f, hFirst]⟩
  have hRootCard := Finset.card_le_card_of_injOn f hRootMap hinj
  have hUnionBound := Finset.card_union_le MY MZ
  constructor
  · simpa only [Xset, Ω, C, k, Finset.card_powersetCard] using hcard
  · have hSum := hRootCard.trans hUnionBound
    simpa only [Xset, Ω, C, k, M, MY, MZ,
      Finset.card_powersetCard] using hSum

/-- The global missing-star count, projected from the stronger root-sum
version of (IV.2.2). -/
theorem overlap_trade_missing_star_count
    {H : Family α} {W E F : Edge α} {v : α} {r : ℕ}
    (hH : Admissible H)
    (hE : E ∈ H) (hF : F ∈ H)
    (hEsub : E ⊆ W) (hFsub : F ⊆ W)
    (hEcard : E.card = r) (hFcard : F.card = r)
    (hEF : E ≠ F) (hShared : (E ∩ F).Nonempty)
    (hvW : v ∉ W) :
    ((W \ (E ∪ F)).card).choose (r - 1 - (E \ F).card) ≤
      (missingStarFacets H W v r).card :=
  (overlap_trade_missing_star_count_and_root_sum hH hE hF hEsub hFsub
    hEcard hFcard hEF hShared hvW).1

/-- The same count written in the numerical form of the all-rank manuscript
equation (IV.2.2), where `k = |E \ F|`. -/
theorem overlap_trade_missing_star_binomial_and_root_sum
    {H : Family α} {W E F : Edge α} {v : α} {r : ℕ}
    (hH : Admissible H)
    (hE : E ∈ H) (hF : F ∈ H)
    (hEsub : E ⊆ W) (hFsub : F ⊆ W)
    (hEcard : E.card = r) (hFcard : F.card = r)
    (hEF : E ≠ F) (hShared : (E ∩ F).Nonempty)
    (hvW : v ∉ W) :
    (W.card - r - (E \ F).card).choose (r - 1 - (E \ F).card) ≤
      (missingStarFacets H W v r).card ∧
    (W.card - r - (E \ F).card).choose (r - 1 - (E \ F).card) ≤
      ((missingStarFacets H W v r).filter
        fun S => E \ F ⊆ S).card +
      ((missingStarFacets H W v r).filter
        fun S => F \ E ⊆ S).card := by
  have hUnionSub : E ∪ F ⊆ W := Finset.union_subset hEsub hFsub
  have hUnionCard : (E ∪ F).card = r + (E \ F).card := by
    have hInc := Finset.card_union_add_card_inter E F
    have hDiff := Finset.card_sdiff_add_card_inter E F
    omega
  have hFreshCard : (W \ (E ∪ F)).card =
      W.card - r - (E \ F).card := by
    rw [Finset.card_sdiff_of_subset hUnionSub, hUnionCard]
    omega
  rw [← hFreshCard]
  exact overlap_trade_missing_star_count_and_root_sum
    hH hE hF hEsub hFsub hEcard hFcard hEF hShared hvW

/-- The global `q ≥ Λ_k` half of (IV.2.2). -/
theorem overlap_trade_missing_star_binomial
    {H : Family α} {W E F : Edge α} {v : α} {r : ℕ}
    (hH : Admissible H)
    (hE : E ∈ H) (hF : F ∈ H)
    (hEsub : E ⊆ W) (hFsub : F ⊆ W)
    (hEcard : E.card = r) (hFcard : F.card = r)
    (hEF : E ≠ F) (hShared : (E ∩ F).Nonempty)
    (hvW : v ∉ W) :
    (W.card - r - (E \ F).card).choose (r - 1 - (E \ F).card) ≤
      (missingStarFacets H W v r).card :=
  (overlap_trade_missing_star_binomial_and_root_sum
    hH hE hF hEsub hFsub hEcard hFcard hEF hShared hvW).1

/-- The two-root missing-facet multiplicity half of (IV.2.2). -/
theorem overlap_trade_root_multiplicity_bound
    {H : Family α} {W E F : Edge α} {v : α} {r : ℕ}
    (hH : Admissible H)
    (hE : E ∈ H) (hF : F ∈ H)
    (hEsub : E ⊆ W) (hFsub : F ⊆ W)
    (hEcard : E.card = r) (hFcard : F.card = r)
    (hEF : E ≠ F) (hShared : (E ∩ F).Nonempty)
    (hvW : v ∉ W) :
    (W.card - r - (E \ F).card).choose (r - 1 - (E \ F).card) ≤
      ((missingStarFacets H W v r).filter
        fun S => E \ F ⊆ S).card +
      ((missingStarFacets H W v r).filter
        fun S => F \ E ⊆ S).card :=
  (overlap_trade_missing_star_binomial_and_root_sum
    hH hE hF hEsub hFsub hEcard hFcard hEF hShared hvW).2

/-- Every pair of overlapping outside edges has a bad difference set on
at least one side, with the threshold convention of §IV.2. -/
theorem overlap_has_bad_difference
    {H : Family α} {W E F : Edge α} {v : α} {r : ℕ}
    (hH : Admissible H)
    (hE : E ∈ H) (hF : F ∈ H)
    (hEsub : E ⊆ W) (hFsub : F ⊆ W)
    (hEcard : E.card = r) (hFcard : F.card = r)
    (hEF : E ≠ F) (hShared : (E ∩ F).Nonempty)
    (hvW : v ∉ W) :
    let Λ := (W.card - r - (E \ F).card).choose
      (r - 1 - (E \ F).card)
    Λ ≤ 2 * ((missingStarFacets H W v r).filter
      fun S => E \ F ⊆ S).card ∨
    Λ ≤ 2 * ((missingStarFacets H W v r).filter
      fun S => F \ E ⊆ S).card := by
  have hRoot := overlap_trade_root_multiplicity_bound
    hH hE hF hEsub hFsub hEcard hFcard hEF hShared hvW
  dsimp
  omega

end JSP523
