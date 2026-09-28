import JSP523.Rank5.StarLayerCollisionCount

/-!
# Reindexing distinct star-layer collisions

This module makes the global incidence injection behind (IV.3.3): a
distinct pair of link members sharing a facet has unique extra vertices
`x,y`, so its incidence is represented in the cross-completion cell indexed
by `(x,y)` and the shared facet.
-/

namespace JSP523.Rank5

variable {α : Type*} [DecidableEq α]

/-- The unique point in `T \ P` when this difference is a singleton. -/
noncomputable def singletonDifferenceVertex (T P : Edge α) [Inhabited α] : α :=
  if h : (T \ P).card = 1 then
    Classical.choose (Finset.card_eq_one.mp h)
  else default

theorem singletonDifferenceVertex_spec
    [Inhabited α] {T P : Edge α} (h : (T \ P).card = 1) :
    T \ P = {singletonDifferenceVertex T P} := by
  unfold singletonDifferenceVertex
  rw [dite_eq_left h]
  exact Classical.choose_spec (Finset.card_eq_one.mp h)

/-- Source incidences: a distinct pair of link members together with a shared
codimension-one facet. -/
def distinctStarLayerIncidences
    (U : Edge α) (A B : Family α) (k : ℕ) :
    Finset (Σ _T : Edge α, Σ _S : Edge α, Edge α) :=
  A.sigma fun T =>
    (B.filter fun S => S ≠ T).sigma fun S =>
      sharedStarLayerFacets U T S k

/-- Target incidences indexed by an ordered pair of distinct completion
vertices and a tail in their actual cross cell. -/
noncomputable def crossCellIncidences
    (H : Family α) (U : Edge α) (z w : α) (r : ℕ) :
    Finset (Σ _x : α, Σ _y : α, Edge α) := by
  classical
  exact U.sigma fun x =>
    (U.erase x).sigma fun y => starLayerCrossCell H U z w x y r

/-- The distinct-link incidence injection used for the global IV.3.2
collision reindexing. -/
theorem distinctStarLayerIncidence_injects_crossCells
    [Inhabited α] {H : Family α} {U : Edge α} {z w : α} {r : ℕ}
    (hzu : z ∉ U) (hwu : w ∉ U) (hr : 4 ≤ r)
    (A B : Family α)
    (hA : A ⊆ actualStarLink H U z r)
    (hB : B ⊆ actualStarLink H U w r) :
    (distinctStarLayerIncidences U A B (r - 1)).card ≤
      (crossCellIncidences H U z w r).card := by
  classical
  let src := distinctStarLayerIncidences U A B (r - 1)
  let dst := crossCellIncidences H U z w r
  let f : (Σ T : Edge α, Σ S : Edge α, Edge α) →
      (Σ x : α, Σ y : α, Edge α) := fun p =>
        ⟨singletonDifferenceVertex p.1 p.2.2,
          ⟨singletonDifferenceVertex p.2.1 p.2.2, p.2.2⟩⟩
  have hMap : ∀ p ∈ src, f p ∈ dst := by
    intro p hp
    obtain ⟨T, pRest⟩ := p
    obtain ⟨S, P⟩ := pRest
    obtain ⟨hTlink, hRest⟩ := Finset.mem_sigma.mp hp
    obtain ⟨hSneT, hPmem⟩ := Finset.mem_sigma.mp hRest
    have hSfam : S ∈ B := (Finset.mem_filter.mp hSneT).1
    have hSne : S ≠ T := (Finset.mem_filter.mp hSneT).2
    have hTactual : T ∈ actualStarLink H U z r := hA hTlink
    have hSactual : S ∈ actualStarLink H U w r := hB hSfam
    have hPmem' := Finset.mem_filter.mp hPmem
    have hPU := (Finset.mem_powersetCard.mp hPmem'.1).1
    have hPmemU : P ∈ U.powersetCard (r - 2) := by
      have hidx : (r - 1) - 1 = r - 2 := by omega
      have hpow := hPmem'.1
      rw [hidx] at hpow
      exact hpow
    have hPcard : P.card = r - 2 := by
      have hcard := (Finset.mem_powersetCard.mp hPmem'.1).2
      have hidx : (r - 1) - 1 = r - 2 := by omega
      rw [hidx] at hcard
      exact hcard
    have hTcard : T.card = r - 1 :=
      (Finset.mem_powersetCard.mp (Finset.mem_filter.mp (hA hTlink)).1).2
    have hScard : S.card = r - 1 :=
      (Finset.mem_powersetCard.mp (Finset.mem_filter.mp (hB hSfam)).1).2
    have hPT : P ⊆ T := hPmem'.2.1
    have hPS : P ⊆ S := hPmem'.2.2
    have hTdiff : (T \ P).card = 1 := by
      rw [Finset.card_sdiff_of_subset hPT, hTcard, hPcard]
      omega
    have hSdiff : (S \ P).card = 1 := by
      rw [Finset.card_sdiff_of_subset hPS, hScard, hPcard]
      omega
    let x := singletonDifferenceVertex T P
    let y := singletonDifferenceVertex S P
    have hTdiffEq : T \ P = {x} :=
      singletonDifferenceVertex_spec hTdiff
    have hSdiffEq : S \ P = {y} :=
      singletonDifferenceVertex_spec hSdiff
    have hxT : x ∈ T \ P := by rw [hTdiffEq]; simp
    have hyS : y ∈ S \ P := by rw [hSdiffEq]; simp
    have hxU : x ∈ U :=
      (Finset.mem_powersetCard.mp (Finset.mem_filter.mp (hA hTlink)).1).1
        (Finset.mem_sdiff.mp hxT).1
    have hyU : y ∈ U :=
      (Finset.mem_powersetCard.mp (Finset.mem_filter.mp (hB hSfam)).1).1
        (Finset.mem_sdiff.mp hyS).1
    have hTrep : T = P ∪ {x} := by
      calc
        T = P ∪ (T \ P) := (Finset.union_sdiff_of_subset hPT).symm
        _ = P ∪ {x} := by rw [hTdiffEq]
    have hSrep : S = P ∪ {y} := by
      calc
        S = P ∪ (S \ P) := (Finset.union_sdiff_of_subset hPS).symm
        _ = P ∪ {y} := by rw [hSdiffEq]
    have hxy : x ≠ y := by
      intro hEq
      apply hSne.symm
      rw [hTrep, hSrep, hEq]
    obtain ⟨x₀, y₀, hx₀, hy₀, hxy₀, hCross⟩ :=
      distinct_star_link_members_land_in_cross_cell hzu hwu hTactual hSactual hr
        hPmemU
        hPT hPS hSne.symm
    have hxEq : x = x₀ := by
      have hx₀' : x₀ ∈ T \ P := hx₀
      rw [hTdiffEq] at hx₀'
      simp at hx₀'
      exact hx₀'.symm
    have hyEq : y = y₀ := by
      have hy₀' : y₀ ∈ S \ P := hy₀
      rw [hSdiffEq] at hy₀'
      simp at hy₀'
      exact hy₀'.symm
    have hCross' : P ∈ starLayerCrossCell H U z w x y r := by
      simpa [hxEq, hyEq] using hCross
    change ⟨singletonDifferenceVertex T P,
      ⟨singletonDifferenceVertex S P, P⟩⟩ ∈ U.sigma (fun x =>
      (U.erase x).sigma fun y => starLayerCrossCell H U z w x y r)
    apply Finset.mem_sigma.mpr
    refine ⟨hxU, Finset.mem_sigma.mpr ?_⟩
    refine ⟨Finset.mem_erase.mpr ⟨hxy.symm, hyU⟩, ?_⟩
    exact hCross'
  have hInj : Set.InjOn f (src : Set _) := by
    intro p hp q hq hEq
    obtain ⟨T, pRest⟩ := p
    obtain ⟨S, P⟩ := pRest
    obtain ⟨T', qRest⟩ := q
    obtain ⟨S', P'⟩ := qRest
    obtain ⟨hTlink, hRest⟩ := Finset.mem_sigma.mp hp
    obtain ⟨hSneT, hPmem⟩ := Finset.mem_sigma.mp hRest
    obtain ⟨hT'link, hRest'⟩ := Finset.mem_sigma.mp hq
    obtain ⟨hSneT', hPmem'⟩ := Finset.mem_sigma.mp hRest'
    have hSfam : S ∈ B := (Finset.mem_filter.mp hSneT).1
    have hS'fam : S' ∈ B := (Finset.mem_filter.mp hSneT').1
    have hTsub : P ⊆ T := (Finset.mem_filter.mp hPmem).2.1
    have hSsub : P ⊆ S := (Finset.mem_filter.mp hPmem).2.2
    have hT'sub : P' ⊆ T' := (Finset.mem_filter.mp hPmem').2.1
    have hS'sub : P' ⊆ S' := (Finset.mem_filter.mp hPmem').2.2
    have hTcard : T.card = r - 1 :=
      (Finset.mem_powersetCard.mp (Finset.mem_filter.mp (hA hTlink)).1).2
    have hScard : S.card = r - 1 :=
      (Finset.mem_powersetCard.mp (Finset.mem_filter.mp (hB hSfam)).1).2
    have hT'card : T'.card = r - 1 :=
      (Finset.mem_powersetCard.mp (Finset.mem_filter.mp (hA hT'link)).1).2
    have hS'card : S'.card = r - 1 :=
      (Finset.mem_powersetCard.mp (Finset.mem_filter.mp (hB hS'fam)).1).2
    have hPcard : P.card = r - 2 := by
      have h := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hPmem).1).2
      have hi : (r - 1) - 1 = r - 2 := by omega
      rw [hi] at h
      exact h
    have hP'card : P'.card = r - 2 := by
      have h := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hPmem').1).2
      have hi : (r - 1) - 1 = r - 2 := by omega
      rw [hi] at h
      exact h
    have hfx : singletonDifferenceVertex T P =
        singletonDifferenceVertex T' P' := by
      have := congrArg Sigma.fst hEq
      exact this
    have hfy : singletonDifferenceVertex S P =
        singletonDifferenceVertex S' P' := by
      have := congrArg (fun q : Σ x : α, Σ y : α, Edge α => q.2.1) hEq
      exact this
    have hfp : P = P' := by
      have := congrArg (fun q : Σ x : α, Σ y : α, Edge α => q.2.2) hEq
      exact this
    have hTdiff : (T \ P).card = 1 := by
      rw [Finset.card_sdiff_of_subset hTsub, hTcard, hPcard]
      omega
    have hSdiff : (S \ P).card = 1 := by
      rw [Finset.card_sdiff_of_subset hSsub, hScard, hPcard]
      omega
    have hT'diff : (T' \ P').card = 1 := by
      rw [Finset.card_sdiff_of_subset hT'sub, hT'card, hP'card]
      omega
    have hS'diff : (S' \ P').card = 1 := by
      rw [Finset.card_sdiff_of_subset hS'sub, hS'card, hP'card]
      omega
    have hTrep : T = P ∪ {singletonDifferenceVertex T P} := by
      calc
          T = P ∪ (T \ P) := (Finset.union_sdiff_of_subset hTsub).symm
        _ = P ∪ {singletonDifferenceVertex T P} :=
          by rw [singletonDifferenceVertex_spec hTdiff]
    have hSrep : S = P ∪ {singletonDifferenceVertex S P} := by
      calc
          S = P ∪ (S \ P) := (Finset.union_sdiff_of_subset hSsub).symm
        _ = P ∪ {singletonDifferenceVertex S P} :=
          by rw [singletonDifferenceVertex_spec hSdiff]
    have hT'rep : T' = P' ∪ {singletonDifferenceVertex T' P'} := by
      calc
          T' = P' ∪ (T' \ P') := (Finset.union_sdiff_of_subset hT'sub).symm
        _ = P' ∪ {singletonDifferenceVertex T' P'} :=
          by rw [singletonDifferenceVertex_spec hT'diff]
    have hS'rep : S' = P' ∪ {singletonDifferenceVertex S' P'} := by
      calc
          S' = P' ∪ (S' \ P') := (Finset.union_sdiff_of_subset hS'sub).symm
        _ = P' ∪ {singletonDifferenceVertex S' P'} :=
          by rw [singletonDifferenceVertex_spec hS'diff]
    have hfx' : singletonDifferenceVertex T P' =
        singletonDifferenceVertex T' P' := by simpa [hfp] using hfx
    have hfy' : singletonDifferenceVertex S P' =
        singletonDifferenceVertex S' P' := by simpa [hfp] using hfy
    have hTeq : T = T' := by
      calc
        T = P ∪ {singletonDifferenceVertex T P} := hTrep
        _ = P' ∪ {singletonDifferenceVertex T' P'} := by rw [hfp, hfx']
        _ = T' := hT'rep.symm
    have hSeq : S = S' := by
      calc
        S = P ∪ {singletonDifferenceVertex S P} := hSrep
        _ = P' ∪ {singletonDifferenceVertex S' P'} := by rw [hfp, hfy']
        _ = S' := hS'rep.symm
    cases hTeq
    cases hSeq
    cases hfp
    rfl
  exact Finset.card_le_card_of_injOn f hMap hInj

/-- Counting the source incidences by their ordered link-member pair gives
exactly the distinct-member part of the pairwise collision identity. -/
theorem distinctStarLayerIncidences_card_eq_sum
    (U : Edge α) (A B : Family α) (k : ℕ) :
    (distinctStarLayerIncidences U A B k).card =
      ∑ T ∈ A, ∑ S ∈ B.filter (fun S => S ≠ T),
        (sharedStarLayerFacets U T S k).card := by
  classical
  unfold distinctStarLayerIncidences
  rw [Finset.card_sigma]
  apply Finset.sum_congr rfl
  intro T hT
  rw [Finset.card_sigma]

/-- The actual collision moment for two star layers is bounded by the
equal-completion and distinct-completion codegree budgets in (IV.3.3). -/
theorem starLayerActualCollision_moment_le
    [Inhabited α] {H : Family α} {U : Edge α} {z w : α} {r D₂ D₃ : ℕ}
    (hH : Admissible H) (hzw : z ≠ w)
    (hzU : z ∉ U) (hwU : w ∉ U) (hr : 4 ≤ r)
    (hD₂ : ∀ S : Edge α, S.card = 2 →
      (H.filter fun E => S ⊆ E).card ≤ D₂)
    (hD₃ : ∀ S : Edge α, S.card = 3 →
      (H.filter fun E => S ⊆ E).card ≤ D₃) :
    (∑ P ∈ U.powersetCard (r - 2),
      starLayerPrefixDegree (actualStarLink H U z r) P *
        starLayerPrefixDegree (actualStarLink H U w r) P) ≤
      (r - 1) * (r - 1) * D₂ +
        U.card * (U.card - 1) * (r - 2) * D₃ := by
  classical
  let A := actualStarLink H U z r
  let B := actualStarLink H U w r
  let C := commonPrefixTails H U ({z} : Edge α) {w} (r - 1)
  have hCell : C.card ≤ (r - 1) * D₂ :=
    starLayerEqualCompletionCell_card_le hH hzw hzU hwU (by omega) hD₂
  have hABsub : A ∩ B ⊆ C := by
    intro T hT
    obtain ⟨hTA, hTB⟩ := Finset.mem_inter.mp hT
    have hTA' := Finset.mem_filter.mp hTA
    have hTB' := Finset.mem_filter.mp hTB
    have hTpow := Finset.mem_powersetCard.mp hTA'.1
    have hDisj : Disjoint T ({z} ∪ ({w} : Edge α)) := by
      apply Finset.disjoint_left.mpr
      intro x hxT hxzw
      rcases Finset.mem_union.mp hxzw with hxz | hxw
      · have hxz' : x = z := Finset.mem_singleton.mp hxz
        subst z
        exact hzU (hTpow.1 hxT)
      · have hxw' : x = w := Finset.mem_singleton.mp hxw
        subst w
        exact hwU (hTpow.1 hxT)
    apply mem_commonPrefixTails.mpr
    refine ⟨hTpow.1, hTpow.2, hDisj, ?_, ?_⟩
    · simpa [A, actualStarLink] using hTA'.2
    · simpa [B, actualStarLink] using hTB'.2
  have hEqualCard : (A ∩ B).card ≤ (r - 1) * D₂ :=
    (Finset.card_le_card hABsub).trans hCell
  have hDistinct := distinctStarLayerIncidence_injects_crossCells
    hzU hwU hr A B (by intro T hT; exact hT)
      (by intro T hT; exact hT)
  have hDistinctBound : (distinctStarLayerIncidences U A B (r - 1)).card ≤
      U.card * (U.card - 1) * (r - 2) * D₃ := by
    calc
      _ ≤ (crossCellIncidences H U z w r).card := hDistinct
      _ = starLayerDistinctCompletionIncidence H U z w r := by
        simp [crossCellIncidences, starLayerDistinctCompletionIncidence]
      _ ≤ U.card * (U.card - 1) * (r - 2) * D₃ :=
        starLayerDistinctCompletionIncidence_le hH hzw hzU hwU hr hD₃
  have hSourceSum := distinctStarLayerIncidences_card_eq_sum U A B (r - 1)
  have hPairId := starLayerPairwiseCollision_identity U (r - 1) A B
  have hRow : ∀ T ∈ A,
      (∑ S ∈ B, (sharedStarLayerFacets U T S (r - 1)).card) ≤
        (if T ∈ B then r - 1 else 0) +
          ∑ S ∈ B.filter (fun S => S ≠ T),
            (sharedStarLayerFacets U T S (r - 1)).card := by
    intro T hT
    by_cases hTB : T ∈ B
    · have hErase : B.erase T = B.filter (fun S => S ≠ T) := by
        ext S
        simp only [Finset.mem_erase, Finset.mem_filter]
        constructor
        · rintro ⟨hTS, hSB⟩
          exact ⟨hSB, fun hST => hTS hST⟩
        · rintro ⟨hSB, hST⟩
          exact ⟨fun hTS => hST hTS, hSB⟩
      have hAdd := Finset.add_sum_erase B
        (fun S => (sharedStarLayerFacets U T S (r - 1)).card) hTB
      rw [← hErase, ← hAdd]
      have hTsize :=
        (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hT).1).2
      have hTsub := (Finset.mem_powersetCard.mp
        (Finset.mem_filter.mp hT).1).1
      rw [sharedStarLayerFacets_card_eq_of_eq U T (r - 1)
        hTsub hTsize (by omega)]
      simp [hTB]
    · have hFilter : B.filter (fun S => S ≠ T) = B := by
        ext S
        simp only [Finset.mem_filter]
        constructor
        · exact And.left
        · intro hSB
          refine ⟨hSB, ?_⟩
          intro hST
          apply hTB
          simpa [hST] using hSB
      rw [hFilter]
      simp [hTB]
  have hRows :
      (∑ T ∈ A, ∑ S ∈ B,
        (sharedStarLayerFacets U T S (r - 1)).card) ≤
      (∑ T ∈ A, if T ∈ B then r - 1 else 0) +
        (distinctStarLayerIncidences U A B (r - 1)).card := by
    calc
      (∑ T ∈ A, ∑ S ∈ B,
          (sharedStarLayerFacets U T S (r - 1)).card)
        ≤ ∑ T ∈ A,
            ((if T ∈ B then r - 1 else 0) +
              ∑ S ∈ B.filter (fun S => S ≠ T),
                (sharedStarLayerFacets U T S (r - 1)).card) :=
          Finset.sum_le_sum hRow
      _ = (∑ T ∈ A, if T ∈ B then r - 1 else 0) +
          (distinctStarLayerIncidences U A B (r - 1)).card := by
          rw [Finset.sum_add_distrib, hSourceSum]
  have hDiag :
      (∑ T ∈ A, if T ∈ B then r - 1 else 0) ≤ (r - 1) * (r - 1) * D₂ := by
    have hDiagEq :
        (∑ T ∈ A, if T ∈ B then r - 1 else 0) =
          (A ∩ B).card * (r - 1) := by
      calc
        (∑ T ∈ A, if T ∈ B then r - 1 else 0) =
            ∑ T ∈ A.filter (fun T => T ∈ B), (r - 1) := by
          rw [Finset.sum_filter]
        _ = (A ∩ B).card * (r - 1) := by
          have hfilter : A.filter (fun T => T ∈ B) = A ∩ B := by
            ext T
            simp [Finset.mem_inter]
          rw [hfilter]
          simp [Finset.sum_const, Nat.mul_comm]
    rw [hDiagEq]
    calc
      (A ∩ B).card * (r - 1) ≤ ((r - 1) * D₂) * (r - 1) :=
        Nat.mul_le_mul_right _ hEqualCard
      _ = (r - 1) * (r - 1) * D₂ := by
        simp [Nat.mul_left_comm, Nat.mul_comm]
  have hIndex : (r - 1) - 1 = r - 2 := by omega
  rw [hIndex] at hPairId
  calc
    (∑ P ∈ U.powersetCard (r - 2),
      starLayerPrefixDegree A P * starLayerPrefixDegree B P)
      = ∑ T ∈ A, ∑ S ∈ B,
          (sharedStarLayerFacets U T S (r - 1)).card := hPairId
    _ ≤ (∑ T ∈ A, if T ∈ B then r - 1 else 0) +
          (distinctStarLayerIncidences U A B (r - 1)).card := hRows
    _ ≤ (r - 1) * (r - 1) * D₂ +
          U.card * (U.card - 1) * (r - 2) * D₃ :=
      Nat.add_le_add hDiag hDistinctBound

end JSP523.Rank5
