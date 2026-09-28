import JSP523.Coarse.AllRank

/-!
# Coarse all-rank bound on a finite ground set

The all-rank bound is applied to the subtype of a prescribed finite set
of vertices. The edge family is transported to that subtype by lifting
each edge along the inclusion.
-/

namespace JSP523.Coarse

open JSP523

variable {α : Type*} [DecidableEq α]

/-- Lift an edge supported on `W` to an edge on the subtype of `W`. -/
private def liftGroundEdge (W : Finset α) (E : Edge α) (hE : E ⊆ W) :
    Edge {x // x ∈ W} :=
  E.attach.image fun x => (⟨x.1, hE x.2⟩ : {x // x ∈ W})

private theorem mem_liftGroundEdge_iff
    (W : Finset α) (E : Edge α) (hE : E ⊆ W)
    (x : {x // x ∈ W}) :
    x ∈ liftGroundEdge W E hE ↔ (x : α) ∈ E := by
  constructor
  · intro hx
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hx
    have hval : (y : α) = x := congrArg Subtype.val hxy
    simpa [hval] using y.2
  · intro hx
    apply Finset.mem_image.mpr
    refine ⟨⟨x.1, hx⟩, Finset.mem_attach _ _, ?_⟩
    apply Subtype.ext
    rfl

private theorem liftGroundEdge_val
    (W : Finset α) (E : Edge α) (hE : E ⊆ W) :
    (liftGroundEdge W E hE).image Subtype.val = E := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hx
    subst x
    exact (mem_liftGroundEdge_iff W E hE y).mp hy
  · intro hx
    let y : {x // x ∈ W} := ⟨x, hE hx⟩
    apply Finset.mem_image.mpr
    refine ⟨y, (mem_liftGroundEdge_iff W E hE y).2 hx, ?_⟩
    rfl

private theorem liftGroundEdge_card
    (W : Finset α) (E : Edge α) (hE : E ⊆ W) :
    (liftGroundEdge W E hE).card = E.card := by
  calc
    (liftGroundEdge W E hE).card =
        ((liftGroundEdge W E hE).image Subtype.val).card :=
      (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ = E.card := congrArg Finset.card (liftGroundEdge_val W E hE)

/-- The arbitrary finite-ground-set version of the all-rank coarse bound.
The universe size on the right is the size of `W`, irrespective of the
ambient type containing the edges. -/
theorem coarse_bound_on_ground_set
    (H : Family α) (W : Finset α) (r : ℕ) (hr : 3 ≤ r)
    (hU : Uniform r H) (hAdm : Admissible H)
    (hW : ∀ E ∈ H, E ⊆ W) :
    r.factorial * H.card ≤ 3 * r ^ r * W.card ^ (r - 1) := by
  classical
  let β := {x // x ∈ W}
  let lift : {E // E ∈ H} → Edge β := fun E =>
    liftGroundEdge W E.1 (hW E.1 E.2)
  let K : Family β := H.attach.image lift
  have hLiftInj : Set.InjOn lift (H.attach : Set {E // E ∈ H}) := by
    intro E hE E' hE' hEq
    have hv := congrArg (fun T : Edge β => T.image Subtype.val) hEq
    simpa [lift, liftGroundEdge_val] using hv
  have hKcard : K.card = H.card := by
    simp [K, Finset.card_image_of_injOn hLiftInj]
  have hKU : Uniform r K := by
    intro A hA
    obtain ⟨E, hE, rfl⟩ := Finset.mem_image.mp hA
    exact (liftGroundEdge_card W E.1 (hW E.1 E.2)).trans (hU E.2)
  have hKAdm : Admissible K := by
    intro A B C D hA hB hC hD hq
    obtain ⟨EA, hEA, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨EB, hEB, rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨EC, hEC, rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨ED, hED, rfl⟩ := Finset.mem_image.mp hD
    let eA := EA.1
    let eB := EB.1
    let eC := EC.1
    let eD := ED.1
    have hAneB : eA ≠ eB := by
      intro h
      apply hq.distinct.ab
      subst eB
      have : EA = EB := Subtype.ext h
      subst EB
      rfl
    have hAneC : eA ≠ eC := by
      intro h
      apply hq.distinct.ac
      subst eC
      have : EA = EC := Subtype.ext h
      subst EC
      rfl
    have hAneD : eA ≠ eD := by
      intro h
      apply hq.distinct.ad
      subst eD
      have : EA = ED := Subtype.ext h
      subst ED
      rfl
    have hBneC : eB ≠ eC := by
      intro h
      apply hq.distinct.bc
      subst eC
      have : EB = EC := Subtype.ext h
      subst EC
      rfl
    have hBneD : eB ≠ eD := by
      intro h
      apply hq.distinct.bd
      subst eD
      have : EB = ED := Subtype.ext h
      subst ED
      rfl
    have hCneD : eC ≠ eD := by
      intro h
      apply hq.distinct.cd
      subst eD
      have : EC = ED := Subtype.ext h
      subst ED
      rfl
    have hdisjAB : Disjoint eA eB := by
      apply Finset.disjoint_left.mpr
      intro x hxA hxB
      have hxA' : (⟨x, hW eA EA.2 hxA⟩ : β) ∈ liftGroundEdge W eA (hW eA EA.2) :=
        (mem_liftGroundEdge_iff W eA _ _).2 hxA
      have hxB' : (⟨x, hW eB EB.2 hxB⟩ : β) ∈ liftGroundEdge W eB (hW eB EB.2) :=
        (mem_liftGroundEdge_iff W eB _ _).2 hxB
      exact (Finset.disjoint_left.mp hq.disjAB) hxA' hxB'
    have hdisjCD : Disjoint eC eD := by
      apply Finset.disjoint_left.mpr
      intro x hxC hxD
      have hxC' : (⟨x, hW eC EC.2 hxC⟩ : β) ∈ liftGroundEdge W eC (hW eC EC.2) :=
        (mem_liftGroundEdge_iff W eC _ _).2 hxC
      have hxD' : (⟨x, hW eD ED.2 hxD⟩ : β) ∈ liftGroundEdge W eD (hW eD ED.2) :=
        (mem_liftGroundEdge_iff W eD _ _).2 hxD
      exact (Finset.disjoint_left.mp hq.disjCD) hxC' hxD'
    have hUnion : eA ∪ eB = eC ∪ eD := by
      have hv := congrArg (fun T : Edge β => T.image Subtype.val) hq.sameUnion
      simp only [Finset.image_union] at hv
      change (liftGroundEdge W eA (hW eA EA.2)).image Subtype.val ∪
          (liftGroundEdge W eB (hW eB EB.2)).image Subtype.val =
        (liftGroundEdge W eC (hW eC EC.2)).image Subtype.val ∪
          (liftGroundEdge W eD (hW eD ED.2)).image Subtype.val at hv
      rw [liftGroundEdge_val, liftGroundEdge_val,
        liftGroundEdge_val, liftGroundEdge_val] at hv
      exact hv
    exact hAdm EA.2 EB.2 EC.2 ED.2
      ⟨⟨hAneB, hAneC, hAneD, hBneC, hBneD, hCneD⟩,
        hdisjAB, hdisjCD, hUnion⟩
  have hBound := coarse_bound_all_rank K r hr hKU hKAdm
  have hCardSubtype : Fintype.card β = W.card := by simp [β]
  simpa [hKcard, hCardSubtype] using hBound

end JSP523.Coarse
