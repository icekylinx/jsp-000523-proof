import JSP523.Rank4.LocalDirtyPairGraph
import JSP523.Rank4.LocalDirtyRoot

/-!
# Finite dirty-edge charging for the near-star pair graph
-/

namespace JSP523.Rank4

variable {α : Type*} [DecidableEq α]

/-- The subfamily of `B₀` edges containing at least one pair from `Bad`. -/
def badPairDirtyEdges (B₀ Bad : Family α) : Family α :=
  B₀.filter fun E => ∃ P ∈ Bad, P ⊆ E

@[simp] theorem mem_badPairDirtyEdges {B₀ Bad : Family α} {E : Edge α} :
    E ∈ badPairDirtyEdges B₀ Bad ↔ E ∈ B₀ ∧ ∃ P ∈ Bad, P ⊆ E := by
  simp [badPairDirtyEdges]

/-- Select an exceptional pair root for each dirty edge. -/
noncomputable def chosenDirtyRoot (B₀ Bad : Family α)
    (E : {E : Edge α // E ∈ badPairDirtyEdges B₀ Bad}) :
    {P : Edge α // P ∈ Bad ∧ P ⊆ E.val} := by
  classical
  have hex : ∃ P, P ∈ Bad ∧ P ⊆ E.val := (Finset.mem_filter.mp E.property).2
  exact ⟨Classical.choose hex, Classical.choose_spec hex⟩

/-- The complementary pair to a selected bad root. -/
noncomputable def chosenDirtyTail (B₀ Bad : Family α)
    (E : {E : Edge α // E ∈ badPairDirtyEdges B₀ Bad}) : Edge α :=
  E.val \ (chosenDirtyRoot B₀ Bad E).val

/-- Encode a dirty edge by its selected root when its complementary pair is
not bad, and by the graph edge joining the two bad pairs otherwise. -/
noncomputable def chosenDirtyCode (B₀ Bad : Family α) [Fintype α]
    (hBadUniform : Uniform 2 Bad)
    (E : {E : Edge α // E ∈ badPairDirtyEdges B₀ Bad}) :
    Sum {P : Edge α // P ∈ Bad}
      {e : Sym2 {P : Edge α // P ∈ Bad} //
        e ∈ (badPairUnionGraph Bad B₀).edgeFinset} := by
  classical
  let G := badPairUnionGraph Bad B₀
  let p := chosenDirtyRoot B₀ Bad E
  let pv : {P : Edge α // P ∈ Bad} := ⟨p.val, p.property.1⟩
  let q : Edge α := chosenDirtyTail B₀ Bad E
  by_cases hq : q ∈ Bad
  · let qv : {P : Edge α // P ∈ Bad} := ⟨q, hq⟩
    have hPcard : p.val.card = 2 := hBadUniform p.property.1
    have hDisj : Disjoint p.val q := by
      apply Finset.disjoint_left.mpr
      intro x hxP hxq
      exact (Finset.mem_sdiff.mp hxq).2 hxP
    have hPneQ : p.val ≠ q := by
      intro heq
      obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < p.val.card)
      exact (Finset.disjoint_left.mp hDisj) hx (heq ▸ hx)
    have hUnion : p.val ∪ q = E.val := by
      dsimp [q, chosenDirtyTail]
      exact Finset.union_sdiff_of_subset p.property.2
    have hAdj : G.Adj pv qv := by
      refine ⟨?_, hDisj, ?_⟩
      · intro h
        exact hPneQ (congrArg Subtype.val h)
      · change p.val ∪ q ∈ B₀
        rw [hUnion]
        exact (Finset.mem_filter.mp E.property).1
    exact Sum.inr ⟨Sym2.mk pv qv, by
      simpa [G, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hAdj⟩
  · exact Sum.inl ⟨p.val, p.property.1⟩

/-- The charging code is injective: graph codes determine the union edge,
and root-only codes are unique by the nonbad-tail lemma. -/
theorem chosen_dirty_code_injective
    {B₀ Bad : Family α} [Fintype α]
    (hBadUniform : Uniform 2 Bad)
    (hRootUnique : ∀ ⦃P E F : Edge α⦄, P ∈ Bad → E ∈ B₀ → F ∈ B₀ →
      P ⊆ E → P ⊆ F → E \ P ∉ Bad → F \ P ∉ Bad → E = F) :
    Function.Injective (chosenDirtyCode B₀ Bad hBadUniform) := by
  classical
  let G := badPairUnionGraph Bad B₀
  let V := {P : Edge α // P ∈ Bad}
  let ECode := {e : Sym2 V // e ∈ G.edgeFinset}
  intro E F hCode
  by_cases hETail : chosenDirtyTail B₀ Bad E ∈ Bad
  · by_cases hFTail : chosenDirtyTail B₀ Bad F ∈ Bad
    · have hPairEq :
          Sym2.mk
              (⟨(chosenDirtyRoot B₀ Bad E).val,
                (chosenDirtyRoot B₀ Bad E).property.1⟩ : V)
              (⟨chosenDirtyTail B₀ Bad E, hETail⟩ : V) =
            Sym2.mk
              (⟨(chosenDirtyRoot B₀ Bad F).val,
                (chosenDirtyRoot B₀ Bad F).property.1⟩ : V)
              (⟨chosenDirtyTail B₀ Bad F, hFTail⟩ : V) := by
          have h := congrArg
            (fun c : Sum V ECode => c.elim
              (fun _ => (none : Option (Sym2 V))) (fun e => some e.val)) hCode
          simpa [chosenDirtyCode, hETail, hFTail, G, V, ECode] using h
      have hPairs := Sym2.eq_iff.mp hPairEq
      rcases hPairs with hPairs | hPairs
      · rcases hPairs with ⟨hP, hQ⟩
        have hPval : (chosenDirtyRoot B₀ Bad E).val =
            (chosenDirtyRoot B₀ Bad F).val := congrArg Subtype.val hP
        have hQval : chosenDirtyTail B₀ Bad E =
            chosenDirtyTail B₀ Bad F := congrArg Subtype.val hQ
        have hUnionE :
            (chosenDirtyRoot B₀ Bad E).val ∪ chosenDirtyTail B₀ Bad E = E.val := by
          change (chosenDirtyRoot B₀ Bad E).val ∪
            (E.val \ (chosenDirtyRoot B₀ Bad E).val) = E.val
          exact Finset.union_sdiff_of_subset
            (chosenDirtyRoot B₀ Bad E).property.2
        have hUnionF :
            (chosenDirtyRoot B₀ Bad F).val ∪ chosenDirtyTail B₀ Bad F = F.val := by
          change (chosenDirtyRoot B₀ Bad F).val ∪
            (F.val \ (chosenDirtyRoot B₀ Bad F).val) = F.val
          exact Finset.union_sdiff_of_subset
            (chosenDirtyRoot B₀ Bad F).property.2
        apply Subtype.ext
        rw [← hUnionE, ← hUnionF, hPval, hQval]
      · rcases hPairs with ⟨hP, hQ⟩
        have hPval : (chosenDirtyRoot B₀ Bad E).val =
            chosenDirtyTail B₀ Bad F := by simpa using congrArg Subtype.val hP
        have hQval : chosenDirtyTail B₀ Bad E =
            (chosenDirtyRoot B₀ Bad F).val := by simpa using congrArg Subtype.val hQ
        have hUnionE :
            (chosenDirtyRoot B₀ Bad E).val ∪ chosenDirtyTail B₀ Bad E = E.val := by
          change (chosenDirtyRoot B₀ Bad E).val ∪
            (E.val \ (chosenDirtyRoot B₀ Bad E).val) = E.val
          exact Finset.union_sdiff_of_subset
            (chosenDirtyRoot B₀ Bad E).property.2
        have hUnionF :
            (chosenDirtyRoot B₀ Bad F).val ∪ chosenDirtyTail B₀ Bad F = F.val := by
          change (chosenDirtyRoot B₀ Bad F).val ∪
            (F.val \ (chosenDirtyRoot B₀ Bad F).val) = F.val
          exact Finset.union_sdiff_of_subset
            (chosenDirtyRoot B₀ Bad F).property.2
        apply Subtype.ext
        rw [← hUnionE, ← hUnionF, hPval, hQval]
        exact Finset.union_comm _ _
    · simp [chosenDirtyCode, hETail, hFTail] at hCode
  · by_cases hFTail : chosenDirtyTail B₀ Bad F ∈ Bad
    · simp [chosenDirtyCode, hETail, hFTail] at hCode
    · have hRootEq : (chosenDirtyRoot B₀ Bad E).val =
          (chosenDirtyRoot B₀ Bad F).val := by
        have h := congrArg
          (fun c : Sum V ECode => c.elim
            (fun p => some p.val) (fun _ => (none : Option (Edge α)))) hCode
        simpa [chosenDirtyCode, hETail, hFTail] using h
      have hERoot := (chosenDirtyRoot B₀ Bad E).property
      have hFRoot := (chosenDirtyRoot B₀ Bad F).property
      have hSubset : (chosenDirtyRoot B₀ Bad E).val ⊆ F.val := by
        simpa [hRootEq] using hFRoot.2
      have hTailNotBad : F.val \ (chosenDirtyRoot B₀ Bad E).val ∉ Bad := by
        simpa [chosenDirtyTail, hRootEq] using hFTail
      have hEF : E.val = F.val := hRootUnique hERoot.1
        (Finset.mem_filter.mp E.property).1 (Finset.mem_filter.mp F.property).1
        hERoot.2 hSubset
        (by simpa [chosenDirtyTail] using hETail)
        hTailNotBad
      exact Subtype.ext hEF

/-- The actual finite charging inequality of (III.C.6), before applying the
C₄ extremal estimate. -/
theorem bad_pair_dirty_edges_card_le
    {B₀ Bad : Family α} [Fintype α]
    (hBadUniform : Uniform 2 Bad)
    (hRootUnique : ∀ ⦃P E F : Edge α⦄, P ∈ Bad → E ∈ B₀ → F ∈ B₀ →
      P ⊆ E → P ⊆ F → E \ P ∉ Bad → F \ P ∉ Bad → E = F) :
    (badPairDirtyEdges B₀ Bad).card ≤
      Bad.card + (badPairUnionGraph Bad B₀).edgeFinset.card := by
  classical
  let G := badPairUnionGraph Bad B₀
  let V := {P : Edge α // P ∈ Bad}
  let ECode := {e : Sym2 V // e ∈ G.edgeFinset}
  calc
    (badPairDirtyEdges B₀ Bad).card =
        Fintype.card {E : Edge α // E ∈ badPairDirtyEdges B₀ Bad} := by
          simp only [Fintype.card_coe]
    _ ≤ Fintype.card (Sum V ECode) :=
      Fintype.card_le_of_injective (chosenDirtyCode B₀ Bad hBadUniform)
        (chosen_dirty_code_injective hBadUniform hRootUnique)
    _ = Bad.card + G.edgeFinset.card := by
      have hV : Fintype.card V = Bad.card := by
        change Fintype.card {P : Edge α // P ∈ Bad} = Bad.card
        simp only [Fintype.card_coe]
      have hE : Fintype.card ECode = G.edgeFinset.card := by
        change Fintype.card {e : Sym2 V // e ∈ G.edgeFinset} = G.edgeFinset.card
        simp only [Fintype.card_coe]
      simp only [Fintype.card_sum, hV, hE]

/-- Ordinary outside edges containing at least one exceptional pair. -/
def nearStarDirtyOutsideEdges (H : Family α) (W : Edge α) (v : α) : Family α :=
  (nearStarOrdinaryOutsideEdges H W v).filter fun E =>
    ∃ P ∈ nearStarBadPairs H W v, P ⊆ E

@[simp] theorem mem_nearStarDirtyOutsideEdges {H : Family α} {W : Edge α}
    {v : α} {E : Edge α} :
    E ∈ nearStarDirtyOutsideEdges H W v ↔
      E ∈ nearStarOrdinaryOutsideEdges H W v ∧
        ∃ P ∈ nearStarBadPairs H W v, P ⊆ E := by
  simp [nearStarDirtyOutsideEdges]

/-- III.C.6's injection for the actual near-star exceptional pairs. -/
theorem near_star_actual_dirty_edge_bound_of_root_unique
    {H : Family α} {W : Edge α} {v : α} [Fintype α]
    (hBadUniform : Uniform 2 (nearStarBadPairs H W v))
    (hRootUnique : ∀ ⦃P E F : Edge α⦄,
      P ∈ nearStarBadPairs H W v →
      E ∈ nearStarOrdinaryOutsideEdges H W v →
      F ∈ nearStarOrdinaryOutsideEdges H W v →
      P ⊆ E → P ⊆ F →
      E \ P ∉ nearStarBadPairs H W v →
      F \ P ∉ nearStarBadPairs H W v → E = F) :
    (nearStarDirtyOutsideEdges H W v).card ≤
      (nearStarBadPairs H W v).card +
        (badPairUnionGraph (nearStarBadPairs H W v)
          (nearStarOrdinaryOutsideEdges H W v)).edgeFinset.card := by
  classical
  simpa [nearStarDirtyOutsideEdges, badPairDirtyEdges] using
    (bad_pair_dirty_edges_card_le hBadUniform hRootUnique)

/-- At a fixed bad-pair root, there is at most one ordinary outside edge
whose complementary pair is nonexceptional. -/
theorem near_star_bad_root_has_unique_nondirty_completion
    {H : Family α} {W P E F : Edge α} {v : α}
    (hH : Admissible H) (hUniform : Uniform 4 H) (hvW : v ∉ W)
    (hP : P ∈ nearStarBadPairs H W v)
    (hE : E ∈ nearStarOrdinaryOutsideEdges H W v)
    (hF : F ∈ nearStarOrdinaryOutsideEdges H W v)
    (hPE : P ⊆ E) (hPF : P ⊆ F)
    (hETail : E \ P ∉ nearStarBadPairs H W v)
    (hFTail : F \ P ∉ nearStarBadPairs H W v) : E = F := by
  by_contra hEF
  have hOrdH : nearStarOrdinaryOutsideEdges H W v ⊆ H := by
    intro X hX
    exact (Finset.mem_filter.mp hX).1
  have hOrdU : ∀ X ∈ nearStarOrdinaryOutsideEdges H W v,
      X ⊆ W \ badSingletonVertices H W v 4 := by
    intro X hX
    exact (Finset.mem_filter.mp hX).2
  have hNoTriple := no_triple_overlap_of_ordinary_unique_completion
    hH hUniform hOrdH hOrdU Finset.Subset.rfl hvW
  have hPcard : P.card = 2 := by
    exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hP).1).2
  have hEcard : E.card = 4 := hUniform (hOrdH hE)
  have hFcard : F.card = 4 := hUniform (hOrdH hF)
  have hInterSub : P ⊆ E ∩ F := by
    intro x hx
    exact Finset.mem_inter.mpr ⟨hPE hx, hPF hx⟩
  have hInterGe : 2 ≤ (E ∩ F).card := by
    calc
      2 = P.card := hPcard.symm
      _ ≤ (E ∩ F).card := Finset.card_le_card hInterSub
  have hInterLe : (E ∩ F).card ≤ 2 := hNoTriple hE hF hEF
  have hInterCard : (E ∩ F).card = 2 := by omega
  have hInterEq : E ∩ F = P :=
    (Finset.eq_of_subset_of_card_le hInterSub (by omega)).symm
  have hDiffE : E \ F = E \ P := by
    rw [← hInterEq]
    ext x
    simp
  have hDiffF : F \ E = F \ P := by
    have hInterEq' : F ∩ E = P := by simpa [Finset.inter_comm] using hInterEq
    rw [← hInterEq']
    ext x
    simp
  have hTailCard : (E \ P).card = 2 := by
    have h := Finset.card_sdiff_add_card_inter E P
    have hInter : E ∩ P = P := Finset.inter_eq_right.mpr hPE
    rw [hInter, hEcard, hPcard] at h
    omega
  have hShared : (E ∩ F).Nonempty := Finset.card_pos.mp (by omega)
  exact near_star_pair_root_at_most_one_nonbad_tail
    hH hvW (hOrdH hE) (hOrdH hF)
    (fun x hx => (Finset.mem_sdiff.mp (hOrdU E hE hx)).1)
    (fun x hx => (Finset.mem_sdiff.mp (hOrdU F hF hx)).1)
    hEcard hFcard hShared hEF hDiffE hDiffF hTailCard hETail hFTail

/-- III.C.6's dirty-edge injection for the actual near-star exceptional
pairs. -/
theorem near_star_actual_dirty_edge_bound
    {H : Family α} {W : Edge α} {v : α} [Fintype α]
    (hH : Admissible H) (hUniform : Uniform 4 H) (hvW : v ∉ W) :
    (nearStarDirtyOutsideEdges H W v).card ≤
      (nearStarBadPairs H W v).card +
        (badPairUnionGraph (nearStarBadPairs H W v)
          (nearStarOrdinaryOutsideEdges H W v)).edgeFinset.card := by
  classical
  have hBadUniform : Uniform 2 (nearStarBadPairs H W v) := by
    intro P hP
    exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hP).1).2
  have hRootUnique : ∀ ⦃P E F : Edge α⦄,
      P ∈ nearStarBadPairs H W v →
      E ∈ nearStarOrdinaryOutsideEdges H W v →
      F ∈ nearStarOrdinaryOutsideEdges H W v →
      P ⊆ E → P ⊆ F →
      E \ P ∉ nearStarBadPairs H W v →
      F \ P ∉ nearStarBadPairs H W v → E = F := by
    intro P E F hP hE hF hPE hPF hETail hFTail
    exact near_star_bad_root_has_unique_nondirty_completion
      hH hUniform hvW hP hE hF hPE hPF hETail hFTail
  exact near_star_actual_dirty_edge_bound_of_root_unique hBadUniform hRootUnique

/-- The complete III.C.6 count for `B₀`: charge single-root dirty edges to
their root, the remaining dirty edges to `G`, and the clean family by
opposite-facet incidence. -/
theorem near_star_outside_b_0_bound
    {H : Family α} {W : Edge α} {v : α} [Fintype α]
    (hH : Admissible H) (hUniform : Uniform 4 H) (hvW : v ∉ W) :
    ((nearStarOrdinaryOutsideEdges H W v).card : ℝ) ≤
      (((W \ badSingletonVertices H W v 4).card : ℝ) +
        (missingStarTriples H (W \ badSingletonVertices H W v 4) v).card) / 4 +
        (5 * (nearStarBadPairs H W v).card : ℝ) / 4 +
        Real.sqrt (((nearStarBadPairs H W v).card : ℝ) ^ 3) / 2 := by
  classical
  let B₀ := nearStarOrdinaryOutsideEdges H W v
  let Bad := nearStarBadPairs H W v
  let U := W \ badSingletonVertices H W v 4
  let Dirty := nearStarDirtyOutsideEdges H W v
  let Clean := nearStarCleanOutsideEdges H W v
  have hSplit : B₀.card = Dirty.card + Clean.card := by
    have h := Finset.card_filter_add_card_filter_not
      (s := B₀) (p := fun E => ∃ P ∈ Bad, P ⊆ E)
    have hClean : B₀.filter (fun E => ¬ ∃ P ∈ Bad, P ⊆ E) = Clean := by
      ext E
      simp [Clean, B₀, Bad, nearStarCleanOutsideEdges,
        nearStarOrdinaryOutsideEdges]
    have hDirty : B₀.filter (fun E => ∃ P ∈ Bad, P ⊆ E) = Dirty := by
      ext E
      simp [Dirty, B₀, Bad, nearStarDirtyOutsideEdges,
        nearStarOrdinaryOutsideEdges]
    rw [hDirty, hClean] at h
    omega
  have hCleanCount := near_star_clean_outside_incidence hH hUniform hvW
  have hDirtyCount := near_star_actual_dirty_edge_bound hH hUniform hvW
  have hGraphCount := near_star_actual_bad_pair_graph_edge_bound hH hUniform hvW
  have hSplitR : (B₀.card : ℝ) = (Dirty.card : ℝ) + (Clean.card : ℝ) := by
    exact_mod_cast hSplit
  have hCleanR : 4 * (Clean.card : ℝ) ≤ U.card +
      (missingStarTriples H U v).card := by
    exact_mod_cast hCleanCount
  have hDirtyR : (Dirty.card : ℝ) ≤ Bad.card +
      (badPairUnionGraph Bad B₀).edgeFinset.card := by
    exact_mod_cast hDirtyCount
  have hGraphR : ((badPairUnionGraph Bad B₀).edgeFinset.card : ℝ) ≤
      (Real.sqrt ((Bad.card : ℝ) ^ 3) + (Bad.card : ℝ) / 2) / 2 := by
    exact_mod_cast hGraphCount
  dsimp [B₀, Bad, U, Dirty, Clean] at hSplitR hCleanR hDirtyR hGraphR ⊢
  nlinarith

/-- Under the exceptional-count outputs `D = ∅` and `h ≤ 18`, equation
(III.C.6) gives the refined estimate `4b ≤ q + w + 244`. -/
theorem near_star_outside_refined_244
    {H : Family α} {W : Edge α} {v : α} [Fintype α]
    (hH : Admissible H) (hUniform : Uniform 4 H) (hvW : v ∉ W)
    (hD : (badSingletonVertices H W v 4).card = 0)
    (hBad : (nearStarBadPairs H W v).card ≤ 18) :
    4 * (outsideEdges H W).card ≤
      (missingStarTriples H W v).card + W.card + 244 := by
  classical
  have hDset : badSingletonVertices H W v 4 = ∅ :=
    Finset.card_eq_zero.mp hD
  have hB₀eq : nearStarOrdinaryOutsideEdges H W v = outsideEdges H W := by
    ext E
    simp [nearStarOrdinaryOutsideEdges, outsideEdges, hDset]
  have hbound := near_star_outside_b_0_bound hH hUniform hvW
  have hbound' : ((outsideEdges H W).card : ℝ) ≤
      ((W.card : ℝ) + (missingStarTriples H W v).card) / 4 +
        (5 * (nearStarBadPairs H W v).card : ℝ) / 4 +
        Real.sqrt (((nearStarBadPairs H W v).card : ℝ) ^ 3) / 2 := by
    simpa [hB₀eq, hDset] using hbound
  have hBadR : (nearStarBadPairs H W v).card ≤ (18 : ℝ) := by
    exact_mod_cast hBad
  have hBadNonneg :
      (0 : ℝ) ≤ (nearStarBadPairs H W v).card := by positivity
  have hPow : ((nearStarBadPairs H W v).card : ℝ) ^ 3 ≤ 18 ^ 3 :=
    pow_le_pow_left₀ hBadNonneg hBadR 3
  have hSqrt : Real.sqrt (((nearStarBadPairs H W v).card : ℝ) ^ 3) ≤ 77 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, hPow.trans (by norm_num)⟩
  have hscaled := mul_le_mul_of_nonneg_left hbound' (by norm_num : 0 ≤ (4 : ℝ))
  have hfour : (4 : ℝ) * (outsideEdges H W).card ≤
      (missingStarTriples H W v).card + W.card + 244 := by
    nlinarith [hscaled, hSqrt, hBadR]
  exact_mod_cast hfour

end JSP523.Rank4
