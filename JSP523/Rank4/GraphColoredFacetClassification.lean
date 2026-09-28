import JSP523.Rank4.GraphFacetLabelUniformity
import JSP523.Rank4.GraphCompletionData

/-!
# Canonical completion-clique size and coloring

The completion set of a colored facet is treated as a whole.  If it has no
monochromatic triangle, all its triangles are rainbow; the three available
facet colors then bound its order by four.
-/

namespace JSP523.Rank4

variable {α : Type*} [DecidableEq α]

noncomputable def canonicalCompletionEnum [Fintype α] (C : Finset α) :
    Fin C.card → α := fun i =>
  ((Fintype.equivFin {x // x ∈ C}).symm (Fin.cast (by simp) i)).val

omit [DecidableEq α] in
theorem canonical_completion_enum_mem [Fintype α] (C : Finset α)
    (i : Fin C.card) : canonicalCompletionEnum C i ∈ C :=
  (Fintype.equivFin {x // x ∈ C}).symm (Fin.cast (by simp) i) |>.property

omit [DecidableEq α] in
theorem canonical_completion_enum_injective [Fintype α] (C : Finset α) :
    Function.Injective (canonicalCompletionEnum C) := by
  intro i j hij
  have hSub : (Fintype.equivFin {x // x ∈ C}).symm (Fin.cast (by simp) i) =
      (Fintype.equivFin {x // x ∈ C}).symm (Fin.cast (by simp) j) := by
    apply Subtype.ext
    exact hij
  have hFin := (Equiv.injective (Fintype.equivFin {x // x ∈ C}).symm) hSub
  apply Fin.ext
  simpa using congrArg Fin.val hFin

noncomputable def canonicalTriangleCompletion [Fintype α] (D : FiniteCompletionCliqueData α)
    (T : Edge α) (hcard : (graphFacetCompletions D.K D.ground T).card = 3) :
    Fin 3 → α := fun i => canonicalCompletionEnum
      (graphFacetCompletions D.K D.ground T) (Fin.cast hcard.symm i)

noncomputable def canonicalK4Completion [Fintype α] (D : FiniteCompletionCliqueData α)
    (T : Edge α) (hcard : (graphFacetCompletions D.K D.ground T).card = 4) :
    Fin 4 → α := fun i => canonicalCompletionEnum
      (graphFacetCompletions D.K D.ground T) (Fin.cast hcard.symm i)

theorem canonical_triangle_completion_mem [Fintype α] (D : FiniteCompletionCliqueData α)
    (T : Edge α) (hcard : (graphFacetCompletions D.K D.ground T).card = 3)
    (i : Fin 3) :
    canonicalTriangleCompletion D T hcard i ∈ graphFacetCompletions D.K D.ground T :=
  canonical_completion_enum_mem _ _

theorem canonical_k4_completion_mem [Fintype α] (D : FiniteCompletionCliqueData α)
    (T : Edge α) (hcard : (graphFacetCompletions D.K D.ground T).card = 4)
    (i : Fin 4) :
    canonicalK4Completion D T hcard i ∈ graphFacetCompletions D.K D.ground T :=
  canonical_completion_enum_mem _ _

theorem canonical_triangle_completion_injective [Fintype α] (D : FiniteCompletionCliqueData α)
    (T : Edge α) (hcard : (graphFacetCompletions D.K D.ground T).card = 3) :
    Function.Injective (canonicalTriangleCompletion D T hcard) := by
  intro i j hij
  have h := (canonical_completion_enum_injective
    (graphFacetCompletions D.K D.ground T)) hij
  apply Fin.ext
  simpa using congrArg Fin.val h

theorem canonical_k4_completion_injective [Fintype α] (D : FiniteCompletionCliqueData α)
    (T : Edge α) (hcard : (graphFacetCompletions D.K D.ground T).card = 4) :
    Function.Injective (canonicalK4Completion D T hcard) := by
  intro i j hij
  have h := (canonical_completion_enum_injective
    (graphFacetCompletions D.K D.ground T)) hij
  apply Fin.ext
  simpa using congrArg Fin.val h

noncomputable def canonicalTriangleMark [Fintype α]
    (D : FiniteCompletionCliqueData α) (T : Edge α)
    (hcard : (graphFacetCompletions D.K D.ground T).card = 3) : CliqueColor → α :=
  fun i => D.label (completionTriangleEnds (canonicalTriangleCompletion D T hcard) i).1
    (completionTriangleEnds (canonicalTriangleCompletion D T hcard) i).2

noncomputable def canonicalK4Mark [Fintype α]
    (D : FiniteCompletionCliqueData α) (T : Edge α)
    (hcard : (graphFacetCompletions D.K D.ground T).card = 4) : CliqueColor → α :=
  fun i => D.label
    (completionK4Ends (canonicalK4Completion D T hcard) ⟨i.val, by omega⟩).1
    (completionK4Ends (canonicalK4Completion D T hcard) ⟨i.val, by omega⟩).2

def CompletionTriangleRainbow (D : FiniteCompletionCliqueData α)
    (C : Finset α) : Prop :=
  ∀ a ∈ C, ∀ b ∈ C, ∀ c ∈ C, a ≠ b → a ≠ c → b ≠ c →
      D.label a b ≠ D.label a c ∧
      D.label a b ≠ D.label b c ∧ D.label a c ≠ D.label b c

private theorem four_distinct_in_three_impossible (T : Finset α)
    (z x y w : α) (hTcard : T.card = 3)
    (hz : z ∈ T) (hx : x ∈ T) (hy : y ∈ T) (hw : w ∈ T)
    (hzx : z ≠ x) (hzy : z ≠ y) (hzw : z ≠ w)
    (hxy : x ≠ y) (hxw : x ≠ w) (hyw : y ≠ w) : False := by
  have hsub : ({z, x, y, w} : Finset α) ⊆ T := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact hz
    · exact hx
    · exact hy
    · exact hw
  have hcard : ({z, x, y, w} : Finset α).card = 4 := by
    simp [hzx, hzy, hzw, hxy, hxw, hyw]
  have := Finset.card_le_card hsub
  rw [hcard, hTcard] at this
  omega

/-- A colored completion facet has no monochromatic completion triangle.
If a triangle were monochromatic, the no-bicolored condition and the
three available facet labels force every label on the completion clique
to be constant. -/
theorem divergent_completion_facet_no_monochromatic_triangle
    (D : FiniteCompletionCliqueData α) (T : Edge α)
    (hTcard : T.card = 3) (hTsub : T ⊆ D.ground)
    (hDivergent : FacetHasDivergentLabels
      (graphFacetCompletions D.K D.ground T) D.label) :
    ∀ p ∈ graphFacetCompletions D.K D.ground T,
      ∀ q ∈ graphFacetCompletions D.K D.ground T,
      ∀ r ∈ graphFacetCompletions D.K D.ground T,
        p ≠ q → p ≠ r → q ≠ r →
          ¬ (D.label p q = D.label p r ∧ D.label p q = D.label q r) := by
  classical
  let C := graphFacetCompletions D.K D.ground T
  have hLabelMem : ∀ a ∈ C, ∀ b ∈ C, a ≠ b → D.label a b ∈ T := by
    intro a ha b hb hab
    exact completion_pair_label_mem_facet D T hTcard hTsub a b ha hb hab
  intro p hp q hq r hr hpq hpr hqr hMono
  let z := D.label p q
  have hpqz : D.label p q = z := rfl
  have hprz : D.label p r = z := hMono.1.symm.trans hpqz
  have hqrz : D.label q r = z := hMono.2.symm.trans hpqz
  have hzT : z ∈ T := hLabelMem p hp q hq hpq
  have hSpoke : ∀ d ∈ C, d ≠ p → D.label p d = z := by
    intro d hd hdp
    by_cases hdq : d = q
    · subst d
      exact hpqz
    by_cases hdr : d = r
    · subst d
      exact hprz
    have hpd : p ≠ d := hdp.symm
    have hqd : q ≠ d := by
      intro h
      exact hdq h.symm
    have hrd : r ≠ d := by
      intro h
      exact hdr h.symm
    let x := D.label p d
    let y := D.label q d
    let w := D.label r d
    have hxT : x ∈ T := hLabelMem p hp d hd hpd
    have hyT : y ∈ T := hLabelMem q hq d hd hqd
    have hwT : w ∈ T := hLabelMem r hr d hd hrd
    have hPqd := completion_triangle_mono_or_rainbow D T p q d hp hq hd
      hpq hpd hqd
    have hPrd := completion_triangle_mono_or_rainbow D T p r d hp hr hd
      hpr hpd hrd
    have hQrd := completion_triangle_mono_or_rainbow D T q r d hq hr hd
      hqr hqd hrd
    by_cases hxz : x = z
    · have hyz : y = z := by
        rcases hPqd with hmono | hrain
        · exact hmono.2.symm.trans hpqz
        · exact False.elim (hrain.1 (by simpa [x, z] using hxz.symm))
      have hwz : w = z := by
        rcases hPrd with hmono | hrain
        · exact hmono.2.symm.trans hprz
        · exact False.elim (hrain.1 (hprz.trans hxz.symm))
      exact hxz
    · have hyz : y ≠ z := by
        rcases hPqd with hmono | hrain
        · have hzx : z = x := by simpa [z, x] using hmono.1
          exact False.elim (hxz hzx.symm)
        · intro h
          exact hrain.2.1 (by simpa [y, z] using h.symm)
      have hxy : x ≠ y := by
        rcases hPqd with hmono | hrain
        · have hzx : z = x := by simpa [z, x] using hmono.1
          exact False.elim (hxz hzx.symm)
        · exact hrain.2.2
      have hwz : w ≠ z := by
        rcases hPrd with hmono | hrain
        · have hzx : z = x := hprz.symm.trans hmono.1
          exact False.elim (hxz hzx.symm)
        · intro h
          exact hrain.2.1 (hprz.trans h.symm)
      have hxw : x ≠ w := by
        rcases hPrd with hmono | hrain
        · have hzx : z = x := hprz.symm.trans hmono.1
          exact False.elim (hxz hzx.symm)
        · exact hrain.2.2
      have hyw : y = w := by
        by_contra hyw
        exact four_distinct_in_three_impossible T z x y w hTcard hzT hxT hyT hwT
          (by intro h; exact hxz h.symm) (by intro h; exact hyz h.symm)
          (by intro h; exact hwz h.symm) hxy hxw hyw
      rcases hQrd with hmono | hrain
      · have hzy : z = y := hqrz.symm.trans hmono.1
        exact False.elim (hyz hzy.symm)
      · exact False.elim (hrain.2.2 hyw)
  have hAll : ∀ a ∈ C, ∀ b ∈ C, a ≠ b → D.label a b = z := by
    intro a ha b hb hab
    by_cases hap : a = p
    · subst a
      exact hSpoke b hb (by intro h; exact hab h.symm)
    by_cases hbp : b = p
    · subst b
      rw [D.label_symm]
      exact hSpoke a ha hap
    have hpa := hSpoke a ha hap
    have hpb := hSpoke b hb hbp
    have hTri := completion_triangle_mono_or_rainbow D T p a b hp ha hb
      (by intro h; exact hap h.symm) (by intro h; exact hbp h.symm) hab
    rcases hTri with hmono | hrain
    · exact hmono.2.symm.trans hpa
    · exact False.elim (hrain.1 (hpa.trans hpb.symm))
  rcases hDivergent with ⟨a, ha, b, hb, c, hc, hab, hac, hbc, hDiff⟩
  exact hDiff ((hAll a ha b hb hab).trans (hAll a ha c hc hac).symm)

theorem canonical_triangle_mark_injective [Fintype α]
    (D : FiniteCompletionCliqueData α) (T : Edge α)
    (hcard : (graphFacetCompletions D.K D.ground T).card = 3)
    (hRainbow : CompletionTriangleRainbow D
      (graphFacetCompletions D.K D.ground T)) :
    Function.Injective (canonicalTriangleMark D T hcard) := by
  let v := canonicalTriangleCompletion D T hcard
  have hv := canonical_triangle_completion_injective D T hcard
  have hm := fun i => canonical_triangle_completion_mem D T hcard i
  have h01 := (hRainbow (v 0) (hm 0) (v 1) (hm 1) (v 2) (hm 2)
    (by intro h; have hh := hv h; norm_num at hh)
    (by intro h; have hh := hv h; norm_num at hh)
    (by intro h; have hh := hv h; norm_num at hh)).1
  have h02 := (hRainbow (v 0) (hm 0) (v 1) (hm 1) (v 2) (hm 2)
    (by intro h; have hh := hv h; norm_num at hh)
    (by intro h; have hh := hv h; norm_num at hh)
    (by intro h; have hh := hv h; norm_num at hh)).2.1
  have h12 := (hRainbow (v 0) (hm 0) (v 1) (hm 1) (v 2) (hm 2)
    (by intro h; have hh := hv h; norm_num at hh)
    (by intro h; have hh := hv h; norm_num at hh)
    (by intro h; have hh := hv h; norm_num at hh)).2.2
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [v, canonicalTriangleMark, canonicalTriangleCompletion,
      completionTriangleEnds, completionTriangleIndexPair]

theorem canonical_triangle_labels_are_marked [Fintype α]
    (D : FiniteCompletionCliqueData α) (T : Edge α)
    (hcard : (graphFacetCompletions D.K D.ground T).card = 3) :
    ∀ i : Fin 3,
      D.label
          (completionTriangleEnds (canonicalTriangleCompletion D T hcard) i).1
          (completionTriangleEnds (canonicalTriangleCompletion D T hcard) i).2 =
        (canonicalTriangleMark D T hcard)
          (rainbowTriangleEdgeColor (0 : CliqueColor) 1 2 i) := by
  intro i
  fin_cases i <;>
    simp [canonicalTriangleMark, canonicalTriangleCompletion,
      rainbowTriangleEdgeColor, completionTriangleEnds]

theorem canonical_triangle_mark_mem_facet [Fintype α]
    (D : FiniteCompletionCliqueData α) (T : Edge α)
    (hcard : (graphFacetCompletions D.K D.ground T).card = 3)
    (hTcard : T.card = 3) (hTsub : T ⊆ D.ground) :
    ∀ x : CliqueColor, canonicalTriangleMark D T hcard x ∈ T := by
  intro x
  fin_cases x
  all_goals
    unfold canonicalTriangleMark
    apply completion_pair_label_mem_facet D T hTcard hTsub
    · exact canonical_triangle_completion_mem D T hcard _
    · exact canonical_triangle_completion_mem D T hcard _
    · intro h
      exact (completion_triangle_ends_offdiag
        (canonicalTriangleCompletion D T hcard)
        (canonical_triangle_completion_injective D T hcard) _) h


theorem completion_facet_triangle_rainbow_of_no_mono
    (D : FiniteCompletionCliqueData α) (T : Edge α)
    (hNoMono : ∀ a ∈ graphFacetCompletions D.K D.ground T,
      ∀ b ∈ graphFacetCompletions D.K D.ground T,
      ∀ c ∈ graphFacetCompletions D.K D.ground T,
        a ≠ b → a ≠ c → b ≠ c →
          ¬ (D.label a b = D.label a c ∧ D.label a b = D.label b c)) :
    CompletionTriangleRainbow D (graphFacetCompletions D.K D.ground T) := by
  intro a ha b hb c hc hab hac hbc
  rcases completion_triangle_mono_or_rainbow D T a b c ha hb hc hab hac hbc with
    hmono | hrainbow
  · exact False.elim (hNoMono a ha b hb c hc hab hac hbc hmono)
  · exact hrainbow

def CompletionProperlyEdgeColored (D : FiniteCompletionCliqueData α)
    (C : Finset α) : Prop :=
  ∀ a ∈ C, ∀ b ∈ C, ∀ c ∈ C, a ≠ b → a ≠ c → b ≠ c →
    D.label a b ≠ D.label a c

def CompletionLabelsInFacet (D : FiniteCompletionCliqueData α)
    (T C : Finset α) : Prop :=
  ∀ a ∈ C, ∀ b ∈ C, a ≠ b → D.label a b ∈ T

theorem completion_labels_in_facet
    (D : FiniteCompletionCliqueData α) (T : Edge α)
    (hTcard : T.card = 3) (hTsub : T ⊆ D.ground) :
    CompletionLabelsInFacet D T (graphFacetCompletions D.K D.ground T) := by
  intro a ha b hb hab
  exact completion_pair_label_mem_facet D T hTcard hTsub a b ha hb hab

theorem completion_triangle_rainbow_implies_proper
    (D : FiniteCompletionCliqueData α) (C : Finset α)
    (hRainbow : CompletionTriangleRainbow D C) :
    CompletionProperlyEdgeColored D C := by
  intro a ha b hb c hc hab hac hbc
  exact (hRainbow a ha b hb c hc hab hac hbc).1

theorem colored_completion_facet_card_le_four
    (D : FiniteCompletionCliqueData α) (T : Edge α)
    (hTcard : T.card = 3) (hTsub : T ⊆ D.ground)
    (hRainbow : CompletionTriangleRainbow D
      (graphFacetCompletions D.K D.ground T)) :
    (graphFacetCompletions D.K D.ground T).card ≤ 4 := by
  classical
  let C := graphFacetCompletions D.K D.ground T
  by_cases hEmpty : C = ∅
  · simp [C, hEmpty]
  · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
    let N := C.erase x
    let f : {y // y ∈ N} → {z // z ∈ T} := fun y =>
      ⟨D.label x y.1, completion_pair_label_mem_facet D T hTcard hTsub
        x y.1 hx (by
          have hyC : y.1 ∈ C := (Finset.mem_erase.mp y.2).2
          exact hyC) (by
          intro h
          exact (Finset.mem_erase.mp y.2).1 h.symm)⟩
    have hf : Function.Injective f := by
      intro y z hyz
      apply Subtype.ext
      have hlabels : D.label x y.1 = D.label x z.1 := congrArg Subtype.val hyz
      by_contra hyz'
      have hyC : y.1 ∈ C := (Finset.mem_erase.mp y.2).2
      have hzC : z.1 ∈ C := (Finset.mem_erase.mp z.2).2
      have hxy : x ≠ y.1 := by
        intro h
        exact (Finset.mem_erase.mp y.2).1 h.symm
      have hxz : x ≠ z.1 := by
        intro h
        exact (Finset.mem_erase.mp z.2).1 h.symm
      have hyz'' : y.1 ≠ z.1 := by
        intro h
        exact hyz' h
      exact (hRainbow x hx y.1 hyC z.1 hzC hxy hxz hyz'').1 hlabels
    have hN : N.card ≤ T.card := by
      have hcard := Fintype.card_le_of_injective f hf
      simpa [N] using hcard
    have hC : C.card = N.card + 1 := by
      exact (Finset.card_erase_add_one (by simpa [N] using hx)).symm
    rw [hC]
    omega

theorem colored_completion_facet_classification
    (D : FiniteCompletionCliqueData α) (T : Edge α)
    (hTcard : T.card = 3) (hTsub : T ⊆ D.ground)
    (hNoMono : ∀ a ∈ graphFacetCompletions D.K D.ground T,
      ∀ b ∈ graphFacetCompletions D.K D.ground T,
      ∀ c ∈ graphFacetCompletions D.K D.ground T,
        a ≠ b → a ≠ c → b ≠ c →
          ¬ (D.label a b = D.label a c ∧ D.label a b = D.label b c))
    (hLarge : 3 ≤ (graphFacetCompletions D.K D.ground T).card) :
    let C := graphFacetCompletions D.K D.ground T
    (C.card = 3 ∧ CompletionTriangleRainbow D C) ∨
      (C.card = 4 ∧ CompletionProperlyEdgeColored D C ∧
        CompletionLabelsInFacet D T C) := by
  let C := graphFacetCompletions D.K D.ground T
  have hRainbow := completion_facet_triangle_rainbow_of_no_mono
    D T hNoMono
  have hle := colored_completion_facet_card_le_four D T hTcard hTsub hRainbow
  have hLabels := completion_labels_in_facet D T hTcard hTsub
  change 3 ≤ C.card at hLarge
  change C.card ≤ 4 at hle
  rcases hle.eq_or_lt with hEq | hLt
  · have h4 : C.card = 4 := hEq
    exact Or.inr ⟨h4, completion_triangle_rainbow_implies_proper D C hRainbow,
      hLabels⟩
  · have hThree : C.card = 3 := by omega
    exact Or.inl ⟨hThree, hRainbow⟩

theorem divergent_completion_facet_classification
    (D : FiniteCompletionCliqueData α) (T : Edge α)
    (hTcard : T.card = 3) (hTsub : T ⊆ D.ground)
    (hDivergent : FacetHasDivergentLabels
      (graphFacetCompletions D.K D.ground T) D.label)
    (hLarge : 3 ≤ (graphFacetCompletions D.K D.ground T).card) :
    let C := graphFacetCompletions D.K D.ground T
    (C.card = 3 ∧ CompletionTriangleRainbow D C) ∨
      (C.card = 4 ∧ CompletionProperlyEdgeColored D C ∧
        CompletionLabelsInFacet D T C) := by
  exact colored_completion_facet_classification D T hTcard hTsub
    (divergent_completion_facet_no_monochromatic_triangle
      D T hTcard hTsub hDivergent) hLarge

end JSP523.Rank4
