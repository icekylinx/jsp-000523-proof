import JSP523.Rank4.GraphCompletionClique
import JSP523.Rank4.CommonTripleCells
import JSP523.Rank4.GraphVertexDeficit
import JSP523.Rank4.GraphUniqueRecords
import JSP523.Rank4.PreprocessSmallCells

/-!
# Finite completion cliques and their pair records

The data below uses the actual finite rank-four family representation.
The local no-bicolored-triangle property is stated on completion vertices;
it is the cleaned `K` condition consumed by the finite clique
classification. Pair records remember the facet with its label vertex
removed and the two completion endpoints.
-/

namespace JSP523.Rank4

variable {α : Type*} [DecidableEq α]

/-- A finite ground vertex type has only finitely many facets. -/
noncomputable instance completionEdgeFintype [Fintype α] :
    Fintype (Edge α) :=
  Fintype.ofInjective (fun T : Edge α => fun x : α => decide (x ∈ T)) (by
    intro T U h
    apply Finset.ext
    intro x
    have hx := congrFun h x
    simpa using hx)

/-- Completions of a triple facet inside a chosen finite ground set. -/
def graphFacetCompletions (K : Family α) (V T : Edge α) : Finset α :=
  V.filter fun x => insert x T ∈ K

/-- The forbidden triangle pattern with exactly two equal edge labels. -/
def bicoloredTriangle (a b c : α) : Prop :=
  (a = b ∧ a ≠ c) ∨ (a = c ∧ a ≠ b) ∨ (b = c ∧ b ≠ a)

/-- A finite cleaned rank-four completion system: actual edges in `K`,
completion-pair labels, and the no-bicolored-triangle condition. -/
structure FiniteCompletionCliqueData (α : Type*) [DecidableEq α] where
  ground : Edge α
  K : Family α
  uniform_four : Uniform 4 K
  admissible : Admissible K
  label : α → α → α
  label_symm : ∀ x y, label x y = label y x
  label_center : ∀ x y, x ≠ y →
    ∀ P ∈ commonTripleCell K ground x y, label x y ∈ P
  no_bicolored_triangle : ∀ T : Edge α, ∀ x ∈ graphFacetCompletions K ground T,
    ∀ y ∈ graphFacetCompletions K ground T,
    ∀ z ∈ graphFacetCompletions K ground T,
      x ≠ y → x ≠ z → y ≠ z →
        ¬ bicoloredTriangle (label x y) (label x z) (label y z)

/-- The no-bicolored condition gives the monochromatic/rainbow
alternative for every actual completion triangle. -/
theorem completion_triangle_mono_or_rainbow
    (D : FiniteCompletionCliqueData α) (T : Edge α)
    (x y z : α) (hx : x ∈ graphFacetCompletions D.K D.ground T)
    (hy : y ∈ graphFacetCompletions D.K D.ground T)
    (hz : z ∈ graphFacetCompletions D.K D.ground T)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ((D.label x y = D.label x z ∧ D.label x y = D.label y z) ∨
      (D.label x y ≠ D.label x z ∧ D.label x y ≠ D.label y z ∧
        D.label x z ≠ D.label y z)) := by
  let a := D.label x y
  let b := D.label x z
  let c := D.label y z
  by_cases hab : a = b
  · by_cases hac : a = c
    · exact Or.inl ⟨hab, hac⟩
    · exact False.elim (D.no_bicolored_triangle T x hx y hy z hz
        hxy hxz hyz (Or.inl ⟨hab, hac⟩))
  · by_cases hac : a = c
    · exact False.elim (D.no_bicolored_triangle T x hx y hy z hz
        hxy hxz hyz (Or.inr (Or.inl ⟨hac, hab⟩)))
    · by_cases hbc : b = c
      · exact False.elim (D.no_bicolored_triangle T x hx y hy z hz
          hxy hxz hyz (Or.inr (Or.inr ⟨hbc, by
            intro h
            exact hab (by simpa [a, b, c] using h.symm)⟩)))
      · exact Or.inr ⟨hab, hac, hbc⟩

/-- On an actual triple facet inside the ground set, the center label of a
completion pair belongs to the facet itself. This follows by putting the
facet into the common triple cell and using uniformity to show the two
completion vertices are outside it. -/
theorem completion_pair_label_mem_facet
    (D : FiniteCompletionCliqueData α) (T : Edge α)
    (hTcard : T.card = 3) (hTsub : T ⊆ D.ground)
    (x y : α) (hx : x ∈ graphFacetCompletions D.K D.ground T)
    (hy : y ∈ graphFacetCompletions D.K D.ground T) (hxy : x ≠ y) :
    D.label x y ∈ T := by
  have hx' := Finset.mem_filter.mp hx
  have hy' := Finset.mem_filter.mp hy
  have hxNot : x ∉ T := by
    intro hmem
    have hEq : insert x T = T := Finset.insert_eq_of_mem hmem
    have hFour := D.uniform_four (by simpa [hEq] using hx'.2)
    omega
  have hyNot : y ∉ T := by
    intro hmem
    have hEq : insert y T = T := Finset.insert_eq_of_mem hmem
    have hFour := D.uniform_four (by simpa [hEq] using hy'.2)
    omega
  have hDisj : Disjoint T ({x, y} : Edge α) := by
    apply Finset.disjoint_left.mpr
    intro z hzT hzxy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hzxy
    rcases hzxy with rfl | rfl
    · exact hxNot hzT
    · exact hyNot hzT
  have hCell : T ∈ commonTripleCell D.K D.ground x y := by
    apply mem_common_triple_cell.mpr
    exact ⟨hTsub, hTcard, hDisj, hx'.2, hy'.2⟩
  exact D.label_center x y hxy T hCell

/-- A record indexed by a colored completion pair `(x,y)` of a facet `T`
is the pair `(T \ {label(x,y)}, (x,y))` used in (III.B.10). -/
def completionPairRecord {ι : Type*} (label : α → α → α)
    (facet : ι → Edge α) (ends : ι → α × α) (i : ι) :
    Edge α × (α × α) :=
  Prod.mk ((facet i).erase (label (ends i).1 (ends i).2)) (ends i)

/-- Distinct colored completion-pair occurrences give distinct `(Q,ab)` records.
The label determines the vertex deleted from the facet, so the record and
its pair endpoints reconstruct the original facet. -/
theorem completion_pair_record_injective
    {ι : Type*} [DecidableEq ι]
    (label : α → α → α) (facet : ι → Edge α)
    (ends : ι → α × α)
    (hLabelMem : ∀ i, label (ends i).1 (ends i).2 ∈ facet i)
    (hSource : ∀ i j, facet i = facet j → ends i = ends j → i = j) :
    Function.Injective (completionPairRecord label facet ends) := by
  intro i j hij
  have hEnds : ends i = ends j := congrArg Prod.snd hij
  have hErase : (facet i).erase (label (ends i).1 (ends i).2) =
      (facet j).erase (label (ends j).1 (ends j).2) := congrArg Prod.fst hij
  have hLabel : label (ends i).1 (ends i).2 =
      label (ends j).1 (ends j).2 := by rw [hEnds]
  rw [hLabel] at hErase
  have hFacet : facet i = facet j := by
    calc
      facet i = insert (label (ends i).1 (ends i).2)
          ((facet i).erase (label (ends i).1 (ends i).2)) :=
            (Finset.insert_erase (hLabelMem i)).symm
      _ = insert (label (ends j).1 (ends j).2)
          ((facet j).erase (label (ends j).1 (ends j).2)) := by rw [hLabel, hErase]
      _ = facet j := Finset.insert_erase (hLabelMem j)
  exact hSource i j hFacet hEnds

/-- Actual occurrences `(T,(x,y))` in a finite completion clique. The
facets are triples, and `x,y` are distinct completions whose pair label is
one of the three vertices of `T`. -/
def CompletionRecordIndex (D : FiniteCompletionCliqueData α) :=
  {p : Edge α × (α × α) //
    p.1.card = 3 ∧
    p.1 ⊆ D.ground ∧
    p.2.1 ∈ graphFacetCompletions D.K D.ground p.1 ∧
    p.2.2 ∈ graphFacetCompletions D.K D.ground p.1 ∧
    p.2.1 ≠ p.2.2}

noncomputable instance completionRecordIndexFintype
    (D : FiniteCompletionCliqueData α) [Fintype α] : Fintype (CompletionRecordIndex D) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

/-- Every actual completion-pair occurrence determines its `(Q,ab)` key. -/
def actualCompletionRecord (D : FiniteCompletionCliqueData α)
    (i : CompletionRecordIndex D) : Edge α × (α × α) :=
  (i.val.1.erase (D.label i.val.2.1 i.val.2.2), i.val.2)

/-- The concrete record map is injective: its pair component gives the
completion endpoints, whose label restores the deleted facet vertex. -/
theorem actual_completion_record_injective
    (D : FiniteCompletionCliqueData α) :
    Function.Injective (actualCompletionRecord D) := by
  intro i j hij
  change (i.val.1.erase (D.label i.val.2.1 i.val.2.2), i.val.2) =
      (j.val.1.erase (D.label j.val.2.1 j.val.2.2), j.val.2) at hij
  rcases Prod.mk.inj hij with ⟨hErase, hPair⟩
  have hLabel : D.label i.val.2.1 i.val.2.2 =
      D.label j.val.2.1 j.val.2.2 := by rw [hPair]
  have hLabelMemI : D.label i.val.2.1 i.val.2.2 ∈ i.val.1 :=
    completion_pair_label_mem_facet D i.val.1 i.property.1 i.property.2.1
      i.val.2.1 i.val.2.2 i.property.2.2.1 i.property.2.2.2.1
      i.property.2.2.2.2
  have hLabelMemJ : D.label j.val.2.1 j.val.2.2 ∈ j.val.1 :=
    completion_pair_label_mem_facet D j.val.1 j.property.1 j.property.2.1
      j.val.2.1 j.val.2.2 j.property.2.2.1 j.property.2.2.2.1
      j.property.2.2.2.2
  rw [hLabel] at hErase
  have hFacet : i.val.1 = j.val.1 := by
    calc
      i.val.1 = insert (D.label i.val.2.1 i.val.2.2)
          (i.val.1.erase (D.label i.val.2.1 i.val.2.2)) :=
            (Finset.insert_erase hLabelMemI).symm
      _ = insert (D.label j.val.2.1 j.val.2.2)
          (j.val.1.erase (D.label j.val.2.1 j.val.2.2)) := by rw [hLabel, hErase]
      _ = j.val.1 := Finset.insert_erase hLabelMemJ
  apply Subtype.ext
  apply Prod.ext hFacet
  exact hPair

/-- The three edges of a completion triangle, ordered `01, 02, 12`. -/
def completionTriangleEnds {α : Type*} (v : Fin 3 → α) (i : Fin 3) : α × α :=
  let p := completionTriangleIndexPair i
  (v p.1, v p.2)

/-- The six edges of a completion K4, in the order above. -/
def completionK4Ends {α : Type*} (v : Fin 4 → α) (i : Fin 6) : α × α :=
  let p := completionK4IndexPair i
  (v p.1, v p.2)

theorem completion_triangle_ends_injective {α : Type*} (v : Fin 3 → α)
    (hv : Function.Injective v) : Function.Injective (completionTriangleEnds v) := by
  intro i j hij
  apply completion_triangle_index_pair_injective
  apply Prod.ext
  · apply hv
    exact congrArg Prod.fst hij
  · apply hv
    exact congrArg Prod.snd hij

theorem completion_k4_ends_injective {α : Type*} (v : Fin 4 → α)
    (hv : Function.Injective v) : Function.Injective (completionK4Ends v) := by
  intro i j hij
  apply completion_k4_index_pair_injective
  apply Prod.ext
  · apply hv
    exact congrArg Prod.fst hij
  · apply hv
    exact congrArg Prod.snd hij

theorem completion_triangle_index_pair_offdiag (i : Fin 3) :
    (completionTriangleIndexPair i).1 ≠
      (completionTriangleIndexPair i).2 := by
  fin_cases i <;> norm_num [completionTriangleIndexPair]

theorem completion_k4_index_pair_offdiag (i : Fin 6) :
    (completionK4IndexPair i).1 ≠ (completionK4IndexPair i).2 := by
  fin_cases i <;> norm_num [completionK4IndexPair]

omit [DecidableEq α] in
theorem completion_triangle_ends_offdiag (v : Fin 3 → α)
    (hv : Function.Injective v) (i : Fin 3) :
    (completionTriangleEnds v i).1 ≠ (completionTriangleEnds v i).2 := by
  intro h
  exact completion_triangle_index_pair_offdiag i (hv h)

omit [DecidableEq α] in
theorem completion_k4_ends_offdiag (v : Fin 4 → α)
    (hv : Function.Injective v) (i : Fin 6) :
    (completionK4Ends v i).1 ≠ (completionK4Ends v i).2 := by
  intro h
  exact completion_k4_index_pair_offdiag i (hv h)

theorem pair_finset_eq_oriented_eq
    {a b x y : α} (hxy : x ≠ y)
    (h : ({a, b} : Edge α) = {x, y}) :
    (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by
  have hx : x = a ∨ x = b := by
    have hx' : x ∈ ({a, b} : Edge α) := by rw [h]; simp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hx'
  have hy : y = a ∨ y = b := by
    have hy' : y ∈ ({a, b} : Edge α) := by rw [h]; simp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hy'
  rcases hx with hxa | hxb <;> rcases hy with hya | hyb
  · exact False.elim (hxy (hxa.trans hya.symm))
  · exact Or.inl ⟨hxa, hyb⟩
  · exact Or.inr ⟨hxb, hya⟩
  · exact False.elim (hxy (hxb.trans hyb.symm))

/-- A triangle edge occurrence is an actual completion-pair index when
its three vertices really complete the base triple. -/
def completionTriangleActualIndex (D : FiniteCompletionCliqueData α)
    (T : Edge α) (v : Fin 3 → α) (i : Fin 3)
    (hTcard : T.card = 3) (hTsub : T ⊆ D.ground)
    (hCompletion : ∀ j, v j ∈ graphFacetCompletions D.K D.ground T)
    (hv : Function.Injective v) : CompletionRecordIndex D :=
  ⟨(T, completionTriangleEnds v i), hTcard, hTsub,
    hCompletion (completionTriangleIndexPair i).1,
    hCompletion (completionTriangleIndexPair i).2,
    completion_triangle_ends_offdiag v hv i⟩

/-- A proper-K4 edge occurrence is an actual completion-pair index under
the corresponding four completion hypotheses. -/
def completionK4ActualIndex (D : FiniteCompletionCliqueData α)
    (T : Edge α) (v : Fin 4 → α) (i : Fin 6)
    (hTcard : T.card = 3) (hTsub : T ⊆ D.ground)
    (hCompletion : ∀ j, v j ∈ graphFacetCompletions D.K D.ground T)
    (hv : Function.Injective v) : CompletionRecordIndex D :=
  ⟨(T, completionK4Ends v i), hTcard, hTsub,
    hCompletion (completionK4IndexPair i).1,
    hCompletion (completionK4IndexPair i).2,
    completion_k4_ends_offdiag v hv i⟩

/-- Actual `(Q,ab)` record keys for the three edge occurrences of a
completion triangle. -/
def completionTriangleRecordKeys (D : FiniteCompletionCliqueData α)
    (T : Edge α) (v : Fin 3 → α) (i : Fin 3) : Edge α × (α × α) :=
  completionPairRecord D.label (fun _ : Fin 3 => T) (completionTriangleEnds v) i

/-- Actual `(Q,ab)` record keys for the six edge occurrences of a
completion K4. -/
def completionK4RecordKeys (D : FiniteCompletionCliqueData α)
    (T : Edge α) (v : Fin 4 → α) (i : Fin 6) : Edge α × (α × α) :=
  completionPairRecord D.label (fun _ : Fin 6 => T) (completionK4Ends v) i

@[simp] theorem actual_triangle_index_record_key
    (D : FiniteCompletionCliqueData α) (T : Edge α) (v : Fin 3 → α)
    (i : Fin 3) (hTcard : T.card = 3) (hTsub : T ⊆ D.ground)
    (hCompletion : ∀ j, v j ∈ graphFacetCompletions D.K D.ground T)
    (hv : Function.Injective v) :
    actualCompletionRecord D
      (completionTriangleActualIndex D T v i hTcard hTsub hCompletion hv) =
      completionTriangleRecordKeys D T v i := by
  rfl

@[simp] theorem actual_K4_index_record_key
    (D : FiniteCompletionCliqueData α) (T : Edge α) (v : Fin 4 → α)
    (i : Fin 6) (hTcard : T.card = 3) (hTsub : T ⊆ D.ground)
    (hCompletion : ∀ j, v j ∈ graphFacetCompletions D.K D.ground T)
    (hv : Function.Injective v) :
    actualCompletionRecord D
      (completionK4ActualIndex D T v i hTcard hTsub hCompletion hv) =
      completionK4RecordKeys D T v i := by
  rfl

theorem completion_triangle_record_keys_injective
    (D : FiniteCompletionCliqueData α) (T : Edge α) (v : Fin 3 → α)
    (hv : Function.Injective v)
    (hLabelMem : ∀ i, D.label (completionTriangleEnds v i).1
      (completionTriangleEnds v i).2 ∈ T) :
    Function.Injective (completionTriangleRecordKeys D T v) := by
  apply completion_pair_record_injective D.label (fun _ : Fin 3 => T)
    (completionTriangleEnds v)
  · exact hLabelMem
  · intro i j _ hEnds
    exact completion_triangle_ends_injective v hv hEnds

theorem completion_k4_record_keys_injective
    (D : FiniteCompletionCliqueData α) (T : Edge α) (v : Fin 4 → α)
    (hv : Function.Injective v)
    (hLabelMem : ∀ i, D.label (completionK4Ends v i).1
      (completionK4Ends v i).2 ∈ T) :
    Function.Injective (completionK4RecordKeys D T v) := by
  apply completion_pair_record_injective D.label (fun _ : Fin 6 => T)
    (completionK4Ends v)
  · exact hLabelMem
  · intro i j _ hEnds
    exact completion_k4_ends_injective v hv hEnds

/-- The concrete `(Q,ab)` keys in one color class of an actual completion
triangle. The colors are read from `D.label`; the key uses the actual label
to erase the facet vertex. -/
def actualTriangleColorSlotRecords (D : FiniteCompletionCliqueData α)
    (T : Edge α) (v : Fin 3 → α) (mark : CliqueColor → α)
    (x : CliqueColor) : Finset (Edge α × (α × α)) :=
  coloredSlotRecordImage
    (Finset.univ.filter fun i : Fin 3 =>
      D.label (completionTriangleEnds v i).1 (completionTriangleEnds v i).2 = mark x)
    (completionTriangleRecordKeys D T v)

/-- The actual unique-pair records of each color in a rainbow triangle have
cardinality one. -/
theorem actual_triangle_color_slot_records_card
    (D : FiniteCompletionCliqueData α) (T : Edge α) (v : Fin 3 → α)
    (mark : CliqueColor → α) (a b c x : CliqueColor)
    (hv : Function.Injective v) (hmark : Function.Injective mark)
    (hLabelMem : ∀ i, D.label (completionTriangleEnds v i).1
      (completionTriangleEnds v i).2 ∈ T)
    (hColor : ∀ i, D.label (completionTriangleEnds v i).1
      (completionTriangleEnds v i).2 = mark (rainbowTriangleEdgeColor a b c i))
    (hRainbow : a ≠ b ∧ a ≠ c ∧ b ≠ c) :
    (actualTriangleColorSlotRecords D T v mark x).card = 1 := by
  have hKeys := completion_triangle_record_keys_injective D T v hv hLabelMem
  have hSlots :
      (Finset.univ.filter fun i : Fin 3 =>
        D.label (completionTriangleEnds v i).1 (completionTriangleEnds v i).2 = mark x) =
      rainbowTriangleColorRecords a b c x := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      rainbowTriangleColorRecords]
    constructor
    · intro hi
      exact hmark ((hColor i).symm.trans hi)
    · intro hi
      rw [hColor i, hi]
  unfold actualTriangleColorSlotRecords
  rw [colored_slot_record_image_card]
  · rw [hSlots, rainbow_triangle_color_records_card a b c hRainbow x]
  · exact hKeys

theorem actual_triangle_color_slots_disjoint
    (D : FiniteCompletionCliqueData α) (T : Edge α) (v : Fin 3 → α)
    (mark : CliqueColor → α) {x y : CliqueColor} (hxy : x ≠ y)
    (hv : Function.Injective v) (hmark : Function.Injective mark)
    (hLabelMem : ∀ i, D.label (completionTriangleEnds v i).1
      (completionTriangleEnds v i).2 ∈ T) :
    Disjoint (actualTriangleColorSlotRecords D T v mark x)
      (actualTriangleColorSlotRecords D T v mark y) := by
  have hKeys := completion_triangle_record_keys_injective D T v hv hLabelMem
  apply colored_slot_record_image_disjoint _ _ _ hKeys
  apply Finset.disjoint_left.mpr
  intro i hi hj
  have hix := (Finset.mem_filter.mp hi).2
  have hiy := (Finset.mem_filter.mp hj).2
  exact hxy (hmark (hix.symm.trans hiy))

/-- Actual rainbow records that survive because both completion endpoints
are selected. -/
def selectedActualTriangleColorSlotRecords (D : FiniteCompletionCliqueData α)
    (T : Edge α) (v : Fin 3 → α) (mark : CliqueColor → α)
    (x : CliqueColor) (S : Finset (Fin 3)) : Finset (Edge α × (α × α)) :=
  coloredSlotRecordImage
    (Finset.univ.filter fun i : Fin 3 =>
      D.label (completionTriangleEnds v i).1 (completionTriangleEnds v i).2 = mark x ∧
      (completionTriangleIndexPair i).1 ∈ S ∧ (completionTriangleIndexPair i).2 ∈ S)
    (completionTriangleRecordKeys D T v)

theorem selected_actual_triangle_color_slot_records_card_lower_bound
    (D : FiniteCompletionCliqueData α) (T : Edge α) (v : Fin 3 → α)
    (mark : CliqueColor → α) (a b c x : CliqueColor) (S : Finset (Fin 3))
    (hv : Function.Injective v) (hmark : Function.Injective mark)
    (hLabelMem : ∀ i, D.label (completionTriangleEnds v i).1
      (completionTriangleEnds v i).2 ∈ T)
    (hColor : ∀ i, D.label (completionTriangleEnds v i).1
      (completionTriangleEnds v i).2 = mark (rainbowTriangleEdgeColor a b c i))
    (hRainbow : a ≠ b ∧ a ≠ c ∧ b ≠ c) :
    1 - (if S.card < 3 then 1 else 0) ≤
      (selectedActualTriangleColorSlotRecords D T v mark x S).card := by
  have hKeys := completion_triangle_record_keys_injective D T v hv hLabelMem
  have hSlots :
      (Finset.univ.filter fun i : Fin 3 =>
        D.label (completionTriangleEnds v i).1 (completionTriangleEnds v i).2 = mark x ∧
        (completionTriangleIndexPair i).1 ∈ S ∧
        (completionTriangleIndexPair i).2 ∈ S) =
      selectedRainbowColorRecords a b c x S := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      selectedRainbowColorRecords, rainbowTriangleColorRecords]
    constructor
    · rintro ⟨hi, hleft, hright⟩
      exact ⟨hmark ((hColor i).symm.trans hi), hleft, hright⟩
    · rintro ⟨hi, hleft, hright⟩
      exact ⟨(hColor i).trans (congrArg mark hi), hleft, hright⟩
  unfold selectedActualTriangleColorSlotRecords
  rw [colored_slot_record_image_card]
  · rw [hSlots]
    exact selected_rainbow_records_lower_bound a b c hRainbow S x
  · exact hKeys

/-- The concrete `(Q,ab)` keys in one color class of an actual completion
K4. -/
def actualK4ColorSlotRecords (D : FiniteCompletionCliqueData α)
    (T : Edge α) (v : Fin 4 → α) (mark : CliqueColor → α)
    (x : CliqueColor) : Finset (Edge α × (α × α)) :=
  coloredSlotRecordImage
    (Finset.univ.filter fun i : Fin 6 =>
      D.label (completionK4Ends v i).1 (completionK4Ends v i).2 = mark x)
    (completionK4RecordKeys D T v)

/-- Each color in a proper completion K4 gives two distinct actual
unique-pair records. -/
theorem actual_k4_color_slot_records_card
    (D : FiniteCompletionCliqueData α) (T : Edge α) (v : Fin 4 → α)
    (mark : CliqueColor → α) (a b c x : CliqueColor)
    (hv : Function.Injective v) (hmark : Function.Injective mark)
    (hLabelMem : ∀ i, D.label (completionK4Ends v i).1
      (completionK4Ends v i).2 ∈ T)
    (hColor : ∀ i, D.label (completionK4Ends v i).1
      (completionK4Ends v i).2 = mark (properK4EdgeColor a b c i))
    (hProper : a ≠ b ∧ a ≠ c ∧ b ≠ c) :
    (actualK4ColorSlotRecords D T v mark x).card = 2 := by
  have hKeys := completion_k4_record_keys_injective D T v hv hLabelMem
  have hSlots :
      (Finset.univ.filter fun i : Fin 6 =>
        D.label (completionK4Ends v i).1 (completionK4Ends v i).2 = mark x) =
      properK4ColorRecords a b c x := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      properK4ColorRecords]
    constructor
    · intro hi
      exact hmark ((hColor i).symm.trans hi)
    · intro hi
      rw [hColor i, hi]
  unfold actualK4ColorSlotRecords
  rw [colored_slot_record_image_card]
  · rw [hSlots, proper_k4_color_records_card a b c hProper x]
  · exact hKeys

theorem actual_k4_color_slots_disjoint
    (D : FiniteCompletionCliqueData α) (T : Edge α) (v : Fin 4 → α)
    (mark : CliqueColor → α) {x y : CliqueColor} (hxy : x ≠ y)
    (hv : Function.Injective v) (hmark : Function.Injective mark)
    (hLabelMem : ∀ i, D.label (completionK4Ends v i).1
      (completionK4Ends v i).2 ∈ T) :
    Disjoint (actualK4ColorSlotRecords D T v mark x)
      (actualK4ColorSlotRecords D T v mark y) := by
  have hKeys := completion_k4_record_keys_injective D T v hv hLabelMem
  apply colored_slot_record_image_disjoint _ _ _ hKeys
  apply Finset.disjoint_left.mpr
  intro i hi hj
  have hix := (Finset.mem_filter.mp hi).2
  have hiy := (Finset.mem_filter.mp hj).2
  exact hxy (hmark (hix.symm.trans hiy))

/-- Actual proper-K4 records that survive because both completion endpoints
are selected. -/
def selectedActualK4ColorSlotRecords (D : FiniteCompletionCliqueData α)
    (T : Edge α) (v : Fin 4 → α) (mark : CliqueColor → α)
    (x : CliqueColor) (S : Finset (Fin 4)) : Finset (Edge α × (α × α)) :=
  coloredSlotRecordImage
    (Finset.univ.filter fun i : Fin 6 =>
      D.label (completionK4Ends v i).1 (completionK4Ends v i).2 = mark x ∧
      (completionK4IndexPair i).1 ∈ S ∧ (completionK4IndexPair i).2 ∈ S)
    (completionK4RecordKeys D T v)

theorem selected_actual_k4_color_slot_records_card_lower_bound
    (D : FiniteCompletionCliqueData α) (T : Edge α) (v : Fin 4 → α)
    (mark : CliqueColor → α) (a b c x : CliqueColor) (S : Finset (Fin 4))
    (hv : Function.Injective v) (hmark : Function.Injective mark)
    (hLabelMem : ∀ i, D.label (completionK4Ends v i).1
      (completionK4Ends v i).2 ∈ T)
    (hColor : ∀ i, D.label (completionK4Ends v i).1 (completionK4Ends v i).2 =
      mark (properK4EdgeColor a b c i))
    (hProper : a ≠ b ∧ a ≠ c ∧ b ≠ c) :
    2 - min 2 (4 - S.card) ≤
      (selectedActualK4ColorSlotRecords D T v mark x S).card := by
  have hKeys := completion_k4_record_keys_injective D T v hv hLabelMem
  have hSlots :
      (Finset.univ.filter fun i : Fin 6 =>
        D.label (completionK4Ends v i).1 (completionK4Ends v i).2 = mark x ∧
        (completionK4IndexPair i).1 ∈ S ∧
        (completionK4IndexPair i).2 ∈ S) =
      selectedProperK4ColorRecords a b c x S := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      selectedProperK4ColorRecords, properK4ColorRecords]
    constructor
    · rintro ⟨hi, hleft, hright⟩
      exact ⟨hmark ((hColor i).symm.trans hi), hleft, hright⟩
    · rintro ⟨hi, hleft, hright⟩
      exact ⟨(hColor i).trans (congrArg mark hi), hleft, hright⟩
  unfold selectedActualK4ColorSlotRecords
  rw [colored_slot_record_image_card]
  · rw [hSlots]
    exact selected_proper_k4_records_lower_bound a b c hProper S x
  · exact hKeys

/-- The pair link on a pair `Q`: an edge `ab` represents the four-edge
`Q ∪ {a,b}`. Vertices outside the pair and ground set are excluded. -/
def completionPairLinkGraph (D : FiniteCompletionCliqueData α)
    (Q : Edge α) : SimpleGraph α where
  Adj a b := a ∉ Q ∧ b ∉ Q ∧ a ∈ D.ground ∧ b ∈ D.ground ∧
    a ≠ b ∧ insert a (insert b Q) ∈ D.K
  symm := {
    symm := by
      intro a b h
      rcases h with ⟨haQ, hbQ, haV, hbV, hab, hE⟩
      exact ⟨hbQ, haQ, hbV, haV, hab.symm, by
        simpa [Finset.insert_comm] using hE⟩ }
  loopless := {
    irrefl := by
      intro a h
      exact h.2.2.2.2.1 rfl }

/-- The actual center-label property makes a labeled completion pair have
exactly one common neighbor in its pair-link graph. Any second common
neighbor would give a second tail in `J_ab` omitting the label. -/
theorem completion_pair_link_unique_common_neighbor
    (D : FiniteCompletionCliqueData α) [Fintype α]
    (Q : Edge α) (z a b : α)
    (hQcard : Q.card = 2) (hQground : Q ⊆ D.ground)
    (hzQ : z ∉ Q) (haQ : a ∉ Q)
    (haNeB : a ≠ b) (hLabel : D.label a b = z)
    [DecidableRel (completionPairLinkGraph D Q).Adj]
    (hza : (completionPairLinkGraph D Q).Adj z a)
    (hzb : (completionPairLinkGraph D Q).Adj z b) :
    graphCommonMultiplicity (completionPairLinkGraph D Q) a b = 1 := by
  classical
  let F := completionPairLinkGraph D Q
  have hzA : z ∈ F.neighborFinset a := by
    simpa [SimpleGraph.mem_neighborFinset] using hza.symm
  have hzB : F.Adj b z := hzb.symm
  have hFilter : (F.neighborFinset a).filter (fun w => F.Adj b w) = {z} := by
    ext w
    constructor
    · intro hw
      rw [Finset.mem_filter] at hw
      have hwa := hw.1
      have hbw := hw.2
      have haw : F.Adj a w := by
        simpa [SimpleGraph.mem_neighborFinset] using hwa
      rcases haw with ⟨haQ', hwQ, haGround, hwGround, hawne, hEdgeA⟩
      rcases hbw with ⟨hbQ, hwQ', hbGround, hwGround', hbwne, hEdgeB⟩
      have hTailCard : (insert w Q).card = 3 := by
        rw [Finset.card_insert_of_notMem hwQ, hQcard]
      have hTailGround : insert w Q ⊆ D.ground := by
        intro t ht
        rcases Finset.mem_insert.mp ht with rfl | htQ
        · exact hwGround
        · exact hQground htQ
      have hTailDisj : Disjoint (insert w Q) ({a, b} : Edge α) := by
        apply Finset.disjoint_left.mpr
        intro t ht htab
        rcases Finset.mem_insert.mp ht with rfl | htQ
        · simp only [Finset.mem_insert, Finset.mem_singleton] at htab
          rcases htab with h | h
          · exact hawne h.symm
          · exact hbwne h.symm
        · simp only [Finset.mem_insert, Finset.mem_singleton] at htab
          rcases htab with h | h
          · exact haQ (h ▸ htQ)
          · exact hbQ (h ▸ htQ)
      have hCell : insert w Q ∈ commonTripleCell D.K D.ground a b := by
        apply mem_common_triple_cell.mpr
        refine ⟨hTailGround, hTailCard, hTailDisj, ?_, ?_⟩
        · exact hEdgeA
        · exact hEdgeB
      have hzTail := D.label_center a b haNeB (insert w Q) hCell
      rw [hLabel] at hzTail
      have hzEq : z = w := by
        have : z ∈ insert w Q := hzTail
        simp only [Finset.mem_insert] at this
        rcases this with rfl | hzQ'
        · rfl
        · exact (hzQ hzQ').elim
      simp [hzEq]
    · intro hw
      have hwz : w = z := Finset.mem_singleton.mp hw
      subst w
      exact Finset.mem_filter.mpr ⟨hzA, hzB⟩
  unfold graphCommonMultiplicity
  have hCard := congrArg Finset.card hFilter
  simpa [F] using hCard

/-- Each actual `(T,(a,b))` completion occurrence yields the labeled common
neighbor in the link at `Q=T\{label(a,b)}`. -/
theorem actual_completion_record_has_unique_link_neighbor
    (D : FiniteCompletionCliqueData α) [Fintype α]
    (i : CompletionRecordIndex D)
    [DecidableRel (completionPairLinkGraph D
      (i.val.1.erase (D.label i.val.2.1 i.val.2.2))).Adj] :
    graphCommonMultiplicity
      (completionPairLinkGraph D (i.val.1.erase (D.label i.val.2.1 i.val.2.2)))
      i.val.2.1 i.val.2.2 = 1 ∧
    (completionPairLinkGraph D
      (i.val.1.erase (D.label i.val.2.1 i.val.2.2))).Adj
      (D.label i.val.2.1 i.val.2.2) i.val.2.1 ∧
    (completionPairLinkGraph D
      (i.val.1.erase (D.label i.val.2.1 i.val.2.2))).Adj
      (D.label i.val.2.1 i.val.2.2) i.val.2.2 := by
  classical
  let T := i.val.1
  let a := i.val.2.1
  let b := i.val.2.2
  let z := D.label a b
  let Q := T.erase z
  have hTcard : T.card = 3 := i.property.1
  have hzT : z ∈ T := completion_pair_label_mem_facet D T i.property.1
    i.property.2.1 a b i.property.2.2.1 i.property.2.2.2.1
    i.property.2.2.2.2
  have hzQ : z ∉ Q := Finset.notMem_erase z T
  have hTdecomp : T = insert z Q := by
    dsimp [Q]
    exact (Finset.insert_erase hzT).symm
  have hQcard : Q.card = 2 := by
    dsimp [Q]
    rw [Finset.card_erase_of_mem hzT]
    omega
  have hQground : Q ⊆ D.ground := by
    intro w hw
    exact i.property.2.1 (Finset.mem_of_mem_erase hw)
  have haT : a ∉ T := by
    intro ha
    have hFour := D.uniform_four (by
      exact (Finset.mem_filter.mp i.property.2.2.1).2)
    change (insert a T).card = 4 at hFour
    have hcard : (insert a T).card = T.card := by
      simp [Finset.insert_eq_of_mem ha]
    have hFour' : T.card = 4 := by simpa [Finset.insert_eq_of_mem ha] using hFour
    omega
  have hbT : b ∉ T := by
    intro hb
    have hFour := D.uniform_four (by
      exact (Finset.mem_filter.mp i.property.2.2.2.1).2)
    change (insert b T).card = 4 at hFour
    have hcard : (insert b T).card = T.card := by
      simp [Finset.insert_eq_of_mem hb]
    have hFour' : T.card = 4 := by simpa [Finset.insert_eq_of_mem hb] using hFour
    omega
  have haQ : a ∉ Q := fun ha => haT (Finset.mem_of_mem_erase ha)
  have hbQ : b ∉ Q := fun hb => hbT (Finset.mem_of_mem_erase hb)
  have hzGround : z ∈ D.ground := i.property.2.1 hzT
  have haGround := (Finset.mem_filter.mp i.property.2.2.1).1
  have hbGround := (Finset.mem_filter.mp i.property.2.2.2.1).1
  have haz : a ≠ z := fun h => haT (h ▸ hzT)
  have hbz : b ≠ z := fun h => hbT (h ▸ hzT)
  have hza : (completionPairLinkGraph D Q).Adj z a := by
    change z ∉ Q ∧ a ∉ Q ∧ z ∈ D.ground ∧ a ∈ D.ground ∧
      z ≠ a ∧ insert z (insert a Q) ∈ D.K
    refine ⟨hzQ, haQ, hzGround, haGround, haz.symm, ?_⟩
    have hEdge := (Finset.mem_filter.mp i.property.2.2.1).2
    change insert a T ∈ D.K at hEdge
    rw [hTdecomp] at hEdge
    simpa [Finset.insert_comm] using hEdge
  have hzb : (completionPairLinkGraph D Q).Adj z b := by
    change z ∉ Q ∧ b ∉ Q ∧ z ∈ D.ground ∧ b ∈ D.ground ∧
      z ≠ b ∧ insert z (insert b Q) ∈ D.K
    refine ⟨hzQ, hbQ, hzGround, hbGround, hbz.symm, ?_⟩
    have hEdge := (Finset.mem_filter.mp i.property.2.2.2.1).2
    change insert b T ∈ D.K at hEdge
    rw [hTdecomp] at hEdge
    simpa [Finset.insert_comm] using hEdge
  have hUnique := completion_pair_link_unique_common_neighbor D Q z a b
    hQcard hQground hzQ haQ i.property.2.2.2.2
    (by rfl) hza hzb
  exact ⟨hUnique, hza, hzb⟩

/-- Restricting a graph to a selected vertex set preserves a common pair's
unique common neighbor whenever all three vertices are selected. -/
def selectedPairLinkGraph {α : Type*} (F : SimpleGraph α)
    (S : Finset α) : SimpleGraph α where
  Adj a b := F.Adj a b ∧ a ∈ S ∧ b ∈ S
  symm := {
    symm := by
      intro a b h
      rcases h with ⟨hab, ha, hb⟩
      exact ⟨hab.symm, hb, ha⟩ }
  loopless := {
    irrefl := by
      intro a h
      exact F.loopless.irrefl a h.1 }

theorem selected_link_preserves_unique_common_neighbor
    {α : Type*} [Fintype α] [DecidableEq α]
    (F : SimpleGraph α) [DecidableRel F.Adj]
    (S : Finset α) (a b z : α)
    [DecidableRel (selectedPairLinkGraph F S).Adj]
    (hUnique : graphCommonMultiplicity F a b = 1)
    (hza : F.Adj z a) (hzb : F.Adj z b)
    (ha : a ∈ S) (hb : b ∈ S) (hz : z ∈ S) :
    graphCommonMultiplicity (selectedPairLinkGraph F S) a b = 1 := by
  classical
  let F' := selectedPairLinkGraph F S
  let base := (F.neighborFinset a).filter fun w => F.Adj b w
  have hBaseCard : base.card = 1 := by
    simpa [base, graphCommonMultiplicity] using hUnique
  obtain ⟨w, hBase⟩ := Finset.card_eq_one.mp hBaseCard
  have hzBase : z ∈ base := by
    simp only [base, Finset.mem_filter]
    exact ⟨by simpa [SimpleGraph.mem_neighborFinset] using hza.symm, hzb.symm⟩
  have hwz : w = z := by
    rw [hBase] at hzBase
    exact (Finset.mem_singleton.mp hzBase).symm
  have hSelected :
      (F'.neighborFinset a).filter (fun x => F'.Adj b x) = {z} := by
    ext x
    rw [Finset.mem_filter]
    constructor
    · rintro ⟨hxa, hbx⟩
      have hxaAdj : F'.Adj a x := by
        simpa [SimpleGraph.mem_neighborFinset] using hxa
      have hxa' : F.Adj a x := hxaAdj.1
      have hbx' : F.Adj b x := hbx.1
      have hxBase : x ∈ base := by
        simp [base, SimpleGraph.mem_neighborFinset, hxa', hbx']
      have hxw : x = w := by
        rw [hBase] at hxBase
        simpa using hxBase
      simp [hxw, hwz]
    · intro hx
      have hxz : x = z := Finset.mem_singleton.mp hx
      subst x
      have hAdjAz : F'.Adj a z := ⟨hza.symm, ha, hz⟩
      have hAdjBz : F'.Adj b z := ⟨hzb.symm, hb, hz⟩
      have hzN : z ∈ F'.neighborFinset a := by
        simpa [SimpleGraph.mem_neighborFinset] using hAdjAz
      exact ⟨hzN, hAdjBz⟩
  change ((F'.neighborFinset a).filter (fun x => F'.Adj b x)).card = 1
  rw [hSelected]
  simp

/-- An actual completion record remains a unique-pair record after the
selected-link restriction whenever its labeled center and both endpoints
survive the slot selection. -/
theorem actual_selected_completion_record_unique
    (D : FiniteCompletionCliqueData α) [Fintype α]
    (i : CompletionRecordIndex D)
    [DecidableRel (completionPairLinkGraph D
      (i.val.1.erase (D.label i.val.2.1 i.val.2.2))).Adj]
    (S : Finset α)
    [DecidableRel (selectedPairLinkGraph
      (completionPairLinkGraph D
        (i.val.1.erase (D.label i.val.2.1 i.val.2.2))) S).Adj]
    (hLeft : i.val.2.1 ∈ S) (hRight : i.val.2.2 ∈ S)
    (hLabel : D.label i.val.2.1 i.val.2.2 ∈ S) :
    graphCommonMultiplicity
      (selectedPairLinkGraph
        (completionPairLinkGraph D
          (i.val.1.erase (D.label i.val.2.1 i.val.2.2))) S)
      i.val.2.1 i.val.2.2 = 1 := by
  have hData := actual_completion_record_has_unique_link_neighbor D i
  exact selected_link_preserves_unique_common_neighbor
    (completionPairLinkGraph D
      (i.val.1.erase (D.label i.val.2.1 i.val.2.2))) S
    i.val.2.1 i.val.2.2 (D.label i.val.2.1 i.val.2.2)
    hData.1 hData.2.1 hData.2.2 hLeft hRight hLabel

/-- Actual completion records whose two endpoints and label center survive
selection. The index retains orientation so it can be injected directly
into the directed unique-pair family of selected pair-link graphs. -/
def SelectedCompletionRecordIndex (D : FiniteCompletionCliqueData α)
    (S : Finset α) :=
  {i : CompletionRecordIndex D //
    i.val.2.1 ∈ S ∧ i.val.2.2 ∈ S ∧
      D.label i.val.2.1 i.val.2.2 ∈ S}

noncomputable instance selectedCompletionRecordIndexFintype
    (D : FiniteCompletionCliqueData α) [Fintype α] (S : Finset α) :
    Fintype (SelectedCompletionRecordIndex D S) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

/-- The global set of actual directed `(Q,ab)` keys surviving selection. -/
noncomputable def selectedActualCompletionRecordKeys (D : FiniteCompletionCliqueData α)
    [Fintype α] (S : Finset α) : Finset (Edge α × (α × α)) :=
  Finset.univ.image fun i : SelectedCompletionRecordIndex D S =>
    actualCompletionRecord D i.val

/-- Forget orientation in the globally selected completion-record keys. -/
noncomputable def selectedUndirectedCompletionRecordKeys
    (D : FiniteCompletionCliqueData α) [Fintype α] (S : Finset α) :
    Finset (Edge α × Edge α) :=
  (selectedActualCompletionRecordKeys D S).image fun p =>
    (p.1, ({p.2.1, p.2.2} : Edge α))

def SelectedUndirectedCompletionRecordIndex
    (D : FiniteCompletionCliqueData α) [Fintype α] (S : Finset α) :=
  {p : Edge α × Edge α //
    p ∈ selectedUndirectedCompletionRecordKeys D S}

noncomputable instance selectedUndirectedCompletionRecordIndexFintype
    (D : FiniteCompletionCliqueData α) [Fintype α] (S : Finset α) :
    Fintype (SelectedUndirectedCompletionRecordIndex D S) :=
  Fintype.ofFinset (selectedUndirectedCompletionRecordKeys D S) (fun _ => Iff.rfl)

/-- The actual selected pair-link at a base pair `Q`. -/
def selectedCompletionPairGraph (D : FiniteCompletionCliqueData α)
    (S : Finset α) (Q : Edge α) : SimpleGraph α :=
  selectedPairLinkGraph (completionPairLinkGraph D Q) S

theorem selected_undirected_record_pair_card
    (D : FiniteCompletionCliqueData α) [Fintype α] (S : Finset α)
    (r : SelectedUndirectedCompletionRecordIndex D S) :
    r.val.2.card = 2 := by
  obtain ⟨q, hq, hrq⟩ := Finset.mem_image.mp r.property
  obtain ⟨i, hi, hqi⟩ := Finset.mem_image.mp hq
  have hne : i.val.val.2.1 ≠ i.val.val.2.2 :=
    i.val.property.2.2.2.2
  have hPair : i.val.val.2 = q.2 := by
    simpa [actualCompletionRecord] using congrArg Prod.snd hqi
  calc
    r.val.2.card = ({q.2.1, q.2.2} : Edge α).card := by
      rw [← hrq]
    _ = ({i.val.val.2.1, i.val.val.2.2} : Edge α).card := by rw [← hPair]
    _ = 2 := Finset.card_pair hne

set_option linter.style.haveILetI false in
/-- The distinct selected unoriented `(Q,{a,b})` records have the required
half ordered unique-pair bound in the actual selected pair-link family. -/
theorem selected_actual_undirected_records_card_le_of_graph
    (D : FiniteCompletionCliqueData α) [Fintype α] (S : Finset α)
    (F : Edge α → SimpleGraph α)
    [instRaw : ∀ Q : Edge α, DecidableRel (completionPairLinkGraph D Q).Adj]
    [instSelected : ∀ Q : Edge α,
      DecidableRel (selectedCompletionPairGraph D S Q).Adj]
    [instF : ∀ Q : Edge α, DecidableRel (F Q).Adj]
    (hSub : ∀ Q a b, (F Q).Adj a b →
      (selectedCompletionPairGraph D S Q).Adj a b)
    (hCenter : ∀ i : SelectedCompletionRecordIndex D S,
      (F (i.val.val.1.erase (D.label i.val.val.2.1 i.val.val.2.2))).Adj
        (D.label i.val.val.2.1 i.val.val.2.2) i.val.val.2.1 ∧
      (F (i.val.val.1.erase (D.label i.val.val.2.1 i.val.val.2.2))).Adj
        (D.label i.val.val.2.1 i.val.val.2.2) i.val.val.2.2) :
    (Fintype.card (SelectedUndirectedCompletionRecordIndex D S) : ℚ) ≤
      (∑ Q : Edge α, orderedUniquePairCount (F Q)) / 2 := by
  classical
  let owner : SelectedUndirectedCompletionRecordIndex D S → Edge α :=
    fun r => r.val.1
  let ends : SelectedUndirectedCompletionRecordIndex D S → α × α :=
    fun r => pairRootRep r.val.2 (selected_undirected_record_pair_card D S r)
  have hne : ∀ r, (ends r).1 ≠ (ends r).2 := by
    intro r
    exact (pair_root_rep_spec r.val.2
      (selected_undirected_record_pair_card D S r)).1
  have hUnique : ∀ r,
      graphCommonMultiplicity (F (owner r)) (ends r).1 (ends r).2 = 1 := by
    intro r
    obtain ⟨q, hq, hrq⟩ := Finset.mem_image.mp r.property
    obtain ⟨i, hi, hqi⟩ := Finset.mem_image.mp hq
    have hEq : (q.1, ({q.2.1, q.2.2} : Edge α)) = r.val := hrq
    have hSourceKey : actualCompletionRecord D i.val = q := hqi
    have hOwner : owner r =
        (i.val.val.1.erase (D.label i.val.val.2.1 i.val.val.2.2)) := by
      calc
        owner r = q.1 := (congrArg Prod.fst hEq).symm
        _ = (actualCompletionRecord D i.val).1 :=
          (congrArg Prod.fst hSourceKey).symm
        _ = i.val.val.1.erase (D.label i.val.val.2.1 i.val.val.2.2) := rfl
    have hSourceEnds : i.val.val.2 = q.2 := by
      simpa [actualCompletionRecord] using congrArg Prod.snd hSourceKey
    have hPair :
        ({q.2.1, q.2.2} : Edge α) =
          ({(ends r).1, (ends r).2} : Edge α) := by
      calc
        ({q.2.1, q.2.2} : Edge α) = r.val.2 := congrArg Prod.snd hEq
        _ = ({(ends r).1, (ends r).2} : Edge α) :=
          (pair_root_rep_spec r.val.2
            (selected_undirected_record_pair_card D S r)).2
    have hPairSource :
        ({i.val.val.2.1, i.val.val.2.2} : Edge α) =
          ({(ends r).1, (ends r).2} : Edge α) := by
      calc
        ({i.val.val.2.1, i.val.val.2.2} : Edge α) =
            ({q.2.1, q.2.2} : Edge α) := by rw [hSourceEnds]
        _ = ({(ends r).1, (ends r).2} : Edge α) := hPair
    have horient := pair_finset_eq_oriented_eq
      (i.val.property.2.2.2.2) hPairSource.symm
    letI : DecidableRel
        (completionPairLinkGraph D
          (i.val.val.1.erase (D.label i.val.val.2.1 i.val.val.2.2))).Adj := by
      exact instRaw (i.val.val.1.erase (D.label i.val.val.2.1 i.val.val.2.2))
    letI : DecidableRel
        (selectedPairLinkGraph
          (completionPairLinkGraph D
            (i.val.val.1.erase (D.label i.val.val.2.1 i.val.val.2.2))) S).Adj := by
      exact instSelected (i.val.val.1.erase (D.label i.val.val.2.1 i.val.val.2.2))
    letI : DecidableRel (F (i.val.val.1.erase
        (D.label i.val.val.2.1 i.val.val.2.2))).Adj :=
      instF (i.val.val.1.erase (D.label i.val.val.2.1 i.val.val.2.2))
    have hSourceUnique := actual_selected_completion_record_unique D i.val S
      i.property.1 i.property.2.1 i.property.2.2
    have hAtMost : graphCommonMultiplicity
        (F (i.val.val.1.erase (D.label i.val.val.2.1 i.val.val.2.2)))
        i.val.val.2.1 i.val.val.2.2 ≤ 1 := by
      calc
        _ ≤ graphCommonMultiplicity
              (selectedCompletionPairGraph D S
              (i.val.val.1.erase (D.label i.val.val.2.1 i.val.val.2.2)))
            i.val.val.2.1 i.val.val.2.2 :=
              graph_common_multiplicity_le_of_adj_mono
                (fun a b hab => hSub
                  (i.val.val.1.erase (D.label i.val.val.2.1 i.val.val.2.2))
                  a b hab) _ _
        _ = 1 := by simpa [selectedCompletionPairGraph] using hSourceUnique
    have hCenterI := hCenter i
    have hPositive : 0 < graphCommonMultiplicity
        (F (i.val.val.1.erase (D.label i.val.val.2.1 i.val.val.2.2)))
        i.val.val.2.1 i.val.val.2.2 := by
      unfold graphCommonMultiplicity
      apply Finset.card_pos.mpr
      refine ⟨D.label i.val.val.2.1 i.val.val.2.2, Finset.mem_filter.mpr ?_⟩
      constructor
      · simpa [SimpleGraph.mem_neighborFinset] using hCenterI.1.symm
      · exact hCenterI.2.symm
    have hAtSource : graphCommonMultiplicity
        (F (i.val.val.1.erase (D.label i.val.val.2.1 i.val.val.2.2)))
        i.val.val.2.1 i.val.val.2.2 = 1 := by omega
    rcases horient with hSame | hSwap
    · rw [← hSame.1, ← hSame.2, hOwner]
      exact hAtSource
    · rw [← hSwap.1, ← hSwap.2, hOwner]
      rw [graph_common_multiplicity_symm]
      exact hAtSource
  have hOrient : Function.Injective (fun ro :
      SelectedUndirectedCompletionRecordIndex D S × Bool =>
      (owner ro.1, if ro.2 then (ends ro.1).swap else ends ro.1)) := by
    intro ⟨r, o⟩ ⟨s, o'⟩ h
    change (owner r, if o then (ends r).swap else ends r) =
      (owner s, if o' then (ends s).swap else ends s) at h
    have hOwnerEq : owner r = owner s := by
      exact congrArg (fun p : Edge α × (α × α) => p.1) h
    have hEnds : (if o then (ends r).swap else ends r) =
        (if o' then (ends s).swap else ends s) :=
      congrArg (fun p : Edge α × (α × α) => p.2) h
    have hOwner : r.val.1 = s.val.1 := by simpa [owner] using hOwnerEq
    let pairSet : α × α → Edge α := fun e => {e.1, e.2}
    have hSwap (e : α × α) :
        pairSet e = pairSet e.swap := by
      ext x
      simp [pairSet, or_comm]
    have hLeftOrient : pairSet (ends r) =
        pairSet (if o then (ends r).swap else ends r) := by
      cases o
      · rfl
      · exact hSwap (ends r)
    have hRightOrient :
        pairSet (if o' then (ends s).swap else ends s) = pairSet (ends s) := by
      cases o'
      · rfl
      · exact (hSwap (ends s)).symm
    have hSetOrient : pairSet (ends r) = pairSet (ends s) :=
      hLeftOrient.trans ((congrArg pairSet hEnds).trans hRightOrient)
    have hPair : r.val.2 = s.val.2 := by
      calc
        r.val.2 = pairSet (ends r) :=
          (pair_root_rep_spec r.val.2
            (selected_undirected_record_pair_card D S r)).2
        _ = pairSet (ends s) := hSetOrient
        _ = s.val.2 := (pair_root_rep_spec s.val.2
          (selected_undirected_record_pair_card D S s)).2.symm
    have hrs : r = s := by
      apply Subtype.ext
      exact Prod.ext hOwner hPair
    cases hrs
    have hBool : o = o' := by
      cases o <;> cases o'
      · rfl
      · have hEq := congrArg Prod.fst hEnds
        have hEq' : (ends r).1 = (ends r).2 := by simpa [Prod.swap] using hEq
        exact (hne r hEq').elim
      · have hEq := congrArg Prod.fst hEnds
        have hEq' : (ends r).2 = (ends r).1 := by simpa [Prod.swap] using hEq
        exact (hne r hEq'.symm).elim
      · rfl
    exact Prod.ext rfl hBool
  exact undirected_record_family_le_half_ordered_count
    (F := F) owner ends hne hUnique hOrient

set_option linter.style.haveILetI false in
/-- The raw selected completion pair links are the default instance of the
conditional subgraph record bound. -/
theorem selected_actual_undirected_records_card_le
    (D : FiniteCompletionCliqueData α) [Fintype α] (S : Finset α)
    [instRaw : ∀ Q : Edge α, DecidableRel (completionPairLinkGraph D Q).Adj]
    [instSelected : ∀ Q : Edge α,
      DecidableRel (selectedCompletionPairGraph D S Q).Adj] :
    (Fintype.card (SelectedUndirectedCompletionRecordIndex D S) : ℚ) ≤
      (∑ Q : Edge α,
        orderedUniquePairCount (selectedCompletionPairGraph D S Q)) / 2 := by
  apply selected_actual_undirected_records_card_le_of_graph
    D S (selectedCompletionPairGraph D S)
  · intro Q a b h
    exact h
  · intro i
    let Q := i.val.val.1.erase (D.label i.val.val.2.1 i.val.val.2.2)
    letI : DecidableRel (completionPairLinkGraph D Q).Adj := instRaw Q
    letI : DecidableRel (selectedCompletionPairGraph D S Q).Adj := instSelected Q
    have hData := actual_completion_record_has_unique_link_neighbor D i.val
    constructor
    · change (completionPairLinkGraph D Q).Adj
          (D.label i.val.val.2.1 i.val.val.2.2) i.val.val.2.1 ∧
        D.label i.val.val.2.1 i.val.val.2.2 ∈ S ∧ i.val.val.2.1 ∈ S
      exact ⟨hData.2.1, i.property.2.2, i.property.1⟩
    · change (completionPairLinkGraph D Q).Adj
          (D.label i.val.val.2.1 i.val.val.2.2) i.val.val.2.2 ∧
        D.label i.val.val.2.1 i.val.val.2.2 ∈ S ∧ i.val.val.2.2 ∈ S
      exact ⟨hData.2.2, i.property.2.2, i.property.2.1⟩

/-- Every genuinely realized selected completion-triangle pair contributes
its actual directed record key to the global selected record set. -/
theorem completion_triangle_selected_record_mem
    (D : FiniteCompletionCliqueData α) [Fintype α]
    (T : Edge α) (v : Fin 3 → α) (i : Fin 3) (S : Finset α)
    (hTcard : T.card = 3) (hTsub : T ⊆ D.ground)
    (hCompletion : ∀ j, v j ∈ graphFacetCompletions D.K D.ground T)
    (hv : Function.Injective v)
    (hLeft : (completionTriangleEnds v i).1 ∈ S)
    (hRight : (completionTriangleEnds v i).2 ∈ S)
    (hLabel : D.label (completionTriangleEnds v i).1
      (completionTriangleEnds v i).2 ∈ S) :
    completionTriangleRecordKeys D T v i ∈
      selectedActualCompletionRecordKeys D S := by
  let j := completionTriangleActualIndex D T v i hTcard hTsub hCompletion hv
  have hmem : actualCompletionRecord D j ∈
      selectedActualCompletionRecordKeys D S :=
    Finset.mem_image.mpr ⟨⟨j, ⟨hLeft, hRight, hLabel⟩⟩,
      Finset.mem_univ _, rfl⟩
  simpa [j] using hmem

/-- The corresponding selected-key inclusion for an actual completion K4. -/
theorem completion_k4_selected_record_mem
    (D : FiniteCompletionCliqueData α) [Fintype α]
    (T : Edge α) (v : Fin 4 → α) (i : Fin 6) (S : Finset α)
    (hTcard : T.card = 3) (hTsub : T ⊆ D.ground)
    (hCompletion : ∀ j, v j ∈ graphFacetCompletions D.K D.ground T)
    (hv : Function.Injective v)
    (hLeft : (completionK4Ends v i).1 ∈ S)
    (hRight : (completionK4Ends v i).2 ∈ S)
    (hLabel : D.label (completionK4Ends v i).1
      (completionK4Ends v i).2 ∈ S) :
    completionK4RecordKeys D T v i ∈
      selectedActualCompletionRecordKeys D S := by
  let j := completionK4ActualIndex D T v i hTcard hTsub hCompletion hv
  have hmem : actualCompletionRecord D j ∈
      selectedActualCompletionRecordKeys D S :=
    Finset.mem_image.mpr ⟨⟨j, ⟨hLeft, hRight, hLabel⟩⟩,
      Finset.mem_univ _, rfl⟩
  simpa [j] using hmem

set_option linter.style.haveILetI false in
/-- All actual directed completion records surviving selection inject into
the disjoint family of directed unique-pair sets in the selected pair links.
This supplies the global record bound after identifying the two orientations
of each `(Q,ab)` record. -/
theorem selected_actual_directed_records_card_le
    (D : FiniteCompletionCliqueData α) [Fintype α] (S : Finset α)
    [instRaw : ∀ Q : Edge α, DecidableRel (completionPairLinkGraph D Q).Adj]
    [instSelected : ∀ Q : Edge α,
      DecidableRel (selectedCompletionPairGraph D S Q).Adj] :
      (Fintype.card (SelectedCompletionRecordIndex D S) : ℚ) ≤
      ∑ Q : Edge α, orderedUniquePairCount (selectedCompletionPairGraph D S Q) := by
  let owner : SelectedCompletionRecordIndex D S → Edge α := fun i =>
    i.val.val.1.erase (D.label i.val.val.2.1 i.val.val.2.2)
  let ends : SelectedCompletionRecordIndex D S → α × α := fun i => i.val.val.2
  let record : SelectedCompletionRecordIndex D S →
      FamilyUniquePairRecord (selectedCompletionPairGraph D S) := fun i =>
    ⟨owner i, ⟨ends i, by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · exact i.val.property.2.2.2.2
      · letI : DecidableRel
            (completionPairLinkGraph D (owner i)).Adj := instRaw (owner i)
        letI : DecidableRel
            (selectedPairLinkGraph
              (completionPairLinkGraph D
                (i.val.val.1.erase
                  (D.label i.val.val.2.1 i.val.val.2.2))) S).Adj := by
          change DecidableRel (selectedCompletionPairGraph D S (owner i)).Adj
          exact instSelected (owner i)
        exact actual_selected_completion_record_unique D i.val S
          i.property.1 i.property.2.1 i.property.2.2⟩⟩
  have hrecord : Function.Injective record := by
    intro i j hij
    apply Subtype.ext
    apply actual_completion_record_injective D
    apply Prod.ext
    · exact congrArg Sigma.fst hij
    · exact congrArg (fun q : FamilyUniquePairRecord
        (selectedCompletionPairGraph D S) => q.2.1) hij
  have hcard := Fintype.card_le_of_injective record hrecord
  have hq : (Fintype.card (SelectedCompletionRecordIndex D S) : ℚ) ≤
      (Fintype.card (FamilyUniquePairRecord
        (selectedCompletionPairGraph D S)) : ℚ) := Nat.cast_le.mpr hcard
  rw [family_unique_pair_record_card_eq] at hq
  exact hq

end JSP523.Rank4
