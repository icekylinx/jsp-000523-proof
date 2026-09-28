import JSP523.Rank4.GraphActualEligibleSlots
import JSP523.Rank4.GraphPaymentScalar
import JSP523.Rank4.GraphColoredFacetClassification
import JSP523.Rank4.ColoredSlotPayment

/-!
# Colored records in the actual selected record ledger

This file connects the per-clique colored-slot images to the global selected
record set.  The selected slot indices already enforce endpoint survival;
the remaining center-membership condition is stated explicitly.
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

def completionRecordForgetOrientation (p : Edge α × (α × α)) :
    Edge α × Edge α := (p.1, {p.2.1, p.2.2})

omit [Fintype α] in
theorem colored_facet_record_sum_le_ledger
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Finset ι) (R : ι → CliqueColor → Finset (Edge α × Edge α))
    (U : Finset (Edge α × Edge α))
    (hSub : ∀ t ∈ C, ∀ x, R t x ⊆ U)
    (hDisjoint : ∀ t ∈ C, ∀ x, ∀ t' ∈ C, ∀ x',
      (t, x) ≠ (t', x') → Disjoint (R t x) (R t' x')) :
    (∑ t ∈ C, ∑ x : CliqueColor, (R t x).card) ≤ U.card := by
  classical
  let I := C.product (Finset.univ : Finset CliqueColor)
  let record : ι × CliqueColor → Finset (Edge α × Edge α) := fun p => R p.1 p.2
  have hDisj : Set.Pairwise (↑I : Set (ι × CliqueColor))
      fun p q => Disjoint (record p) (record q) := by
    intro p hp q hq hpq
    exact hDisjoint p.1 (Finset.mem_product.mp hp).1 p.2
      q.1 (Finset.mem_product.mp hq).1 q.2 (by
        intro h
        apply hpq
        exact Prod.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
  have hUnionSub : I.biUnion record ⊆ U := by
    intro r hr
    obtain ⟨p, hp, hpr⟩ := Finset.mem_biUnion.mp hr
    exact hSub p.1 (Finset.mem_product.mp hp).1 p.2 (by simpa [record] using hpr)
  have hCard : (I.biUnion record).card = ∑ p ∈ I, (record p).card :=
    Finset.card_biUnion hDisj
  have hProduct : (∑ p ∈ I, (record p).card) =
      ∑ t ∈ C, ∑ x : CliqueColor, (R t x).card := by
    simp [I, record, Finset.sum_product]
  rw [← hProduct, ← hCard]
  exact Finset.card_le_card hUnionSub

def actualColoredRecordBase (d : ℕ) : ℕ := if d = 3 then 3 else 6

def actualColoredSlotBase (d : ℕ) : ℕ := if d = 3 then 1 else 2

def actualColoredSlotLoss (d k : ℕ) : ℕ :=
  if d = 3 then rainbowRecordLoss k else properFourRecordLoss k

theorem actual_colored_slot_losses_le_base (d : ℕ)
    (k : CliqueColor → ℕ) (hd : d = 3 ∨ d = 4) :
    (∑ x : CliqueColor, actualColoredSlotLoss d (k x)) ≤
      actualColoredRecordBase d := by
  rcases hd with h3 | h4
  · subst d
    have heach : ∀ x : CliqueColor,
        actualColoredSlotLoss 3 (k x) ≤ 1 := by
      intro x
      have h : (if k x < 3 then 1 else 0 : ℕ) ≤ 1 := by
        split <;> omega
      simpa [actualColoredSlotLoss, rainbowRecordLoss] using h
    have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset CliqueColor))
      (fun x _ => heach x)
    simpa [actualColoredRecordBase, Fintype.card_fin] using hsum
  · subst d
    have heach : ∀ x : CliqueColor,
        actualColoredSlotLoss 4 (k x) ≤ 2 := by
      intro x
      change properFourRecordLoss (k x) ≤ 2
      exact min_le_left _ _
    have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset CliqueColor))
      (fun x _ => heach x)
    simpa [actualColoredRecordBase, Fintype.card_fin] using hsum

omit [Fintype α] in
/-- Summing actual per-color selected-record lower bounds over a finite,
pairwise distinct colored-facet family gives the global record term in
`hRecords`. -/
theorem actual_colored_records_loss_le_ledger
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Finset ι) (d : ι → ℕ) (k : ι → CliqueColor → ℕ)
    (R : ι → CliqueColor → Finset (Edge α × Edge α))
    (U : Finset (Edge α × Edge α))
    (hd : ∀ t ∈ C, d t = 3 ∨ d t = 4)
    (hSlot : ∀ t ∈ C, ∀ x : CliqueColor,
      actualColoredSlotBase (d t) ≤
        (R t x).card + actualColoredSlotLoss (d t) (k t x))
    (hSub : ∀ t ∈ C, ∀ x, R t x ⊆ U)
    (hDisjoint : ∀ t ∈ C, ∀ x, ∀ t' ∈ C, ∀ x',
      (t, x) ≠ (t', x') → Disjoint (R t x) (R t' x')) :
    (∑ t ∈ C, (actualColoredRecordBase (d t) -
      ∑ x : CliqueColor, actualColoredSlotLoss (d t) (k t x))) ≤ U.card := by
  have hCard := colored_facet_record_sum_le_ledger C R U hSub hDisjoint
  have hLocal : ∀ t ∈ C,
      actualColoredRecordBase (d t) -
        ∑ x : CliqueColor, actualColoredSlotLoss (d t) (k t x) ≤
        ∑ x : CliqueColor, (R t x).card := by
    intro t ht
    have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset CliqueColor))
      (fun x _ => hSlot t ht x)
    have hBase : actualColoredRecordBase (d t) =
        ∑ x : CliqueColor, actualColoredSlotBase (d t) := by
      rcases hd t ht with h | h <;>
        simp [actualColoredRecordBase, actualColoredSlotBase, h, Fintype.card_fin]
    rw [← hBase] at hsum
    have hAdd : actualColoredRecordBase (d t) ≤
        (∑ x : CliqueColor, (R t x).card) +
          ∑ x : CliqueColor, actualColoredSlotLoss (d t) (k t x) := by
      simpa [Finset.sum_add_distrib] using hsum
    omega
  have hsum := Finset.sum_le_sum (s := C) hLocal
  have hRearrange :
      (∑ t ∈ C, (actualColoredRecordBase (d t) -
        ∑ x : CliqueColor, actualColoredSlotLoss (d t) (k t x))) ≤
        ∑ t ∈ C, ∑ x : CliqueColor, (R t x).card := by
    simpa using hsum
  exact hRearrange.trans hCard

omit [Fintype α] in
/-- Cast the actual finite record ledger bound into the rational `hRecords`
input used by colored slot payment. -/
theorem actual_colored_records_loss_le_ledger_rat
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Finset ι) (d : ι → ℕ) (k : ι → CliqueColor → ℕ)
    (R : ι → CliqueColor → Finset (Edge α × Edge α))
    (U : Finset (Edge α × Edge α))
    (hd : ∀ t ∈ C, d t = 3 ∨ d t = 4)
    (hSlot : ∀ t ∈ C, ∀ x : CliqueColor,
      actualColoredSlotBase (d t) ≤
        (R t x).card + actualColoredSlotLoss (d t) (k t x))
    (hSub : ∀ t ∈ C, ∀ x, R t x ⊆ U)
    (hDisjoint : ∀ t ∈ C, ∀ x, ∀ t' ∈ C, ∀ x',
      (t, x) ≠ (t', x') → Disjoint (R t x) (R t' x')) :
    (∑ t ∈ C, (coloredFacetRecords (d t) -
      ∑ x : CliqueColor, coloredSlotLoss (d t) (k t x))) ≤ (U.card : ℚ) := by
  let lossNat := fun t => ∑ x : CliqueColor, actualColoredSlotLoss (d t) (k t x)
  let deficitNat := fun t => actualColoredRecordBase (d t) - lossNat t
  have hNat := actual_colored_records_loss_le_ledger C d k R U
    hd hSlot hSub hDisjoint
  have hLossBound : ∀ t ∈ C,
      (∑ x : CliqueColor, actualColoredSlotLoss (d t) (k t x)) ≤
        actualColoredRecordBase (d t) := by
    intro t ht
    exact actual_colored_slot_losses_le_base (d t) (k t)
      (hd t ht)
  have hEachCast : ∀ t ∈ C,
      (deficitNat t : ℚ) = coloredFacetRecords (d t) -
        ∑ x : CliqueColor, coloredSlotLoss (d t) (k t x) := by
    intro t ht
    have hBase : (actualColoredRecordBase (d t) : ℚ) =
        coloredFacetRecords (d t) := by
      simp [actualColoredRecordBase, coloredFacetRecords]
    have hLoss :
        ((∑ x : CliqueColor, actualColoredSlotLoss (d t) (k t x)) : ℚ) =
          ∑ x : CliqueColor, coloredSlotLoss (d t) (k t x) := by
      simp [actualColoredSlotLoss, coloredSlotLoss]
    dsimp [deficitNat, lossNat]
    rw [Nat.cast_sub (hLossBound t ht), hBase, Nat.cast_sum, hLoss]
  have hDeficitNat : (∑ t ∈ C, deficitNat t) ≤ U.card := by
    simpa [deficitNat, lossNat] using hNat
  have hSumCast :
      ((∑ t ∈ C, deficitNat t : ℕ) : ℚ) =
        ∑ t ∈ C, (coloredFacetRecords (d t) -
          ∑ x : CliqueColor, coloredSlotLoss (d t) (k t x)) := by
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro t ht
    exact hEachCast t ht
  rw [← hSumCast]
  exact Nat.cast_le.mpr hDeficitNat

theorem directed_selected_records_forget_orientation_subset
    (D : FiniteCompletionCliqueData α) (S : Finset α)
    (R : Finset (Edge α × (α × α)))
    (hR : R ⊆ selectedActualCompletionRecordKeys D S) :
    R.image completionRecordForgetOrientation ⊆
      selectedUndirectedCompletionRecordKeys D S := by
  intro q hq
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
  exact Finset.mem_image.mpr ⟨p, hR hp, rfl⟩

def actualTriangleUndirectedRecordKey (D : FiniteCompletionCliqueData α)
    (T : Edge α) (v : Fin 3 → α) (i : Fin 3) : Edge α × Edge α :=
  completionRecordForgetOrientation (completionTriangleRecordKeys D T v i)

def actualK4UndirectedRecordKey (D : FiniteCompletionCliqueData α)
    (T : Edge α) (v : Fin 4 → α) (i : Fin 6) : Edge α × Edge α :=
  completionRecordForgetOrientation (completionK4RecordKeys D T v i)

omit [Fintype α] in
theorem actual_triangle_undirected_record_key_injective
    (D : FiniteCompletionCliqueData α) (T : Edge α) (v : Fin 3 → α)
    (hv : Function.Injective v) :
    Function.Injective (actualTriangleUndirectedRecordKey D T v) := by
  intro i j hij
  have hEndsSet : ({(completionTriangleEnds v i).1,
      (completionTriangleEnds v i).2} : Edge α) =
      ({(completionTriangleEnds v j).1,
      (completionTriangleEnds v j).2} : Edge α) := by
    have h := congrArg Prod.snd hij
    simpa [actualTriangleUndirectedRecordKey, completionTriangleRecordKeys,
      completionPairRecord, completionRecordForgetOrientation] using h
  have horient := pair_finset_eq_oriented_eq
    (completion_triangle_ends_offdiag v hv j) hEndsSet
  rcases horient with hSame | hSwap
  · exact completion_triangle_ends_injective v hv (Prod.ext hSame.1.symm hSame.2.symm)
  · have hIndex : completionTriangleIndexPair i =
        (completionTriangleIndexPair j).swap := by
      apply Prod.ext <;> apply hv
      · simpa [completionTriangleEnds] using hSwap.2.symm
      · simpa [completionTriangleEnds] using hSwap.1.symm
    fin_cases i <;> fin_cases j <;>
      norm_num [completionTriangleIndexPair] at hIndex

omit [Fintype α] in
theorem actual_k4_undirected_record_key_injective
    (D : FiniteCompletionCliqueData α) (T : Edge α) (v : Fin 4 → α)
    (hv : Function.Injective v) :
    Function.Injective (actualK4UndirectedRecordKey D T v) := by
  intro i j hij
  have hEndsSet : ({(completionK4Ends v i).1,
      (completionK4Ends v i).2} : Edge α) =
      ({(completionK4Ends v j).1,
      (completionK4Ends v j).2} : Edge α) := by
    have h := congrArg Prod.snd hij
    simpa [actualK4UndirectedRecordKey, completionK4RecordKeys,
      completionPairRecord, completionRecordForgetOrientation] using h
  have horient := pair_finset_eq_oriented_eq
    (completion_k4_ends_offdiag v hv j) hEndsSet
  rcases horient with hSame | hSwap
  · exact completion_k4_ends_injective v hv (Prod.ext hSame.1.symm hSame.2.symm)
  · have hIndex : completionK4IndexPair i =
        (completionK4IndexPair j).swap := by
      apply Prod.ext <;> apply hv
      · simpa [completionK4Ends] using hSwap.2.symm
      · simpa [completionK4Ends] using hSwap.1.symm
    fin_cases i <;> fin_cases j <;>
      norm_num [completionK4IndexPair] at hIndex

omit [Fintype α] in
theorem actual_triangle_undirected_key_eq_implies_facet_eq
    (D : FiniteCompletionCliqueData α)
    (T T' : Edge α) (v : Fin 3 → α) (w : Fin 3 → α) (i j : Fin 3)
    (hTcard : T.card = 3) (hTsub : T ⊆ D.ground)
    (hTCompletion : ∀ k, v k ∈ graphFacetCompletions D.K D.ground T)
    (hv : Function.Injective v)
    (hT'card : T'.card = 3) (hT'sub : T' ⊆ D.ground)
    (hT'Completion : ∀ k, w k ∈ graphFacetCompletions D.K D.ground T')
    (hw : Function.Injective w)
    (hKey : actualTriangleUndirectedRecordKey D T v i =
      actualTriangleUndirectedRecordKey D T' w j) : T = T' := by
  have hOwner : T.erase (D.label (completionTriangleEnds v i).1
      (completionTriangleEnds v i).2) =
      T'.erase (D.label (completionTriangleEnds w j).1
      (completionTriangleEnds w j).2) := by
    simpa [actualTriangleUndirectedRecordKey, completionTriangleRecordKeys,
      completionPairRecord, completionRecordForgetOrientation] using
      congrArg Prod.fst hKey
  have hSet : ({(completionTriangleEnds v i).1,
      (completionTriangleEnds v i).2} : Edge α) =
      ({(completionTriangleEnds w j).1,
      (completionTriangleEnds w j).2} : Edge α) := by
    simpa [actualTriangleUndirectedRecordKey, completionTriangleRecordKeys,
      completionPairRecord, completionRecordForgetOrientation] using
      congrArg Prod.snd hKey
  have hOrient := pair_finset_eq_oriented_eq
    (completion_triangle_ends_offdiag w hw j) hSet
  have hLabel : D.label (completionTriangleEnds v i).1
      (completionTriangleEnds v i).2 =
      D.label (completionTriangleEnds w j).1 (completionTriangleEnds w j).2 := by
    rcases hOrient with h | h
    · rw [h.1, h.2]
    · rw [h.1, h.2]
      exact D.label_symm _ _
  have hLabelT := completion_pair_label_mem_facet D T hTcard hTsub
    (completionTriangleEnds v i).1 (completionTriangleEnds v i).2
    (hTCompletion (completionTriangleIndexPair i).1)
    (hTCompletion (completionTriangleIndexPair i).2)
    (completion_triangle_ends_offdiag v hv i)
  have hLabelT' := completion_pair_label_mem_facet D T' hT'card hT'sub
    (completionTriangleEnds w j).1 (completionTriangleEnds w j).2
    (hT'Completion (completionTriangleIndexPair j).1)
    (hT'Completion (completionTriangleIndexPair j).2)
    (completion_triangle_ends_offdiag w hw j)
  have hErase : T.erase (D.label (completionTriangleEnds w j).1
      (completionTriangleEnds w j).2) =
      T'.erase (D.label (completionTriangleEnds w j).1
      (completionTriangleEnds w j).2) := by
    calc
      _ = T.erase (D.label (completionTriangleEnds v i).1
          (completionTriangleEnds v i).2) := by rw [← hLabel]
      _ = _ := hOwner
  calc
    T = insert (D.label (completionTriangleEnds v i).1
        (completionTriangleEnds v i).2)
        (T.erase (D.label (completionTriangleEnds v i).1
          (completionTriangleEnds v i).2)) := (Finset.insert_erase hLabelT).symm
    _ = insert (D.label (completionTriangleEnds w j).1
        (completionTriangleEnds w j).2)
        (T'.erase (D.label (completionTriangleEnds w j).1
          (completionTriangleEnds w j).2)) := by rw [hLabel, hErase]
    _ = T' := Finset.insert_erase hLabelT'

omit [Fintype α] in
theorem actual_k4_undirected_key_eq_implies_facet_eq
    (D : FiniteCompletionCliqueData α)
    (T T' : Edge α) (v : Fin 4 → α) (w : Fin 4 → α) (i : Fin 6) (j : Fin 6)
    (hTcard : T.card = 3) (hTsub : T ⊆ D.ground)
    (hTCompletion : ∀ k, v k ∈ graphFacetCompletions D.K D.ground T)
    (hv : Function.Injective v)
    (hT'card : T'.card = 3) (hT'sub : T' ⊆ D.ground)
    (hT'Completion : ∀ k, w k ∈ graphFacetCompletions D.K D.ground T')
    (hw : Function.Injective w)
    (hKey : actualK4UndirectedRecordKey D T v i =
      actualK4UndirectedRecordKey D T' w j) : T = T' := by
  have hOwner : T.erase (D.label (completionK4Ends v i).1
      (completionK4Ends v i).2) =
      T'.erase (D.label (completionK4Ends w j).1
      (completionK4Ends w j).2) := by
    simpa [actualK4UndirectedRecordKey, completionK4RecordKeys,
      completionPairRecord, completionRecordForgetOrientation] using
      congrArg Prod.fst hKey
  have hSet : ({(completionK4Ends v i).1,
      (completionK4Ends v i).2} : Edge α) =
      ({(completionK4Ends w j).1,
      (completionK4Ends w j).2} : Edge α) := by
    simpa [actualK4UndirectedRecordKey, completionK4RecordKeys,
      completionPairRecord, completionRecordForgetOrientation] using
      congrArg Prod.snd hKey
  have hOrient := pair_finset_eq_oriented_eq
    (completion_k4_ends_offdiag w hw j) hSet
  have hLabel : D.label (completionK4Ends v i).1
      (completionK4Ends v i).2 =
      D.label (completionK4Ends w j).1 (completionK4Ends w j).2 := by
    rcases hOrient with h | h
    · rw [h.1, h.2]
    · rw [h.1, h.2]
      exact D.label_symm _ _
  have hLabelT := completion_pair_label_mem_facet D T hTcard hTsub
    (completionK4Ends v i).1 (completionK4Ends v i).2
    (hTCompletion (completionK4IndexPair i).1)
    (hTCompletion (completionK4IndexPair i).2)
    (completion_k4_ends_offdiag v hv i)
  have hLabelT' := completion_pair_label_mem_facet D T' hT'card hT'sub
    (completionK4Ends w j).1 (completionK4Ends w j).2
    (hT'Completion (completionK4IndexPair j).1)
    (hT'Completion (completionK4IndexPair j).2)
    (completion_k4_ends_offdiag w hw j)
  have hErase : T.erase (D.label (completionK4Ends w j).1
      (completionK4Ends w j).2) =
      T'.erase (D.label (completionK4Ends w j).1
      (completionK4Ends w j).2) := by
    calc
      _ = T.erase (D.label (completionK4Ends v i).1
          (completionK4Ends v i).2) := by rw [← hLabel]
      _ = _ := hOwner
  calc
    T = insert (D.label (completionK4Ends v i).1
        (completionK4Ends v i).2)
        (T.erase (D.label (completionK4Ends v i).1
          (completionK4Ends v i).2)) := (Finset.insert_erase hLabelT).symm
    _ = insert (D.label (completionK4Ends w j).1
        (completionK4Ends w j).2)
        (T'.erase (D.label (completionK4Ends w j).1
          (completionK4Ends w j).2)) := by rw [hLabel, hErase]
    _ = T' := Finset.insert_erase hLabelT'

omit [Fintype α] in
theorem actual_triangle_k4_undirected_key_eq_implies_facet_eq
    (D : FiniteCompletionCliqueData α)
    (T T' : Edge α) (v : Fin 3 → α) (w : Fin 4 → α) (i : Fin 3) (j : Fin 6)
    (hTcard : T.card = 3) (hTsub : T ⊆ D.ground)
    (hTCompletion : ∀ k, v k ∈ graphFacetCompletions D.K D.ground T)
    (hv : Function.Injective v)
    (hT'card : T'.card = 3) (hT'sub : T' ⊆ D.ground)
    (hT'Completion : ∀ k, w k ∈ graphFacetCompletions D.K D.ground T')
    (hw : Function.Injective w)
    (hKey : actualTriangleUndirectedRecordKey D T v i =
      actualK4UndirectedRecordKey D T' w j) : T = T' := by
  have hOwner : T.erase (D.label (completionTriangleEnds v i).1
      (completionTriangleEnds v i).2) =
      T'.erase (D.label (completionK4Ends w j).1
      (completionK4Ends w j).2) := by
    simpa [actualTriangleUndirectedRecordKey, actualK4UndirectedRecordKey,
      completionTriangleRecordKeys, completionK4RecordKeys,
      completionPairRecord, completionRecordForgetOrientation] using
      congrArg Prod.fst hKey
  have hSet : ({(completionTriangleEnds v i).1,
      (completionTriangleEnds v i).2} : Edge α) =
      ({(completionK4Ends w j).1,
      (completionK4Ends w j).2} : Edge α) := by
    simpa [actualTriangleUndirectedRecordKey, actualK4UndirectedRecordKey,
      completionTriangleRecordKeys, completionK4RecordKeys,
      completionPairRecord, completionRecordForgetOrientation] using
      congrArg Prod.snd hKey
  have hOrient := pair_finset_eq_oriented_eq
    (completion_k4_ends_offdiag w hw j) hSet
  have hLabel : D.label (completionTriangleEnds v i).1
      (completionTriangleEnds v i).2 =
      D.label (completionK4Ends w j).1 (completionK4Ends w j).2 := by
    rcases hOrient with h | h
    · rw [h.1, h.2]
    · rw [h.1, h.2]
      exact D.label_symm _ _
  have hLabelT := completion_pair_label_mem_facet D T hTcard hTsub
    (completionTriangleEnds v i).1 (completionTriangleEnds v i).2
    (hTCompletion (completionTriangleIndexPair i).1)
    (hTCompletion (completionTriangleIndexPair i).2)
    (completion_triangle_ends_offdiag v hv i)
  have hLabelT' := completion_pair_label_mem_facet D T' hT'card hT'sub
    (completionK4Ends w j).1 (completionK4Ends w j).2
    (hT'Completion (completionK4IndexPair j).1)
    (hT'Completion (completionK4IndexPair j).2)
    (completion_k4_ends_offdiag w hw j)
  have hErase : T.erase (D.label (completionK4Ends w j).1
      (completionK4Ends w j).2) =
      T'.erase (D.label (completionK4Ends w j).1
      (completionK4Ends w j).2) := by
    calc
      _ = T.erase (D.label (completionTriangleEnds v i).1
          (completionTriangleEnds v i).2) := by rw [← hLabel]
      _ = _ := hOwner
  calc
    T = insert (D.label (completionTriangleEnds v i).1
        (completionTriangleEnds v i).2)
        (T.erase (D.label (completionTriangleEnds v i).1
          (completionTriangleEnds v i).2)) := (Finset.insert_erase hLabelT).symm
    _ = insert (D.label (completionK4Ends w j).1
        (completionK4Ends w j).2)
        (T'.erase (D.label (completionK4Ends w j).1
          (completionK4Ends w j).2)) := by rw [hLabel, hErase]
    _ = T' := Finset.insert_erase hLabelT'

def selectedActualTriangleUndirectedColorSlotRecords
    (D : FiniteCompletionCliqueData α) (T : Edge α) (v : Fin 3 → α)
    (mark : CliqueColor → α) (x : CliqueColor) (S : Finset (Fin 3)) :
    Finset (Edge α × Edge α) :=
  coloredSlotRecordImage
    (Finset.univ.filter fun i : Fin 3 =>
      D.label (completionTriangleEnds v i).1 (completionTriangleEnds v i).2 = mark x ∧
      (completionTriangleIndexPair i).1 ∈ S ∧ (completionTriangleIndexPair i).2 ∈ S)
    (actualTriangleUndirectedRecordKey D T v)

def selectedActualK4UndirectedColorSlotRecords
    (D : FiniteCompletionCliqueData α) (T : Edge α) (v : Fin 4 → α)
    (mark : CliqueColor → α) (x : CliqueColor) (S : Finset (Fin 4)) :
    Finset (Edge α × Edge α) :=
  coloredSlotRecordImage
    (Finset.univ.filter fun i : Fin 6 =>
      D.label (completionK4Ends v i).1 (completionK4Ends v i).2 = mark x ∧
      (completionK4IndexPair i).1 ∈ S ∧ (completionK4IndexPair i).2 ∈ S)
    (actualK4UndirectedRecordKey D T v)

omit [Fintype α] in
theorem selected_actual_triangle_undirected_records_card_eq
    (D : FiniteCompletionCliqueData α) (T : Edge α) (v : Fin 3 → α)
    (mark : CliqueColor → α) (x : CliqueColor) (S : Finset (Fin 3))
    (hv : Function.Injective v)
    (hLabelMem : ∀ i, D.label (completionTriangleEnds v i).1
      (completionTriangleEnds v i).2 ∈ T) :
    (selectedActualTriangleUndirectedColorSlotRecords D T v mark x S).card =
      (selectedActualTriangleColorSlotRecords D T v mark x S).card := by
  unfold selectedActualTriangleUndirectedColorSlotRecords
    selectedActualTriangleColorSlotRecords
  rw [colored_slot_record_image_card _ _
      (actual_triangle_undirected_record_key_injective D T v hv),
    colored_slot_record_image_card _ _ (completion_triangle_record_keys_injective
      D T v hv hLabelMem)]

omit [Fintype α] in
theorem selected_actual_k4_undirected_records_card_eq
    (D : FiniteCompletionCliqueData α) (T : Edge α) (v : Fin 4 → α)
    (mark : CliqueColor → α) (x : CliqueColor) (S : Finset (Fin 4))
    (hv : Function.Injective v)
    (hLabelMem : ∀ i, D.label (completionK4Ends v i).1
      (completionK4Ends v i).2 ∈ T) :
    (selectedActualK4UndirectedColorSlotRecords D T v mark x S).card =
      (selectedActualK4ColorSlotRecords D T v mark x S).card := by
  unfold selectedActualK4UndirectedColorSlotRecords
    selectedActualK4ColorSlotRecords
  rw [colored_slot_record_image_card _ _
      (actual_k4_undirected_record_key_injective D T v hv),
    colored_slot_record_image_card _ _ (completion_k4_record_keys_injective
      D T v hv hLabelMem)]

omit [Fintype α] in
theorem selected_actual_triangle_undirected_records_card_lower_bound
    (D : FiniteCompletionCliqueData α) (T : Edge α) (v : Fin 3 → α)
    (mark : CliqueColor → α) (a b c x : CliqueColor) (S : Finset (Fin 3))
    (k : ℕ) (hk : k = S.card)
    (hv : Function.Injective v) (hmark : Function.Injective mark)
    (hLabelMem : ∀ i, D.label (completionTriangleEnds v i).1
      (completionTriangleEnds v i).2 ∈ T)
    (hColor : ∀ i, D.label (completionTriangleEnds v i).1
      (completionTriangleEnds v i).2 = mark (rainbowTriangleEdgeColor a b c i))
    (hRainbow : a ≠ b ∧ a ≠ c ∧ b ≠ c) :
    1 - rainbowRecordLoss k ≤
      (selectedActualTriangleUndirectedColorSlotRecords D T v mark x S).card := by
  have h := selected_actual_triangle_color_slot_records_card_lower_bound
    D T v mark a b c x S hv hmark hLabelMem hColor hRainbow
  have hEq := selected_actual_triangle_undirected_records_card_eq
    D T v mark x S hv hLabelMem
  rw [hk]
  rw [hEq]
  simpa [rainbowRecordLoss] using h

theorem canonical_actual_triangle_undirected_records_card_lower_bound
    (D : FiniteCompletionCliqueData α) (T : Edge α)
    (hcard : (graphFacetCompletions D.K D.ground T).card = 3)
    (hTcard : T.card = 3) (hTsub : T ⊆ D.ground)
    (hRainbow : CompletionTriangleRainbow D
      (graphFacetCompletions D.K D.ground T))
    (x : CliqueColor) (S : Finset (Fin 3)) (k : ℕ)
    (hk : k = S.card) :
    1 - rainbowRecordLoss k ≤
      (selectedActualTriangleUndirectedColorSlotRecords D T
        (canonicalTriangleCompletion D T hcard)
        (canonicalTriangleMark D T hcard) x S).card := by
  let v := canonicalTriangleCompletion D T hcard
  let mark := canonicalTriangleMark D T hcard
  have hv : Function.Injective v := canonical_triangle_completion_injective D T hcard
  have hmark : Function.Injective mark := canonical_triangle_mark_injective
    D T hcard hRainbow
  have hLabelMem : ∀ i, D.label (completionTriangleEnds v i).1
      (completionTriangleEnds v i).2 ∈ T := by
    intro i
    have hcolor := canonical_triangle_labels_are_marked D T hcard i
    rw [← show v = canonicalTriangleCompletion D T hcard from rfl] at hcolor
    rw [← show mark = canonicalTriangleMark D T hcard from rfl] at hcolor
    rw [hcolor]
    exact canonical_triangle_mark_mem_facet D T hcard hTcard hTsub _
  have hColor : ∀ i, D.label (completionTriangleEnds v i).1
      (completionTriangleEnds v i).2 = mark (rainbowTriangleEdgeColor 0 1 2 i) := by
    intro i
    exact canonical_triangle_labels_are_marked D T hcard i
  have hColors : (0 : CliqueColor) ≠ 1 ∧
      (0 : CliqueColor) ≠ 2 ∧ (1 : CliqueColor) ≠ 2 := by decide
  simpa [v, mark] using
    selected_actual_triangle_undirected_records_card_lower_bound
      D T (canonicalTriangleCompletion D T hcard)
      (canonicalTriangleMark D T hcard) 0 1 2 x S k hk hv hmark
      hLabelMem hColor hColors

omit [Fintype α] in
theorem selected_actual_k4_undirected_records_card_lower_bound
    (D : FiniteCompletionCliqueData α) (T : Edge α) (v : Fin 4 → α)
    (mark : CliqueColor → α) (a b c x : CliqueColor) (S : Finset (Fin 4))
    (k : ℕ) (hk : k = S.card)
    (hv : Function.Injective v) (hmark : Function.Injective mark)
    (hLabelMem : ∀ i, D.label (completionK4Ends v i).1
      (completionK4Ends v i).2 ∈ T)
    (hColor : ∀ i, D.label (completionK4Ends v i).1
      (completionK4Ends v i).2 = mark (properK4EdgeColor a b c i))
    (hProper : a ≠ b ∧ a ≠ c ∧ b ≠ c) :
    2 - properFourRecordLoss k ≤
      (selectedActualK4UndirectedColorSlotRecords D T v mark x S).card := by
  have h := selected_actual_k4_color_slot_records_card_lower_bound
    D T v mark a b c x S hv hmark hLabelMem hColor hProper
  have hEq := selected_actual_k4_undirected_records_card_eq
    D T v mark x S hv hLabelMem
  rw [hk]
  rw [hEq]
  simpa [properFourRecordLoss] using h

omit [Fintype α] in
theorem selected_actual_triangle_undirected_records_eq_forget
    (D : FiniteCompletionCliqueData α) (T : Edge α) (v : Fin 3 → α)
    (mark : CliqueColor → α) (x : CliqueColor) (S : Finset (Fin 3)) :
    selectedActualTriangleUndirectedColorSlotRecords D T v mark x S =
      (selectedActualTriangleColorSlotRecords D T v mark x S).image
        completionRecordForgetOrientation := by
  ext p
  simp [selectedActualTriangleUndirectedColorSlotRecords,
    selectedActualTriangleColorSlotRecords, coloredSlotRecordImage,
    actualTriangleUndirectedRecordKey, completionRecordForgetOrientation,
    completionTriangleRecordKeys, completionPairRecord]

omit [Fintype α] in
theorem selected_actual_k4_undirected_records_eq_forget
    (D : FiniteCompletionCliqueData α) (T : Edge α) (v : Fin 4 → α)
    (mark : CliqueColor → α) (x : CliqueColor) (S : Finset (Fin 4)) :
    selectedActualK4UndirectedColorSlotRecords D T v mark x S =
      (selectedActualK4ColorSlotRecords D T v mark x S).image
        completionRecordForgetOrientation := by
  ext p
  simp [selectedActualK4UndirectedColorSlotRecords,
    selectedActualK4ColorSlotRecords, coloredSlotRecordImage,
    actualK4UndirectedRecordKey, completionRecordForgetOrientation,
    completionK4RecordKeys, completionPairRecord]


omit [Fintype α] in
theorem completion_triangle_record_key_eq_implies_facet_eq
    (D : FiniteCompletionCliqueData α)
    (T T' : Edge α) (v : Fin 3 → α) (w : Fin 3 → α) (i j : Fin 3)
    (hTcard : T.card = 3) (hTsub : T ⊆ D.ground)
    (hTCompletion : ∀ k, v k ∈ graphFacetCompletions D.K D.ground T)
    (hv : Function.Injective v)
    (hT'card : T'.card = 3) (hT'sub : T' ⊆ D.ground)
    (hT'Completion : ∀ k, w k ∈ graphFacetCompletions D.K D.ground T')
    (hw : Function.Injective w)
    (hKey : completionTriangleRecordKeys D T v i =
      completionTriangleRecordKeys D T' w j) : T = T' := by
  let p := completionTriangleActualIndex D T v i hTcard hTsub hTCompletion hv
  let q := completionTriangleActualIndex D T' w j hT'card hT'sub hT'Completion hw
  have hEq : actualCompletionRecord D p = actualCompletionRecord D q := by
    rw [actual_triangle_index_record_key, actual_triangle_index_record_key]
    exact hKey
  have hIndices := actual_completion_record_injective D hEq
  exact congrArg (fun p : CompletionRecordIndex D => p.val.1) hIndices

omit [Fintype α] in
theorem completion_k4_record_key_eq_implies_facet_eq
    (D : FiniteCompletionCliqueData α)
    (T T' : Edge α) (v : Fin 4 → α) (w : Fin 4 → α) (i j : Fin 6)
    (hTcard : T.card = 3) (hTsub : T ⊆ D.ground)
    (hTCompletion : ∀ k, v k ∈ graphFacetCompletions D.K D.ground T)
    (hv : Function.Injective v)
    (hT'card : T'.card = 3) (hT'sub : T' ⊆ D.ground)
    (hT'Completion : ∀ k, w k ∈ graphFacetCompletions D.K D.ground T')
    (hw : Function.Injective w)
    (hKey : completionK4RecordKeys D T v i =
      completionK4RecordKeys D T' w j) : T = T' := by
  let p := completionK4ActualIndex D T v i hTcard hTsub hTCompletion hv
  let q := completionK4ActualIndex D T' w j hT'card hT'sub hT'Completion hw
  have hEq : actualCompletionRecord D p = actualCompletionRecord D q := by
    rw [actual_K4_index_record_key, actual_K4_index_record_key]
    exact hKey
  have hIndices := actual_completion_record_injective D hEq
  exact congrArg (fun p : CompletionRecordIndex D => p.val.1) hIndices

theorem selected_actual_triangle_color_records_subset_global
    (D : FiniteCompletionCliqueData α)
    (T : Edge α) (v : Fin 3 → α) (mark : CliqueColor → α)
    (x : CliqueColor) (S : Finset α) (S₀ : Finset (Fin 3))
    (hmarkS : mark x ∈ S)
    (hSelected : ∀ i, i ∈ S₀ → v i ∈ S)
    (hTcard : T.card = 3) (hTsub : T ⊆ D.ground)
    (hCompletion : ∀ j, v j ∈ graphFacetCompletions D.K D.ground T)
    (hv : Function.Injective v) :
    selectedActualTriangleColorSlotRecords D T v mark x S₀ ⊆
        selectedActualCompletionRecordKeys D S := by
  intro r hr
  obtain ⟨i, hi, hir⟩ := Finset.mem_image.mp hr
  have hslot := (Finset.mem_filter.mp hi).2
  have hleft : (completionTriangleEnds v i).1 ∈ S := by
    simpa [completionTriangleEnds] using hSelected (completionTriangleIndexPair i).1 hslot.2.1
  have hright : (completionTriangleEnds v i).2 ∈ S := by
    simpa [completionTriangleEnds] using hSelected (completionTriangleIndexPair i).2 hslot.2.2
  have hlabel : D.label (completionTriangleEnds v i).1
      (completionTriangleEnds v i).2 ∈ S := by
    rw [hslot.1]
    exact hmarkS
  have hm := completion_triangle_selected_record_mem D T v i S
    hTcard hTsub hCompletion hv hleft hright hlabel
  rw [← hir]
  exact hm

theorem selected_actual_k4_color_records_subset_global
    (D : FiniteCompletionCliqueData α)
    (T : Edge α) (v : Fin 4 → α) (mark : CliqueColor → α)
    (x : CliqueColor) (S : Finset α) (S₀ : Finset (Fin 4))
    (hmarkS : mark x ∈ S)
    (hSelected : ∀ i, i ∈ S₀ → v i ∈ S)
    (hTcard : T.card = 3) (hTsub : T ⊆ D.ground)
    (hCompletion : ∀ j, v j ∈ graphFacetCompletions D.K D.ground T)
    (hv : Function.Injective v) :
    selectedActualK4ColorSlotRecords D T v mark x S₀ ⊆
        selectedActualCompletionRecordKeys D S := by
  intro r hr
  obtain ⟨i, hi, hir⟩ := Finset.mem_image.mp hr
  have hslot := (Finset.mem_filter.mp hi).2
  have hleft : (completionK4Ends v i).1 ∈ S := by
    simpa [completionK4Ends] using hSelected (completionK4IndexPair i).1 hslot.2.1
  have hright : (completionK4Ends v i).2 ∈ S := by
    simpa [completionK4Ends] using hSelected (completionK4IndexPair i).2 hslot.2.2
  have hlabel : D.label (completionK4Ends v i).1
      (completionK4Ends v i).2 ∈ S := by
    rw [hslot.1]
    exact hmarkS
  have hm := completion_k4_selected_record_mem D T v i S
    hTcard hTsub hCompletion hv hleft hright hlabel
  rw [← hir]
  exact hm

theorem selected_actual_triangle_color_undirected_records_subset_global
    (D : FiniteCompletionCliqueData α)
    (T : Edge α) (v : Fin 3 → α) (mark : CliqueColor → α)
    (x : CliqueColor) (S : Finset α) (S₀ : Finset (Fin 3))
    (hmarkS : mark x ∈ S)
    (hSelected : ∀ i, i ∈ S₀ → v i ∈ S)
    (hTcard : T.card = 3) (hTsub : T ⊆ D.ground)
    (hCompletion : ∀ j, v j ∈ graphFacetCompletions D.K D.ground T)
    (hv : Function.Injective v) :
    (selectedActualTriangleColorSlotRecords D T v mark x S₀).image
      (fun p => (p.1, ({p.2.1, p.2.2} : Edge α))) ⊆
        selectedUndirectedCompletionRecordKeys D S := by
  apply directed_selected_records_forget_orientation_subset
  exact selected_actual_triangle_color_records_subset_global
    D T v mark x S S₀ hmarkS hSelected hTcard hTsub hCompletion hv

theorem selected_actual_k4_color_undirected_records_subset_global
    (D : FiniteCompletionCliqueData α)
    (T : Edge α) (v : Fin 4 → α) (mark : CliqueColor → α)
    (x : CliqueColor) (S : Finset α) (S₀ : Finset (Fin 4))
    (hmarkS : mark x ∈ S)
    (hSelected : ∀ i, i ∈ S₀ → v i ∈ S)
    (hTcard : T.card = 3) (hTsub : T ⊆ D.ground)
    (hCompletion : ∀ j, v j ∈ graphFacetCompletions D.K D.ground T)
    (hv : Function.Injective v) :
    (selectedActualK4ColorSlotRecords D T v mark x S₀).image
      (fun p => (p.1, ({p.2.1, p.2.2} : Edge α))) ⊆
        selectedUndirectedCompletionRecordKeys D S := by
  apply directed_selected_records_forget_orientation_subset
  exact selected_actual_k4_color_records_subset_global
    D T v mark x S S₀ hmarkS hSelected hTcard hTsub hCompletion hv

omit [Fintype α] in
theorem selected_triangle_color_records_disjoint_across_facets
    (D : FiniteCompletionCliqueData α)
    (T T' : Edge α) (v w : Fin 3 → α) (mark : CliqueColor → α)
    (x y : CliqueColor) (S S' : Finset (Fin 3)) (hTT' : T ≠ T')
    (hTcard : T.card = 3) (hTsub : T ⊆ D.ground)
    (hTCompletion : ∀ i, v i ∈ graphFacetCompletions D.K D.ground T)
    (hv : Function.Injective v)
    (hT'card : T'.card = 3) (hT'sub : T' ⊆ D.ground)
    (hT'Completion : ∀ i, w i ∈ graphFacetCompletions D.K D.ground T')
    (hw : Function.Injective w) :
    Disjoint (selectedActualTriangleColorSlotRecords D T v mark x S)
      (selectedActualTriangleColorSlotRecords D T' w mark y S') := by
  apply Finset.disjoint_left.mpr
  intro r hr hs
  obtain ⟨i, _, hri⟩ := Finset.mem_image.mp hr
  obtain ⟨j, _, hrj⟩ := Finset.mem_image.mp hs
  have hFacet := completion_triangle_record_key_eq_implies_facet_eq
    D T T' v w i j hTcard hTsub hTCompletion hv hT'card hT'sub
    hT'Completion hw (hri.trans hrj.symm)
  exact hTT' hFacet

omit [Fintype α] in
theorem selected_k4_color_records_disjoint_across_facets
    (D : FiniteCompletionCliqueData α)
    (T T' : Edge α) (v w : Fin 4 → α) (mark : CliqueColor → α)
    (x y : CliqueColor) (S S' : Finset (Fin 4)) (hTT' : T ≠ T')
    (hTcard : T.card = 3) (hTsub : T ⊆ D.ground)
    (hTCompletion : ∀ i, v i ∈ graphFacetCompletions D.K D.ground T)
    (hv : Function.Injective v)
    (hT'card : T'.card = 3) (hT'sub : T' ⊆ D.ground)
    (hT'Completion : ∀ i, w i ∈ graphFacetCompletions D.K D.ground T')
    (hw : Function.Injective w) :
    Disjoint (selectedActualK4ColorSlotRecords D T v mark x S)
      (selectedActualK4ColorSlotRecords D T' w mark y S') := by
  apply Finset.disjoint_left.mpr
  intro r hr hs
  obtain ⟨i, _, hri⟩ := Finset.mem_image.mp hr
  obtain ⟨j, _, hrj⟩ := Finset.mem_image.mp hs
  have hFacet := completion_k4_record_key_eq_implies_facet_eq
    D T T' v w i j hTcard hTsub hTCompletion hv hT'card hT'sub
    hT'Completion hw (hri.trans hrj.symm)
  exact hTT' hFacet

omit [Fintype α] in
theorem selected_triangle_undirected_records_disjoint_across_facets
    (D : FiniteCompletionCliqueData α)
    (T T' : Edge α) (v w : Fin 3 → α) (mark mark' : CliqueColor → α)
    (x y : CliqueColor) (S S' : Finset (Fin 3)) (hTT' : T ≠ T')
    (hTcard : T.card = 3) (hTsub : T ⊆ D.ground)
    (hTCompletion : ∀ i, v i ∈ graphFacetCompletions D.K D.ground T)
    (hv : Function.Injective v)
    (hT'card : T'.card = 3) (hT'sub : T' ⊆ D.ground)
    (hT'Completion : ∀ i, w i ∈ graphFacetCompletions D.K D.ground T')
    (hw : Function.Injective w) :
    Disjoint (selectedActualTriangleUndirectedColorSlotRecords D T v mark x S)
      (selectedActualTriangleUndirectedColorSlotRecords D T' w mark' y S') := by
  apply Finset.disjoint_left.mpr
  intro r hr hs
  obtain ⟨i, _, hri⟩ := Finset.mem_image.mp hr
  obtain ⟨j, _, hrj⟩ := Finset.mem_image.mp hs
  have hFacet := actual_triangle_undirected_key_eq_implies_facet_eq
    D T T' v w i j hTcard hTsub hTCompletion hv hT'card hT'sub
    hT'Completion hw (hri.trans hrj.symm)
  exact hTT' hFacet

omit [Fintype α] in
theorem selected_k4_undirected_records_disjoint_across_facets
    (D : FiniteCompletionCliqueData α)
    (T T' : Edge α) (v w : Fin 4 → α) (mark mark' : CliqueColor → α)
    (x y : CliqueColor) (S S' : Finset (Fin 4)) (hTT' : T ≠ T')
    (hTcard : T.card = 3) (hTsub : T ⊆ D.ground)
    (hTCompletion : ∀ i, v i ∈ graphFacetCompletions D.K D.ground T)
    (hv : Function.Injective v)
    (hT'card : T'.card = 3) (hT'sub : T' ⊆ D.ground)
    (hT'Completion : ∀ i, w i ∈ graphFacetCompletions D.K D.ground T')
    (hw : Function.Injective w) :
    Disjoint (selectedActualK4UndirectedColorSlotRecords D T v mark x S)
      (selectedActualK4UndirectedColorSlotRecords D T' w mark' y S') := by
  apply Finset.disjoint_left.mpr
  intro r hr hs
  obtain ⟨i, _, hri⟩ := Finset.mem_image.mp hr
  obtain ⟨j, _, hrj⟩ := Finset.mem_image.mp hs
  have hFacet := actual_k4_undirected_key_eq_implies_facet_eq
    D T T' v w i j hTcard hTsub hTCompletion hv hT'card hT'sub
    hT'Completion hw (hri.trans hrj.symm)
  exact hTT' hFacet

omit [Fintype α] in
theorem selected_triangle_k4_undirected_records_disjoint_across_facets
    (D : FiniteCompletionCliqueData α)
    (T T' : Edge α) (v : Fin 3 → α) (w : Fin 4 → α)
    (mark mark' : CliqueColor → α) (x y : CliqueColor)
    (S : Finset (Fin 3)) (S' : Finset (Fin 4)) (hTT' : T ≠ T')
    (hTcard : T.card = 3) (hTsub : T ⊆ D.ground)
    (hTCompletion : ∀ i, v i ∈ graphFacetCompletions D.K D.ground T)
    (hv : Function.Injective v)
    (hT'card : T'.card = 3) (hT'sub : T' ⊆ D.ground)
    (hT'Completion : ∀ i, w i ∈ graphFacetCompletions D.K D.ground T')
    (hw : Function.Injective w) :
    Disjoint (selectedActualTriangleUndirectedColorSlotRecords D T v mark x S)
      (selectedActualK4UndirectedColorSlotRecords D T' w mark' y S') := by
  apply Finset.disjoint_left.mpr
  intro r hr hs
  obtain ⟨i, _, hri⟩ := Finset.mem_image.mp hr
  obtain ⟨j, _, hrj⟩ := Finset.mem_image.mp hs
  have hFacet := actual_triangle_k4_undirected_key_eq_implies_facet_eq
    D T T' v w i j hTcard hTsub hTCompletion hv hT'card hT'sub
    hT'Completion hw (hri.trans hrj.symm)
  exact hTT' hFacet

omit [Fintype α] in
theorem selected_actual_triangle_undirected_color_slots_disjoint
    (D : FiniteCompletionCliqueData α) (T : Edge α) (v : Fin 3 → α)
    (mark : CliqueColor → α) {x y : CliqueColor} (hxy : x ≠ y)
    (S S' : Finset (Fin 3)) (hv : Function.Injective v)
    (hmark : Function.Injective mark) :
    Disjoint (selectedActualTriangleUndirectedColorSlotRecords D T v mark x S)
      (selectedActualTriangleUndirectedColorSlotRecords D T v mark y S') := by
  apply Finset.disjoint_left.mpr
  intro r hr hs
  obtain ⟨i, hi, hri⟩ := Finset.mem_image.mp hr
  obtain ⟨j, hj, hrj⟩ := Finset.mem_image.mp hs
  have hij : i = j := actual_triangle_undirected_record_key_injective D T v hv
    (hri.trans hrj.symm)
  subst j
  have hcol := (Finset.mem_filter.mp hi).2.1
  have hcol' := (Finset.mem_filter.mp hj).2.1
  exact hxy (hmark (hcol.symm.trans hcol'))

omit [Fintype α] in
theorem selected_actual_k4_undirected_color_slots_disjoint
    (D : FiniteCompletionCliqueData α) (T : Edge α) (v : Fin 4 → α)
    (mark : CliqueColor → α) {x y : CliqueColor} (hxy : x ≠ y)
    (S S' : Finset (Fin 4)) (hv : Function.Injective v)
    (hmark : Function.Injective mark) :
    Disjoint (selectedActualK4UndirectedColorSlotRecords D T v mark x S)
      (selectedActualK4UndirectedColorSlotRecords D T v mark y S') := by
  apply Finset.disjoint_left.mpr
  intro r hr hs
  obtain ⟨i, hi, hri⟩ := Finset.mem_image.mp hr
  obtain ⟨j, hj, hrj⟩ := Finset.mem_image.mp hs
  have hij : i = j := actual_k4_undirected_record_key_injective D T v hv
    (hri.trans hrj.symm)
  subst j
  have hcol := (Finset.mem_filter.mp hi).2.1
  have hcol' := (Finset.mem_filter.mp hj).2.1
  exact hxy (hmark (hcol.symm.trans hcol'))

theorem selected_actual_triangle_undirected_records_subset_global
    (D : FiniteCompletionCliqueData α) (T : Edge α) (v : Fin 3 → α)
    (mark : CliqueColor → α) (x : CliqueColor) (S : Finset α)
    (S₀ : Finset (Fin 3)) (hmarkS : mark x ∈ S)
    (hSelected : ∀ i, i ∈ S₀ → v i ∈ S)
    (hTcard : T.card = 3) (hTsub : T ⊆ D.ground)
    (hCompletion : ∀ i, v i ∈ graphFacetCompletions D.K D.ground T)
    (hv : Function.Injective v) :
    selectedActualTriangleUndirectedColorSlotRecords D T v mark x S₀ ⊆
      selectedUndirectedCompletionRecordKeys D S := by
  rw [selected_actual_triangle_undirected_records_eq_forget]
  apply directed_selected_records_forget_orientation_subset
  exact selected_actual_triangle_color_records_subset_global
    D T v mark x S S₀ hmarkS hSelected hTcard hTsub hCompletion hv

theorem selected_actual_k4_undirected_records_subset_global
    (D : FiniteCompletionCliqueData α) (T : Edge α) (v : Fin 4 → α)
    (mark : CliqueColor → α) (x : CliqueColor) (S : Finset α)
    (S₀ : Finset (Fin 4)) (hmarkS : mark x ∈ S)
    (hSelected : ∀ i, i ∈ S₀ → v i ∈ S)
    (hTcard : T.card = 3) (hTsub : T ⊆ D.ground)
    (hCompletion : ∀ i, v i ∈ graphFacetCompletions D.K D.ground T)
    (hv : Function.Injective v) :
    selectedActualK4UndirectedColorSlotRecords D T v mark x S₀ ⊆
      selectedUndirectedCompletionRecordKeys D S := by
  rw [selected_actual_k4_undirected_records_eq_forget]
  apply directed_selected_records_forget_orientation_subset
  exact selected_actual_k4_color_records_subset_global
    D T v mark x S S₀ hmarkS hSelected hTcard hTsub hCompletion hv

end JSP523.Rank4
