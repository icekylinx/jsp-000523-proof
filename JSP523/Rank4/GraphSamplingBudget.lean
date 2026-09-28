import JSP523.Rank4.GraphEdgeAccounting
import Mathlib.Data.Finset.Powerset

/-!
# Finite vertex sampling for the rank-four star budget

The graph potential of III.B.5 applies to every induced sample.  The
sampled graph below retains the original vertex type and isolates all
vertices outside the sample, so common-neighbor and edge events can later
be counted by ordinary finite-set incidence.
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Restrict a finite graph to a selected set while retaining its original
vertex type. -/
def sampledGraph (F : SimpleGraph α) (S : Finset α) : SimpleGraph α where
  Adj a b := F.Adj a b ∧ a ∈ S ∧ b ∈ S
  symm := ⟨by
    intro a b hab
    exact ⟨hab.1.symm, hab.2.2, hab.2.1⟩⟩
  loopless := ⟨by
    intro a haa
    exact F.loopless.irrefl a haa.1⟩

instance sampledGraph_decidableRel
    (F : SimpleGraph α) [DecidableRel F.Adj] (S : Finset α) :
    DecidableRel (sampledGraph F S).Adj := by
  intro a b
  change Decidable (F.Adj a b ∧ a ∈ S ∧ b ∈ S)
  infer_instance

omit [Fintype α] [DecidableEq α] in
theorem sampledGraph_adj (F : SimpleGraph α) (S : Finset α)
    (a b : α) :
    (sampledGraph F S).Adj a b ↔ F.Adj a b ∧ a ∈ S ∧ b ∈ S :=
  Iff.rfl

/-- An edge survives precisely when both its endpoints are sampled. -/
theorem sampledGraph_edgeFinset_eq_filter
    (F : SimpleGraph α) [DecidableRel F.Adj] (S : Finset α) :
    (sampledGraph F S).edgeFinset =
      F.edgeFinset.filter fun e => e.toFinset ⊆ S := by
  classical
  ext e
  induction e using Sym2.inductionOn with
  | hf a b =>
      simp [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        sampledGraph_adj, Finset.subset_iff]

/-- Vertex support also controls the two endpoints of each edge record. -/
theorem edge_support_of_adj_support
    (F : SimpleGraph α) [DecidableRel F.Adj]
    (V : Finset α)
    (hSupport : ∀ a b, F.Adj a b → a ∈ V ∧ b ∈ V) :
    ∀ e ∈ F.edgeFinset, e.toFinset ⊆ V := by
  classical
  intro e he
  induction e using Sym2.inductionOn with
  | hf a b =>
      have hab : F.Adj a b := by
        simpa [SimpleGraph.mem_edgeFinset,
          SimpleGraph.mem_edgeSet] using he
      obtain ⟨ha, hb⟩ := hSupport a b hab
      simpa [Sym2.toFinset_mk_eq, Finset.insert_subset_iff] using
        (show a ∈ V ∧ b ∈ V from ⟨ha, hb⟩)

/-- Every sampled graph inherits the unmarked graph potential. -/
theorem sampled_graph_potential
    (F : SimpleGraph α) [DecidableRel F.Adj] (S : Finset α) :
    2 * ((sampledGraph F S).edgeFinset.card : ℚ) ≤
      orderedCommonPairCount (sampledGraph F S) +
      activeVertexCount (sampledGraph F S) := by
  classical
  have h := graphDeficit_nonneg (sampledGraph F S)
  unfold graphDeficit at h
  linarith

/-- Summing the graph potential over all fixed-size samples is the
finite starting point of (III.B.13). -/
theorem summed_sampled_graph_potential
    (F : SimpleGraph α) [DecidableRel F.Adj]
    (V : Finset α) (m : ℕ) :
    2 * (∑ S ∈ V.powersetCard m,
      ((sampledGraph F S).edgeFinset.card : ℚ)) ≤
      (∑ S ∈ V.powersetCard m,
        orderedCommonPairCount (sampledGraph F S)) +
      (∑ S ∈ V.powersetCard m,
        activeVertexCount (sampledGraph F S)) := by
  classical
  have h := Finset.sum_le_sum (s := V.powersetCard m)
    (fun S _ => sampled_graph_potential F S)
  simpa only [Finset.mul_sum, Finset.sum_add_distrib] using h

/-- An edge of the original graph appears in exactly the fixed-size
samples containing its two endpoints. -/
theorem sum_sampled_edge_count
    (F : SimpleGraph α) [DecidableRel F.Adj]
    (V : Finset α) (m : ℕ)
    (hm : 2 ≤ m)
    (hSupport : ∀ e ∈ F.edgeFinset, e.toFinset ⊆ V) :
    (∑ S ∈ V.powersetCard m,
      (sampledGraph F S).edgeFinset.card) =
        F.edgeFinset.card * (V.card - 2).choose (m - 2) := by
  classical
  calc
    (∑ S ∈ V.powersetCard m,
        (sampledGraph F S).edgeFinset.card) =
      ∑ S ∈ V.powersetCard m,
        (F.edgeFinset.filter fun e => e.toFinset ⊆ S).card := by
          apply Finset.sum_congr rfl
          intro S _
          rw [sampledGraph_edgeFinset_eq_filter]
    _ = ∑ S ∈ V.powersetCard m,
          ∑ e ∈ F.edgeFinset, if e.toFinset ⊆ S then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro S _
          rw [Finset.card_filter]
    _ = ∑ e ∈ F.edgeFinset,
          ∑ S ∈ V.powersetCard m,
            if e.toFinset ⊆ S then 1 else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ e ∈ F.edgeFinset,
          ((V.card - 2).choose (m - 2)) := by
          apply Finset.sum_congr rfl
          intro e he
          rw [← Finset.card_filter]
          have heCard : e.toFinset.card = 2 :=
            F.card_toFinset_mem_edgeFinset ⟨e, he⟩
          rw [Finset.card_filter_powersetCard_subset
            e.toFinset V m (hSupport e he)]
          · rw [heCard]
          · omega
    _ = F.edgeFinset.card * (V.card - 2).choose (m - 2) := by
          simp [Finset.sum_const, mul_comm]

/-- Every nonisolated vertex of the sampled graph belongs to the sample. -/
theorem sampled_active_vertex_in_sample
    (F : SimpleGraph α) [DecidableRel F.Adj]
    (S : Finset α) (x : α)
    (hx : 0 < (sampledGraph F S).degree x) : x ∈ S := by
  classical
  have hNbr : 0 < ((sampledGraph F S).neighborFinset x).card := hx
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hNbr
  have hAdj : (sampledGraph F S).Adj x y := by
    simpa [SimpleGraph.mem_neighborFinset] using hy
  exact (sampledGraph_adj F S x y).mp hAdj |>.2.1

/-- The active-vertex term in a sampled graph is at most the sample size. -/
theorem sampled_active_count_le_card
    (F : SimpleGraph α) [DecidableRel F.Adj] (S : Finset α) :
    activeVertexCount (sampledGraph F S) ≤ S.card := by
  classical
  have hPoint (x : α) :
      (if 0 < (sampledGraph F S).degree x then (1 : ℚ) else 0) ≤
        if x ∈ S then 1 else 0 := by
    by_cases hx : 0 < (sampledGraph F S).degree x
    · have hxS := sampled_active_vertex_in_sample F S x hx
      simp [hx, hxS]
    · simp only [hx, ↓reduceIte]
      split_ifs <;> norm_num
  have hSum := Finset.sum_le_sum (s := Finset.univ)
    (fun x _ => hPoint x)
  have hCard :
      (∑ x : α, if x ∈ S then (1 : ℚ) else 0) = S.card := by
    rw [← Finset.sum_filter]
    simp
  unfold activeVertexCount
  rw [hCard] at hSum
  exact hSum

/-- The total active-vertex payment over fixed-size samples. -/
theorem sum_sampled_active_count_le
    (F : SimpleGraph α) [DecidableRel F.Adj]
    (V : Finset α) (m : ℕ) :
    (∑ S ∈ V.powersetCard m,
      activeVertexCount (sampledGraph F S)) ≤
        (m : ℚ) * (V.card.choose m) := by
  classical
  calc
    (∑ S ∈ V.powersetCard m,
        activeVertexCount (sampledGraph F S)) ≤
      ∑ S ∈ V.powersetCard m, (S.card : ℚ) := by
        apply Finset.sum_le_sum
        intro S _
        exact sampled_active_count_le_card F S
    _ = ∑ _S ∈ V.powersetCard m, (m : ℚ) := by
        apply Finset.sum_congr rfl
        intro S hS
        exact congrArg Nat.cast (Finset.mem_powersetCard.mp hS).2
    _ = (m : ℚ) * (V.card.choose m) := by
        simp [Finset.sum_const, Finset.card_powersetCard, mul_comm]

/-- A common neighbor surviving a sample was already a common neighbor
in the original graph, and the two endpoints and witness lie in the
sample. -/
theorem sampled_common_neighbor_witness
    (F : SimpleGraph α) [DecidableRel F.Adj]
    (S : Finset α) (x y : α)
    (hSample : 0 < graphCommonMultiplicity (sampledGraph F S) x y) :
    ∃ z : α, F.Adj x z ∧ F.Adj y z ∧
      x ∈ S ∧ y ∈ S ∧ z ∈ S := by
  classical
  unfold graphCommonMultiplicity at hSample
  obtain ⟨z, hz⟩ := Finset.card_pos.mp hSample
  obtain ⟨hzNbr, hzAdj⟩ := Finset.mem_filter.mp hz
  have hxz : (sampledGraph F S).Adj x z := by
    simpa [SimpleGraph.mem_neighborFinset] using hzNbr
  obtain ⟨hF, hxS, hzS⟩ := (sampledGraph_adj F S x z).mp hxz
  obtain ⟨hFy, hyS, _⟩ := (sampledGraph_adj F S y z).mp hzAdj
  exact ⟨z, hF, hFy, hxS, hyS, hzS⟩

/-- A sample producing a common-neighbor record for a unique pair must
contain a fixed three-element set of vertices. -/
theorem unique_common_pair_sample_contains_triple
    (F : SimpleGraph α) [DecidableRel F.Adj]
    (x y : α) (hxy : x ≠ y)
    (hUnique : graphCommonMultiplicity F x y = 1) :
    ∃ z : α,
      F.Adj x z ∧ F.Adj y z ∧
      ({x, y, z} : Finset α).card = 3 ∧
      (∀ S : Finset α,
        0 < graphCommonMultiplicity (sampledGraph F S) x y →
          ({x, y, z} : Finset α) ⊆ S) := by
  classical
  let N := (F.neighborFinset x).filter fun z => F.Adj y z
  have hN : N.card = 1 := hUnique
  obtain ⟨z, hNeq⟩ := Finset.card_eq_one.mp hN
  have hzN : z ∈ N := by simp [hNeq]
  have hxz : F.Adj x z := by
    simpa [N, SimpleGraph.mem_neighborFinset] using
      (Finset.mem_filter.mp hzN).1
  have hyz : F.Adj y z := (Finset.mem_filter.mp hzN).2
  have hxzNe : x ≠ z := hxz.ne
  have hyzNe : y ≠ z := hyz.ne
  have hCard : ({x, y, z} : Finset α).card = 3 := by
    simp [Finset.card_insert_of_notMem, hxy, hxzNe, hyzNe]
  refine ⟨z, hxz, hyz, hCard, ?_⟩
  intro S hSample
  obtain ⟨t, hxt, hyt, hxS, hyS, htS⟩ :=
    sampled_common_neighbor_witness F S x y hSample
  have htN : t ∈ N := by
    apply Finset.mem_filter.mpr
    exact ⟨by simpa [SimpleGraph.mem_neighborFinset] using hxt, hyt⟩
  have htz : t = z := by
    rw [hNeq] at htN
    simpa using htN
  intro w hw
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact hxS
  · exact hyS
  · exact htz ▸ htS

/-- Fixed-size samples in which an ordered pair retains a common
neighbor. -/
def sampledCommonPairEvents
    (F : SimpleGraph α) [DecidableRel F.Adj]
    (V : Finset α) (m : ℕ) (x y : α) : Finset (Finset α) :=
  (V.powersetCard m).filter fun S =>
    0 < graphCommonMultiplicity (sampledGraph F S) x y

/-- An actual unique common-neighbor record survives in at most as many
samples as contain its fixed endpoint-and-witness triple. -/
theorem sampled_unique_pair_event_count_le
    (F : SimpleGraph α) [DecidableRel F.Adj]
    (V : Finset α) (m : ℕ) (hm : 3 ≤ m)
    (hSupport : ∀ a b, F.Adj a b → a ∈ V ∧ b ∈ V)
    (x y : α) (hxy : x ≠ y)
    (hUnique : graphCommonMultiplicity F x y = 1) :
    (sampledCommonPairEvents F V m x y).card ≤
      (V.card - 3).choose (m - 3) := by
  classical
  obtain ⟨z, hxz, hyz, hCard, hContain⟩ :=
    unique_common_pair_sample_contains_triple F x y hxy hUnique
  let T : Finset α := {x, y, z}
  have hTV : T ⊆ V := by
    intro w hw
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with hwx | hwy | hwz
    · exact hwx ▸ (hSupport x z hxz).1
    · exact hwy ▸ (hSupport y z hyz).1
    · exact hwz ▸ (hSupport x z hxz).2
  have hSub : sampledCommonPairEvents F V m x y ⊆
      (V.powersetCard m).filter fun S => T ⊆ S := by
    intro S hS
    have hS' := Finset.mem_filter.mp hS
    exact Finset.mem_filter.mpr
      ⟨hS'.1, hContain S hS'.2⟩
  have hBound := Finset.card_le_card hSub
  have hTcard : T.card = 3 := hCard
  have hTm : T.card ≤ m := by omega
  rw [Finset.card_filter_powersetCard_subset T V m hTV hTm] at hBound
  simpa only [hTcard] using hBound

/-- With no multiplicity restriction, retaining a common-neighbor record
still requires sampling its two endpoints. -/
theorem sampled_pair_event_count_le
    (F : SimpleGraph α) [DecidableRel F.Adj]
    (V : Finset α) (m : ℕ) (hm : 2 ≤ m)
    (hSupport : ∀ a b, F.Adj a b → a ∈ V ∧ b ∈ V)
    (x y : α) (hxy : x ≠ y) :
    (sampledCommonPairEvents F V m x y).card ≤
      (V.card - 2).choose (m - 2) := by
  classical
  let P : Finset α := {x, y}
  by_cases hEvent : (sampledCommonPairEvents F V m x y).Nonempty
  · obtain ⟨S, hS⟩ := hEvent
    have hWitness := sampled_common_neighbor_witness F S x y
      (Finset.mem_filter.mp hS).2
    obtain ⟨z, hxz, hyz, _, _, _⟩ := hWitness
    have hPV : P ⊆ V := by
      intro w hw
      simp only [P, Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with hwx | hwy
      · exact hwx ▸ (hSupport x z hxz).1
      · exact hwy ▸ (hSupport y z hyz).1
    have hSub : sampledCommonPairEvents F V m x y ⊆
        (V.powersetCard m).filter fun S => P ⊆ S := by
      intro R hR
      obtain ⟨_, _, _, hxR, hyR, _⟩ :=
        sampled_common_neighbor_witness F R x y
          (Finset.mem_filter.mp hR).2
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hR).1, by
          intro w hw
          simp only [P, Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl
          · exact hxR
          · exact hyR⟩
    have hBound := Finset.card_le_card hSub
    have hPcard : P.card = 2 := Finset.card_pair hxy
    have hPm : P.card ≤ m := by omega
    rw [Finset.card_filter_powersetCard_subset P V m hPV hPm] at hBound
    simpa only [hPcard] using hBound
  · have hEmpty : sampledCommonPairEvents F V m x y = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hEvent
    simp [hEmpty]

/-- Double-count sample/common-pair incidences, first by the sample and
then by the ordered endpoint pair. -/
theorem sum_sampled_common_pairs_eq_event_counts
    (F : SimpleGraph α) [DecidableRel F.Adj]
    (V : Finset α) (m : ℕ) :
    (∑ S ∈ V.powersetCard m,
      orderedCommonPairCount (sampledGraph F S)) =
    ∑ x : α, ∑ y ∈ (Finset.univ : Finset α).erase x,
      ((sampledCommonPairEvents F V m x y).card : ℚ) := by
  classical
  unfold orderedCommonPairCount
  calc
    (∑ S ∈ V.powersetCard m,
      ∑ x : α, ∑ y ∈ (Finset.univ : Finset α).erase x,
        if 0 < graphCommonMultiplicity (sampledGraph F S) x y
          then (1 : ℚ) else 0) =
      ∑ x : α, ∑ S ∈ V.powersetCard m,
        ∑ y ∈ (Finset.univ : Finset α).erase x,
          if 0 < graphCommonMultiplicity (sampledGraph F S) x y
            then (1 : ℚ) else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ x : α, ∑ y ∈ (Finset.univ : Finset α).erase x,
          ∑ S ∈ V.powersetCard m,
            if 0 < graphCommonMultiplicity (sampledGraph F S) x y
              then (1 : ℚ) else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.sum_comm]
    _ = ∑ x : α, ∑ y ∈ (Finset.univ : Finset α).erase x,
          ((sampledCommonPairEvents F V m x y).card : ℚ) := by
          apply Finset.sum_congr rfl
          intro x _
          apply Finset.sum_congr rfl
          intro y _
          unfold sampledCommonPairEvents
          rw [← Finset.sum_filter]
          simp

/-- A pair with no original common neighbor cannot acquire one by
sampling. -/
theorem sampledCommonPairEvents_eq_empty_of_zero
    (F : SimpleGraph α) [DecidableRel F.Adj]
    (V : Finset α) (m : ℕ) (x y : α)
    (hZero : graphCommonMultiplicity F x y = 0) :
    sampledCommonPairEvents F V m x y = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro S hS
  obtain ⟨z, hxz, hyz, _, _, _⟩ :=
    sampled_common_neighbor_witness F S x y
      (Finset.mem_filter.mp hS).2
  have hz : z ∈ (F.neighborFinset x).filter fun t => F.Adj y t :=
    Finset.mem_filter.mpr
      ⟨by simpa [SimpleGraph.mem_neighborFinset] using hxz, hyz⟩
  have hPos : 0 < graphCommonMultiplicity F x y := by
    unfold graphCommonMultiplicity
    exact Finset.card_pos.mpr ⟨z, hz⟩
  omega

/-- Ordered pairs with at least two common neighbors. -/
def orderedMultiPairCount
    (F : SimpleGraph α) [DecidableRel F.Adj] : ℚ :=
  ∑ x : α, ∑ y ∈ (Finset.univ : Finset α).erase x,
    if 2 ≤ graphCommonMultiplicity F x y then (1 : ℚ) else 0

/-- The exact finite sampling payment by unique versus repeated
common-neighbor records. -/
theorem sum_sampled_common_pairs_le
    (F : SimpleGraph α) [DecidableRel F.Adj]
    (V : Finset α) (m : ℕ) (hm : 3 ≤ m)
    (hSupport : ∀ a b, F.Adj a b → a ∈ V ∧ b ∈ V) :
    (∑ S ∈ V.powersetCard m,
      orderedCommonPairCount (sampledGraph F S)) ≤
      ((V.card - 3).choose (m - 3) : ℚ) *
        orderedUniquePairCount F +
      ((V.card - 2).choose (m - 2) : ℚ) *
        orderedMultiPairCount F := by
  classical
  let c₃ : ℚ := (V.card - 3).choose (m - 3)
  let c₂ : ℚ := (V.card - 2).choose (m - 2)
  have hTerm (x y : α) (hxy : y ∈ (Finset.univ : Finset α).erase x) :
      ((sampledCommonPairEvents F V m x y).card : ℚ) ≤
        c₃ * (if graphCommonMultiplicity F x y = 1 then 1 else 0) +
        c₂ * (if 2 ≤ graphCommonMultiplicity F x y then 1 else 0) := by
    have hne : x ≠ y := by
      exact (Finset.ne_of_mem_erase hxy).symm
    by_cases hOne : graphCommonMultiplicity F x y = 1
    · have hBound := sampled_unique_pair_event_count_le
        F V m hm hSupport x y hne hOne
      have hBoundQ : ((sampledCommonPairEvents F V m x y).card : ℚ) ≤
          c₃ := by
            change ((sampledCommonPairEvents F V m x y).card : ℚ) ≤
              ((V.card - 3).choose (m - 3) : ℚ)
            exact_mod_cast hBound
      simp [hOne, c₃] at *
      exact hBoundQ
    by_cases hMany : 2 ≤ graphCommonMultiplicity F x y
    · have hBound := sampled_pair_event_count_le
        F V m (by omega) hSupport x y hne
      have hBoundQ : ((sampledCommonPairEvents F V m x y).card : ℚ) ≤
          c₂ := by
            change ((sampledCommonPairEvents F V m x y).card : ℚ) ≤
              ((V.card - 2).choose (m - 2) : ℚ)
            exact_mod_cast hBound
      simpa [hOne, hMany, c₂] using hBoundQ
    · have hZero : graphCommonMultiplicity F x y = 0 := by omega
      have hEmpty := sampledCommonPairEvents_eq_empty_of_zero
        F V m x y hZero
      simp [hEmpty, hZero]
  rw [sum_sampled_common_pairs_eq_event_counts]
  calc
    (∑ x : α, ∑ y ∈ (Finset.univ : Finset α).erase x,
      ((sampledCommonPairEvents F V m x y).card : ℚ)) ≤
        ∑ x : α, ∑ y ∈ (Finset.univ : Finset α).erase x,
          (c₃ * (if graphCommonMultiplicity F x y = 1 then 1 else 0) +
           c₂ * (if 2 ≤ graphCommonMultiplicity F x y then 1 else 0)) := by
          apply Finset.sum_le_sum
          intro x _
          apply Finset.sum_le_sum
          intro y hy
          exact hTerm x y hy
    _ = c₃ * orderedUniquePairCount F +
          c₂ * orderedMultiPairCount F := by
          simp only [orderedUniquePairCount, orderedMultiPairCount,
            Finset.sum_add_distrib, Finset.mul_sum]
    _ = ((V.card - 3).choose (m - 3) : ℚ) *
          orderedUniquePairCount F +
        ((V.card - 2).choose (m - 2) : ℚ) *
          orderedMultiPairCount F := by rfl

/-- Fixed-size finite form of the sampling inequality (III.B.13).  The
unique common-neighbor records require a sampled triple; repeated records
are charged only to their sampled endpoint pair. -/
theorem graph_fixed_size_sampling_inequality
    (F : SimpleGraph α) [DecidableRel F.Adj]
    (V : Finset α) (m : ℕ) (hm : 3 ≤ m)
    (hVertexSupport : ∀ a b, F.Adj a b → a ∈ V ∧ b ∈ V) :
    2 * ((V.card - 2).choose (m - 2) : ℚ) *
        (F.edgeFinset.card : ℚ) ≤
      ((V.card - 3).choose (m - 3) : ℚ) *
        orderedUniquePairCount F +
      ((V.card - 2).choose (m - 2) : ℚ) *
        orderedMultiPairCount F +
      (m : ℚ) * (V.card.choose m) := by
  classical
  have hEdgesNat := sum_sampled_edge_count F V m
    (by omega) (edge_support_of_adj_support F V hVertexSupport)
  have hEdges :
      (∑ S ∈ V.powersetCard m,
        ((sampledGraph F S).edgeFinset.card : ℚ)) =
          (F.edgeFinset.card : ℚ) *
            ((V.card - 2).choose (m - 2) : ℚ) := by
    exact_mod_cast hEdgesNat
  have hPotential := summed_sampled_graph_potential F V m
  have hCommon := sum_sampled_common_pairs_le
    F V m hm hVertexSupport
  have hActive := sum_sampled_active_count_le F V m
  rw [hEdges] at hPotential
  nlinarith

end JSP523.Rank4
