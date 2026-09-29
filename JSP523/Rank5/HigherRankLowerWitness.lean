import JSP523.Rank5.HigherRankFacetWitness

/-! # Lower-deletion witnesses with three-element roots

The lower core has size n, the upper core n+1, and parent edges n+3.
This is the s=3 pinned upper count in IV.9.3.
-/
namespace JSP523.Rank5.HigherRankLower
variable {α : Type*} [DecidableEq α] (n : ℕ)

noncomputable def parentTripleLink (K : Family α) (V B : Edge α) : Family α :=
  actualCoreLink K V B 3

theorem mem_parent_triple_link {K : Family α} {V B R : Edge α} :
    R ∈ parentTripleLink K V B ↔
      R ⊆ V ∧ R.card = 3 ∧ Disjoint R B ∧ B ∪ R ∈ K :=
  mem_actual_core_link

noncomputable def badIncidences
    (K : Family α) (V : Edge α) (m : ℕ)
    (upper lower : Edge α → α) : Finset ((Edge α × Edge α) × α) := by
  classical
  exact ((K ×ˢ V.powersetCard m) ×ˢ V).filter fun i =>
    i.1.2 ⊆ i.1.1 ∧ i.1.2 ∈ V.powersetCard m ∧
      i.2 ∈ i.1.2 ∧ i.2 ≠ upper i.1.2 ∧ lower (i.1.2.erase i.2) ≠ upper i.1.2

theorem actual_strong_partner_symm
    (H : Family α) (V P Q : Edge α) (k t : ℕ) (z : α)
    (hP : P ∈ V.powersetCard 3)
    (hStrong : ActualStrongPartner H V P Q 3 k t z) :
    ActualStrongPartner H V Q P 3 k t z := by
  have hCell := common_prefix_tails_comm H V P Q k
  refine ⟨hP, hStrong.2.1.symm, ?_, ?_⟩
  · rw [← hCell]
    exact hStrong.2.2.1
  · rw [← hCell]
    exact hStrong.2.2.2

noncomputable def badTriplePartners (H : Family α) (V B R : Edge α)
    (good : Edge α → Edge α → Edge α → Prop) : Family α := by
  classical
  exact (parentTripleLink H V B).filter fun T => ¬ good B R T

def lowerWitnessCore (i : (Edge α × Edge α) × α) : Edge α :=
  i.1.2.erase i.2

def lowerWitnessRoot (i : (Edge α × Edge α) × α) : Edge α :=
  i.1.1 \ lowerWitnessCore i

noncomputable def lowerWitnessSecondRoots
    (K : Family α) (V : Edge α) (i : (Edge α × Edge α) × α) :
    Family α := by
  classical
  exact (parentTripleLink K V (lowerWitnessCore i)).filter fun R₁ =>
    lowerWitnessRoot i ∩ R₁ = {i.2}

def lowerWitnessTuple
    (w : (_i : (Edge α × Edge α) × α) × ((_R₁ : Edge α) × Edge α)) :
    ((Edge α × Edge α) × (Edge α × Edge α)) × α :=
  (((lowerWitnessCore w.1, lowerWitnessRoot w.1),
    (w.2.1, w.2.2)), w.1.2)

def lowerWitnessPinnedKey
    (w : (_i : (Edge α × Edge α) × α) × ((_R₁ : Edge α) × Edge α)) :
    (((Edge α × Edge α) × α) × Edge α) :=
  (((lowerWitnessRoot w.1, w.2.2), w.1.2), w.2.1)

def lowerWitnessTripleKey
    (w : (_i : (Edge α × Edge α) × α) × ((_R₁ : Edge α) × Edge α)) :
    (Edge α × Edge α) × α :=
  ((lowerWitnessRoot w.1, w.2.2), w.1.2)

def lowerWitnessTripleKeys (V : Edge α) :
    Finset ((Edge α × Edge α) × α) :=
  ((V.powersetCard 3) ×ˢ (V.powersetCard 3)).biUnion fun p =>
    p.1.image fun a => (p, a)

theorem lower_witness_triple_keys_card_le
    (V : Edge α) :
    (lowerWitnessTripleKeys V).card ≤
      3 * (V.powersetCard 3).card ^ 2 := by
  classical
  let P := V.powersetCard 3
  calc
    (lowerWitnessTripleKeys V).card ≤
        ∑ p ∈ P ×ˢ P, (p.1.image fun a => (p, a)).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ p ∈ P ×ˢ P, p.1.card := by
      apply Finset.sum_le_sum
      intro p hp
      exact Finset.card_image_le
    _ = ∑ _p ∈ P ×ˢ P, 3 := by
      apply Finset.sum_congr rfl
      intro p hp
      exact (Finset.mem_powersetCard.mp (Finset.mem_product.mp hp).1).2
    _ = 3 * P.card ^ 2 := by
      simp [pow_two, mul_comm]

theorem lower_bad_incidence_labels_in_core
    (K : Family α) (V : Edge α)
    (facetCenter tripleLabel : Edge α → α)
    (hFacetCenter : ActualRankLabels K (n + 1) facetCenter)
    (hTripleLabels : ActualRankLabels K n tripleLabel)
    {i : (Edge α × Edge α) × α}
    (hi : i ∈ badIncidences K V (n + 1) facetCenter tripleLabel) :
    facetCenter i.1.2 ∈ lowerWitnessCore i ∧
      tripleLabel (lowerWitnessCore i) ∈ lowerWitnessCore i ∧
      facetCenter i.1.2 ≠ tripleLabel (lowerWitnessCore i) := by
  have hSource := (Finset.mem_filter.mp hi).1
  have hE : i.1.1 ∈ K :=
    (Finset.mem_product.mp (Finset.mem_product.mp hSource).1).1
  have hAcard : i.1.2.card = n + 1 :=
    (Finset.mem_powersetCard.mp
      (Finset.mem_product.mp (Finset.mem_product.mp hSource).1).2).2
  have hParts := (Finset.mem_filter.mp hi).2
  have hAE : i.1.2 ⊆ i.1.1 := hParts.1
  have hShared : i.1.2 ∈ V.powersetCard (n + 1) := hParts.2.1
  have ha : i.2 ∈ i.1.2 := hParts.2.2.1
  have hNotCenter : i.2 ≠ facetCenter i.1.2 := hParts.2.2.2.1
  have hMismatch : tripleLabel (i.1.2.erase i.2) ≠
      facetCenter i.1.2 := hParts.2.2.2.2
  have hBcard : (lowerWitnessCore i).card = n := by
    have herase := Finset.card_erase_add_one ha
    change (i.1.2.erase i.2).card = n
    omega
  have hBE : lowerWitnessCore i ⊆ i.1.1 :=
    (Finset.erase_subset i.2 i.1.2).trans hAE
  refine ⟨?_, hTripleLabels (lowerWitnessCore i)
    ⟨i.1.1, hE, hBE⟩ hBcard, ?_⟩
  · exact Finset.mem_erase.mpr
      ⟨hNotCenter.symm, hFacetCenter i.1.2 ⟨i.1.1, hE, hAE⟩ hAcard⟩
  · exact hMismatch.symm

theorem lower_bad_incidence_core_eq_parent_sdiff_root
    (K : Family α) (V : Edge α)
    (facetCenter tripleLabel : Edge α → α)
    {i : (Edge α × Edge α) × α}
    (hi : i ∈ badIncidences K V (n + 1) facetCenter tripleLabel) :
    lowerWitnessCore i = i.1.1 \ lowerWitnessRoot i := by
  have hAE : i.1.2 ⊆ i.1.1 := (Finset.mem_filter.mp hi).2.1
  have hBE : lowerWitnessCore i ⊆ i.1.1 :=
    (Finset.erase_subset i.2 i.1.2).trans hAE
  exact (Finset.sdiff_sdiff_eq_self hBE).symm

noncomputable def lowerWitnessThirdRoots
    (H : Family α) (V : Edge α) (t : ℕ)
    (tripleLabel : Edge α → α)
    (i : (Edge α × Edge α) × α) (R₁ : Edge α) : Family α := by
  classical
  let B := lowerWitnessCore i
  let R₀ := lowerWitnessRoot i
  exact (parentTripleLink H V B).filter fun T =>
    Disjoint T (R₀ ∪ R₁) ∧
      ActualStrongPartner H V R₀ T 3 n t (tripleLabel B) ∧
      ActualStrongPartner H V R₁ T 3 n t (tripleLabel B)

theorem lower_third_roots_half_of_retained_partner_bounds
    (K H : Family α) (V : Edge α) (t q : ℕ)
    (tripleLabel : Edge α → α)
    (hKH : K ⊆ H)
    (i : (Edge α × Edge α) × α) (R₁ : Edge α)
    (hLarge : 4 * q ≤ (parentTripleLink K V (lowerWitnessCore i)).card)
    (hBad₀ : (badTriplePartners H V (lowerWitnessCore i)
      (lowerWitnessRoot i)
      (fun B P T => ActualStrongPartner H V P T 3 n t (tripleLabel B))).card ≤ q)
    (hBad₁ : (badTriplePartners H V (lowerWitnessCore i) R₁
      (fun B P T => ActualStrongPartner H V P T 3 n t (tripleLabel B))).card ≤ q) :
    (parentTripleLink K V (lowerWitnessCore i)).card ≤
      2 * (lowerWitnessThirdRoots n H V t tripleLabel i R₁).card := by
  classical
  let B := lowerWitnessCore i
  let R₀ := lowerWitnessRoot i
  let L := parentTripleLink K V B
  let strong₀ : Edge α → Prop := fun T =>
    ActualStrongPartner H V R₀ T 3 n t (tripleLabel B)
  let strong₁ : Edge α → Prop := fun T =>
    ActualStrongPartner H V R₁ T 3 n t (tripleLabel B)
  let bad₀ := L.filter fun T => ¬ strong₀ T
  let bad₁ := L.filter fun T => ¬ strong₁ T
  let both := L.filter fun T => strong₀ T ∧ strong₁ T
  have hLinkH : ∀ T ∈ L, T ∈ parentTripleLink H V B := by
    intro T hT
    have hParts := mem_parent_triple_link.mp hT
    exact mem_parent_triple_link.mpr
      ⟨hParts.1, hParts.2.1, hParts.2.2.1, hKH hParts.2.2.2⟩
  have hBad₀Sub : bad₀ ⊆ badTriplePartners H V B R₀
      (fun B P T => ActualStrongPartner H V P T 3 n t (tripleLabel B)) := by
    intro T hT
    have hParts := Finset.mem_filter.mp hT
    change T ∈ (parentTripleLink H V B).filter (fun T => ¬ strong₀ T)
    exact Finset.mem_filter.mpr ⟨hLinkH T hParts.1, hParts.2⟩
  have hBad₁Sub : bad₁ ⊆ badTriplePartners H V B R₁
      (fun B P T => ActualStrongPartner H V P T 3 n t (tripleLabel B)) := by
    intro T hT
    have hParts := Finset.mem_filter.mp hT
    change T ∈ (parentTripleLink H V B).filter (fun T => ¬ strong₁ T)
    exact Finset.mem_filter.mpr ⟨hLinkH T hParts.1, hParts.2⟩
  have hBad₀Card : bad₀.card ≤ q :=
    (Finset.card_le_card hBad₀Sub).trans hBad₀
  have hBad₁Card : bad₁.card ≤ q :=
    (Finset.card_le_card hBad₁Sub).trans hBad₁
  have hCover : L ⊆ bad₀ ∪ bad₁ ∪ both := by
    intro T hT
    by_cases h₀ : strong₀ T
    · by_cases h₁ : strong₁ T
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hT, h₀, h₁⟩)
      · exact Finset.mem_union_left _
          (Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨hT, h₁⟩))
    · exact Finset.mem_union_left _
        (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨hT, h₀⟩))
  have hCard : L.card ≤ bad₀.card + bad₁.card + both.card := by
    have hUnion := Finset.card_le_card hCover
    have hU₀ := Finset.card_union_le bad₀ bad₁
    have hU₁ := Finset.card_union_le (bad₀ ∪ bad₁) both
    omega
  have hBothSub : both ⊆ lowerWitnessThirdRoots n H V t tripleLabel i R₁ := by
    intro T hT
    have hParts := Finset.mem_filter.mp hT
    have hStrong₀ : strong₀ T := hParts.2.1
    have hStrong₁ : strong₁ T := hParts.2.2
    have hDisj : Disjoint T (R₀ ∪ R₁) := by
      apply Finset.disjoint_left.mpr
      intro x hxT hxU
      rcases Finset.mem_union.mp hxU with hx₀ | hx₁
      · exact (Finset.disjoint_left.mp hStrong₀.2.1) hx₀ hxT
      · exact (Finset.disjoint_left.mp hStrong₁.2.1) hx₁ hxT
    change T ∈ (parentTripleLink H V B).filter
      (fun T => Disjoint T (R₀ ∪ R₁) ∧ strong₀ T ∧ strong₁ T)
    exact Finset.mem_filter.mpr
      ⟨hLinkH T hParts.1, hDisj, hStrong₀, hStrong₁⟩
  have hBothCard := Finset.card_le_card hBothSub
  change 4 * q ≤ L.card at hLarge
  change L.card ≤ 2 * (lowerWitnessThirdRoots n H V t tripleLabel i R₁).card
  omega

noncomputable def facetPinnedSecondRoots
    (K H : Family α) (V : Edge α) (t : ℕ)
    (tripleLabel : Edge α → α)
    (i : (Edge α × Edge α) × α) (T : Edge α) : Family α := by
  classical
  exact (lowerWitnessSecondRoots K V i).filter fun R₁ =>
    T ∈ lowerWitnessThirdRoots n H V t tripleLabel i R₁

theorem lower_pinned_second_roots_bound
    (K H : Family α) (V : Edge α) (t D₄ Dₙ : ℕ)
    (tripleLabel : Edge α → α)
    (ht : 1 ≤ t)
    (hD₄ : ∀ S : Edge α, S.card = 4 →
      (H.filter fun E => S ⊆ E).card ≤ D₄)
    (hDₙ : ∀ S : Edge α, S.card = n + 1 →
      (H.filter fun E => S ⊆ E).card ≤ Dₙ)
    (i : (Edge α × Edge α) × α) (T : Edge α) :
    t * (facetPinnedSecondRoots n K H V t tripleLabel i T).card ≤
      D₄ * Dₙ := by
  classical
  let F := facetPinnedSecondRoots n K H V t tripleLabel i T
  by_cases hEmpty : F = ∅
  · change t * F.card ≤ D₄ * Dₙ
    simp [hEmpty]
  have hNonempty : F.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEmpty
  obtain ⟨R₁, hR₁⟩ := hNonempty
  have hThird : T ∈ lowerWitnessThirdRoots n H V t tripleLabel i R₁ :=
    (Finset.mem_filter.mp hR₁).2
  have hThirdParts := Finset.mem_filter.mp hThird
  have hTlink : T ∈ parentTripleLink H V (lowerWitnessCore i) :=
    hThirdParts.1
  have hTcard : T.card = 3 := (mem_parent_triple_link.mp hTlink).2.1
  let z := tripleLabel (lowerWitnessCore i)
  have hStrong₀ : ActualStrongPartner H V (lowerWitnessRoot i) T 3 n t z :=
    hThirdParts.2.2.1
  have hzNotT : z ∉ T := by
    have hCellPos : 0 <
        (commonPrefixTails H V (lowerWitnessRoot i) T n).card := by
      have hThreshold := hStrong₀.2.2.1
      omega
    obtain ⟨C, hC⟩ := Finset.card_pos.mp hCellPos
    have hzC : z ∈ C := hStrong₀.2.2.2.1 C hC
    have hDisjCT : Disjoint C T :=
      (Finset.disjoint_union_right.mp
        (mem_common_prefix_tails.mp hC).2.2.1).2
    intro hzT
    exact (Finset.disjoint_left.mp hDisjCT) hzC hzT
  have hSub : F ⊆ actualCenterPartners H V T 3 n t z {i.2} := by
    intro R hR
    have hSecond : R ∈ lowerWitnessSecondRoots K V i :=
      (Finset.mem_filter.mp hR).1
    have hInter : lowerWitnessRoot i ∩ R = {i.2} :=
      (Finset.mem_filter.mp hSecond).2
    have haR : i.2 ∈ R := by
      have haInter : i.2 ∈ lowerWitnessRoot i ∩ R := by
        rw [hInter]
        simp
      exact (Finset.mem_inter.mp haInter).2
    have hRlink : R ∈ parentTripleLink K V (lowerWitnessCore i) :=
      (Finset.mem_filter.mp hSecond).1
    have hRpow : R ∈ V.powersetCard 3 := by
      exact Finset.mem_powersetCard.mpr
        ⟨(mem_parent_triple_link.mp hRlink).1,
          (mem_parent_triple_link.mp hRlink).2.1⟩
    have hThirdR : T ∈ lowerWitnessThirdRoots n H V t tripleLabel i R :=
      (Finset.mem_filter.mp hR).2
    have hStrongR : ActualStrongPartner H V R T 3 n t z :=
      (Finset.mem_filter.mp hThirdR).2.2.2
    have hSymm := actual_strong_partner_symm H V R T n t z hRpow hStrongR
    change R ∈ (V.powersetCard 3).filter
      (fun Q => ActualStrongPartner H V T Q 3 n t z ∧ {i.2} ⊆ Q)
    exact Finset.mem_filter.mpr
      ⟨hRpow, hSymm, Finset.singleton_subset_iff.mpr haR⟩
  have hPinned := repeated_center_partner_bound_from_codegrees
    H V T 3 n t z {i.2} 1 D₄ Dₙ
    hTcard hzNotT (by simp) hD₄ hDₙ
  have hCard := Finset.card_le_card hSub
  exact (Nat.mul_le_mul_left t hCard).trans hPinned

noncomputable def lowerWitnessesFor
    (K H : Family α) (V : Edge α) (t : ℕ)
    (tripleLabel : Edge α → α)
    (i : (Edge α × Edge α) × α) :
    Finset ((_R₁ : Edge α) × Edge α) := by
  classical
  exact (lowerWitnessSecondRoots K V i).sigma
    (lowerWitnessThirdRoots n H V t tripleLabel i)

noncomputable def lowerInheritanceWitnesses
    (I : Finset ((Edge α × Edge α) × α))
    (K H : Family α) (V : Edge α) (t : ℕ)
    (tripleLabel : Edge α → α) :
    Finset ((_i : (Edge α × Edge α) × α) × ((_R₁ : Edge α) × Edge α)) := by
  classical
  exact I.sigma (lowerWitnessesFor n K H V t tripleLabel)

noncomputable def lowerUpperStrongWitnesses
    (I : Finset ((Edge α × Edge α) × α))
    (K H : Family α) (V : Edge α) (tLower tUpper : ℕ)
    (facetCenter : Edge α → α) (tripleLabel : Edge α → α) := by
  classical
  exact (lowerInheritanceWitnesses n I K H V tLower tripleLabel).filter fun w =>
    ActualStrongPartner H V
      ((lowerWitnessRoot w.1).erase w.1.2)
      (w.2.1.erase w.1.2) 2 (n + 1) tUpper
      (facetCenter w.1.1.2)

theorem lower_upper_strong_witnesses_eq
    (I : Finset ((Edge α × Edge α) × α))
    (K H : Family α) (V : Edge α) (tLower tUpper : ℕ)
    (facetCenter : Edge α → α) (tripleLabel : Edge α → α)
    (hFacetStrong : ∀ i ∈ I,
      ∀ R₁ ∈ lowerWitnessSecondRoots K V i,
        ActualStrongPartner H V
          ((lowerWitnessRoot i).erase i.2) (R₁.erase i.2)
          2 (n + 1) tUpper (facetCenter i.1.2)) :
    lowerUpperStrongWitnesses n I K H V tLower tUpper
      facetCenter tripleLabel =
      lowerInheritanceWitnesses n I K H V tLower tripleLabel := by
  classical
  ext w
  constructor
  · intro hw
    exact (Finset.mem_filter.mp hw).1
  · intro hw
    have hi : w.1 ∈ I := (Finset.mem_sigma.mp hw).1
    have hR₁ : w.2.1 ∈ lowerWitnessSecondRoots K V w.1 :=
      (Finset.mem_sigma.mp (Finset.mem_sigma.mp hw).2).1
    exact Finset.mem_filter.mpr
      ⟨hw, hFacetStrong w.1 hi w.2.1 hR₁⟩

theorem lower_witness_tuple_injective
    (I : Finset ((Edge α × Edge α) × α))
    (K H : Family α) (V : Edge α) (t : ℕ)
    (facetCenter tripleLabel : Edge α → α)
    (hI : I ⊆ badIncidences K V (n + 1) facetCenter tripleLabel) :
    Set.InjOn lowerWitnessTuple
      (lowerInheritanceWitnesses n I K H V t tripleLabel :
        Set ((_i : (Edge α × Edge α) × α) × ((_R₁ : Edge α) × Edge α))) := by
  classical
  intro w hw w' hw' hTuple
  have hBad (x : (_i : (Edge α × Edge α) × α) × ((_R₁ : Edge α) × Edge α))
      (hx : x ∈ lowerInheritanceWitnesses n I K H V t tripleLabel) :
      x.1.1.2 ⊆ x.1.1.1 ∧ x.1.2 ∈ x.1.1.2 := by
    have hxI : x.1 ∈ I := (Finset.mem_sigma.mp hx).1
    have hxBad := hI hxI
    change x.1 ∈ ((K ×ˢ V.powersetCard (n + 1)) ×ˢ V).filter _ at hxBad
    have hParts := (Finset.mem_filter.mp hxBad).2
    exact ⟨hParts.1, hParts.2.2.1⟩
  have hRecon (x : (_i : (Edge α × Edge α) × α) × ((_R₁ : Edge α) × Edge α))
      (hx : x ∈ lowerInheritanceWitnesses n I K H V t tripleLabel) :
      x.1.1.1 = lowerWitnessCore x.1 ∪ lowerWitnessRoot x.1 ∧
      x.1.1.2 = lowerWitnessCore x.1 ∪ {x.1.2} := by
    obtain ⟨hAE, haA⟩ := hBad x hx
    have hBE : lowerWitnessCore x.1 ⊆ x.1.1.1 :=
      (Finset.erase_subset x.1.2 x.1.1.2).trans hAE
    constructor
    · simpa [lowerWitnessRoot, Finset.union_comm] using
        (Finset.sdiff_union_of_subset hBE).symm
    · simp [lowerWitnessCore, Finset.union_singleton,
        Finset.insert_erase haA]
  have hB : lowerWitnessCore w.1 = lowerWitnessCore w'.1 :=
    congrArg (fun q => q.1.1.1) hTuple
  have hR : lowerWitnessRoot w.1 = lowerWitnessRoot w'.1 :=
    congrArg (fun q => q.1.1.2) hTuple
  have hR₁ : w.2.1 = w'.2.1 := congrArg (fun q => q.1.2.1) hTuple
  have hT : w.2.2 = w'.2.2 := congrArg (fun q => q.1.2.2) hTuple
  have ha : w.1.2 = w'.1.2 := congrArg (fun q => q.2) hTuple
  have hRw := hRecon w hw
  have hRw' := hRecon w' hw'
  have hi : w.1 = w'.1 := by
    apply Prod.ext
    · apply Prod.ext
      · calc
          w.1.1.1 = lowerWitnessCore w.1 ∪ lowerWitnessRoot w.1 := hRw.1
          _ = lowerWitnessCore w'.1 ∪ lowerWitnessRoot w'.1 := by rw [hB, hR]
          _ = w'.1.1.1 := hRw'.1.symm
      · calc
          w.1.1.2 = lowerWitnessCore w.1 ∪ {w.1.2} := hRw.2
          _ = lowerWitnessCore w'.1 ∪ {w'.1.2} := by rw [hB, ha]
          _ = w'.1.1.2 := hRw'.2.symm
    · exact ha
  cases w with
  | mk i p =>
    cases w' with
    | mk j p' =>
      dsimp at hi hR₁ hT
      cases hi
      cases p with
      | mk R₁ T =>
        cases p' with
        | mk R₁' T' =>
          dsimp at hR₁ hT
          cases hR₁
          cases hT
          rfl

theorem lower_upper_witness_parent_injective_on_key
    (I : Finset ((Edge α × Edge α) × α))
    (K H : Family α) (V : Edge α) (tLower tUpper : ℕ)
    (facetCenter tripleLabel : Edge α → α)
    (hI : I ⊆ badIncidences K V (n + 1) facetCenter tripleLabel)
    (key : (((Edge α × Edge α) × α) × Edge α)) :
    Set.InjOn (fun w : (_i : (Edge α × Edge α) × α) ×
        ((_R₁ : Edge α) × Edge α) => w.1.1.1)
      ((lowerUpperStrongWitnesses n I K H V tLower tUpper
        facetCenter tripleLabel).filter
          (fun w => lowerWitnessPinnedKey w = key) :
        Set ((_i : (Edge α × Edge α) × α) × ((_R₁ : Edge α) × Edge α))) := by
  classical
  intro w hw w' hw' hE
  have hW : w ∈ lowerInheritanceWitnesses n I K H V tLower tripleLabel :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).1
  have hW' : w' ∈ lowerInheritanceWitnesses n I K H V tLower tripleLabel :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hw').1).1
  have hKey : lowerWitnessPinnedKey w = lowerWitnessPinnedKey w' :=
    (Finset.mem_filter.mp hw).2.trans (Finset.mem_filter.mp hw').2.symm
  have hR₀ : lowerWitnessRoot w.1 = lowerWitnessRoot w'.1 :=
    congrArg (fun x => x.1.1.1) hKey
  have hT : w.2.2 = w'.2.2 := congrArg (fun x => x.1.1.2) hKey
  have ha : w.1.2 = w'.1.2 := congrArg (fun x => x.1.2) hKey
  have hR₁ : w.2.1 = w'.2.1 := congrArg (fun x => x.2) hKey
  have hBad : w.1 ∈ badIncidences K V (n + 1) facetCenter tripleLabel :=
    hI (Finset.mem_sigma.mp hW).1
  have hBad' : w'.1 ∈ badIncidences K V (n + 1) facetCenter tripleLabel :=
    hI (Finset.mem_sigma.mp hW').1
  have hB : lowerWitnessCore w.1 = lowerWitnessCore w'.1 := by
    have hE' : w.1.1.1 = w'.1.1.1 := hE
    calc
      lowerWitnessCore w.1 = w.1.1.1 \ lowerWitnessRoot w.1 :=
        lower_bad_incidence_core_eq_parent_sdiff_root n K V
          facetCenter tripleLabel hBad
      _ = w'.1.1.1 \ lowerWitnessRoot w'.1 := by rw [hE', hR₀]
      _ = lowerWitnessCore w'.1 :=
        (lower_bad_incidence_core_eq_parent_sdiff_root n K V
          facetCenter tripleLabel hBad').symm
  have hTuple : lowerWitnessTuple w = lowerWitnessTuple w' := by
    apply Prod.ext
    · apply Prod.ext
      · exact Prod.ext hB hR₀
      · exact Prod.ext hR₁ hT
    · exact ha
  exact lower_witness_tuple_injective n I K H V tLower
    facetCenter tripleLabel hI hW hW' hTuple

theorem lower_upper_witness_labels_eq_on_key
    (I : Finset ((Edge α × Edge α) × α))
    (K H : Family α) (V : Edge α) (tLower tUpper : ℕ)
    (facetCenter tripleLabel : Edge α → α)
    {w w' : (_i : (Edge α × Edge α) × α) ×
      ((_R₁ : Edge α) × Edge α)}
    (hw : w ∈ lowerUpperStrongWitnesses n I K H V tLower tUpper
      facetCenter tripleLabel)
    (hw' : w' ∈ lowerUpperStrongWitnesses n I K H V tLower tUpper
      facetCenter tripleLabel)
    (hKey : lowerWitnessPinnedKey w = lowerWitnessPinnedKey w') :
    tripleLabel (lowerWitnessCore w.1) =
      tripleLabel (lowerWitnessCore w'.1) ∧
    facetCenter w.1.1.2 = facetCenter w'.1.1.2 := by
  classical
  have hR₀ : lowerWitnessRoot w.1 = lowerWitnessRoot w'.1 :=
    congrArg (fun x => x.1.1.1) hKey
  have hT : w.2.2 = w'.2.2 := congrArg (fun x => x.1.1.2) hKey
  have ha : w.1.2 = w'.1.2 := congrArg (fun x => x.1.2) hKey
  have hR₁ : w.2.1 = w'.2.1 := congrArg (fun x => x.2) hKey
  have hBase := (Finset.mem_filter.mp hw).1
  have hBase' := (Finset.mem_filter.mp hw').1
  have hTmem := (Finset.mem_sigma.mp (Finset.mem_sigma.mp hBase).2).2
  have hTmem' := (Finset.mem_sigma.mp (Finset.mem_sigma.mp hBase').2).2
  have hStrong := (Finset.mem_filter.mp hTmem).2.2.1
  have hStrong' := (Finset.mem_filter.mp hTmem').2.2.1
  have hUpper := (Finset.mem_filter.mp hw).2
  have hUpper' := (Finset.mem_filter.mp hw').2
  constructor
  · have hStrong'' : ActualStrongPartner H V
        (lowerWitnessRoot w.1) w.2.2 3 n tLower
        (tripleLabel (lowerWitnessCore w'.1)) := by
      simpa only [hR₀, hT] using hStrong'
    exact actual_strong_partner_center_unique H V
      (lowerWitnessRoot w.1) w.2.2 3 n tLower hStrong hStrong''
  · have hUpper'' : ActualStrongPartner H V
        ((lowerWitnessRoot w.1).erase w.1.2)
        (w.2.1.erase w.1.2) 2 (n + 1) tUpper
        (facetCenter w'.1.1.2) := by
      simpa only [hR₀, hR₁, ha] using hUpper'
    exact actual_strong_partner_center_unique H V
      ((lowerWitnessRoot w.1).erase w.1.2)
      (w.2.1.erase w.1.2) 2 (n + 1) tUpper hUpper hUpper''

theorem lower_upper_witness_key_fiber_le_four_codegree
    (I : Finset ((Edge α × Edge α) × α))
    (K H : Family α) (V : Edge α) (tLower tUpper D₅ : ℕ)
    (facetCenter tripleLabel : Edge α → α)
    (hI : I ⊆ badIncidences K V (n + 1) facetCenter tripleLabel)
    (hKH : K ⊆ H) (hUniform : Uniform (n + 3) K)
    (hFacetCenter : ActualRankLabels K (n + 1) facetCenter)
    (hTripleLabels : ActualRankLabels K n tripleLabel)
    (hD₅ : ∀ S : Edge α, S.card = 5 →
      (H.filter fun E => S ⊆ E).card ≤ D₅)
    (key : (((Edge α × Edge α) × α) × Edge α)) :
    ((lowerUpperStrongWitnesses n I K H V tLower tUpper
      facetCenter tripleLabel).filter
        (fun w => lowerWitnessPinnedKey w = key)).card ≤ D₅ := by
  classical
  let F := (lowerUpperStrongWitnesses n I K H V tLower tUpper
    facetCenter tripleLabel).filter
      (fun w => lowerWitnessPinnedKey w = key)
  change F.card ≤ D₅
  by_cases hEmpty : F = ∅
  · simp [hEmpty]
  obtain ⟨w₀, hw₀⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
  have hUpper₀ : w₀ ∈ lowerUpperStrongWitnesses n I K H V tLower tUpper
      facetCenter tripleLabel := (Finset.mem_filter.mp hw₀).1
  have hBad₀ : w₀.1 ∈ badIncidences K V (n + 1) facetCenter tripleLabel := by
    have hBase := (Finset.mem_filter.mp hUpper₀).1
    exact hI (Finset.mem_sigma.mp hBase).1
  let B₀ := lowerWitnessCore w₀.1
  let R₀ := lowerWitnessRoot w₀.1
  let zA := facetCenter w₀.1.1.2
  let zB := tripleLabel B₀
  let S : Edge α := R₀ ∪ {zA, zB}
  have hLabels₀ := lower_bad_incidence_labels_in_core n K V
    facetCenter tripleLabel hFacetCenter hTripleLabels hBad₀
  have hSource₀ := (Finset.mem_filter.mp hBad₀).1
  have hE₀ : w₀.1.1.1 ∈ K :=
    (Finset.mem_product.mp (Finset.mem_product.mp hSource₀).1).1
  have hAcard₀ : w₀.1.1.2.card = n + 1 :=
    (Finset.mem_powersetCard.mp
      (Finset.mem_product.mp (Finset.mem_product.mp hSource₀).1).2).2
  have ha₀ : w₀.1.2 ∈ w₀.1.1.2 :=
    (Finset.mem_filter.mp hBad₀).2.2.2.1
  have hBcard₀ : B₀.card = n := by
    have herase := Finset.card_erase_add_one ha₀
    change (w₀.1.1.2.erase w₀.1.2).card = n
    omega
  have hBE₀ : B₀ ⊆ w₀.1.1.1 :=
    (Finset.erase_subset w₀.1.2 w₀.1.1.2).trans
      (Finset.mem_filter.mp hBad₀).2.1
  have hRcard₀ : R₀.card = 3 := by
    change (w₀.1.1.1 \ B₀).card = 3
    rw [Finset.card_sdiff_of_subset hBE₀, hUniform hE₀]
    omega
  have hRdisjB : Disjoint R₀ B₀ := by
    apply Finset.disjoint_left.mpr
    intro x hxR hxB
    exact (Finset.mem_sdiff.mp hxR).2 hxB
  have hPairDisj : Disjoint R₀ ({zA, zB} : Edge α) := by
    apply Finset.disjoint_left.mpr
    intro x hxR hxPair
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxPair
    rcases hxPair with rfl | rfl
    · exact (Finset.disjoint_left.mp hRdisjB) hxR hLabels₀.1
    · exact (Finset.disjoint_left.mp hRdisjB) hxR hLabels₀.2.1
  have hScard : S.card = 5 := by
    rw [Finset.card_union_of_disjoint hPairDisj]
    rw [Finset.card_pair hLabels₀.2.2, hRcard₀]
  have hMap : ∀ w ∈ F, w.1.1.1 ∈ H.filter (fun E => S ⊆ E) := by
    intro w hw
    have hUpper : w ∈ lowerUpperStrongWitnesses n I K H V tLower tUpper
        facetCenter tripleLabel := (Finset.mem_filter.mp hw).1
    have hBase := (Finset.mem_filter.mp hUpper).1
    have hBad : w.1 ∈ badIncidences K V (n + 1) facetCenter tripleLabel :=
      hI (Finset.mem_sigma.mp hBase).1
    have hKeyEq : lowerWitnessPinnedKey w₀ = lowerWitnessPinnedKey w :=
      (Finset.mem_filter.mp hw₀).2.trans (Finset.mem_filter.mp hw).2.symm
    have hR₀w : R₀ = lowerWitnessRoot w.1 :=
      congrArg (fun x => x.1.1.1) hKeyEq
    have hColors := lower_upper_witness_labels_eq_on_key n I K H V
      tLower tUpper facetCenter tripleLabel hUpper₀ hUpper hKeyEq
    have hLabels := lower_bad_incidence_labels_in_core n K V
      facetCenter tripleLabel hFacetCenter hTripleLabels hBad
    have hBE : lowerWitnessCore w.1 ⊆ w.1.1.1 :=
      (Finset.erase_subset w.1.2 w.1.1.2).trans
        (Finset.mem_filter.mp hBad).2.1
    have hRE : lowerWitnessRoot w.1 ⊆ w.1.1.1 := Finset.sdiff_subset
    have hSource := (Finset.mem_filter.mp hBad).1
    have hE : w.1.1.1 ∈ K :=
      (Finset.mem_product.mp (Finset.mem_product.mp hSource).1).1
    have hzAw : zA ∈ lowerWitnessCore w.1 := by
      change facetCenter w₀.1.1.2 ∈ lowerWitnessCore w.1
      rw [hColors.2]
      exact hLabels.1
    have hzBw : zB ∈ lowerWitnessCore w.1 := by
      change tripleLabel (lowerWitnessCore w₀.1) ∈ lowerWitnessCore w.1
      rw [hColors.1]
      exact hLabels.2.1
    apply Finset.mem_filter.mpr
    refine ⟨hKH hE, ?_⟩
    intro x hx
    rcases Finset.mem_union.mp hx with hxR | hxPair
    · exact hRE (hR₀w ▸ hxR)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hxPair
      rcases hxPair with rfl | rfl
      · exact hBE hzAw
      · exact hBE hzBw
  have hInj := lower_upper_witness_parent_injective_on_key n I K H V
    tLower tUpper facetCenter tripleLabel hI key
  have hCount := Finset.card_le_card_of_injOn
    (fun w : (_i : (Edge α × Edge α) × α) ×
      ((_R₁ : Edge α) × Edge α) => w.1.1.1) hMap hInj
  exact hCount.trans (hD₅ S hScard)

theorem lower_upper_witness_triple_fiber_pinned_cap
    (I : Finset ((Edge α × Edge α) × α))
    (K H : Family α) (V : Edge α) (tLower tUpper D₄ Dₙ : ℕ)
    (facetCenter tripleLabel : Edge α → α)
    (ht : 1 ≤ tLower)
    (hD₄ : ∀ S : Edge α, S.card = 4 →
      (H.filter fun E => S ⊆ E).card ≤ D₄)
    (hDₙ : ∀ S : Edge α, S.card = n + 1 →
      (H.filter fun E => S ⊆ E).card ≤ Dₙ)
    (key : (Edge α × Edge α) × α) :
    tLower * (((lowerUpperStrongWitnesses n I K H V tLower tUpper
      facetCenter tripleLabel).filter
        (fun w => lowerWitnessTripleKey w = key)).image
          (fun w => w.2.1)).card ≤ D₄ * Dₙ := by
  classical
  let F := (lowerUpperStrongWitnesses n I K H V tLower tUpper
    facetCenter tripleLabel).filter
      (fun w => lowerWitnessTripleKey w = key)
  change tLower * (F.image (fun w => w.2.1)).card ≤ D₄ * Dₙ
  by_cases hEmpty : F = ∅
  · simp [hEmpty]
  obtain ⟨w₀, hw₀⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
  have hBase₀ := (Finset.mem_filter.mp (Finset.mem_filter.mp hw₀).1).1
  have hThird₀ := (Finset.mem_sigma.mp (Finset.mem_sigma.mp hBase₀).2).2
  have hThirdParts₀ := Finset.mem_filter.mp hThird₀
  have hTcard : w₀.2.2.card = 3 :=
    (mem_parent_triple_link.mp hThirdParts₀.1).2.1
  let z := tripleLabel (lowerWitnessCore w₀.1)
  have hStrong₀ : ActualStrongPartner H V
      (lowerWitnessRoot w₀.1) w₀.2.2 3 n tLower z :=
    hThirdParts₀.2.2.1
  have hzNotT : z ∉ w₀.2.2 := by
    have hCellPos : 0 <
        (commonPrefixTails H V (lowerWitnessRoot w₀.1) w₀.2.2 n).card := by
      have hThreshold := hStrong₀.2.2.1
      omega
    obtain ⟨C, hC⟩ := Finset.card_pos.mp hCellPos
    have hzC : z ∈ C := hStrong₀.2.2.2.1 C hC
    have hDisjCT : Disjoint C w₀.2.2 :=
      (Finset.disjoint_union_right.mp
        (mem_common_prefix_tails.mp hC).2.2.1).2
    intro hzT
    exact (Finset.disjoint_left.mp hDisjCT) hzC hzT
  have hSub : F.image (fun w => w.2.1) ⊆
      actualCenterPartners H V w₀.2.2 3 n tLower z {w₀.1.2} := by
    intro R₁ hR₁
    obtain ⟨w, hw, hRw⟩ := Finset.mem_image.mp hR₁
    have hBase := (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).1
    have hSecond := (Finset.mem_sigma.mp (Finset.mem_sigma.mp hBase).2).1
    have hThird := (Finset.mem_sigma.mp (Finset.mem_sigma.mp hBase).2).2
    have hKey : lowerWitnessTripleKey w₀ = lowerWitnessTripleKey w :=
      (Finset.mem_filter.mp hw₀).2.trans (Finset.mem_filter.mp hw).2.symm
    have hR₀ : lowerWitnessRoot w₀.1 = lowerWitnessRoot w.1 :=
      congrArg (fun x => x.1.1) hKey
    have hT : w₀.2.2 = w.2.2 := congrArg (fun x => x.1.2) hKey
    have ha : w₀.1.2 = w.1.2 := congrArg (fun x => x.2) hKey
    have hStrong₀w := (Finset.mem_filter.mp hThird).2.2.1
    have hStrong₀w' : ActualStrongPartner H V
        (lowerWitnessRoot w₀.1) w₀.2.2 3 n tLower
        (tripleLabel (lowerWitnessCore w.1)) := by
      simpa only [hR₀, hT] using hStrong₀w
    have hzEq : z = tripleLabel (lowerWitnessCore w.1) :=
      actual_strong_partner_center_unique H V
        (lowerWitnessRoot w₀.1) w₀.2.2 3 n tLower
        hStrong₀ hStrong₀w'
    have hRlink := (Finset.mem_filter.mp hSecond).1
    have hRpow : w.2.1 ∈ V.powersetCard 3 :=
      Finset.mem_powersetCard.mpr
        ⟨(mem_parent_triple_link.mp hRlink).1,
          (mem_parent_triple_link.mp hRlink).2.1⟩
    have hInter := (Finset.mem_filter.mp hSecond).2
    have haR : w.1.2 ∈ w.2.1 := by
      have haInter : w.1.2 ∈ lowerWitnessRoot w.1 ∩ w.2.1 := by
        rw [hInter]
        simp
      exact (Finset.mem_inter.mp haInter).2
    have hStrong₁w := (Finset.mem_filter.mp hThird).2.2.2
    have hStrong₁w' : ActualStrongPartner H V
        w₀.2.2 w.2.1 3 n tLower z := by
      have hSymm := actual_strong_partner_symm H V
        w.2.1 w.2.2 n tLower
        (tripleLabel (lowerWitnessCore w.1)) hRpow hStrong₁w
      simpa only [← hT, ← hzEq] using hSymm
    change R₁ ∈ (V.powersetCard 3).filter
      (fun Q => ActualStrongPartner H V w₀.2.2 Q 3 n tLower z ∧
        {w₀.1.2} ⊆ Q)
    have hR₁Eq : w.2.1 = R₁ := hRw
    subst R₁
    exact Finset.mem_filter.mpr
      ⟨hRpow, hStrong₁w', Finset.singleton_subset_iff.mpr (ha ▸ haR)⟩
  have hPinned := repeated_center_partner_bound_from_codegrees
    H V w₀.2.2 3 n tLower z {w₀.1.2} 1 D₄ Dₙ
    hTcard hzNotT (by simp) hD₄ hDₙ
  exact (Nat.mul_le_mul_left tLower (Finset.card_le_card hSub)).trans hPinned

theorem lower_upper_witness_triple_fiber_bound
    (I : Finset ((Edge α × Edge α) × α))
    (K H : Family α) (V : Edge α) (tLower tUpper D₄ D₅ Dₙ : ℕ)
    (facetCenter tripleLabel : Edge α → α)
    (hI : I ⊆ badIncidences K V (n + 1) facetCenter tripleLabel)
    (hKH : K ⊆ H) (hUniform : Uniform (n + 3) K)
    (hFacetCenter : ActualRankLabels K (n + 1) facetCenter)
    (hTripleLabels : ActualRankLabels K n tripleLabel)
    (ht : 1 ≤ tLower)
    (hD₄ : ∀ S : Edge α, S.card = 4 →
      (H.filter fun E => S ⊆ E).card ≤ D₄)
    (hDₙ : ∀ S : Edge α, S.card = n + 1 →
      (H.filter fun E => S ⊆ E).card ≤ Dₙ)
    (hD₅ : ∀ S : Edge α, S.card = 5 →
      (H.filter fun E => S ⊆ E).card ≤ D₅)
    (key : (Edge α × Edge α) × α) :
    tLower * ((lowerUpperStrongWitnesses n I K H V tLower tUpper
      facetCenter tripleLabel).filter
        (fun w => lowerWitnessTripleKey w = key)).card ≤
      D₄ * Dₙ * D₅ := by
  classical
  let F := (lowerUpperStrongWitnesses n I K H V tLower tUpper
    facetCenter tripleLabel).filter
      (fun w => lowerWitnessTripleKey w = key)
  have hOne (R₁ : Edge α) :
      (F.filter fun w => w.2.1 = R₁).card ≤ D₅ := by
    have hEq : (F.filter fun w => w.2.1 = R₁) =
        (lowerUpperStrongWitnesses n I K H V tLower tUpper
          facetCenter tripleLabel).filter
          (fun w => lowerWitnessPinnedKey w = (key, R₁)) := by
      ext w
      simp only [F, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hw, hKey⟩, hR⟩
        exact ⟨hw, by simp [lowerWitnessPinnedKey,
          lowerWitnessTripleKey, ← hKey, ← hR]⟩
      · rintro ⟨hw, hKey⟩
        have hTriple : lowerWitnessTripleKey w = key :=
          congrArg Prod.fst hKey
        have hR : w.2.1 = R₁ := congrArg Prod.snd hKey
        exact ⟨⟨hw, hTriple⟩, hR⟩
    rw [hEq]
    exact lower_upper_witness_key_fiber_le_four_codegree n
      I K H V tLower tUpper D₅ facetCenter tripleLabel
      hI hKH hUniform hFacetCenter hTripleLabels hD₅ (key, R₁)
  have hCount := Finset.card_eq_sum_card_fiberwise
    (f := fun w : (_i : (Edge α × Edge α) × α) ×
      ((_R₁ : Edge α) × Edge α) => w.2.1)
    (s := F) (t := F.image (fun w => w.2.1))
    (fun w hw => Finset.mem_image_of_mem _ hw)
  have hFiber : F.card ≤ (F.image (fun w => w.2.1)).card * D₅ := by
    rw [hCount]
    calc
      (∑ R₁ ∈ F.image (fun w => w.2.1),
        (F.filter fun w => w.2.1 = R₁).card) ≤
          ∑ _R₁ ∈ F.image (fun w => w.2.1), D₅ :=
        Finset.sum_le_sum (fun R₁ hR₁ => hOne R₁)
      _ = (F.image (fun w => w.2.1)).card * D₅ := by simp
  have hPinned := lower_upper_witness_triple_fiber_pinned_cap n
    I K H V tLower tUpper D₄ Dₙ facetCenter tripleLabel
    ht hD₄ hDₙ key
  change tLower * F.card ≤ D₄ * Dₙ * D₅
  have hScaled := Nat.mul_le_mul_left tLower hFiber
  nlinarith [Nat.mul_le_mul_right D₅ hPinned]

theorem lower_upper_witness_key_mem
    (I : Finset ((Edge α × Edge α) × α))
    (K H : Family α) (V : Edge α) (tLower tUpper : ℕ)
    (facetCenter tripleLabel : Edge α → α)
    (hI : I ⊆ badIncidences K V (n + 1) facetCenter tripleLabel)
    (hUniform : Uniform (n + 3) K)
    (hAmbient : ∀ E ∈ K, E ⊆ V)
    {w : (_i : (Edge α × Edge α) × α) ×
      ((_R₁ : Edge α) × Edge α)}
    (hw : w ∈ lowerUpperStrongWitnesses n I K H V tLower tUpper
      facetCenter tripleLabel) :
    lowerWitnessTripleKey w ∈ lowerWitnessTripleKeys V := by
  classical
  have hBase := (Finset.mem_filter.mp hw).1
  have hBad : w.1 ∈ badIncidences K V (n + 1) facetCenter tripleLabel :=
    hI (Finset.mem_sigma.mp hBase).1
  have hSource := (Finset.mem_filter.mp hBad).1
  have hE : w.1.1.1 ∈ K :=
    (Finset.mem_product.mp (Finset.mem_product.mp hSource).1).1
  have hAcard : w.1.1.2.card = n + 1 :=
    (Finset.mem_powersetCard.mp
      (Finset.mem_product.mp (Finset.mem_product.mp hSource).1).2).2
  have hParts := (Finset.mem_filter.mp hBad).2
  have hAE : w.1.1.2 ⊆ w.1.1.1 := hParts.1
  have ha : w.1.2 ∈ w.1.1.2 := hParts.2.2.1
  have hBcard : (lowerWitnessCore w.1).card = n := by
    have herase := Finset.card_erase_add_one ha
    change (w.1.1.2.erase w.1.2).card = n
    omega
  have hBE : lowerWitnessCore w.1 ⊆ w.1.1.1 :=
    (Finset.erase_subset w.1.2 w.1.1.2).trans hAE
  have hRcard : (lowerWitnessRoot w.1).card = 3 := by
    change (w.1.1.1 \ lowerWitnessCore w.1).card = 3
    rw [Finset.card_sdiff_of_subset hBE, hUniform hE]
    omega
  have hRpow : lowerWitnessRoot w.1 ∈ V.powersetCard 3 :=
    Finset.mem_powersetCard.mpr
      ⟨Finset.sdiff_subset.trans (hAmbient w.1.1.1 hE), hRcard⟩
  have hTmem := (Finset.mem_sigma.mp (Finset.mem_sigma.mp hBase).2).2
  have hTlink := (Finset.mem_filter.mp hTmem).1
  have hTparts := mem_parent_triple_link.mp hTlink
  have hTpow : w.2.2 ∈ V.powersetCard 3 :=
    Finset.mem_powersetCard.mpr ⟨hTparts.1, hTparts.2.1⟩
  have haNotB : w.1.2 ∉ lowerWitnessCore w.1 := by
    intro haB
    exact (Finset.mem_erase.mp haB).1 rfl
  have haR : w.1.2 ∈ lowerWitnessRoot w.1 :=
    Finset.mem_sdiff.mpr ⟨hAE ha, haNotB⟩
  exact Finset.mem_biUnion.mpr
    ⟨(lowerWitnessRoot w.1, w.2.2),
      Finset.mem_product.mpr ⟨hRpow, hTpow⟩,
      Finset.mem_image.mpr ⟨w.1.2, haR, rfl⟩⟩

theorem lower_upper_strong_witness_global_pinned_bound
    (I : Finset ((Edge α × Edge α) × α))
    (K H : Family α) (V : Edge α) (tLower tUpper D₄ D₅ Dₙ : ℕ)
    (facetCenter tripleLabel : Edge α → α)
    (hI : I ⊆ badIncidences K V (n + 1) facetCenter tripleLabel)
    (hKH : K ⊆ H) (hUniform : Uniform (n + 3) K)
    (hAmbient : ∀ E ∈ K, E ⊆ V)
    (hFacetCenter : ActualRankLabels K (n + 1) facetCenter)
    (hTripleLabels : ActualRankLabels K n tripleLabel)
    (ht : 1 ≤ tLower)
    (hD₄ : ∀ S : Edge α, S.card = 4 →
      (H.filter fun E => S ⊆ E).card ≤ D₄)
    (hDₙ : ∀ S : Edge α, S.card = n + 1 →
      (H.filter fun E => S ⊆ E).card ≤ Dₙ)
    (hD₅ : ∀ S : Edge α, S.card = 5 →
      (H.filter fun E => S ⊆ E).card ≤ D₅) :
    tLower * (lowerUpperStrongWitnesses n I K H V tLower tUpper
      facetCenter tripleLabel).card ≤
        3 * (V.powersetCard 3).card ^ 2 * D₄ * Dₙ * D₅ := by
  classical
  let W := lowerUpperStrongWitnesses n I K H V tLower tUpper
    facetCenter tripleLabel
  let Keys := lowerWitnessTripleKeys V
  have hMap : ∀ w ∈ W, lowerWitnessTripleKey w ∈ Keys := by
    intro w hw
    exact lower_upper_witness_key_mem n I K H V tLower tUpper
      facetCenter tripleLabel hI hUniform hAmbient hw
  have hCount := Finset.card_eq_sum_card_fiberwise
    (f := lowerWitnessTripleKey) (s := W) (t := Keys) hMap
  have hFiber : ∀ key ∈ Keys,
      tLower * (W.filter fun w => lowerWitnessTripleKey w = key).card ≤
        D₄ * Dₙ * D₅ := by
    intro key hkey
    exact lower_upper_witness_triple_fiber_bound n I K H V
      tLower tUpper D₄ D₅ Dₙ facetCenter tripleLabel hI hKH hUniform
      hFacetCenter hTripleLabels ht hD₄ hDₙ hD₅ key
  have hKeys := lower_witness_triple_keys_card_le V
  calc
    tLower * W.card =
        ∑ key ∈ Keys,
          tLower * (W.filter fun w => lowerWitnessTripleKey w = key).card := by
      rw [hCount, Finset.mul_sum]
    _ ≤ ∑ _key ∈ Keys, D₄ * Dₙ * D₅ :=
      Finset.sum_le_sum hFiber
    _ = Keys.card * (D₄ * Dₙ * D₅) := by simp
    _ ≤ (3 * (V.powersetCard 3).card ^ 2) *
          (D₄ * Dₙ * D₅) := Nat.mul_le_mul_right _ hKeys
    _ = 3 * (V.powersetCard 3).card ^ 2 * D₄ * Dₙ * D₅ := by ring

theorem lower_witnesses_for_card_eq_pinned_fiber_sum
    (K H : Family α) (V : Edge α) (t : ℕ)
    (tripleLabel : Edge α → α)
    (i : (Edge α × Edge α) × α) :
    (lowerWitnessesFor n K H V t tripleLabel i).card =
      ∑ T ∈ V.powersetCard 3,
        (facetPinnedSecondRoots n K H V t tripleLabel i T).card := by
  classical
  let W := lowerWitnessesFor n K H V t tripleLabel i
  have hMap : ∀ w ∈ W, w.2 ∈ V.powersetCard 3 := by
    intro w hw
    have hThird := (Finset.mem_sigma.mp hw).2
    have hTlink := (Finset.mem_filter.mp hThird).1
    have hParts := mem_parent_triple_link.mp hTlink
    exact Finset.mem_powersetCard.mpr ⟨hParts.1, hParts.2.1⟩
  have hFiber (T : Edge α) :
      (W.filter fun w => w.2 = T).card =
        (facetPinnedSecondRoots n K H V t tripleLabel i T).card := by
    have hEq : (W.filter fun w => w.2 = T) =
        (facetPinnedSecondRoots n K H V t tripleLabel i T).image
          (fun R₁ => (⟨R₁, T⟩ : (_R₁ : Edge α) × Edge α)) := by
      ext ⟨R₁, U⟩
      simp only [W, lowerWitnessesFor, facetPinnedSecondRoots,
        Finset.mem_filter, Finset.mem_image, Finset.mem_sigma]
      constructor
      · rintro ⟨⟨hR₁, hU⟩, hUT⟩
        refine ⟨R₁, ?_, ?_⟩
        · exact ⟨hR₁, hUT ▸ hU⟩
        · cases hUT
          rfl
      · rintro ⟨R, hR, hEq⟩
        cases hEq
        exact ⟨hR, rfl⟩
    rw [hEq, Finset.card_image_of_injective]
    intro R S hRS
    exact congrArg Sigma.fst hRS
  have hCount := Finset.card_eq_sum_card_fiberwise
    (f := fun w : (_R₁ : Edge α) × Edge α => w.2)
    (s := W) (t := V.powersetCard 3) hMap
  simpa only [hFiber] using hCount

theorem lower_inheritance_witnesses_pinned_upper_bound
    (I : Finset ((Edge α × Edge α) × α))
    (K H : Family α) (V : Edge α) (t D₄ Dₙ : ℕ)
    (tripleLabel : Edge α → α)
    (ht : 1 ≤ t)
    (hD₄ : ∀ S : Edge α, S.card = 4 →
      (H.filter fun E => S ⊆ E).card ≤ D₄)
    (hDₙ : ∀ S : Edge α, S.card = n + 1 →
      (H.filter fun E => S ⊆ E).card ≤ Dₙ) :
    t * (lowerInheritanceWitnesses n I K H V t tripleLabel).card ≤
      I.card * (V.powersetCard 3).card * (D₄ * Dₙ) := by
  classical
  have hOne : ∀ i ∈ I,
      t * (lowerWitnessesFor n K H V t tripleLabel i).card ≤
        (V.powersetCard 3).card * (D₄ * Dₙ) := by
    intro i hi
    rw [lower_witnesses_for_card_eq_pinned_fiber_sum]
    calc
      t * (∑ T ∈ V.powersetCard 3,
          (facetPinnedSecondRoots n K H V t tripleLabel i T).card) =
          ∑ T ∈ V.powersetCard 3,
            t * (facetPinnedSecondRoots n K H V t tripleLabel i T).card := by
        rw [Finset.mul_sum]
      _ ≤ ∑ _T ∈ V.powersetCard 3, D₄ * Dₙ := by
        apply Finset.sum_le_sum
        intro T hT
        exact lower_pinned_second_roots_bound n K H V t D₄ Dₙ
          tripleLabel ht hD₄ hDₙ i T
      _ = (V.powersetCard 3).card * (D₄ * Dₙ) := by simp
  simp only [lowerInheritanceWitnesses, Finset.card_sigma]
  calc
    t * (∑ i ∈ I, (lowerWitnessesFor n K H V t tripleLabel i).card) =
        ∑ i ∈ I, t * (lowerWitnessesFor n K H V t tripleLabel i).card := by
      rw [Finset.mul_sum]
    _ ≤ ∑ _i ∈ I, (V.powersetCard 3).card * (D₄ * Dₙ) :=
      Finset.sum_le_sum hOne
    _ = I.card * (V.powersetCard 3).card * (D₄ * Dₙ) := by
      simp [mul_assoc]

theorem lower_witness_tuple_image_card
    (I : Finset ((Edge α × Edge α) × α))
    (K H : Family α) (V : Edge α) (t : ℕ)
    (facetCenter tripleLabel : Edge α → α)
    (hI : I ⊆ badIncidences K V (n + 1) facetCenter tripleLabel) :
    ((lowerInheritanceWitnesses n I K H V t tripleLabel).image
      lowerWitnessTuple).card =
      (lowerInheritanceWitnesses n I K H V t tripleLabel).card := by
  classical
  exact Finset.card_image_of_injOn
    (lower_witness_tuple_injective n I K H V t facetCenter tripleLabel hI)

theorem lower_inheritance_weighted_witness_lower_bound
    (I : Finset ((Edge α × Edge α) × α))
    (K H : Family α) (V : Edge α) (t : ℕ)
    (tripleLabel : Edge α → α)
    (hFirst : ∀ i ∈ I,
      (facetParents K i.1.2).card ≤
        2 * (lowerWitnessSecondRoots K V i).card)
    (hThird : ∀ i ∈ I, ∀ R₁ ∈ lowerWitnessSecondRoots K V i,
      (parentTripleLink K V (lowerWitnessCore i)).card ≤
        2 * (lowerWitnessThirdRoots n H V t tripleLabel i R₁).card) :
    (∑ i ∈ I,
      (facetParents K i.1.2).card *
        (parentTripleLink K V (lowerWitnessCore i)).card) ≤
      4 * (lowerInheritanceWitnesses n I K H V t tripleLabel).card := by
  classical
  have hOne : ∀ i ∈ I,
      (facetParents K i.1.2).card *
          (parentTripleLink K V (lowerWitnessCore i)).card ≤
        4 * (lowerWitnessesFor n K H V t tripleLabel i).card := by
    intro i hi
    let F := lowerWitnessSecondRoots K V i
    let d := (parentTripleLink K V (lowerWitnessCore i)).card
    let T := lowerWitnessThirdRoots n H V t tripleLabel i
    have hSum : F.card * d ≤
        2 * ∑ R₁ ∈ F, (T R₁).card := by
      calc
        F.card * d = ∑ _R₁ ∈ F, d := by simp
        _ ≤ ∑ R₁ ∈ F, 2 * (T R₁).card := by
          apply Finset.sum_le_sum
          intro R₁ hR₁
          exact hThird i hi R₁ hR₁
        _ = 2 * ∑ R₁ ∈ F, (T R₁).card := by
          rw [Finset.mul_sum]
    have hFirst' := hFirst i hi
    have hCard : (lowerWitnessesFor n K H V t tripleLabel i).card =
        ∑ R₁ ∈ F, (T R₁).card := by
      simp [lowerWitnessesFor, F, T, Finset.card_sigma]
    rw [hCard]
    nlinarith
  calc
    (∑ i ∈ I,
      (facetParents K i.1.2).card *
        (parentTripleLink K V (lowerWitnessCore i)).card) ≤
        ∑ i ∈ I, 4 * (lowerWitnessesFor n K H V t tripleLabel i).card :=
      Finset.sum_le_sum hOne
    _ = 4 * ∑ i ∈ I,
          (lowerWitnessesFor n K H V t tripleLabel i).card := by
      rw [Finset.mul_sum]
    _ = 4 * (lowerInheritanceWitnesses n I K H V t tripleLabel).card := by
      simp [lowerInheritanceWitnesses, Finset.card_sigma]

end JSP523.Rank5.HigherRankLower
