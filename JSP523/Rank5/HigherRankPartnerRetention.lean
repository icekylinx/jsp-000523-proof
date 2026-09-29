import JSP523.Rank5.HigherRankPartnerLabel
import JSP523.Rank5.InheritanceLowRetention
import JSP523.Counting.AssignedPrefixGeometry

/-! # Parent partner guarantees at arbitrary rank -/
namespace JSP523.Rank5
open JSP523.Counting
variable {α : Type*} [DecidableEq α]

/-- Actual multilevel cleanup bounds exceptional partners for any core rank. -/
theorem higher_retained_pair_bad_partners_le
    (K H : Family α) (V : Edge α) (C : Family α) (u q : ℕ)
    (good : Edge α → Edge α → Edge α → Prop)
    (hKH : K ⊆ H)
    (hSurvive : Disjoint K
      (multilevelDeletedEdges H V C 2 u q (fun B P T => ¬ good B P T)))
    {B R : Edge α} (hBC : B ∈ C)
    (hR : R ∈ parentPairLink K V B) :
    (badParentPartners H V B R good).card ≤ q := by
  classical
  have hKeep := retained_pair_root_survives_multilevel_cleanup
    K H V C u q (fun B P T => ¬ good B P T) hKH hSurvive hBC hR
  have hDegree := retained_pair_root_parent_degree_ge
    K H V C u q (fun B P T => ¬ good B P T) hKH hSurvive hBC hR
  have h := retained_tail_exception_degree_le H V B R 2 u q
    (fun B P T => ¬ good B P T) hKeep.1 hDegree hKeep.2
  simpa [actualBadPartnerDegree, badParentPartners,
    actual_core_link_two_eq_parent_pair_link] using h

/-- Assigned triple tails yield retained pair roots at every prefix size. -/
theorem higher_assigned_prefix_tail_mem_pair_link
    (F K : Family α) (V : Edge α) (p : ℕ)
    (chosen : Edge α → Edge α) (hFK : F ⊆ K)
    {P Y : Edge α} {x : α}
    (hP : P ∈ V.powersetCard 3)
    (hY : Y ∈ chosenPrefixesAt F V p chosen P) (hx : x ∈ P) :
    P.erase x ∈ parentPairLink K V (Y ∪ {x}) := by
  have hy := mem_chosen_prefixes_at.mp hY
  have hp := Finset.mem_powersetCard.mp hP
  have hYP : Y ∪ P ∈ K := hFK hy.2.2.1
  have hCommon : P ∈ commonPrefixTriples K V Y Y :=
    mem_common_prefix_triples.mpr ⟨hp.1, hp.2,
      by simpa only [Finset.union_self] using hy.2.1.symm, hYP, hYP⟩
  exact (common_tail_erase_mem_parent_link
    (K := K) (H := K) Finset.Subset.rfl hCommon hx).1

/-- Cleanup supplies the relative parent-partner estimate required by the
    assigned-prefix geometry at arbitrary uniformity. -/
theorem higher_assigned_prefix_bad_partners_relative
    (F K H : Family α) (V : Edge α) (r u q : ℕ) (ε : ℝ)
    (chosen : Edge α → Edge α)
    (good : Edge α → Edge α → Edge α → Prop)
    (hr : 3 ≤ r) (hFK : F ⊆ K) (hKH : K ⊆ H)
    (hSurvive : Disjoint K
      (multilevelDeletedEdges H V (V.powersetCard (r - 2)) 2 u q
        (fun B P T => ¬ good B P T)))
    (hε : 0 ≤ ε) (hScale : (q : ℝ) ≤ ε * (u : ℝ)) :
    ∀ P ∈ V.powersetCard 3,
      ∀ Y ∈ chosenPrefixesAt F V (r - 3) chosen P, ∀ x ∈ P,
        ((badParentPartners H V (Y ∪ {x}) (P.erase x) good).card : ℝ) ≤
          ε * ((parentPairLink H V (Y ∪ {x})).card : ℝ) := by
  intro P hP Y hY x hx
  have hy := mem_chosen_prefixes_at.mp hY
  have hys := Finset.mem_powersetCard.mp hy.1
  have hp := Finset.mem_powersetCard.mp hP
  have hxY : x ∉ Y := fun hxY => (Finset.disjoint_left.mp hy.2.1) hxY hx
  have hBcard : (Y ∪ {x}).card = r - 2 := by
    rw [Finset.union_singleton, Finset.card_insert_of_notMem hxY, hys.2]
    omega
  have hBV : Y ∪ {x} ⊆ V :=
    Finset.union_subset hys.1 (Finset.singleton_subset_iff.mpr (hp.1 hx))
  have hBC : Y ∪ {x} ∈ V.powersetCard (r - 2) :=
    Finset.mem_powersetCard.mpr ⟨hBV, hBcard⟩
  have hR := higher_assigned_prefix_tail_mem_pair_link
    F K V (r - 3) chosen hFK hP hY hx
  have hBad := higher_retained_pair_bad_partners_le K H V
    (V.powersetCard (r - 2)) u q good hKH hSurvive hBC hR
  have hDegree := retained_pair_root_parent_degree_ge K H V
    (V.powersetCard (r - 2)) u q (fun B P T => ¬ good B P T)
    hKH hSurvive hBC hR
  rw [actual_core_link_two_eq_parent_pair_link] at hDegree
  have hBadReal :
      ((badParentPartners H V (Y ∪ {x}) (P.erase x) good).card : ℝ) ≤ q :=
    by exact_mod_cast hBad
  have hDegreeReal : (u : ℝ) ≤ (parentPairLink H V (Y ∪ {x})).card :=
    by exact_mod_cast hDegree
  exact hBadReal.trans (hScale.trans (mul_le_mul_of_nonneg_left hDegreeReal hε))

/-- Surviving cores have actual labels whenever the exception threshold
    is strictly below the parent-degree threshold. -/
theorem higher_actual_rank_labels_of_multilevel_cleanup
    (K H : Family α) (V : Edge α) (r t u q : ℕ) (hr : 2 ≤ r)
    (tripleLabel : Edge α → α)
    (hKH : K ⊆ H) (hUniformK : Uniform r K)
    (hAmbientK : ∀ E ∈ K, E ⊆ V) (hqu : q < u)
    (hSurvive : Disjoint K
      (multilevelDeletedEdges H V (V.powersetCard (r - 2)) 2 u q
        (fun B R T => ¬ ActualStrongPartner H V R T 2 (r - 2) t
          (tripleLabel B)))) : ActualRankLabels K (r - 2) tripleLabel := by
  classical
  intro B hB hBcard
  obtain ⟨E, hEK, hBE⟩ := hB
  have hBV : B ⊆ V := hBE.trans (hAmbientK E hEK)
  have hBC : B ∈ V.powersetCard (r - 2) := Finset.mem_powersetCard.mpr ⟨hBV, hBcard⟩
  let R := E \ B
  have hRcard : R.card = 2 := by
    dsimp [R]
    rw [Finset.card_sdiff_of_subset hBE, hUniformK hEK, hBcard]
    omega
  have hRecon : B ∪ R = E := Finset.union_sdiff_of_subset hBE
  have hR : R ∈ parentPairLink K V B := mem_parent_pair_link.mpr
    ⟨Finset.sdiff_subset.trans (hAmbientK E hEK), hRcard,
      Finset.sdiff_disjoint, hRecon.symm ▸ hEK⟩
  let bad := fun B R T => ¬ ActualStrongPartner H V R T 2 (r - 2) t (tripleLabel B)
  have hKeep := retained_pair_root_survives_multilevel_cleanup K H V
    (V.powersetCard (r - 2)) u q bad hKH hSurvive hBC hR
  have hDegree := retained_pair_root_parent_degree_ge K H V
    (V.powersetCard (r - 2)) u q bad hKH hSurvive hBC hR
  have hBad := retained_tail_exception_degree_le H V B R 2 u q bad
    hKeep.1 hDegree hKeep.2
  by_contra hz
  have hAll : ∀ T ∈ actualCoreLink H V B 2, bad B R T := by
    intro T hT hStrong
    have hp := mem_actual_core_link.mp hKeep.1
    have ht := mem_actual_core_link.mp hT
    have hCell : B ∈ commonPrefixTails H V R T (r - 2) :=
      mem_common_prefix_tails.mpr ⟨hBV, hBcard,
        Finset.disjoint_union_right.mpr ⟨hp.2.2.1.symm, ht.2.2.1.symm⟩,
        by simpa only [Finset.union_comm] using hp.2.2.2,
        by simpa only [Finset.union_comm] using ht.2.2.2⟩
    exact hz (hStrong.2.2.2.1 B hCell)
  have hBadEq : actualBadPartnerDegree H V B 2 bad R =
      (actualCoreLink H V B 2).card := by
    unfold actualBadPartnerDegree
    congr 1
    ext T
    simp only [Finset.mem_filter]
    exact ⟨And.left, fun hT => ⟨hT, hAll T hT⟩⟩
  rw [hBadEq] at hBad
  omega

end JSP523.Rank5
