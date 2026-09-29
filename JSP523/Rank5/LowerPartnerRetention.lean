import JSP523.Rank5.LowerPairLabel
import JSP523.Counting.PrefixAssignment

/-! # Retained lower-core partner bounds for rooted prefix counting -/

namespace JSP523.Rank5

open JSP523.Counting

variable {α : Type*} [DecidableEq α]

/-- IV.7's actual edge deletion gives the parent bad-partner bound on every
    retained pair root at an occurring triple core. -/
theorem retained_triple_pair_bad_partners_le
    (K H : Family α) (V : Edge α)
    (C : Family α) (t u q : ℕ)
    (tripleLabel : Edge α → α)
    (hKH : K ⊆ H)
    (hSurvive : Disjoint K
      (multilevelDeletedEdges H V C 2 u q
        (fun B P T => ¬ ActualStrongPartner H V P T 2 3 t
          (tripleLabel B))))
    {B R : Edge α} (hBC : B ∈ C)
    (hR : R ∈ parentPairLink K V B) :
    (badParentPartners H V B R
      (fun B P T => ActualStrongPartner H V P T 2 3 t
        (tripleLabel B))).card ≤ q := by
  have hKeep := retained_pair_root_survives_multilevel_cleanup
    K H V C u q
    (fun B P T => ¬ ActualStrongPartner H V P T 2 3 t
      (tripleLabel B))
    hKH hSurvive hBC hR
  have hDegree := retained_pair_root_parent_degree_ge K H V C u q
    (fun B P T => ¬ ActualStrongPartner H V P T 2 3 t (tripleLabel B))
    hKH hSurvive hBC hR
  exact retained_strong_bad_parent_partners_le H V B R t u q
    (tripleLabel B) hKeep.1 hDegree hKeep.2

/-- Every tail of an actual chosen-prefix fiber is a retained parent pair
    root at the corresponding extended triple core. -/
theorem assigned_prefix_tail_mem_retained_pair_link
    (F K : Family α) (V : Edge α)
    (chosenPrefix : Edge α → Edge α)
    (hFK : F ⊆ K)
    {P Y : Edge α} {x : α}
    (hP : P ∈ V.powersetCard 3)
    (hY : Y ∈ chosenPrefixesAt F V 2 chosenPrefix P)
    (hx : x ∈ P) :
    P.erase x ∈ parentPairLink K V (Y ∪ {x}) := by
  have hYparts := mem_chosen_prefixes_at.mp hY
  have hPV := (Finset.mem_powersetCard.mp hP).1
  have hPc := (Finset.mem_powersetCard.mp hP).2
  have hYP : Y ∪ P ∈ K := hFK hYparts.2.2.1
  have hDisj : Disjoint P (Y ∪ Y) := by
    simpa [Finset.union_self] using hYparts.2.1.symm
  have hCommon : P ∈ commonPrefixTriples K V Y Y :=
    mem_common_prefix_triples.mpr
      ⟨hPV, hPc, hDisj, hYP, hYP⟩
  exact (common_tail_erase_mem_parent_link
    (K := K) (H := K) (Finset.Subset.rfl) hCommon hx).1

/-- The actual IV.7 deletion set bounds bad partners in every assigned
    rooted-prefix fiber, with no separate partner hypothesis. -/
theorem assigned_prefix_bad_partners_le_of_cleanup
    (F K H : Family α) (V : Edge α)
    (chosenPrefix : Edge α → Edge α)
    (t u q : ℕ) (tripleLabel : Edge α → α)
    (hFK : F ⊆ K) (hKH : K ⊆ H)
    (hPrefixCard : ∀ E ∈ F, (chosenPrefix E).card = 2)
    (hSurvive : Disjoint K
      (multilevelDeletedEdges H V (V.powersetCard 3) 2 u q
        (fun B R T => ¬ ActualStrongPartner H V R T 2 3 t
          (tripleLabel B)))) :
    ∀ P ∈ V.powersetCard 3,
      ∀ Y ∈ chosenPrefixesAt F V 2 chosenPrefix P,
      ∀ x ∈ P,
        (badParentPartners H V (Y ∪ {x}) (P.erase x)
          (fun B R T => ActualStrongPartner H V R T 2 3 t
            (tripleLabel B))).card ≤ q := by
  intro P hP Y hY x hx
  have hYparts := mem_chosen_prefixes_at.mp hY
  have hYcard : Y.card = 2 := by
    have h := hPrefixCard (Y ∪ P) hYparts.2.2.1
    rw [hYparts.2.2.2] at h
    exact h
  have hYV := (Finset.mem_powersetCard.mp hYparts.1).1
  have hPV := (Finset.mem_powersetCard.mp hP).1
  have hxY : x ∉ Y := by
    intro hxY
    exact (Finset.disjoint_left.mp hYparts.2.1) hxY hx
  have hBcard : (Y ∪ {x}).card = 3 := by
    rw [Finset.union_singleton, Finset.card_insert_of_notMem hxY]
    omega
  have hBV : Y ∪ {x} ⊆ V := by
    intro a ha
    rcases Finset.mem_union.mp ha with haY | hax
    · exact hYV haY
    · exact hPV ((Finset.mem_singleton.mp hax) ▸ hx)
  have hBC : Y ∪ {x} ∈ V.powersetCard 3 :=
    Finset.mem_powersetCard.mpr ⟨hBV, hBcard⟩
  have hR := assigned_prefix_tail_mem_retained_pair_link
    F K V chosenPrefix hFK hP hY hx
  exact retained_triple_pair_bad_partners_le K H V
    (V.powersetCard 3) t u q tripleLabel hKH hSurvive
    hBC hR

end JSP523.Rank5
