import JSP523.Rank4.LocalDirtyCount
import JSP523.Coarse.GroundBound
import JSP523.Rank4.LocalExceptionalArithmetic
import JSP523.Rank4.LocalC8Arithmetic
import JSP523.Counting.BinomialThresholdBounds

/-!
# Exceptional-layer deletion in the near-star count
-/

namespace JSP523.Rank4

variable {α : Type*} [DecidableEq α]

/-- The `B₂ ∪ B₃` part of the outside family. -/
def nearStarB23 (H : Family α) (W : Edge α) (v : α) : Family α :=
  (outsideEdges H W).filter fun E =>
    2 ≤ (E ∩ badSingletonVertices H W v 4).card ∧
      (E ∩ badSingletonVertices H W v 4).card ≤ 3

/-- The one-exceptional-vertex layer of the outside family. -/
def nearStarB1 (H : Family α) (W : Edge α) (v : α) : Family α :=
  (outsideEdges H W).filter fun E =>
    (E ∩ badSingletonVertices H W v 4).card = 1

/-- Outside edges whose four vertices all lie in the exceptional set. -/
def nearStarB4 (H : Family α) (W : Edge α) (v : α) : Family α :=
  (outsideEdges H W).filter fun E =>
    (E ∩ badSingletonVertices H W v 4).card = 4

/-- Triples in `W` containing at least two exceptional vertices. -/
def nearStarExceptionalTriples (H : Family α) (W : Edge α) (v : α) : Family α :=
  W.powersetCard 3 |>.filter fun P =>
    2 ≤ (P ∩ badSingletonVertices H W v 4).card

/-- Missing star triples which meet the exceptional vertex set. -/
def nearStarDMissingTriples (H : Family α) (W : Edge α) (v : α) : Family α :=
  (missingStarTriples H W v).filter fun T =>
    0 < (T ∩ badSingletonVertices H W v 4).card

/-- The outside-ordinary missing triples, denoted M∩binom(U,3) in §III.C.7. -/
def nearStarUMissingTriples (H : Family α) (W : Edge α) (v : α) : Family α :=
  missingStarTriples H (W \ badSingletonVertices H W v 4) v

/-- Delete a selected ordinary vertex from each edge in a finite family.
The target is a family of triples. Unique ordinary completion makes this
map injective, yielding the cardinality bound used for `B₂ ∪ B₃`. -/
theorem delete_ordinary_vertex_card_bound
    {B T : Family α}
    (hUniform : Uniform 4 B)
    (choose : {E : Edge α // E ∈ B} → α)
    (hVertex : ∀ E : {E : Edge α // E ∈ B}, choose E ∈ E.val)
    (ordinary : α → Prop)
    (hOrdinary : ∀ E : {E : Edge α // E ∈ B}, ordinary (choose E))
    (hTarget : ∀ E : {E : Edge α // E ∈ B},
      E.val.erase (choose E) ∈ T)
    (hUnique : ∀ ⦃P : Edge α⦄ ⦃x y : α⦄,
      P.card = 3 → x ∉ P → y ∉ P → ordinary x → ordinary y →
      insert x P ∈ B → insert y P ∈ B → x = y) :
    B.card ≤ T.card := by
  classical
  let eraseMap : {E : Edge α // E ∈ B} → {P : Edge α // P ∈ T} :=
    fun E => ⟨E.val.erase (choose E), hTarget E⟩
  have hinj : Function.Injective eraseMap := by
    intro E F hEF
    have hP : E.val.erase (choose E) = F.val.erase (choose F) :=
      congrArg Subtype.val hEF
    have hPcard : (E.val.erase (choose E)).card = 3 := by
      rw [Finset.card_erase_of_mem (hVertex E), hUniform E.property]
    have hxNot : choose E ∉ E.val.erase (choose E) := by simp
    have hyNot : choose F ∉ E.val.erase (choose E) := by rw [hP]; simp
    have hInsE : insert (choose E) (E.val.erase (choose E)) = E.val :=
      Finset.insert_erase (hVertex E)
    have hInsF : insert (choose F) (E.val.erase (choose E)) = F.val := by
      calc
        insert (choose F) (E.val.erase (choose E)) =
            insert (choose F) (F.val.erase (choose F)) := by rw [hP]
        _ = F.val := Finset.insert_erase (hVertex F)
    have hxy := hUnique hPcard hxNot hyNot (hOrdinary E) (hOrdinary F)
      (by rw [hInsE]; exact E.property) (by rw [hInsF]; exact F.property)
    apply Subtype.ext
    rw [← hInsE, ← hInsF, hxy]
  have hcard := Fintype.card_le_of_injective eraseMap hinj
  simpa only [Fintype.card_coe] using hcard

/-- Actual `B₂ ∪ B₃` injection in the near-star setting. The exceptional
intersection has size at most three, so every edge has an ordinary vertex;
deleting it gives a triple with at least two exceptional vertices. -/
theorem near_star_b23_card_le_exceptional_triples
    {H : Family α} {W : Edge α} {v : α} [Fintype α]
    (hH : Admissible H) (hUniform : Uniform 4 H) (hvW : v ∉ W) :
    (nearStarB23 H W v).card ≤
      (nearStarExceptionalTriples H W v).card := by
  classical
  let D := badSingletonVertices H W v 4
  let B := nearStarB23 H W v
  let T := nearStarExceptionalTriples H W v
  have hData (E : {E : Edge α // E ∈ B}) :
      (E.val ∈ H ∧ E.val ⊆ W) ∧ 2 ≤ (E.val ∩ D).card ∧
        (E.val ∩ D).card ≤ 3 := by
    simpa [B, nearStarB23, outsideEdges, D] using E.property
  have hOrdExists (E : {E : Edge α // E ∈ B}) :
      ∃ x, x ∈ E.val \ D := by
    have hEq := Finset.card_sdiff_add_card_inter E.val D
    have hFour := hUniform (hData E).1.1
    have hExc := (hData E).2.2
    have hPos : 0 < (E.val \ D).card := by omega
    exact Finset.card_pos.mp hPos
  let choose : {E : Edge α // E ∈ B} → α := fun E =>
    Classical.choose (hOrdExists E)
  have hOrd (E : {E : Edge α // E ∈ B}) : choose E ∈ W \ D := by
    have hx := Classical.choose_spec (hOrdExists E)
    exact Finset.mem_sdiff.mpr ⟨(hData E).1.2 (Finset.mem_sdiff.mp hx).1,
      (Finset.mem_sdiff.mp hx).2⟩
  have hVertex (E : {E : Edge α // E ∈ B}) : choose E ∈ E.val :=
    (Finset.mem_sdiff.mp (Classical.choose_spec (hOrdExists E))).1
  have hTarget (E : {E : Edge α // E ∈ B}) :
      E.val.erase (choose E) ∈ T := by
    have hxD : choose E ∉ D := (Finset.mem_sdiff.mp (hOrd E)).2
    have hInter : E.val.erase (choose E) ∩ D = E.val ∩ D := by
      rw [Finset.erase_inter]
      simp [hxD]
    have hCard : (E.val.erase (choose E)).card = 3 := by
      rw [Finset.card_erase_of_mem (hVertex E), hUniform (hData E).1.1]
    have hSub : E.val.erase (choose E) ⊆ W :=
      fun x hx => (hData E).1.2 (Finset.mem_of_mem_erase hx)
    simp only [T, nearStarExceptionalTriples, Finset.mem_filter,
      Finset.mem_powersetCard]
    exact ⟨⟨hSub, hCard⟩, by rw [hInter]; exact (hData E).2.1⟩
  have hUnique : ∀ ⦃P : Edge α⦄ ⦃x y : α⦄,
      P.card = 3 → x ∉ P → y ∉ P → x ∈ W \ D → y ∈ W \ D →
      insert x P ∈ B → insert y P ∈ B → x = y := by
    intro P x y hPcard hxP hyP hxOrd hyOrd hEx hEy
    by_contra hxy
    have hExData : (insert x P ∈ H ∧ insert x P ⊆ W) ∧
        2 ≤ (insert x P ∩ D).card ∧ (insert x P ∩ D).card ≤ 3 := by
      simpa [B, nearStarB23, outsideEdges, D] using hEx
    have hEyData : (insert y P ∈ H ∧ insert y P ⊆ W) ∧
        2 ≤ (insert y P ∩ D).card ∧ (insert y P ∩ D).card ≤ 3 := by
      simpa [B, nearStarB23, outsideEdges, D] using hEy
    have hPsub : P ⊆ W := fun z hz => hExData.1.2 (Finset.mem_insert_of_mem hz)
    exact ordinary_vertices_unique_facet_completion hH hUniform hPsub
      (by omega) (by omega) hvW (by simpa [D] using hxOrd)
      (by simpa [D] using hyOrd) hxy hExData.1.1 hEyData.1.1
  have hBuniform : Uniform 4 B := by
    intro E hE
    exact hUniform ((hData ⟨E, hE⟩).1.1)
  exact delete_ordinary_vertex_card_bound hBuniform choose hVertex
    (fun x => x ∈ W \ D) hOrd hTarget hUnique

/-- The exceptional-triple family has at most choose(d,2) * (w-2) members.
Encode each triple by a chosen exceptional pair and its remaining singleton. -/
theorem near_star_exceptional_triples_card_le
    {H : Family α} {W : Edge α} {v : α} [Fintype α] :
    (nearStarExceptionalTriples H W v).card ≤
      (badSingletonVertices H W v 4).card.choose 2 * (W.card - 2) := by
  classical
  let D := badSingletonVertices H W v 4
  have hD : D ⊆ W := by
    intro x hx
    exact (Finset.mem_filter.mp hx).1
  let PairSet := D.powersetCard 2
  let Codes : Finset (Σ P : Edge α, Edge α) :=
    PairSet.sigma fun P => (W \ P).powersetCard 1
  let choosePair (T : {T : Edge α // T ∈ nearStarExceptionalTriples H W v}) :
      Edge α := Classical.choose (Finset.powersetCard_nonempty.mpr (by
        have h := (Finset.mem_filter.mp T.property).2
        exact h))
  let code (T : {T : Edge α // T ∈ nearStarExceptionalTriples H W v}) :
      Σ P : Edge α, Edge α :=
    ⟨choosePair T, T.val \ choosePair T⟩
  have hCode (T : {T : Edge α // T ∈ nearStarExceptionalTriples H W v}) :
      code T ∈ Codes := by
    have hT := Finset.mem_powersetCard.mp
      ((Finset.mem_filter.mp T.property).1)
    have hMany := (Finset.mem_filter.mp T.property).2
    have hPspec := Classical.choose_spec (Finset.powersetCard_nonempty.mpr hMany)
    have hPsubT : choosePair T ⊆ T.val := by
      intro x hx
      exact (Finset.mem_inter.mp (Finset.mem_powersetCard.mp hPspec |>.1 hx)).1
    have hPsubD : choosePair T ⊆ D := by
      intro x hx
      exact (Finset.mem_inter.mp (Finset.mem_powersetCard.mp hPspec |>.1 hx)).2
    have hPcard : (choosePair T).card = 2 := (Finset.mem_powersetCard.mp hPspec).2
    have hRcard : (T.val \ choosePair T).card = 1 := by
      have hEq := Finset.card_sdiff_add_card_inter T.val (choosePair T)
      have hInter : T.val ∩ choosePair T = choosePair T :=
        Finset.inter_eq_right.mpr hPsubT
      rw [hInter, hT.2, hPcard] at hEq
      omega
    have hRsub : T.val \ choosePair T ⊆ W \ choosePair T := by
      intro x hx
      exact Finset.mem_sdiff.mpr ⟨hT.1 (Finset.mem_sdiff.mp hx).1,
        (Finset.mem_sdiff.mp hx).2⟩
    change ⟨choosePair T, T.val \ choosePair T⟩ ∈
      PairSet.sigma (fun P => (W \ P).powersetCard 1)
    simp only [Finset.mem_sigma]
    exact ⟨Finset.mem_powersetCard.mpr ⟨hPsubD, hPcard⟩,
      Finset.mem_powersetCard.mpr ⟨hRsub, hRcard⟩⟩
  have hInj : Function.Injective (fun T => (⟨code T, hCode T⟩ : {c : Σ P : Edge α, Edge α // c ∈ Codes})) := by
    intro T T' hEq
    have hp : choosePair T = choosePair T' := congrArg (fun c => c.val.1) hEq
    have hr : T.val \ choosePair T = T'.val \ choosePair T' :=
      congrArg (fun c => c.val.2) hEq
    have hPsub : choosePair T ⊆ T.val := by
      have hs := Classical.choose_spec (Finset.powersetCard_nonempty.mpr
        ((Finset.mem_filter.mp T.property).2))
      exact fun x hx => (Finset.mem_inter.mp (Finset.mem_powersetCard.mp hs |>.1 hx)).1
    have hPsub' : choosePair T' ⊆ T'.val := by
      have hs := Classical.choose_spec (Finset.powersetCard_nonempty.mpr
        ((Finset.mem_filter.mp T'.property).2))
      exact fun x hx => (Finset.mem_inter.mp (Finset.mem_powersetCard.mp hs |>.1 hx)).1
    have hUnion : choosePair T ∪ (T.val \ choosePair T) = T.val :=
      Finset.union_sdiff_of_subset hPsub
    have hUnion' : choosePair T' ∪ (T'.val \ choosePair T') = T'.val :=
      Finset.union_sdiff_of_subset hPsub'
    apply Subtype.ext
    calc
      T.val = choosePair T ∪ (T.val \ choosePair T) := hUnion.symm
      _ = choosePair T' ∪ (T'.val \ choosePair T') :=
        congrArg₂ (fun P R : Edge α => P ∪ R) hp hr
      _ = T'.val := hUnion'
  have hCardCode : Codes.card =
      (D.powersetCard 2).card * (W.card - 2) := by
    have hsum : Codes.card =
        ∑ P ∈ D.powersetCard 2, ((W \ P).powersetCard 1).card := by
      simp [Codes, PairSet, Finset.sigma, Multiset.card_sigma]
    rw [hsum]
    calc
      (∑ P ∈ D.powersetCard 2, ((W \ P).powersetCard 1).card) =
          ∑ _P ∈ D.powersetCard 2, (W.card - 2) := by
        apply Finset.sum_congr rfl
        intro P hP
        have hPsub : P ⊆ W := (Finset.mem_powersetCard.mp hP).1.trans hD
        have hPcard : P.card = 2 := (Finset.mem_powersetCard.mp hP).2
        have hdiff : (W \ P).card = W.card - 2 := by
          rw [Finset.card_sdiff_of_subset hPsub, hPcard]
        simp [hdiff, Nat.choose_one_right]
      _ = (D.powersetCard 2).card * (W.card - 2) := by simp
  have hCardle := Fintype.card_le_of_injective
    (fun T : {T : Edge α // T ∈ nearStarExceptionalTriples H W v} =>
      (⟨code T, hCode T⟩ : {c : Σ P : Edge α, Edge α // c ∈ Codes})) hInj
  have hDpair : (D.powersetCard 2).card = D.card.choose 2 := by
    simp [Finset.card_powersetCard]
  simpa only [Fintype.card_coe, hCardCode, hDpair] using hCardle

/-- Combined actual B₂∪B₃ estimate by the manuscript's J term. -/
theorem near_star_b23_card_le_j
    {H : Family α} {W : Edge α} {v : α} [Fintype α]
    (hH : Admissible H) (hUniform : Uniform 4 H) (hvW : v ∉ W) :
    (nearStarB23 H W v).card ≤
      (badSingletonVertices H W v 4).card.choose 2 * (W.card - 2) := by
  exact (near_star_b23_card_le_exceptional_triples hH hUniform hvW).trans
    near_star_exceptional_triples_card_le

/-- Count pair/triple incidences involving exceptional vertices by encoding
an incidence as the pair and the remaining singleton. -/
theorem near_star_missing_pair_incidence_le_j
    {H : Family α} {W : Edge α} {v : α} [Fintype α] :
    (∑ T ∈ missingStarTriples H W v,
      ((T ∩ badSingletonVertices H W v 4).powersetCard 2).card) ≤
      (badSingletonVertices H W v 4).card.choose 2 * (W.card - 2) := by
  classical
  let D := badSingletonVertices H W v 4
  let M := missingStarTriples H W v
  let Pairs := D.powersetCard 2
  let Codes : Finset (Σ P : Edge α, Edge α) :=
    Pairs.sigma fun P => (W \ P).powersetCard 1
  let Inc : Finset (Σ T : Edge α, Edge α) :=
    M.sigma fun T => (T ∩ D).powersetCard 2
  have hDsub : D ⊆ W := by
    intro x hx
    exact (Finset.mem_filter.mp hx).1
  have hIncData (z : {z : Σ T : Edge α, Edge α // z ∈ Inc}) :
      z.val.1 ∈ M ∧ z.val.2 ∈ (z.val.1 ∩ D).powersetCard 2 := by
    have hz := z.property
    simpa only [Inc, Finset.mem_sigma] using hz
  let code (z : {z : Σ T : Edge α, Edge α // z ∈ Inc}) :
      Σ P : Edge α, Edge α :=
    ⟨z.val.2, z.val.1 \ z.val.2⟩
  have hCode (z : {z : Σ T : Edge α, Edge α // z ∈ Inc}) :
      code z ∈ Codes := by
    have hT := Finset.mem_powersetCard.mp
      ((Finset.mem_filter.mp (hIncData z).1).1)
    have hP := Finset.mem_powersetCard.mp (hIncData z).2
    have hPsubT : z.val.2 ⊆ z.val.1 :=
      hP.1.trans Finset.inter_subset_left
    have hPsubD : z.val.2 ⊆ D :=
      hP.1.trans Finset.inter_subset_right
    have hPcard : z.val.2.card = 2 := hP.2
    have hRcard : (z.val.1 \ z.val.2).card = 1 := by
      have hEq := Finset.card_sdiff_add_card_inter z.val.1 z.val.2
      have hInter := Finset.inter_eq_right.mpr hPsubT
      rw [hInter, hT.2, hPcard] at hEq
      omega
    have hRsub : z.val.1 \ z.val.2 ⊆ W \ z.val.2 := by
      intro x hx
      exact Finset.mem_sdiff.mpr
        ⟨(Finset.mem_powersetCard.mp
            (Finset.mem_filter.mp (hIncData z).1).1).1
            ((Finset.mem_sdiff.mp hx).1),
          (Finset.mem_sdiff.mp hx).2⟩
    change ⟨z.val.2, z.val.1 \ z.val.2⟩ ∈
      Pairs.sigma (fun P => (W \ P).powersetCard 1)
    simp only [Finset.mem_sigma]
    exact ⟨Finset.mem_powersetCard.mpr ⟨hPsubD, hPcard⟩,
      Finset.mem_powersetCard.mpr ⟨hRsub, hRcard⟩⟩
  have hInj : Function.Injective (fun z =>
      (⟨code z, hCode z⟩ : {c : Σ P : Edge α, Edge α // c ∈ Codes})) := by
    intro z z' hEq
    have hp : z.val.2 = z'.val.2 := congrArg (fun c => c.val.1) hEq
    have hr : z.val.1 \ z.val.2 = z'.val.1 \ z'.val.2 :=
      congrArg (fun c => c.val.2) hEq
    have hPsub : z.val.2 ⊆ z.val.1 :=
      (Finset.mem_powersetCard.mp (hIncData z).2).1.trans Finset.inter_subset_left
    have hPsub' : z'.val.2 ⊆ z'.val.1 :=
      (Finset.mem_powersetCard.mp (hIncData z').2).1.trans Finset.inter_subset_left
    have hU : z.val.2 ∪ (z.val.1 \ z.val.2) = z.val.1 :=
      Finset.union_sdiff_of_subset hPsub
    have hU' : z'.val.2 ∪ (z'.val.1 \ z'.val.2) = z'.val.1 :=
      Finset.union_sdiff_of_subset hPsub'
    apply Subtype.ext
    apply Sigma.ext
    · calc
        z.val.1 = z.val.2 ∪ (z.val.1 \ z.val.2) := hU.symm
        _ = z'.val.2 ∪ (z'.val.1 \ z'.val.2) :=
          congrArg₂ (fun P R : Edge α => P ∪ R) hp hr
        _ = z'.val.1 := hU'
    · exact heq_of_eq hp
  have hIncCard : Inc.card =
      ∑ T ∈ M, ((T ∩ D).powersetCard 2).card := by
    simp [Inc, Finset.sigma, Multiset.card_sigma]
  have hCodesCard : Codes.card = (Pairs.card) * (W.card - 2) := by
    have hsum : Codes.card =
        ∑ P ∈ Pairs, ((W \ P).powersetCard 1).card := by
      simp [Codes, Pairs, Finset.sigma, Multiset.card_sigma]
    rw [hsum]
    calc
      (∑ P ∈ Pairs, ((W \ P).powersetCard 1).card) =
          ∑ _P ∈ Pairs, (W.card - 2) := by
        apply Finset.sum_congr rfl
        intro P hP
        have hPsub : P ⊆ W := (Finset.mem_powersetCard.mp hP).1.trans hDsub
        have hPcard : P.card = 2 := (Finset.mem_powersetCard.mp hP).2
        have hdiff : (W \ P).card = W.card - 2 := by
          rw [Finset.card_sdiff_of_subset hPsub, hPcard]
        simp [hdiff, Nat.choose_one_right]
      _ = Pairs.card * (W.card - 2) := by simp
  have hLe := Fintype.card_le_of_injective
    (fun z : {z : Σ T : Edge α, Edge α // z ∈ Inc} =>
      (⟨code z, hCode z⟩ : {c : Σ P : Edge α, Edge α // c ∈ Codes})) hInj
  have hPairsCard : Pairs.card = D.card.choose 2 := by
    simp [Pairs, Finset.card_powersetCard]
  have hFinal : Inc.card ≤ Codes.card := by
    simpa only [Fintype.card_coe] using hLe
  rw [hIncCard, hCodesCard, hPairsCard] at hFinal
  simpa [D] using hFinal

/-- The singleton multiplicity sum on D is paid for by missing triples
meeting D plus pair/triple incidences. -/
theorem near_star_bad_singleton_multiplicity_sum_le
    {H : Family α} {W : Edge α} {v : α} [Fintype α] :
    (∑ a ∈ badSingletonVertices H W v 4,
      setMultiplicity (missingStarTriples H W v) ({a} : Edge α)) ≤
      (nearStarDMissingTriples H W v).card +
        (badSingletonVertices H W v 4).card.choose 2 * (W.card - 2) := by
  classical
  let D := badSingletonVertices H W v 4
  let M := missingStarTriples H W v
  let J := D.card.choose 2 * (W.card - 2)
  have hIdentity :
      (∑ a ∈ D, setMultiplicity M ({a} : Edge α)) =
        ∑ T ∈ M, (T ∩ D).card := by
    simp_rw [setMultiplicity, Finset.card_filter]
    calc
      (∑ a ∈ D, ∑ T ∈ M, if ({a} : Edge α) ⊆ T then 1 else 0) =
          ∑ T ∈ M, ∑ a ∈ D, if a ∈ T then 1 else 0 := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro T hT
        apply Finset.sum_congr rfl
        intro a ha
        simp
      _ = ∑ T ∈ M, (T ∩ D).card := by
        apply Finset.sum_congr rfl
        intro T hT
        have hfilter : D.filter (fun a => a ∈ T) = T ∩ D := by
          ext a
          simp [and_comm]
        rw [← Finset.card_filter, hfilter]
  have hTerm (T : Edge α) (hT : T ∈ M) :
      (T ∩ D).card ≤
        (if 0 < (T ∩ D).card then 1 else 0) +
          ((T ∩ D).powersetCard 2).card := by
    have hTcard : T.card = 3 := by
      exact (Finset.mem_powersetCard.mp
        (Finset.mem_filter.mp hT).1).2
    have hm : (T ∩ D).card ≤ 3 :=
      (Finset.card_le_card Finset.inter_subset_left).trans_eq hTcard
    have hchoose : ((T ∩ D).powersetCard 2).card =
        ((T ∩ D).card).choose 2 := by simp [Finset.card_powersetCard]
    rw [hchoose]
    interval_cases hmval : (T ∩ D).card <;> norm_num [hmval]
  have hsumTerm :
      (∑ T ∈ M, (T ∩ D).card) ≤
        (∑ T ∈ M, if 0 < (T ∩ D).card then 1 else 0) +
          ∑ T ∈ M, ((T ∩ D).powersetCard 2).card := by
    calc
      (∑ T ∈ M, (T ∩ D).card) ≤
          ∑ T ∈ M,
            ((if 0 < (T ∩ D).card then 1 else 0) +
              ((T ∩ D).powersetCard 2).card) :=
        Finset.sum_le_sum fun T hT => hTerm T hT
      _ = _ := by simp [Finset.sum_add_distrib]
  have hFirst :
      (∑ T ∈ M, if 0 < (T ∩ D).card then 1 else 0) =
        (nearStarDMissingTriples H W v).card := by
    change (∑ T ∈ M, if 0 < (T ∩ D).card then 1 else 0) =
      (M.filter fun T => 0 < (T ∩ D).card).card
    rw [Finset.card_filter]
  have hPairs := near_star_missing_pair_incidence_le_j (H := H) (W := W) (v := v)
  have hResult :
      (∑ a ∈ D, setMultiplicity M ({a} : Edge α)) ≤
        (nearStarDMissingTriples H W v).card + J := by
    rw [hIdentity]
    calc
      (∑ T ∈ M, (T ∩ D).card) ≤
          (∑ T ∈ M, if 0 < (T ∩ D).card then 1 else 0) +
            ∑ T ∈ M, ((T ∩ D).powersetCard 2).card := hsumTerm
      _ ≤ (nearStarDMissingTriples H W v).card + J := by
        rw [hFirst]
        exact Nat.add_le_add_left hPairs _
  simpa [D, J, M] using hResult

/-- The exact singleton exceptional-set incidence estimate with the
additional J allowance from triples containing multiple exceptional points. -/
theorem near_star_bad_singleton_incidence_le_q_d_add_j
    {H : Family α} {W : Edge α} {v : α} [Fintype α] :
    let Λ := (W.card - 5).choose 2
    Λ * (badSingletonVertices H W v 4).card ≤
      2 * ((nearStarDMissingTriples H W v).card +
        (badSingletonVertices H W v 4).card.choose 2 * (W.card - 2)) := by
  classical
  dsimp only
  let D := badSingletonVertices H W v 4
  let M := missingStarTriples H W v
  let Λ := (W.card - 5).choose 2
  have hThreshold : ∀ a ∈ D, Λ ≤ 2 * setMultiplicity M ({a} : Edge α) := by
    intro a ha
    have hBad := (Finset.mem_filter.mp ha).2
    change {a} ∈ badMissingSets H W v 4 1 Λ at hBad
    have hBad' := Finset.mem_filter.mp hBad
    have hMultiplicity := hBad'.2
    simpa [M, Λ, missingStarFacets, missingStarTriples] using hMultiplicity
  have hLower : Λ * D.card ≤
      ∑ a ∈ D, 2 * setMultiplicity M ({a} : Edge α) := by
    calc
      Λ * D.card = D.card * Λ := Nat.mul_comm _ _
      _ = ∑ _a ∈ D, Λ := by simp [Finset.sum_const]
      _ ≤ _ := Finset.sum_le_sum fun a ha => hThreshold a ha
  have hMult :=
    near_star_bad_singleton_multiplicity_sum_le (H := H) (W := W) (v := v)
  have hBound : Λ * D.card ≤
      2 * ((nearStarDMissingTriples H W v).card + D.card.choose 2 * (W.card - 2)) := by
    calc
      Λ * D.card ≤ ∑ a ∈ D, 2 * setMultiplicity M ({a} : Edge α) := hLower
      _ = 2 * ∑ a ∈ D, setMultiplicity M ({a} : Edge α) := by
        rw [Finset.mul_sum]
      _ ≤ 2 * ((nearStarDMissingTriples H W v).card +
          D.card.choose 2 * (W.card - 2)) := by
        exact Nat.mul_le_mul_left 2 (by simpa [D, M] using hMult)
  simpa [D, Λ] using hBound

/-- Missing triples partition into those wholly on U and those meeting D. -/
theorem near_star_missing_triples_partition
    {H : Family α} {W : Edge α} {v : α} :
    (nearStarUMissingTriples H W v).card +
      (nearStarDMissingTriples H W v).card =
        (missingStarTriples H W v).card := by
  classical
  let D := badSingletonVertices H W v 4
  let M := missingStarTriples H W v
  have hZero : M.filter (fun T => ¬ 0 < (T ∩ D).card) =
      nearStarUMissingTriples H W v := by
    ext T
    constructor
    · intro hT
      have hTdata := Finset.mem_filter.mp hT
      have hM := Finset.mem_filter.mp hTdata.1
      have hZeroCard : (T ∩ D).card = 0 := by omega
      have hEmpty : T ∩ D = ∅ := Finset.card_eq_zero.mp hZeroCard
      have hTU : T ⊆ W \ D := by
        intro x hx
        have hxW := (Finset.mem_powersetCard.mp hM.1).1 hx
        apply Finset.mem_sdiff.mpr
        refine ⟨hxW, ?_⟩
        intro hxD
        have : x ∈ T ∩ D := Finset.mem_inter.mpr ⟨hx, hxD⟩
        simp [hEmpty] at this
      have hTarget : T ∈ nearStarUMissingTriples H W v := by
        simp [nearStarUMissingTriples, missingStarTriples]
        exact ⟨⟨hTU, (Finset.mem_powersetCard.mp hM.1).2⟩, hM.2⟩
      exact hTarget
    · intro hT
      have hTdata : T ∈ missingStarTriples H (W \ D) v := by
        simpa [nearStarUMissingTriples] using hT
      have hU := Finset.mem_filter.mp hTdata
      have hTsubsetU := (Finset.mem_powersetCard.mp hU.1).1
      have hTsubsetW : T ⊆ W := hTsubsetU.trans Finset.sdiff_subset
      have hEmpty : T ∩ D = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        exact (Finset.mem_sdiff.mp (hTsubsetU (Finset.mem_inter.mp hx).1)).2
          (Finset.mem_inter.mp hx).2
      have hM : T ∈ M := by
        change T ∈ missingStarTriples H W v
        unfold missingStarTriples
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_powersetCard.mpr ⟨hTsubsetW,
          (Finset.mem_powersetCard.mp hU.1).2⟩, hU.2⟩
      exact Finset.mem_filter.mpr ⟨hM, by simp [hEmpty]⟩
  have hSplit := Finset.card_filter_add_card_filter_not
    (s := M) (p := fun T => 0 < (T ∩ D).card)
  have hD : M.filter (fun T => 0 < (T ∩ D).card) =
      nearStarDMissingTriples H W v := by rfl
  rw [hD, hZero] at hSplit
  simpa [M, Nat.add_comm] using hSplit

/-- The B₁ incidence bound in (III.C.7): each edge contributes its three
ordinary pairs, and a pair together with its exceptional vertex has at most
one ordinary completion. -/
theorem near_star_b1_three_incidence_bound
    {H : Family α} {W : Edge α} {v : α} [Fintype α]
    (hH : Admissible H) (hUniform : Uniform 4 H) (hvW : v ∉ W) :
    3 * (nearStarB1 H W v).card ≤
      (badSingletonVertices H W v 4).card *
        (W \ badSingletonVertices H W v 4).card.choose 2 := by
  classical
  let D := badSingletonVertices H W v 4
  let U := W \ D
  let B := nearStarB1 H W v
  let Inc : Finset (Σ E : Edge α, Edge α) :=
    B.sigma fun E => (E \ D).powersetCard 2
  let Target : Finset (α × Edge α) := D.product (U.powersetCard 2)
  have hData (E : {E : Edge α // E ∈ B}) :
      (E.val ∈ H ∧ E.val ⊆ W) ∧ (E.val ∩ D).card = 1 := by
    simpa [B, nearStarB1, outsideEdges, D] using E.property
  let badPoint (E : {E : Edge α // E ∈ B}) : α :=
    Classical.choose (Finset.card_eq_one.mp (hData E).2)
  have hBadPoint (E : {E : Edge α // E ∈ B}) :
      E.val ∩ D = {badPoint E} :=
    Classical.choose_spec (Finset.card_eq_one.mp (hData E).2)
  have hIncData (z : {z : Σ E : Edge α, Edge α // z ∈ Inc}) :
      z.val.1 ∈ B ∧ z.val.2 ∈ (z.val.1 \ D).powersetCard 2 := by
    constructor
    · exact (Finset.mem_sigma.mp (show z.val ∈ Inc from z.property)).1
    · simpa using (Finset.mem_sigma.mp (show z.val ∈ Inc from z.property)).2
  let code (z : {z : Σ E : Edge α, Edge α // z ∈ Inc}) : α × Edge α :=
    (badPoint ⟨z.val.1, (hIncData z).1⟩, z.val.2)
  have hCode (z : {z : Σ E : Edge α, Edge α // z ∈ Inc}) :
      code z ∈ Target := by
    have hE := hData ⟨z.val.1, (hIncData z).1⟩
    have hQ := Finset.mem_powersetCard.mp (hIncData z).2
    let eSub : {E : Edge α // E ∈ B} := ⟨z.val.1, (hIncData z).1⟩
    have haIn : badPoint eSub ∈ z.val.1 ∩ D := by
      have hs := hBadPoint eSub
      change z.val.1 ∩ D = {badPoint eSub} at hs
      simp [hs]
    have haD : badPoint eSub ∈ D := (Finset.mem_inter.mp haIn).2
    have hQsubU : z.val.2 ⊆ U := by
      intro x hx
      rcases Finset.mem_sdiff.mp (hQ.1 hx) with ⟨hxE, hxD⟩
      exact Finset.mem_sdiff.mpr ⟨hE.1.2 hxE, hxD⟩
    exact Finset.mem_product.mpr
      ⟨haD, Finset.mem_powersetCard.mpr ⟨hQsubU, hQ.2⟩⟩
  have hInjective : Function.Injective (fun z =>
      (⟨code z, hCode z⟩ : {p : α × Edge α // p ∈ Target})) := by
    intro z z' hEq
    have ha : badPoint ⟨z.val.1, (hIncData z).1⟩ =
        badPoint ⟨z'.val.1, (hIncData z').1⟩ := congrArg (fun p => p.val.1) hEq
    have hQ : z.val.2 = z'.val.2 := congrArg (fun p => p.val.2) hEq
    let E : Edge α := z.val.1
    let F : Edge α := z'.val.1
    let a : α := badPoint ⟨E, (hIncData z).1⟩
    let Q : Edge α := z.val.2
    have hEData : (E ∈ H ∧ E ⊆ W) ∧ (E ∩ D).card = 1 :=
      hData ⟨E, (hIncData z).1⟩
    have hFData : (F ∈ H ∧ F ⊆ W) ∧ (F ∩ D).card = 1 :=
      hData ⟨F, (hIncData z').1⟩
    have haEq : badPoint ⟨F, (hIncData z').1⟩ = a := by
      exact ha.symm
    have hEa : E ∩ D = {a} := hBadPoint ⟨E, (hIncData z).1⟩
    have hFa : F ∩ D = {a} := by
      have hs := hBadPoint ⟨F, (hIncData z').1⟩
      change F ∩ D = {badPoint ⟨F, (hIncData z').1⟩} at hs
      rw [haEq] at hs
      exact hs
    have hQsubE : Q ⊆ E \ D := (Finset.mem_powersetCard.mp (hIncData z).2).1
    have hQsubF : Q ⊆ F \ D := by
      change z.val.2 ⊆ z'.val.1 \ D
      rw [hQ]
      exact (Finset.mem_powersetCard.mp (hIncData z').2).1
    have hQcard : Q.card = 2 :=
      (Finset.mem_powersetCard.mp (hIncData z).2).2
    have haE : a ∈ E := by
      have : a ∈ E ∩ D := by rw [hEa]; simp
      exact (Finset.mem_inter.mp this).1
    have haF : a ∈ F := by
      have : a ∈ F ∩ D := by rw [hFa]; simp
      exact (Finset.mem_inter.mp this).1
    have haNotQ : a ∉ Q := by
      intro haQ
      exact (Finset.mem_sdiff.mp (hQsubE haQ)).2
        ((Finset.mem_inter.mp (by rw [hEa]; simp : a ∈ E ∩ D)).2)
    have hPcard : (insert a Q).card = 3 := by
      rw [Finset.card_insert_of_notMem haNotQ, hQcard]
    have hPsubE : insert a Q ⊆ E := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxQ
      · exact haE
      · exact (Finset.mem_sdiff.mp (hQsubE hxQ)).1
    have hPsubF : insert a Q ⊆ F := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxQ
      · exact haF
      · exact (Finset.mem_sdiff.mp (hQsubF hxQ)).1
    have hEcard := hUniform hEData.1.1
    have hFcard := hUniform hFData.1.1
    have hDiffE : (E \ insert a Q).card = 1 := by
      have hEq := Finset.card_sdiff_add_card_inter E (insert a Q)
      have hInter : E ∩ insert a Q = insert a Q :=
        Finset.inter_eq_right.mpr hPsubE
      rw [hInter, hEcard, hPcard] at hEq
      omega
    have hDiffF : (F \ insert a Q).card = 1 := by
      have hEq := Finset.card_sdiff_add_card_inter F (insert a Q)
      have hInter : F ∩ insert a Q = insert a Q :=
        Finset.inter_eq_right.mpr hPsubF
      rw [hInter, hFcard, hPcard] at hEq
      omega
    obtain ⟨x, hxEq⟩ := Finset.card_eq_one.mp hDiffE
    obtain ⟨y, hyEq⟩ := Finset.card_eq_one.mp hDiffF
    have hxMem : x ∈ E \ insert a Q := by rw [hxEq]; simp
    have hyMem : y ∈ F \ insert a Q := by rw [hyEq]; simp
    have hxOrd : x ∈ W \ D := by
      have hxE := (Finset.mem_sdiff.mp hxMem).1
      have hxW := hEData.1.2 hxE
      have hxD : x ∉ D := by
        intro hxD
        have hxInter : x ∈ E ∩ D := Finset.mem_inter.mpr ⟨hxE, hxD⟩
        have hxA : x = a := by simpa [hEa] using hxInter
        exact (Finset.mem_sdiff.mp hxMem).2 (hxA ▸ Finset.mem_insert_self a Q)
      exact Finset.mem_sdiff.mpr ⟨hxW, hxD⟩
    have hyOrd : y ∈ W \ D := by
      have hyF := (Finset.mem_sdiff.mp hyMem).1
      have hyW := hFData.1.2 hyF
      have hyD : y ∉ D := by
        intro hyD
        have hyInter : y ∈ F ∩ D := Finset.mem_inter.mpr ⟨hyF, hyD⟩
        have hyA : y = a := by simpa [hFa] using hyInter
        exact (Finset.mem_sdiff.mp hyMem).2 (hyA ▸ Finset.mem_insert_self a Q)
      exact Finset.mem_sdiff.mpr ⟨hyW, hyD⟩
    have hPsubW : insert a Q ⊆ W :=
      hPsubE.trans hEData.1.2
    have hInsertE : insert x (insert a Q) = E := by
      apply Finset.eq_of_subset_of_card_le
      · intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hzP
        · exact (Finset.mem_sdiff.mp hxMem).1
        · exact hPsubE hzP
      · rw [Finset.card_insert_of_notMem (by
          intro hxP
          exact (Finset.mem_sdiff.mp hxMem).2 hxP), hPcard, hEcard]
    have hInsertF : insert y (insert a Q) = F := by
      apply Finset.eq_of_subset_of_card_le
      · intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hzP
        · exact (Finset.mem_sdiff.mp hyMem).1
        · exact hPsubF hzP
      · rw [Finset.card_insert_of_notMem (by
          intro hyP
          exact (Finset.mem_sdiff.mp hyMem).2 hyP), hPcard, hFcard]
    have hxy : x = y := by
      by_contra hne
      have hxH : insert x (insert a Q) ∈ H := by
        rw [hInsertE]
        exact hEData.1.1
      have hyH : insert y (insert a Q) ∈ H := by
        rw [hInsertF]
        exact hFData.1.1
      exact ordinary_vertices_unique_facet_completion hH hUniform hPsubW
        hPcard (by omega) hvW hxOrd hyOrd hne hxH hyH
    have hEF : E = F := by
      rw [← hInsertE, ← hInsertF, hxy]
    apply Subtype.ext
    exact Sigma.ext hEF (by simpa [E, F] using hQ)
  have hIncCard : Inc.card = 3 * B.card := by
    have hsum : Inc.card = ∑ E ∈ B, ((E \ D).powersetCard 2).card := by
      simp [Inc, Finset.sigma, Multiset.card_sigma]
    rw [hsum]
    calc
      (∑ E ∈ B, ((E \ D).powersetCard 2).card) =
          ∑ _E ∈ B, 3 := by
        apply Finset.sum_congr rfl
        intro E hE
        have h := hData ⟨E, hE⟩
        have hfour := hUniform h.1.1
        change E.card = 4 at hfour
        have hdiff := Finset.card_sdiff_add_card_inter E D
        rw [Finset.inter_comm] at hdiff
        change (E \ D).card + (D ∩ E).card = E.card at hdiff
        have hint : (D ∩ E).card = 1 := by simpa [Finset.inter_comm] using h.2
        rw [hint] at hdiff
        have hOrdCard : (E \ D).card = 3 := by omega
        simp [hOrdCard]
      _ = 3 * B.card := by simp [mul_comm]
  have hTargetCard : Target.card = D.card * (U.powersetCard 2).card := by
    simp [Target, Finset.card_product]
  have hTargetCount := Fintype.card_le_of_injective
    (fun z : {z : Σ E : Edge α, Edge α // z ∈ Inc} =>
      (⟨code z, hCode z⟩ : {p : α × Edge α // p ∈ Target})) hInjective
  have hUCard : (U.powersetCard 2).card = U.card.choose 2 := by
    simp [Finset.card_powersetCard]
  have hFinal : Inc.card ≤ Target.card := by
    simpa only [Fintype.card_coe] using hTargetCount
  rw [hIncCard, hTargetCard, hUCard] at hFinal
  simpa [B, U, D] using hFinal

/-- The all-exceptional layer is controlled by the finite coarse theorem on
the ground set D, giving the manuscript's 32 d^3 bound. -/
theorem near_star_b4_coarse_bound
    {H : Family α} {W : Edge α} {v : α}
    (hUniform : Uniform 4 H) (hH : Admissible H) :
    (nearStarB4 H W v).card ≤
      32 * (badSingletonVertices H W v 4).card ^ 3 := by
  classical
  let D := badSingletonVertices H W v 4
  let B := nearStarB4 H W v
  have hBH : B ⊆ H := by
    intro E hE
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hE).1).1
  have hBU : Uniform 4 B := by
    intro E hE
    exact hUniform (hBH hE)
  have hBW : ∀ E ∈ B, E ⊆ D := by
    intro E hE
    have hData := Finset.mem_filter.mp hE
    have hOutside := Finset.mem_filter.mp hData.1
    have hInter : (E ∩ D).card = 4 := by simpa [B, nearStarB4, D] using hData.2
    have hEcard : E.card = 4 := hUniform hOutside.1
    have hEq : E ∩ D = E :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    intro x hx
    have hx' : x ∈ E ∩ D := by rw [hEq]; exact hx
    exact (Finset.mem_inter.mp hx').2
  have hCoarse := Coarse.coarse_bound_on_ground_set B D 4 (by omega)
    hBU (admissible_mono hBH hH) hBW
  have hNumeral : 24 * B.card ≤ 768 * D.card ^ 3 := by
    norm_num [Nat.factorial] at hCoarse ⊢
    exact hCoarse
  have hFinal : B.card ≤ 32 * D.card ^ 3 := by omega
  simpa [B, D, nearStarB4] using hFinal

/-- The outside family is partitioned by its number of exceptional vertices
into the ordinary layer, B₁, B₂∪B₃, and B₄. -/
theorem near_star_outside_layer_card_split
    {H : Family α} {W : Edge α} {v : α}
    (hUniform : Uniform 4 H) :
    (outsideEdges H W).card =
      (nearStarOrdinaryOutsideEdges H W v).card +
        (nearStarB1 H W v).card + (nearStarB23 H W v).card +
        (nearStarB4 H W v).card := by
  classical
  let B0 := nearStarOrdinaryOutsideEdges H W v
  let B1 := nearStarB1 H W v
  let B23 := nearStarB23 H W v
  let B4 := nearStarB4 H W v
  let D := badSingletonVertices H W v 4
  have hUnion : outsideEdges H W = (B0 ∪ B1) ∪ (B23 ∪ B4) := by
    ext E
    constructor
    · intro hE
      have hBase := Finset.mem_filter.mp hE
      have hInter : (E ∩ D).card ≤ 4 := by
        calc
          (E ∩ D).card ≤ E.card := Finset.card_le_card Finset.inter_subset_left
          _ = 4 := hUniform hBase.1
      by_cases hz : (E ∩ D).card = 0
      · have hEmpty : E ∩ D = ∅ := Finset.card_eq_zero.mp hz
        have hOrd : E ⊆ W \ D := by
          intro x hx
          apply Finset.mem_sdiff.mpr
          refine ⟨hBase.2 hx, ?_⟩
          intro hxD
          have : x ∈ E ∩ D := Finset.mem_inter.mpr ⟨hx, hxD⟩
          simp [hEmpty] at this
        have : E ∈ B0 := by
          simpa [B0, nearStarOrdinaryOutsideEdges] using ⟨hBase.1, hOrd⟩
        simp [this]
      · by_cases h1 : (E ∩ D).card = 1
        · have : E ∈ B1 := by
            have h1' : (E ∩ badSingletonVertices H W v 4).card = 1 := by simpa [D] using h1
            simpa [B1, nearStarB1, outsideEdges, hBase.1, hBase.2] using h1'
          simp [this]
        · by_cases h4 : (E ∩ D).card = 4
          · have : E ∈ B4 := by
              have h4' : (E ∩ badSingletonVertices H W v 4).card = 4 := by simpa [D] using h4
              simpa [B4, nearStarB4, outsideEdges, hBase.1, hBase.2] using h4'
            simp [this]
          · have h23 : 2 ≤ (E ∩ D).card ∧ (E ∩ D).card ≤ 3 := by omega
            have h23' : 2 ≤ (E ∩ badSingletonVertices H W v 4).card ∧
                (E ∩ badSingletonVertices H W v 4).card ≤ 3 := by simpa [D] using h23
            have : E ∈ B23 := by
              simpa [B23, nearStarB23, outsideEdges, hBase.1, hBase.2] using h23'
            simp [this]
    · intro hE
      rcases Finset.mem_union.mp hE with h01 | h234
      · rcases Finset.mem_union.mp h01 with h0 | h1
        · have hData : E ∈ H ∧ E ⊆ W \ D := by
            simpa [B0, nearStarOrdinaryOutsideEdges] using h0
          exact Finset.mem_filter.mpr ⟨hData.1, hData.2.trans Finset.sdiff_subset⟩
        · exact (Finset.mem_filter.mp h1).1
      · rcases Finset.mem_union.mp h234 with h23 | h4
        · exact Finset.mem_filter.mp h23 |>.1
        · exact Finset.mem_filter.mp h4 |>.1
  have h01Disj : Disjoint B0 B1 := by
    apply Finset.disjoint_left.mpr
    intro E h0 h1
    have h0Data : E ∈ H ∧ E ⊆ W \ D := by
      simpa [B0, nearStarOrdinaryOutsideEdges] using h0
    have h0' : E ⊆ W \ D := h0Data.2
    have h1' : (E ∩ D).card = 1 := by
      simpa [B1, nearStarB1, outsideEdges] using (Finset.mem_filter.mp h1).2
    have hEmpty : E ∩ D = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact (Finset.mem_sdiff.mp (h0' (Finset.mem_inter.mp hx).1)).2
        (Finset.mem_inter.mp hx).2
    simp [hEmpty] at h1'
  have h0xDisj : Disjoint B0 (B23 ∪ B4) := by
    apply Finset.disjoint_left.mpr
    intro E h0 hRest
    have h0Data : E ∈ H ∧ E ⊆ W \ D := by
      simpa [B0, nearStarOrdinaryOutsideEdges] using h0
    have h0' : E ⊆ W \ D := h0Data.2
    rcases Finset.mem_union.mp hRest with h23 | h4
    · have h23' : 2 ≤ (E ∩ D).card ∧ (E ∩ D).card ≤ 3 := by
        simpa [B23, nearStarB23, outsideEdges] using (Finset.mem_filter.mp h23).2
      have hempty : E ∩ D = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        exact (Finset.mem_sdiff.mp (h0' (Finset.mem_inter.mp hx).1)).2
          (Finset.mem_inter.mp hx).2
      have hzero : (E ∩ D).card = 0 := by simp [hempty]
      omega
    · have h4' : (E ∩ D).card = 4 := by
        simpa [B4, nearStarB4, outsideEdges] using (Finset.mem_filter.mp h4).2
      have hempty : E ∩ D = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        exact (Finset.mem_sdiff.mp (h0' (Finset.mem_inter.mp hx).1)).2
          (Finset.mem_inter.mp hx).2
      simp [hempty] at h4'
  have h1RestDisj : Disjoint B1 (B23 ∪ B4) := by
    apply Finset.disjoint_left.mpr
    intro E h1 hRest
    have h1' : (E ∩ D).card = 1 := by
      simpa [B1, nearStarB1, outsideEdges] using (Finset.mem_filter.mp h1).2
    rcases Finset.mem_union.mp hRest with h23 | h4
    · have h23' : 2 ≤ (E ∩ D).card := by
        simpa [B23, nearStarB23, outsideEdges] using
          (Finset.mem_filter.mp h23).2.1
      omega
    · have h4' : (E ∩ D).card = 4 := by
        simpa [B4, nearStarB4, outsideEdges] using (Finset.mem_filter.mp h4).2
      omega
  have h23Disj : Disjoint B23 B4 := by
    apply Finset.disjoint_left.mpr
    intro E h23 h4
    have h23' : (E ∩ D).card ≤ 3 := by
      simpa [B23, nearStarB23, outsideEdges] using
        (Finset.mem_filter.mp h23).2.2
    have h4' : (E ∩ D).card = 4 := by
      simpa [B4, nearStarB4, outsideEdges] using (Finset.mem_filter.mp h4).2
    omega
  have hPairDisj : Disjoint (B0 ∪ B1) (B23 ∪ B4) := by
    apply Finset.disjoint_left.mpr
    intro E h01 h234
    rcases Finset.mem_union.mp h01 with h0 | h1
    · exact (Finset.disjoint_left.mp h0xDisj) h0 h234
    · exact (Finset.disjoint_left.mp h1RestDisj) h1 h234
  have hCardPair : (B0 ∪ B1).card = B0.card + B1.card :=
    Finset.card_union_of_disjoint h01Disj
  have hCardRest : (B23 ∪ B4).card = B23.card + B4.card :=
    Finset.card_union_of_disjoint h23Disj
  have hUnionCard := congrArg Finset.card hUnion
  rw [Finset.card_union_of_disjoint hPairDisj, hCardPair, hCardRest] at hUnionCard
  calc
    (outsideEdges H W).card = B0.card + B1.card + (B23.card + B4.card) := hUnionCard
    _ = B0.card + B1.card + B23.card + B4.card := by omega

/-- Refined B₁ estimate (III.C.7) from its three-incidence injection and the
actual exceptional-singleton multiplicity count. -/
theorem near_star_b1_refined_bound
    {H : Family α} {W : Edge α} {v : α} [Fintype α]
    (hH : Admissible H) (hUniform : Uniform 4 H) (hvW : v ∉ W) :
    3 * (nearStarB1 H W v).card ≤
      2 * (nearStarDMissingTriples H W v).card +
        2 * (badSingletonVertices H W v 4).card.choose 2 * (W.card - 2) +
        (badSingletonVertices H W v 4).card *
          (W.card.choose 2 - (W.card - 5).choose 2) := by
  classical
  let D := badSingletonVertices H W v 4
  let U := W \ D
  let d := D.card
  let qD := (nearStarDMissingTriples H W v).card
  let J := D.card.choose 2 * (W.card - 2)
  let Λ := (W.card - 5).choose 2
  have hInc := near_star_bad_singleton_incidence_le_q_d_add_j (H := H) (W := W) (v := v)
  have hInc' : Λ * d ≤ 2 * (qD + J) := by
    simpa [Λ, d, qD, J, D, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hInc
  have hu : U.card ≤ W.card := by
    rw [Finset.card_sdiff]
    exact Nat.sub_le _ _
  have hChoose : U.card.choose 2 ≤ W.card.choose 2 :=
    Nat.choose_le_choose 2 hu
  have hLambda : Λ ≤ W.card.choose 2 := by
    apply Nat.choose_le_choose 2
    omega
  let Δ := W.card.choose 2 - Λ
  have hSplit : W.card.choose 2 = Λ + Δ := by
    dsimp [Δ]
    omega
  have hB1 := near_star_b1_three_incidence_bound hH hUniform hvW
  have hResult :
      3 * (nearStarB1 H W v).card ≤ 2 * qD + 2 * J + d * Δ := by
    have hmul := Nat.mul_le_mul_left d hChoose
    have hProd : d * U.card.choose 2 ≤ d * W.card.choose 2 := by
      nlinarith
    have hB1' : 3 * (nearStarB1 H W v).card ≤ d * W.card.choose 2 := by
      have hb1 : 3 * (nearStarB1 H W v).card ≤ d * U.card.choose 2 := by
        simpa [D, U, d] using hB1
      exact hb1.trans hProd
    have hInc'' : d * Λ ≤ 2 * (qD + J) := by
      simpa [Nat.mul_comm] using hInc'
    rw [hSplit] at hB1'
    nlinarith [hB1', hInc'']
  simpa [D, d, qD, J, Δ, Λ, Nat.mul_assoc] using hResult


/-- Actual combination of (III.C.6) with the B₁, B₂∪B₃, and B₄ bounds,
giving the finite C7 edge-count inequality. -/
theorem near_star_c7_actual
    {H : Family α} {W : Edge α} {v : α} [Fintype α]
    (hH : Admissible H) (hUniform : Uniform 4 H) (hvW : v ∉ W) :
    ((outsideEdges H W).card : ℝ) ≤
      (nearStarUMissingTriples H W v).card / 4 +
      2 * (nearStarDMissingTriples H W v).card / 3 +
      (W \ badSingletonVertices H W v 4).card / 4 +
      5 * (nearStarBadPairs H W v).card / 4 +
      Real.sqrt (((nearStarBadPairs H W v).card : ℝ) ^ 3) / 2 +
      5 * ((badSingletonVertices H W v 4).card.choose 2 *
        (W.card - 2) : ℕ) / 3 +
      (badSingletonVertices H W v 4).card *
        (W.card.choose 2 - (W.card - 5).choose 2) / 3 +
      32 * (badSingletonVertices H W v 4).card ^ 3 := by
  classical
  let D := badSingletonVertices H W v 4
  let U := W \ D
  let B0 := nearStarOrdinaryOutsideEdges H W v
  let B1 := nearStarB1 H W v
  let B23 := nearStarB23 H W v
  let B4 := nearStarB4 H W v
  let qU := (nearStarUMissingTriples H W v).card
  let qD := (nearStarDMissingTriples H W v).card
  let d := D.card
  let h := (nearStarBadPairs H W v).card
  let J := D.card.choose 2 * (W.card - 2)
  let Δ := W.card.choose 2 - (W.card - 5).choose 2
  have hSplit := near_star_outside_layer_card_split (H := H) (W := W) (v := v) hUniform
  have hB0 := near_star_outside_b_0_bound hH hUniform hvW
  have hB0' : (B0.card : ℝ) ≤
      ((U.card : ℝ) + (qU : ℝ)) / 4 +
        (5 * (h : ℝ)) / 4 + Real.sqrt ((h : ℝ) ^ 3) / 2 := by
    simpa [B0, U, qU, h, nearStarUMissingTriples] using hB0
  have hB1nat : 3 * B1.card ≤ 2 * qD + 2 * J + d * Δ := by
    simpa [B1, qD, J, d, Δ, D, Nat.mul_assoc] using
      (near_star_b1_refined_bound hH hUniform hvW)
  have hB1real : (B1.card : ℝ) ≤
      2 * (qD : ℝ) / 3 + 2 * (J : ℝ) / 3 + (d : ℝ) * Δ / 3 := by
    have hc : (3 : ℝ) * B1.card ≤
        2 * qD + 2 * J + d * Δ := by exact_mod_cast hB1nat
    nlinarith
  have hB23nat : B23.card ≤ J := by
    simpa [B23, J, D] using (near_star_b23_card_le_j hH hUniform hvW)
  have hB4nat : B4.card ≤ 32 * d ^ 3 := by
    simpa [B4, d, D] using (near_star_b4_coarse_bound hUniform hH)
  have hSplitR : ((outsideEdges H W).card : ℝ) =
      (B0.card : ℝ) + B1.card + B23.card + B4.card := by
    exact_mod_cast hSplit
  have hB23R : (B23.card : ℝ) ≤ J := by exact_mod_cast hB23nat
  have hB4R : (B4.card : ℝ) ≤ 32 * (d : ℝ) ^ 3 := by exact_mod_cast hB4nat
  have hqUR : (qU : ℝ) = (nearStarUMissingTriples H W v).card := by rfl
  have hqDR : (qD : ℝ) = (nearStarDMissingTriples H W v).card := by rfl
  have hJR : (J : ℝ) =
      ((D.card.choose 2 * (W.card - 2) : ℕ) : ℝ) := by rfl
  have hLambda : (W.card - 5).choose 2 ≤ W.card.choose 2 :=
    Nat.choose_le_choose 2 (by omega)
  have hDeltaCast : (Δ : ℝ) =
      (W.card.choose 2 : ℝ) - ((W.card - 5).choose 2 : ℝ) := by
    dsimp [Δ]
    exact Nat.cast_sub hLambda
  calc
    ((outsideEdges H W).card : ℝ) =
        (B0.card : ℝ) + B1.card + B23.card + B4.card := hSplitR
    _ ≤ ((U.card : ℝ) + qU) / 4 + 5 * h / 4 + Real.sqrt (h ^ 3) / 2 +
        2 * qD / 3 + 2 * J / 3 + d * Δ / 3 + J + 32 * d ^ 3 := by
      nlinarith [hB0', hB1real, hB23R, hB4R]
    _ ≤ qU / 4 + 2 * qD / 3 + (U.card : ℝ) / 4 +
        5 * h / 4 + Real.sqrt (h ^ 3) / 2 + 5 * J / 3 + d * Δ / 3 +
        32 * d ^ 3 := by
      nlinarith
    _ = (nearStarUMissingTriples H W v).card / 4 +
          2 * (nearStarDMissingTriples H W v).card / 3 +
          (W \ badSingletonVertices H W v 4).card / 4 +
          5 * (nearStarBadPairs H W v).card / 4 +
          Real.sqrt (((nearStarBadPairs H W v).card : ℝ) ^ 3) / 2 +
          5 * ((badSingletonVertices H W v 4).card.choose 2 *
            (W.card - 2) : ℕ) / 3 +
          (badSingletonVertices H W v 4).card *
          (W.card.choose 2 - (W.card - 5).choose 2) / 3 +
          32 * (badSingletonVertices H W v 4).card ^ 3 := by
      dsimp only [D, U, qU, qD, h, J, d]
      rw [hDeltaCast]


end JSP523.Rank4
