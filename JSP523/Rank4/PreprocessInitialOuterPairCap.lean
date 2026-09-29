import JSP523.Rank4.PreprocessCellMoment
import Mathlib.Data.Nat.Choose.Bounds

/-! # Trivial actual pair-degree cap for the first outer decomposition -/

namespace JSP523.Rank4

/-- Every pair in a four-uniform family on `n` vertices belongs to at
most `n²` actual edges. This pays for edges meeting the initial high-degree
set in two or more vertices. -/
theorem rank_four_pair_degree_le_ground_square
    {n : ℕ} (H : Family (Fin n)) (hUniform : Uniform 4 H)
    (P : Edge (Fin n)) (hP : P.card = 2) :
    rankFourPairDegree H P ≤ n ^ 2 := by
  classical
  have hSub : (H.filter fun E => P ⊆ E) ⊆
      ((Finset.univ : Edge (Fin n)).powersetCard 4).filter fun E => P ⊆ E := by
    intro E hE
    have h := Finset.mem_filter.mp hE
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ E, hUniform h.1⟩, h.2⟩
  have hCount := Finset.card_filter_powersetCard_subset P
    (Finset.univ : Edge (Fin n)) 4 (Finset.subset_univ P) (by omega : P.card ≤ 4)
  have hPow : (n - 2).choose 2 ≤ n ^ 2 :=
    (Nat.choose_le_pow (n - 2) 2).trans
      (Nat.pow_le_pow_left (Nat.sub_le n 2) 2)
  unfold rankFourPairDegree
  calc
    _ ≤ (((Finset.univ : Edge (Fin n)).powersetCard 4).filter fun E => P ⊆ E).card :=
      Finset.card_le_card hSub
    _ = (n - 2).choose 2 := by
      simpa only [Finset.card_univ, Fintype.card_fin, hP] using hCount
    _ ≤ n ^ 2 := hPow

end JSP523.Rank4
