import JSP523.Rank3.PartIIClosure
import JSP523.Rank3.PartIILowerBound

/-!
# Corollary II.2: finite rank-three extremal bounds

The upper bound follows from Theorem II.1 for a maximizing admissible
triple system. The lower bound is the full triple star through any vertex
of the ambient set, as in `paper/proof.pdf`.
-/

namespace JSP523.Rank3

variable {α : Type*} [DecidableEq α]

/-- The finite upper half of Corollary II.2 for the extremal function. -/
theorem rank_three_max_avoiding_card_upper (V : Edge α) :
    maxAvoidingCard V 3 ≤ V.card.choose 2 := by
  obtain ⟨F, hSupport, hAdm, hCard⟩ := max_avoiding_card_attained V 3
  have hUniform : Uniform 3 F := by
    intro E hE
    exact (Finset.mem_powersetCard.mp (hSupport hE)).2
  have hGround : ∀ E ∈ F, E ⊆ V := by
    intro E hE
    exact (Finset.mem_powersetCard.mp (hSupport hE)).1
  have hUpper := (rank_three_part_ii_theorem F V hUniform hAdm hGround).2.2
  simpa only [hCard] using hUpper

/-- The finite two-sided inequality of Corollary II.2, for every ambient
vertex set with at least three vertices. -/
theorem corollary_ii_2_finite (V : Edge α) (hV : 3 ≤ V.card) :
    (V.card - 1).choose 2 ≤ maxAvoidingCard V 3 ∧
      maxAvoidingCard V 3 ≤ V.card.choose 2 := by
  obtain ⟨c, hc⟩ : V.Nonempty := Finset.card_pos.mp (by omega)
  exact ⟨corollary_ii_2_lower V c hc, rank_three_max_avoiding_card_upper V⟩

end JSP523.Rank3
