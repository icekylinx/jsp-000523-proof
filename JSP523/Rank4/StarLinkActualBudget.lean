import JSP523.Rank4.StarLinkScale
import JSP523.Rank4.SharedBudget
import JSP523.Rank4.NativeLabelSelection

/-!
# The actual cleaned star layers in the shared budget

The parent matching witnesses of the used completion pairs supply the
off-label common-neighbor condition needed by the finite sampling
budget.  All star triples below are the actual union of pair-owner
cleaned links.
-/

namespace JSP523.Rank4

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Data asserting that one used pair has the three disjoint parent tails
from the rank-four preprocessing lemma. -/
def HasThreeParentTails
    (H : Family α) (V U : Edge α)
    (a b z : α) : Prop :=
  ∃ R S T : Edge α,
    z ∈ U ∧
    Disjoint R S ∧ Disjoint R T ∧ Disjoint S T ∧
    R ⊆ U ∧ S ⊆ U ∧ T ⊆ U ∧
    insert z R ∈ commonTripleCell H V a b ∧
    insert z S ∈ commonTripleCell H V a b ∧
    insert z T ∈ commonTripleCell H V a b

/-- The parent matching argument upgrades a concrete cleaned star-layer
union to the off-label multiplicity condition for every used pair. -/
theorem cleaned_star_off_label_multiplicity
    {H : Family α} {V U : Edge α}
    (L : α → Family α) (centers : Finset α)
    (owner label : Edge α → α) (used : Family α)
    (hH : Admissible H)
    (hUsubV : U ⊆ V)
    (hCentersV : ∀ c ∈ centers, c ∈ V)
    (hCentersU : ∀ c ∈ centers, c ∉ U)
    (hLayerEdges : ∀ c ∈ centers, ∀ Q ∈ L c, insert c Q ∈ H)
    (hLayerGround : ∀ c ∈ centers, ∀ Q ∈ L c,
      Q ∈ U.powersetCard 3)
    (hTails : ∀ a ∈ U, ∀ b ∈ U.erase a,
      ({a, b} : Edge α) ∈ used →
        HasThreeParentTails H V U a b
          (label ({a, b} : Edge α))) :
    ∀ a ∈ U, ∀ b ∈ U.erase a,
      ({a, b} : Edge α) ∈ used →
      ∀ x ∈ U, x ≠ label ({a, b} : Edge α) →
        graphCommonMultiplicity
          (JSP523.Coarse.tripleLinkGraph
            (centers.biUnion (pairOwnerCleanedLink L owner)) x)
          a b ≤ 1 := by
  intro a ha b hb hUsed x _hx hx
  have hbU : b ∈ U := (Finset.mem_erase.mp hb).2
  have hab : a ≠ b := (Finset.mem_erase.mp hb).1.symm
  obtain ⟨R, S, T, hzU, hRS, hRT, hST,
    hRsub, hSsub, hTsub, hR, hS, hT⟩ :=
    hTails a ha b hb hUsed
  exact pair_owner_cleaned_star_link_common_multiplicity_le_one
    L centers owner hH hab hUsubV hCentersV hCentersU
    hLayerEdges hLayerGround ha hbU hzU hRS hRT hST
    hRsub hSsub hTsub hR hS hT hx

/-- The full square-root star/native budget for actual pair-owner cleaned
star links.  The only numerical native input is the genuine bound of the
native active-vertex count by the used-pair count. -/
theorem cleaned_star_native_sqrt_budget
    {H : Family α} {V U : Edge α}
    (L : α → Family α) (centers : Finset α)
    (owner label : Edge α → α) (used : Family α)
    (nativeVertices : ℕ)
    (hH : Admissible H)
    (hUsubV : U ⊆ V)
    (hCentersV : ∀ c ∈ centers, c ∈ V)
    (hCentersU : ∀ c ∈ centers, c ∉ U)
    (hLayerEdges : ∀ c ∈ centers, ∀ Q ∈ L c, insert c Q ∈ H)
    (hLayerGround : ∀ c ∈ centers, ∀ Q ∈ L c,
      Q ∈ U.powersetCard 3)
    (hUsed : used ⊆ U.powersetCard 2)
    (hU : 3 ≤ U.card)
    (hTails : ∀ a ∈ U, ∀ b ∈ U.erase a,
      ({a, b} : Edge α) ∈ used →
        HasThreeParentTails H V U a b
          (label ({a, b} : Edge α)))
    (hNative : nativeVertices ≤ (U.card - 3) * used.card) :
    3 * (centers.biUnion (pairOwnerCleanedLink L owner)).card +
        nativeVertices ≤
      3 * U.card.choose 3 +
        U.card ^ 2 * (Nat.sqrt U.card + 1) := by
  classical
  let A := centers.biUnion (pairOwnerCleanedLink L owner)
  have hGround : ∀ T ∈ A, T ⊆ U := by
    intro T hT
    obtain ⟨c, hc, hTc⟩ := Finset.mem_biUnion.mp hT
    have hTL : T ∈ L c := by
      simp only [pairOwnerCleanedLink, Finset.mem_filter] at hTc
      exact hTc.1
    exact (Finset.mem_powersetCard.mp (hLayerGround c hc T hTL)).1
  have hUniform : ∀ T ∈ A, T.card = 3 := by
    intro T hT
    obtain ⟨c, hc, hTc⟩ := Finset.mem_biUnion.mp hT
    have hTL : T ∈ L c := by
      simp only [pairOwnerCleanedLink, Finset.mem_filter] at hTc
      exact hTc.1
    exact (Finset.mem_powersetCard.mp (hLayerGround c hc T hTL)).2
  exact star_native_sqrt_budget A U used label nativeVertices hUsed hU
    hGround hUniform
    (cleaned_star_off_label_multiplicity L centers owner label used
      hH hUsubV hCentersV hCentersU hLayerEdges hLayerGround hTails)
    hNative

/-- With labels chosen from the actual surviving cells, the native
vertex count is paid automatically.  The remaining matching premise is
the parent-witness conclusion of the preprocessing stage. -/
theorem cleaned_star_chosen_native_sqrt_budget
    {H : Family α} {V U : Edge α}
    (K : Family α) (L : α → Family α) (centers : Finset α)
    (owner : Edge α → α) (fallback : α)
    (hCenters : UniqueCommonRootCenters K U)
    (hH : Admissible H)
    (hUsubV : U ⊆ V)
    (hCentersV : ∀ c ∈ centers, c ∈ V)
    (hCentersU : ∀ c ∈ centers, c ∉ U)
    (hLayerEdges : ∀ c ∈ centers, ∀ Q ∈ L c, insert c Q ∈ H)
    (hLayerGround : ∀ c ∈ centers, ∀ Q ∈ L c,
      Q ∈ U.powersetCard 3)
    (hU : 3 ≤ U.card)
    (hTails : ∀ a ∈ U, ∀ b ∈ U.erase a,
      ({a, b} : Edge α) ∈ nonemptyCommonRoots K U →
        HasThreeParentTails H V U a b
          (chosenCommonRootLabel K U fallback hCenters
            ({a, b} : Edge α))) :
    3 * (centers.biUnion (pairOwnerCleanedLink L owner)).card +
      nativeTailVertexTotal K U (nonemptyCommonRoots K U)
        (chosenCommonRootLabel K U fallback hCenters) ≤
      3 * U.card.choose 3 +
        U.card ^ 2 * (Nat.sqrt U.card + 1) := by
  have hUsed : nonemptyCommonRoots K U ⊆ U.powersetCard 2 := by
    intro P hP
    exact (Finset.mem_filter.mp hP).1
  exact cleaned_star_native_sqrt_budget L centers owner
    (chosenCommonRootLabel K U fallback hCenters)
    (nonemptyCommonRoots K U)
    (nativeTailVertexTotal K U (nonemptyCommonRoots K U)
      (chosenCommonRootLabel K U fallback hCenters))
    hH hUsubV hCentersV hCentersU hLayerEdges hLayerGround
    hUsed hU hTails
    (chosen_native_tail_vertex_total_le K U fallback hCenters)

end JSP523.Rank4
