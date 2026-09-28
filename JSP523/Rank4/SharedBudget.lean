import JSP523.Rank4.CommonTripleCells
import JSP523.Rank4.GraphVertexDeficit
import JSP523.Rank4.PreprocessStarLayers
import JSP523.Coarse.TripleLinks

/-!
# Shared star and native budgets at rank four

This file records the finite deductions in §III.B.4 that do not depend on
asymptotic notation.  In particular, the parent matching argument of
`CommonTripleCells` makes a used completion pair have at most one common
neighbor in every star-triple link other than its labelled link.  The final
master-budget calculation is stated with integral errors, so later
preprocessing estimates can be substituted without rounding conventions.
-/

namespace JSP523.Rank4

variable {α : Type*} [DecidableEq α]

/-- The pair shadow of one cleaned star layer. -/
def starLayerPairShadow (A : Family α) : Family α :=
  A.biUnion fun T => T.powersetCard 2

/-- Equation (III.B.12) bounds common neighbors in every link outside the
labelled one.  Its premise is the exact conclusion supplied by the parent
matching theorem once pair-shadow ownership has identified a star layer. -/
theorem star_link_common_multiplicity_le_one
    [Fintype α]
    (A : Family α) (a b z x : α)
    (hLabel : ∀ P : Edge α,
      insert a P ∈ A → insert b P ∈ A → z ∈ P)
    (hx : x ≠ z) :
    graphCommonMultiplicity (JSP523.Coarse.tripleLinkGraph A x) a b ≤ 1 := by
  classical
  unfold graphCommonMultiplicity
  apply Finset.card_le_one.mpr
  intro y hy t ht
  have hya : (JSP523.Coarse.tripleLinkGraph A x).Adj a y := by
    simpa [SimpleGraph.mem_neighborFinset] using (Finset.mem_filter.mp hy).1
  have hyb : (JSP523.Coarse.tripleLinkGraph A x).Adj b y :=
    (Finset.mem_filter.mp hy).2
  have hta : (JSP523.Coarse.tripleLinkGraph A x).Adj a t := by
    simpa [SimpleGraph.mem_neighborFinset] using (Finset.mem_filter.mp ht).1
  have htb : (JSP523.Coarse.tripleLinkGraph A x).Adj b t :=
    (Finset.mem_filter.mp ht).2
  have hzy : z ∈ ({x, y} : Edge α) := by
    apply hLabel
    · simpa only [JSP523.Coarse.tripleLinkGraph_adj,
        Finset.insert_comm] using hya.2
    · simpa only [JSP523.Coarse.tripleLinkGraph_adj,
        Finset.insert_comm] using hyb.2
  have hzt : z ∈ ({x, t} : Edge α) := by
    apply hLabel
    · simpa only [JSP523.Coarse.tripleLinkGraph_adj,
        Finset.insert_comm] using hta.2
    · simpa only [JSP523.Coarse.tripleLinkGraph_adj,
        Finset.insert_comm] using htb.2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hzy hzt
  rcases hzy with hzx | hzy
  · exact False.elim (hx hzx.symm)
  rcases hzt with hzx | hzt
  · exact False.elim (hx hzx.symm)
  exact hzy.symm.trans hzt

/-- The pair-shadow ownership step of §III.B.4: two layer triples sharing
an actual pair belong to the same center.  It is useful to state this
without choosing a representation of the union of all layers. -/
theorem star_layer_pair_owner_unique
    (A : α → Family α) (C : Finset α)
    (hOwner : ∀ ⦃c d : α⦄, c ∈ C → d ∈ C →
      ∀ ⦃P T S : Edge α⦄, P.card = 2 → T ∈ A c → S ∈ A d →
        P ⊆ T → P ⊆ S → c = d)
    {c d : α} (hc : c ∈ C) (hd : d ∈ C)
    {P : Edge α} (hP : P.card = 2)
    {a b : α}
    (ha : insert a P ∈ A c) (hb : insert b P ∈ A d) : c = d := by
  apply hOwner hc hd hP ha hb
  · exact Finset.subset_insert a P
  · exact Finset.subset_insert b P

/-- Pairwise disjoint pair shadows supply the owner premise directly. -/
theorem star_layer_pair_owner_of_disjoint_shadows
    (A : α → Family α) (C : Finset α)
    (hDisjoint : ∀ ⦃c d : α⦄, c ∈ C → d ∈ C → c ≠ d →
      Disjoint (starLayerPairShadow (A c)) (starLayerPairShadow (A d)))
    {c d : α} (hc : c ∈ C) (hd : d ∈ C)
    {P : Edge α} (hP : P.card = 2)
    {a b : α}
    (ha : insert a P ∈ A c) (hb : insert b P ∈ A d) : c = d := by
  by_contra hcd
  have hPc : P ∈ starLayerPairShadow (A c) := by
    apply Finset.mem_biUnion.mpr
    exact ⟨insert a P, ha,
      Finset.mem_powersetCard.mpr ⟨Finset.subset_insert a P, hP⟩⟩
  have hPd : P ∈ starLayerPairShadow (A d) := by
    apply Finset.mem_biUnion.mpr
    exact ⟨insert b P, hb,
      Finset.mem_powersetCard.mpr ⟨Finset.subset_insert b P, hP⟩⟩
  exact (Finset.disjoint_left.mp (hDisjoint hc hd hcd)) hPc hPd

/-- An actual pair of star-layer triples and the three fixed parent tails
force the native label into their common pair.  The tails need only live
in the original family; they need not survive later deletion. -/
theorem parent_star_pair_label_in_pair
    {H : Family α} {V U P R S T : Edge α}
    {a b c z : α}
    (hH : Admissible H) (hab : a ≠ b)
    (hUsubV : U ⊆ V) (hcV : c ∈ V)
    (hPcard : P.card = 2) (hPsub : P ⊆ U)
    (hPdisj : Disjoint P ({a, b} : Edge α))
    (haU : a ∈ U) (hbU : b ∈ U) (hzU : z ∈ U)
    (hcU : c ∉ U)
    (hAP : insert c (insert a P) ∈ H)
    (hBP : insert c (insert b P) ∈ H)
    (hRS : Disjoint R S) (hRT : Disjoint R T)
    (hST : Disjoint S T)
    (hRsub : R ⊆ U) (hSsub : S ⊆ U) (hTsub : T ⊆ U)
    (hR : insert z R ∈ commonTripleCell H V a b)
    (hS : insert z S ∈ commonTripleCell H V a b)
    (hT : insert z T ∈ commonTripleCell H V a b) :
    z ∈ P := by
  have hcP : c ∉ P := fun hcP => hcU (hPsub hcP)
  have hca : c ≠ a := fun h => hcU (h.symm ▸ haU)
  have hcb : c ≠ b := fun h => hcU (h.symm ▸ hbU)
  have hcz : c ≠ z := fun h => hcU (h.symm ▸ hzU)
  have hCcard : (insert c P).card = 3 := by
    rw [Finset.card_insert_of_notMem hcP, hPcard]
  have hCsub : insert c P ⊆ V := by
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hyP
    · exact hcV
    · exact hUsubV (hPsub hyP)
  have hCdisj : Disjoint (insert c P) ({a, b} : Edge α) := by
    apply Finset.disjoint_left.mpr
    intro y hy hyAB
    rcases Finset.mem_insert.mp hy with rfl | hyP
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hyAB
      rcases hyAB with h | h
      · exact hca h
      · exact hcb h
    · exact (Finset.disjoint_left.mp hPdisj) hyP hyAB
  have hStar : insert c P ∈ commonTripleCell H V a b := by
    apply mem_commonTripleCell.mpr
    refine ⟨hCsub, hCcard, hCdisj, ?_, ?_⟩
    · simpa only [Finset.insert_comm] using hAP
    · simpa only [Finset.insert_comm] using hBP
  have hcR : c ∉ R := fun hcR => hcU (hRsub hcR)
  have hcS : c ∉ S := fun hcS => hcU (hSsub hcS)
  have hcT : c ∉ T := fun hcT => hcU (hTsub hcT)
  exact three_parent_tails_force_label_in_pair hH hab hcz hPcard
    hRS hRT hST hcR hcS hcT hStar hR hS hT

/-- The actual star-layer version of (III.B.12).  A pair of triples in the
union of cleaned layers has a unique owner; its two original star edges
then let the parent matching argument place the native label in `P`. -/
theorem cleaned_star_pair_label_in_pair
    {H : Family α} {V U P R S T : Edge α}
    {a b z : α}
    (A : α → Family α) (C : Finset α)
    (hH : Admissible H) (hab : a ≠ b)
    (hUsubV : U ⊆ V)
    (hCentersV : ∀ c ∈ C, c ∈ V)
    (hCentersU : ∀ c ∈ C, c ∉ U)
    (hLayerEdges : ∀ c ∈ C, ∀ T ∈ A c, insert c T ∈ H)
    (hDisjoint : ∀ ⦃c d : α⦄, c ∈ C → d ∈ C → c ≠ d →
      Disjoint (starLayerPairShadow (A c)) (starLayerPairShadow (A d)))
    (hPcard : P.card = 2) (hPsub : P ⊆ U)
    (hPdisj : Disjoint P ({a, b} : Edge α))
    (haU : a ∈ U) (hbU : b ∈ U) (hzU : z ∈ U)
    (hAP : insert a P ∈ C.biUnion A)
    (hBP : insert b P ∈ C.biUnion A)
    (hRS : Disjoint R S) (hRT : Disjoint R T)
    (hST : Disjoint S T)
    (hRsub : R ⊆ U) (hSsub : S ⊆ U) (hTsub : T ⊆ U)
    (hR : insert z R ∈ commonTripleCell H V a b)
    (hS : insert z S ∈ commonTripleCell H V a b)
    (hT : insert z T ∈ commonTripleCell H V a b) :
    z ∈ P := by
  obtain ⟨c, hc, hAc⟩ := Finset.mem_biUnion.mp hAP
  obtain ⟨d, hd, hBd⟩ := Finset.mem_biUnion.mp hBP
  have hcd := star_layer_pair_owner_of_disjoint_shadows A C hDisjoint
    hc hd hPcard hAc hBd
  subst d
  apply parent_star_pair_label_in_pair hH hab hUsubV
    (hCentersV c hc) hPcard hPsub hPdisj haU hbU hzU
    (hCentersU c hc)
    (hLayerEdges c hc (insert a P) hAc)
    (hLayerEdges c hc (insert b P) hBd)
    hRS hRT hST hRsub hSsub hTsub hR hS hT

/-- In a uniform triple layer, a common neighbor of `a,b` in the link at
`x` presents an actual two-element pair `P={x,y}` disjoint from `a,b`.
This is the finite set manipulation needed to apply (III.B.12). -/
theorem star_link_common_neighbor_pair
    (A : Family α) (U : Edge α)
    (hAU : ∀ T ∈ A, T ⊆ U ∧ T.card = 3)
    {a b x y : α}
    (hya : (JSP523.Coarse.tripleLinkGraph A x).Adj a y)
    (hyb : (JSP523.Coarse.tripleLinkGraph A x).Adj b y) :
    ({x, y} : Edge α).card = 2 ∧
      ({x, y} : Edge α) ⊆ U ∧
      Disjoint ({x, y} : Edge α) ({a, b} : Edge α) ∧
      insert a ({x, y} : Edge α) ∈ A ∧
      insert b ({x, y} : Edge α) ∈ A := by
  let P : Edge α := {x, y}
  have hAP : insert a P ∈ A := by
    simpa only [JSP523.Coarse.tripleLinkGraph_adj,
      Finset.insert_comm] using hya.2
  have hBP : insert b P ∈ A := by
    simpa only [JSP523.Coarse.tripleLinkGraph_adj,
      Finset.insert_comm] using hyb.2
  have hAcard : (insert a P).card = 3 := (hAU _ hAP).2
  have hBcard : (insert b P).card = 3 := (hAU _ hBP).2
  have hPcard : P.card = 2 := by
    have hUpper : P.card ≤ 2 := Finset.card_le_two
    have hLower := Finset.card_insert_le a P
    omega
  have haP : a ∉ P := by
    intro haP
    rw [Finset.card_insert_of_mem haP] at hAcard
    omega
  have hbP : b ∉ P := by
    intro hbP
    rw [Finset.card_insert_of_mem hbP] at hBcard
    omega
  have hPsub : P ⊆ U := by
    intro t ht
    exact (hAU _ hAP).1 (Finset.mem_insert_of_mem ht)
  have hPdisj : Disjoint P ({a, b} : Edge α) := by
    apply Finset.disjoint_left.mpr
    intro t ht htAB
    simp only [Finset.mem_insert, Finset.mem_singleton] at htAB
    rcases htAB with rfl | rfl
    · exact haP ht
    · exact hbP ht
  exact ⟨hPcard, hPsub, hPdisj, hAP, hBP⟩

/-- The near-star label condition for valid two-element pairs implies that
every link except the labelled one has common-neighbor multiplicity at most
one for the used completion pair. -/
theorem star_link_common_multiplicity_le_one_of_valid_pairs
    [Fintype α]
    (A : Family α) (U : Edge α) (a b z x : α)
    (hAU : ∀ T ∈ A, T ⊆ U ∧ T.card = 3)
    (hLabel : ∀ P : Edge α, P.card = 2 → P ⊆ U →
      Disjoint P ({a, b} : Edge α) →
      insert a P ∈ A → insert b P ∈ A → z ∈ P)
    (hx : x ≠ z) :
    graphCommonMultiplicity (JSP523.Coarse.tripleLinkGraph A x) a b ≤ 1 := by
  classical
  unfold graphCommonMultiplicity
  apply Finset.card_le_one.mpr
  intro y hy t ht
  have hya : (JSP523.Coarse.tripleLinkGraph A x).Adj a y := by
    simpa [SimpleGraph.mem_neighborFinset] using (Finset.mem_filter.mp hy).1
  have hyb : (JSP523.Coarse.tripleLinkGraph A x).Adj b y :=
    (Finset.mem_filter.mp hy).2
  have hta : (JSP523.Coarse.tripleLinkGraph A x).Adj a t := by
    simpa [SimpleGraph.mem_neighborFinset] using (Finset.mem_filter.mp ht).1
  have htb : (JSP523.Coarse.tripleLinkGraph A x).Adj b t :=
    (Finset.mem_filter.mp ht).2
  obtain ⟨hPy, hUy, hDy, hAy, hBy⟩ :=
    star_link_common_neighbor_pair A U hAU hya hyb
  obtain ⟨hPt, hUt, hDt, hAt, hBt⟩ :=
    star_link_common_neighbor_pair A U hAU hta htb
  have hzy := hLabel {x, y} hPy hUy hDy hAy hBy
  have hzt := hLabel {x, t} hPt hUt hDt hAt hBt
  simp only [Finset.mem_insert, Finset.mem_singleton] at hzy hzt
  rcases hzy with hzx | hzy
  · exact False.elim (hx hzx.symm)
  rcases hzt with hzx | hzt
  · exact False.elim (hx hzx.symm)
  exact hzy.symm.trans hzt

/-- For a pair with three parent matching witnesses, the actual union of
cleaned star layers has at most one common neighbor in every link whose
root is not the pair's native label.  This is the finite multiplicity
statement used immediately before (III.B.14). -/
theorem cleaned_star_link_common_multiplicity_le_one
    [Fintype α]
    {H : Family α} {V U R S T : Edge α}
    {a b z x : α}
    (A : α → Family α) (C : Finset α)
    (hH : Admissible H) (hab : a ≠ b)
    (hUsubV : U ⊆ V)
    (hCentersV : ∀ c ∈ C, c ∈ V)
    (hCentersU : ∀ c ∈ C, c ∉ U)
    (hLayerEdges : ∀ c ∈ C, ∀ T ∈ A c, insert c T ∈ H)
    (hLayerGround : ∀ c ∈ C, ∀ T ∈ A c, T ⊆ U ∧ T.card = 3)
    (hDisjoint : ∀ ⦃c d : α⦄, c ∈ C → d ∈ C → c ≠ d →
      Disjoint (starLayerPairShadow (A c)) (starLayerPairShadow (A d)))
    (haU : a ∈ U) (hbU : b ∈ U) (hzU : z ∈ U)
    (hRS : Disjoint R S) (hRT : Disjoint R T)
    (hST : Disjoint S T)
    (hRsub : R ⊆ U) (hSsub : S ⊆ U) (hTsub : T ⊆ U)
    (hR : insert z R ∈ commonTripleCell H V a b)
    (hS : insert z S ∈ commonTripleCell H V a b)
    (hT : insert z T ∈ commonTripleCell H V a b)
    (hx : x ≠ z) :
    graphCommonMultiplicity
      (JSP523.Coarse.tripleLinkGraph (C.biUnion A) x) a b ≤ 1 := by
  have hUnionGround : ∀ T ∈ C.biUnion A, T ⊆ U ∧ T.card = 3 := by
    intro Q hQ
    obtain ⟨c, hc, hQc⟩ := Finset.mem_biUnion.mp hQ
    exact hLayerGround c hc Q hQc
  have hLabel : ∀ P : Edge α, P.card = 2 → P ⊆ U →
      Disjoint P ({a, b} : Edge α) →
      insert a P ∈ C.biUnion A → insert b P ∈ C.biUnion A →
      z ∈ P := by
    intro P hPcard hPsub hPdisj hAP hBP
    exact cleaned_star_pair_label_in_pair A C hH hab hUsubV
      hCentersV hCentersU hLayerEdges hDisjoint hPcard hPsub
      hPdisj haU hbU hzU hAP hBP hRS hRT hST
      hRsub hSsub hTsub hR hS hT
  exact star_link_common_multiplicity_le_one_of_valid_pairs
    (C.biUnion A) U a b z x hUnionGround hLabel hx

/-- The unrestricted pair shadow agrees with the ground-set version used by
pair-owner cleaning when every layer triple lies in the ground set. -/
theorem starLayerPairShadow_eq_starLinkPairShadow
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : ι → Family α) (U : Edge α) (i : ι)
    (hGround : ∀ T ∈ L i, T ⊆ U) :
    starLayerPairShadow (L i) = starLinkPairShadow L U i := by
  classical
  ext P
  constructor
  · intro hP
    obtain ⟨T, hT, hPT⟩ := Finset.mem_biUnion.mp hP
    obtain ⟨hPsub, hPcard⟩ := Finset.mem_powersetCard.mp hPT
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_powersetCard.mpr
      ⟨hPsub.trans (hGround T hT), hPcard⟩, T, hT, hPsub⟩
  · intro hP
    obtain ⟨hPU, T, hT, hPT⟩ := Finset.mem_filter.mp hP
    apply Finset.mem_biUnion.mpr
    exact ⟨T, hT, Finset.mem_powersetCard.mpr
      ⟨hPT, (Finset.mem_powersetCard.mp hPU).2⟩⟩

/-- Maximum-degree pair-owner cleaning supplies the disjoint-shadow
premise of the native-label multiplicity theorem.  The original parent
edges remain available as witnesses after cleaning. -/
theorem pair_owner_cleaned_star_link_common_multiplicity_le_one
    [Fintype α]
    {H : Family α} {V U R S T : Edge α}
    {a b z x : α}
    (L : α → Family α) (C : Finset α) (owner : Edge α → α)
    (hH : Admissible H) (hab : a ≠ b)
    (hUsubV : U ⊆ V)
    (hCentersV : ∀ c ∈ C, c ∈ V)
    (hCentersU : ∀ c ∈ C, c ∉ U)
    (hLayerEdges : ∀ c ∈ C, ∀ Q ∈ L c, insert c Q ∈ H)
    (hLayerGround : ∀ c ∈ C, ∀ Q ∈ L c, Q ∈ U.powersetCard 3)
    (haU : a ∈ U) (hbU : b ∈ U) (hzU : z ∈ U)
    (hRS : Disjoint R S) (hRT : Disjoint R T)
    (hST : Disjoint S T)
    (hRsub : R ⊆ U) (hSsub : S ⊆ U) (hTsub : T ⊆ U)
    (hR : insert z R ∈ commonTripleCell H V a b)
    (hS : insert z S ∈ commonTripleCell H V a b)
    (hT : insert z T ∈ commonTripleCell H V a b)
    (hx : x ≠ z) :
    graphCommonMultiplicity
      (JSP523.Coarse.tripleLinkGraph
        (C.biUnion (pairOwnerCleanedLink L owner)) x) a b ≤ 1 := by
  let A := pairOwnerCleanedLink L owner
  have hCleanGround : ∀ c ∈ C, ∀ Q ∈ A c, Q ⊆ U ∧ Q.card = 3 := by
    intro c hc Q hQ
    have hQL : Q ∈ L c := by
      simp only [A, pairOwnerCleanedLink, Finset.mem_filter] at hQ
      exact hQ.1
    exact Finset.mem_powersetCard.mp (hLayerGround c hc Q hQL)
  have hCleanEdges : ∀ c ∈ C, ∀ Q ∈ A c, insert c Q ∈ H := by
    intro c hc Q hQ
    have hQL : Q ∈ L c := by
      simp only [A, pairOwnerCleanedLink, Finset.mem_filter] at hQ
      exact hQ.1
    exact hLayerEdges c hc Q hQL
  have hShadow : ∀ c ∈ C,
      starLayerPairShadow (A c) = starLinkPairShadow A U c := by
    intro c hc
    exact starLayerPairShadow_eq_starLinkPairShadow A U c
      (fun Q hQ => (hCleanGround c hc Q hQ).1)
  have hDisjoint : ∀ ⦃c d : α⦄, c ∈ C → d ∈ C → c ≠ d →
      Disjoint (starLayerPairShadow (A c)) (starLayerPairShadow (A d)) := by
    intro c d hc hd hcd
    rw [hShadow c hc, hShadow d hd]
    exact pair_owner_cleaning_shadows_disjoint L owner U c d hcd
  exact cleaned_star_link_common_multiplicity_le_one A C hH hab
    hUsubV hCentersV hCentersU hCleanEdges hCleanGround hDisjoint
    haU hbU hzU hRS hRT hST hRsub hSsub hTsub hR hS hT hx

/-- The integer form of the master inequality (III.B.15).  The deficit
input is twice (III.B.7), while the other two inputs are (III.B.14) and
the almost-disjoint star/face budget. -/
theorem shared_budget_master
    {a m b m₀ s V N overlapError graphError : ℕ}
    (hDeficit : b + 6 * m₀ + 10 * m ≤ 2 * V + 4 * s)
    (hStarNative : 3 * a + V ≤ 3 * N + graphError)
    (hDisjoint : a + s ≤ N + overlapError) :
    10 * (a + m) + b + 6 * m₀ ≤
      10 * N + 2 * graphError + 4 * overlapError := by
  omega

/-- A finite upper bound on the original edge count after a loss of
`deletionError` edges from the outside remainder and `layerError` edges
from the fixed star-layer decomposition. -/
theorem shared_budget_original_edge_bound
    {Hcard a m b m₀ s V N overlapError graphError
      deletionError layerError outsideCard : ℕ}
    (hDeficit : b + 6 * m₀ + 10 * m ≤ 2 * V + 4 * s)
    (hStarNative : 3 * a + V ≤ 3 * N + graphError)
    (hDisjoint : a + s ≤ N + overlapError)
    (hOriginal : Hcard ≤ a + outsideCard + layerError)
    (hDeletion : outsideCard ≤ m + deletionError) :
    10 * Hcard + b + 6 * m₀ ≤
      10 * N + 2 * graphError + 4 * overlapError +
        10 * (deletionError + layerError) := by
  have hMaster := shared_budget_master hDeficit hStarNative hDisjoint
  omega

/-- Near equality in the original family bounds the finite deficit of the
retained outside remainder.  This is the algebraic part of §III.B.5. -/
theorem shared_budget_deficit_small
    {Hcard a m outsideCard S N masterError
      highError layerError deletionError : ℕ}
    (hMaster : 5 * (a + m) + S ≤ 5 * N + masterError)
    (hHigh : N ≤ Hcard + highError)
    (hOriginal : Hcard ≤ a + outsideCard + layerError)
    (hDeletion : outsideCard ≤ m + deletionError) :
    S ≤ masterError +
      5 * (highError + layerError + deletionError) := by
  omega

/-- A uniform facet-degree tail and the finite deficit bound imply that
the retained outside family is small.  The factor 2M is the one in
(III.B.17); the all-private edges are already paid inside the deficit. -/
theorem shared_budget_retained_outside_small
    {m m₀ b S M tail : ℕ}
    (hMpos : 1 ≤ M)
    (hDeficit : b + 6 * m₀ ≤ 2 * S)
    (hTail : m ≤ m₀ + M * b + tail) :
    m ≤ 2 * M * S + tail := by
  have hWeighted := Nat.mul_le_mul_left M hDeficit
  have hPrivate : m₀ ≤ 6 * M * m₀ := by
    have hMul := Nat.mul_le_mul_right m₀ hMpos
    nlinarith
  nlinarith

end JSP523.Rank4
