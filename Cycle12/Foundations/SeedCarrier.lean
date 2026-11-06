import Cycle12.Foundations.SeedCanonical
import Cycle12.Foundations.CarrierTheorem

/-! Extract the final carrier from a sufficiently large external block,
and apply the already proved carrier construction in both parameter regimes. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable

namespace OrderedSeed
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {root : V} {t p : ℕ}
    (A : OrderedSeed G root t p)

theorem reservoir_degree_balance : G.degree root+seedRho G root A.vertex p=
    (seedReservoir G root A.vertex).card+p := by
  have h := root_degree_balance A.canonicalGraph A.positive
  have hd : A.canonicalGraph.degree (Sum.inr ⟨0,A.positive⟩)=G.degree root := by
    simp only [← ncard_neighborSet]
    change ((G.comap A.hostEquiv).neighborSet (Sum.inr ⟨0,A.positive⟩)).ncard=(G.neighborSet root).ncard
    rw [neighbor_ncard_comap_equiv,A.hostEquiv_inr,A.first]
  have hc : (baseNeighbors A.canonicalGraph A.positive).card=(seedReservoir G root A.vertex).card := by
    rw [← A.canonicalBase_image,card_image_of_injective _ Subtype.val_injective]
  rw [hd,A.canonicalRho,hc] at h
  exact h

theorem model_of_external_block {d : ℕ} (hd : 7*t≤d) (hdegree : d≤G.degree root)
    (ht : 4≤t) (heven : Even t) (B : Finset V) (hBt : B.card<t) (hlarge : t-p≤B.card)
    (hout : ∀ x∈B, x∉univ.image A.vertex)
    (hmiss : ∀ x∈B, missingNeighbors G ((seedReservoir G root A.vertex).erase x) x≤
      B.card+2*p+seedRho G root A.vertex p) : HasBudgetedClique t G := by
  obtain ⟨C,hCB,hCc⟩ := exists_subset_card_eq hlarge
  have htotal : p+C.card=t := by have h := A.small; omega
  have hCpos : 0<C.card := by have h := A.small; omega
  let b := finsetEmbedding C
  have hCb : ∀ i, b i∈C := finsetEmbedding_mem C
  have houtC : ∀ x∈C, x∉univ.image A.vertex := fun x hx => hout x (hCB hx)
  let sep := A.blockVertexDisjoint C houtC
  let φ : (Fin p ⊕ Fin C.card) ↪ V :=
    finSumFinEquiv.toEmbedding.trans (appendVertices A.vertex b sep)
  have hφa : ∀ i, φ (Sum.inl i)=A.vertex i := by intro i; exact appendVertices_left A.vertex b sep i
  have hφb : ∀ i, φ (Sum.inr i)=b i := by intro i; exact appendVertices_right A.vertex b sep i
  let D := seedReservoir G root A.vertex \ C
  have hDsub : D⊆seedReservoir G root A.vertex := sdiff_subset
  have houtside : ∀ v, φ v∉D := by
    rintro (i | i) hv
    · rw [hφa] at hv
      have hh := (mem_sdiff.mp (hDsub hv)).2
      exact hh (mem_image.mpr ⟨i,mem_univ _,rfl⟩)
    · rw [hφb] at hv
      exact (mem_sdiff.mp hv).2 (hCb i)
  have hDcard : 6*t+seedRho G root A.vertex p≤D.card := by
    have hb := A.reservoir_degree_balance
    have hsub : seedReservoir G root A.vertex⊆D∪C := by
      intro v hv
      by_cases hc : v∈C
      · exact mem_union_right _ hc
      · exact mem_union_left _ (mem_sdiff.mpr ⟨hv,hc⟩)
    have hc := (card_le_card hsub).trans (card_union_le D C)
    omega
  have hold : ∀ i, missingNeighbors G D (φ (Sum.inl i))≤
      p+i.val+1+seedRho G root A.vertex (i.val+1) := by
    intro i
    rw [hφa]
    exact (missingNeighbors_mono G hDsub _).trans (A.missing i)
  have hnew : ∀ i, missingNeighbors G D (φ (Sum.inr i))≤t+2*p+seedRho G root A.vertex p := by
    intro i
    rw [hφb]
    have hsub : D⊆(seedReservoir G root A.vertex).erase (b i) := by
      intro v hv
      exact mem_erase.mpr ⟨fun he => (mem_sdiff.mp hv).2 (he ▸ hCb i),hDsub hv⟩
    have hm := (missingNeighbors_mono G hsub _).trans (hmiss (b i) (hCB (hCb i)))
    omega
  have hmodel : HasBudgetedClique (p+C.card) G := by
    exact budgeted_model_of_carrier G D φ houtside hCpos (by omega)
      (by simpa only [htotal] using heven) (seedRho G root A.vertex p)
      (seedRho_le G root A.vertex p) (fun i => seedRho G root A.vertex (i.val+1))
      (fun i => seedRho_le G root A.vertex (i.val+1))
      (fun i => seedRho_monotone G root A.vertex i.isLt)
      (by simpa only [htotal] using hDcard) hold (by simpa only [htotal] using hnew)
  exact htotal ▸ hmodel

end OrderedSeed
end
end Cycle13
