import Cycle12.Foundations.GraphRelabel

/-! Convert an arbitrary ordered seed into the canonical external/prefix
labels and transport the proved GLW block back to the original vertices. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable

namespace OrderedSeed
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {root : V} {t p : ℕ}
    (A : OrderedSeed G root t p)

abbrev Outside := {v : V // v∉univ.image A.vertex}

def hostEquiv : A.Outside ⊕ Fin p ≃ V := Equiv.ofBijective
    (Sum.elim Subtype.val A.vertex) (by
  constructor
  · rintro (x | i) (y | k) h
    · exact congrArg Sum.inl (Subtype.ext h)
    · exact False.elim (x.property (mem_image.mpr ⟨k,mem_univ _,h.symm⟩))
    · exact False.elim (y.property (mem_image.mpr ⟨i,mem_univ _,h⟩))
    · exact congrArg Sum.inr (A.vertex.injective h)
  · intro v
    by_cases hv : v∈univ.image A.vertex
    · obtain ⟨i,_,hi⟩ := mem_image.mp hv
      exact ⟨Sum.inr i,hi⟩
    · exact ⟨Sum.inl ⟨v,hv⟩,rfl⟩)

@[simp] theorem hostEquiv_inl (x : A.Outside) : A.hostEquiv (Sum.inl x)=x.val := rfl
@[simp] theorem hostEquiv_inr (i : Fin p) : A.hostEquiv (Sum.inr i)=A.vertex i := rfl

def canonicalGraph : SimpleGraph (A.Outside ⊕ Fin p) := G.comap A.hostEquiv

theorem canonicalRho (k : ℕ) : prefixRho A.canonicalGraph A.positive k=seedRho G root A.vertex k := by
  unfold prefixRho seedRho
  congr 1
  ext i
  simp only [mem_filter,mem_univ,true_and]
  change (i.val<k ∧ ¬G.Adj (A.vertex ⟨0,A.positive⟩) (A.vertex i)) ↔ _
  rw [A.first]

theorem canonicalBase_image :
    (baseNeighbors A.canonicalGraph A.positive).image Subtype.val=seedReservoir G root A.vertex := by
  ext v
  constructor
  · intro hv
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hv
    have hh := (mem_filter.mp hx).2
    change G.Adj (A.vertex ⟨0,A.positive⟩) x.val at hh
    rw [A.first] at hh
    exact mem_sdiff.mpr ⟨(G.mem_neighborFinset root x.val).mpr hh,x.property⟩
  · intro hv
    have hh := mem_sdiff.mp hv
    refine mem_image.mpr ⟨⟨v,hh.2⟩,mem_filter.mpr ⟨mem_univ _,?_⟩,rfl⟩
    change G.Adj (A.vertex ⟨0,A.positive⟩) v
    rw [A.first]
    exact (G.mem_neighborFinset root v).mp hh.1

theorem canonicalMissing (i : Fin p) : baseMissing A.canonicalGraph A.positive i=
    missingNeighbors G (seedReservoir G root A.vertex) (A.vertex i) := by
  rw [← A.canonicalBase_image]
  unfold baseMissing missingNeighbors
  rw [filter_image,card_image_of_injective _ Subtype.val_injective]
  congr 1

theorem canonical_card : Fintype.card A.Outside+p=Fintype.card V := by
  have h := Fintype.card_congr A.hostEquiv
  simpa only [Fintype.card_sum,Fintype.card_fin] using h

theorem external_block {d : ℕ} (hd : 7*t≤d) (hdegree : d≤G.degree root)
    (hbad : ¬HasBudgetedClique t G) (heven : ∀ v, Even (G.degree v))
    (hdef : degreeDeficiency G d<d) (hminimal : IsMinimumBad G d t) :
    ∃ B : Finset V, B.Nonempty ∧ B.card<t ∧
      (∀ x∈B, x∉univ.image A.vertex) ∧
      ∀ x∈B, missingNeighbors G ((seedReservoir G root A.vertex).erase x) x≤
        B.card+2*p+seedRho G root A.vertex p := by
  have hc : 0<Fintype.card A.Outside := by
    have hn := G.degree_lt_card_verts root
    have he := A.canonical_card
    have hp := A.small
    omega
  letI : Nonempty A.Outside := Fintype.card_pos_iff.mp hc
  have hdeg : d≤A.canonicalGraph.degree (Sum.inr ⟨0,A.positive⟩) := by
    rw [canonicalGraph,degree_comap_equiv,hostEquiv_inr,A.first]
    exact hdegree
  have hb : ¬HasBudgetedClique t A.canonicalGraph :=
    fun h => hbad ((budgetedClique_comap_iff G A.hostEquiv t).mp h)
  have he : ∀ v, Even (A.canonicalGraph.degree v) := by
    intro v
    rw [canonicalGraph,degree_comap_equiv]
    exact heven _
  have hdef' : degreeDeficiency A.canonicalGraph d<d := by
    rw [canonicalGraph,deficiency_comap_equiv]
    exact hdef
  have hm : ∀ H : SimpleGraph (A.Outside ⊕ Fin 0),
      (∀ v, Even (H.degree v)) → degreeDeficiency H d<d → HasBudgetedClique t H := by
    intro H hHe hHd
    apply hminimal _ H _ hHe hHd
    simp only [Fintype.card_sum,Fintype.card_fin]
    have hcard := A.canonical_card
    have hp := A.positive
    omega
  have ho : ∀ i : Fin p, i.val≠0 → baseMissing A.canonicalGraph A.positive i≤
      p+(i.val+1)+prefixRho A.canonicalGraph A.positive (i.val+1) := by
    intro i _
    rw [A.canonicalMissing,A.canonicalRho]
    have h := A.missing i
    omega
  obtain ⟨B,hB,hBt,hBm⟩ := glw_nonempty_external_block A.canonicalGraph A.positive A.small
    hd hdeg hb he hdef' hm ho
  let C := B.image Subtype.val
  have hCc : C.card=B.card := card_image_of_injective _ Subtype.val_injective
  refine ⟨C,hB.image _,hCc ▸ hBt,?_,?_⟩
  · intro v hv
    obtain ⟨x,_,rfl⟩ := mem_image.mp hv
    exact x.property
  · intro v hv
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hv
    rw [hCc,← A.canonicalRho p,← A.canonicalBase_image,← image_erase Subtype.val_injective]
    let f : A.Outside ↪ V := Function.Embedding.subtype _
    have h := missing_image G f ((baseNeighbors A.canonicalGraph A.positive).erase x) x
    change missingNeighbors G (((baseNeighbors A.canonicalGraph A.positive).erase x).image f) (f x)≤_
    rw [h]
    exact hBm x hx

end OrderedSeed
end
end Cycle13
