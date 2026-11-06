import Cycle12.SoftOutlinePacking12
import Cycle12.QuotientPackingLedger12

namespace Cycle12
open Cycle13 SimpleGraph Finset
open OAI.ErdosGallai.Batch
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V W : Type} [Fintype V] [Fintype W] [DecidableEq V]

/-- The sum of all representative-cycle lengths is the exact number of
retained original edges used by the quotient packing. -/
theorem quotient_outline_total_length (G H : SimpleGraph V) (π : V → W)
    (hproper : ∀ {x y},H.Adj x y → π x≠π y)
    (hunique : Set.InjOn (Sym2.map π) H.edgeSet) (Q : CyclePacking (H.map π))
    (c : Fin Q.count → CycleOutline G)
    (hc : ∀ i,(c i).edges=H.edgeSet∩Sym2.map π ⁻¹' Q.parts i) :
    (∑ i,(c i).cycle.length)=Q.used.ncard ∧ Q.used.ncard≤H.edgeSet.ncard := by
  have he (i : Fin Q.count) : (c i).cycle.length=(Q.parts i).ncard := by
    rw [←outline_edges_card,hc]
    exact quotient_edge_pullback_card H π hproper hunique (Q.parts i) (Q.parts_subset i)
  refine ⟨?_,?_⟩
  · simp_rw [he]
    exact (ncard_iUnion_disjoint Q.parts Q.disjoint).symm
  · have hh := quotient_edge_pullback_card H π hproper hunique Q.used Q.used_subset
    rw [←hh]
    exact Set.ncard_le_ncard Set.inter_subset_left

/-- Assemble every routed quotient cycle into an actual packing. Soft
collisions add only their total charge; singleton representatives are exact. -/
theorem soft_quotient_packing_weight (G H : SimpleGraph V) (π : V → W)
    (hproper : ∀ {x y},H.Adj x y → π x≠π y)
    (hunique : Set.InjOn (Sym2.map π) H.edgeSet) (Q : CyclePacking (H.map π))
    (c : Fin Q.count → CycleOutline G)
    (hc : ∀ i,(c i).edges=H.edgeSet∩Sym2.map π ⁻¹' Q.parts i)
    (route : ∀ i,∀ z : (c i).Switch,G.Walk ((c i).start z) ((c i).finish z))
    (hp : ∀ i z,(route i z).IsPath)
    (he : ∀ i,Pairwise (fun z w => Disjoint (route i z).edgeSet (route i w).edgeSet))
    (hi : ∀ i,Pairwise (fun z w => Disjoint (routeInterior (route i z)) (routeInterior (route i w))))
    (hcross : ∀ i,Disjoint H.edgeSet (⋃ z,(route i z).edgeSet))
    (hR : Pairwise (fun i j => Disjoint (⋃ z,(route i z).edgeSet) (⋃ z,(route j z).edgeSet)))
    (hcover : G.edgeSet=H.edgeSet∪⋃ i,⋃ z,(route i z).edgeSet)
    (fee : ∀ i,(c i).Switch → ℝ)
    (hfee : ∀ i z,((routeInterior (route i z)∩(c i).vertices).card:ℝ)≤fee i z) :
    ∃ T : CyclePacking G,T.used=(H.edgeSet∩Sym2.map π ⁻¹' Q.used)∪(⋃ i,⋃ z,(route i z).edgeSet) ∧
      T.weight≤Q.weight+∑ i,∑ z,fee i z := by
  have ho (i : Fin Q.count) (z : (c i).Switch) : Disjoint (c i).edges (route i z).edgeSet := by
    apply (hcross i).mono
    · rw [hc i]; exact Set.inter_subset_left
    · intro e he
      exact Set.mem_iUnion.mpr ⟨z,he⟩
  have hpack := fun i => soft_outline_packing_with_budget (c i) (route i) (hp i) (he i)
    (ho i) (hi i) (fee i) (hfee i)
  choose P hP hcount using hpack
  obtain ⟨T,hT,hTc⟩ := quotient_cycle_family_assembly G H π Q P
    (fun i => ⋃ z,(route i z).edgeSet) (fun i => by rw [hP i,hc i]) hR hcross
    (fun i => ∑ z,fee i z) hcount
  refine ⟨T,hT,?_⟩
  exact lifted_quotient_weight G H π hproper hunique Q T _ hcover
    (Set.disjoint_iUnion_right.mpr hcross) hT hTc

end
end Cycle12
