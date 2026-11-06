import Cycle12.TwoReservoirFragmentClosure12
import Cycle12.Foundations.WeightedPacking

namespace Cycle12
open Cycle13 SimpleGraph Finset
open OAI.ErdosGallai
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V W : Type} [Fintype V] [Fintype W]

/-- Complete first pass, including the actual augmented Lovász partition,
hub replacement in A, closure in B, and precise edge coverage. -/
theorem first_pass_reservoir_packing [Nonempty V]
    (J : SimpleGraph W) (G H : SimpleGraph V) (hHG : H ≤ G)
    (f : J →g G) (hf : Function.Injective f)
    (A B : Finset V) (hAB : Disjoint A B) (hfar : ∀ w, f w ∉ A ∧ f w ∉ B)
    {z upperA upperB : ℝ} (hA : ReservoirSample H A z upperA) (hB : ReservoirSample H B z upperB)
    (hz : 8192 ≤ z) (hzr : z ≤ (Fintype.card V:ℝ))
    (hlog : 8192*Real.log (Fintype.card V:ℝ) ≤ z)
    (hsquare : 2112*(Fintype.card V:ℝ) ≤ z^2) :
    ∃ P : CyclePacking G,
      2*P.count ≤ Fintype.card W+1 ∧
      Sym2.map f '' J.edgeSet ⊆ P.used ∧
      P.used ⊆ (Sym2.map f '' J.edgeSet) ∪ H.edgeSet := by
  obtain ⟨k,F,hk,hd,hc,hs,houter,hnear⟩ := mapped_hub_fragment_partition J G f hf
  have hout : ∀ i, ∀ v ∈ (F i).support, v ∉ A ∧ v ∉ B := by
    intro i v hv
    obtain ⟨w,rfl⟩ := hs i hv
    exact hfar w
  have hcard : Fintype.card (Fin k) ≤ Fintype.card V := by
    have hh := Fintype.card_le_of_injective f hf
    rw [Fintype.card_fin]
    omega
  obtain ⟨C,hC,hCC,hFC,hCH⟩ := close_hub_fragments G H hHG A B hAB hA hB F hd hout houter hnear
    hz hzr hlog hsquare hcard
  let P : CyclePacking G := ⟨k,fun i => (C i).edgeSet,fun i => ⟨_,C i,hC i,rfl⟩,hCC⟩
  refine ⟨P,hk,?_,?_⟩
  · rw [←hc]
    apply Set.iUnion_subset
    intro i
    exact (hFC i).trans (Set.subset_iUnion (fun i => (C i).edgeSet) i)
  · intro e he
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp he
    rcases hCH i hi with hi | hi
    · exact Or.inl (hc ▸ Set.mem_iUnion.mpr ⟨i,hi⟩)
    · exact Or.inr hi

/-- A reserve disjoint from both the exterior graph and the first routing
bank survives the entire first pass as an actual subgraph. -/
theorem packing_preserves_reserve {G R H : SimpleGraph V} (P : CyclePacking G)
    (old : Set (Sym2 V)) (hR : R ≤ G)
    (hused : P.used ⊆ old ∪ H.edgeSet)
    (hRo : Disjoint R.edgeSet old) (hRH : Disjoint R.edgeSet H.edgeSet) : R ≤ P.residue := by
  intro x y hxy
  rw [CyclePacking.residue,deleteEdges_adj]
  change G.Adj x y ∧ s(x,y) ∉ P.used
  refine ⟨hR hxy,?_⟩
  intro he
  rcases hused he with he | he
  · exact Set.disjoint_left.mp hRo hxy he
  · exact Set.disjoint_left.mp hRH hxy he

end
end Cycle12
