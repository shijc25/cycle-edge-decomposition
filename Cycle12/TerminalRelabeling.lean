import Cycle12.TerminalReduction

namespace Cycle12
open SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Transport a terminal packing through an actual bijective vertex labeling,
preserving both the exact order and the exact number of edges. -/
theorem terminal_affine_of_labeling {V W : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (f : W ↪ V) (hsurj : Function.Surjective f)
    (hpack : ∃ P : Cycle13.CyclePacking (G.comap f),
      P.cost ≤ 19*(Fintype.card W-1)+6*(G.comap f).edgeSet.ncard) :
    ∃ P : Cycle13.CyclePacking G,
      P.cost ≤ 19*(Fintype.card V-1)+6*G.edgeSet.ncard := by
  have hmodel : (G.comap f).map f=G := by
    apply le_antisymm (SimpleGraph.map_comap_le f G)
    intro u v huv
    obtain ⟨a,rfl⟩ := hsurj u
    obtain ⟨b,rfl⟩ := hsurj v
    exact (SimpleGraph.map_adj f (G.comap f) (f a) (f b)).mpr ⟨a,b,huv,rfl,rfl⟩
  have hn : Fintype.card W=Fintype.card V :=
    Fintype.card_congr (Equiv.ofBijective f ⟨f.injective,hsurj⟩)
  have hm : (G.comap f).edgeSet.ncard=G.edgeSet.ncard := by
    have hh := congrArg (fun K : SimpleGraph V => K.edgeSet.ncard) hmodel
    rw [SimpleGraph.edgeSet_map,Set.ncard_image_of_injective _ f.sym2Map.injective] at hh
    exact hh
  obtain ⟨P,hP⟩ := hpack
  have hres : ∃ Q : Cycle13.CyclePacking ((G.comap f).map f),
      Q.cost ≤ 19*(Fintype.card V-1)+6*G.edgeSet.ncard := by
    refine ⟨P.mapEmbedding f,?_⟩
    rw [indexed_packing_cost_mapEmbedding]
    simpa only [hn,hm] using hP
  rwa [hmodel] at hres

end
end Cycle12
