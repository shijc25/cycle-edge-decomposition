import Cycle12.Foundations.DisjointBlockContraction
import Cycle12.Foundations.PackingEmbedding
import Cycle12.Foundations.PackingExtension

namespace Cycle12
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V W I : Type} [Fintype V] [Fintype W] [Fintype I]
  [DecidableEq V] [DecidableEq W] [DecidableEq I]

/-- Vertices outside every local active block remain outside their
embedded active blocks in the original graph. -/
theorem outside_blocks_embedding (e : V ↪ W) (A : I → Finset V) (B : I → Finset W)
    (hmap : ∀ i,(A i).map e=B i) {v : V} (hv : v∉blockUnion A) : e v∉blockUnion B := by
  intro he
  obtain ⟨i,hi⟩ := (mem_blockUnion B (e v)).mp he
  rw [←hmap i] at hi
  obtain ⟨u,hu,huv⟩ := mem_map.mp hi
  exact hv ((mem_blockUnion A v).mpr ⟨i,e.injective huv ▸ hu⟩)

def blockEmbedding (e : V ↪ W) (A : I → Finset V) (B : I → Finset W)
    (hmap : ∀ i,(A i).map e=B i) : ContractedVertices A ↪ ContractedVertices B where
  toFun := Sum.elim Sum.inl (fun v => Sum.inr ⟨e v.val,outside_blocks_embedding e A B hmap v.property⟩)
  inj' := by
    intro x y h
    cases x with
    | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (Sum.inl.inj h)
      | inr y => cases h
    | inr x =>
      cases y with
      | inl y => cases h
      | inr y =>
        apply congrArg Sum.inr
        apply Subtype.ext
        exact e.injective (congrArg Subtype.val (Sum.inr.inj h))

theorem blockEmbedding_commutes (e : V ↪ W) (A : I → Finset V) (B : I → Finset W)
    (hmap : ∀ i,(A i).map e=B i)
    (hA : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hB : Pairwise (fun i j => Disjoint (B i) (B j))) (v : V) :
    contractVertex B (e v)=blockEmbedding e A B hmap (contractVertex A v) := by
  by_cases hv : v∈blockUnion A
  · obtain ⟨i,hi⟩ := (mem_blockUnion A v).mp hv
    have he : e v∈B i := by rw [←hmap i]; exact mem_map.mpr ⟨v,hi,rfl⟩
    rw [contractVertex_of_mem A hA hi,contractVertex_of_mem B hB he]
    rfl
  · rw [contractVertex_of_not_mem A v hv,
      contractVertex_of_not_mem B (e v) (outside_blocks_embedding e A B hmap hv)]
    rfl

theorem blockEmbedding_graph (H : SimpleGraph V) (e : V ↪ W) (A : I → Finset V) (B : I → Finset W)
    (hmap : ∀ i,(A i).map e=B i)
    (hA : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hB : Pairwise (fun i j => Disjoint (B i) (B j))) :
    (H.map e).map (contractVertex B)=(H.map (contractVertex A)).map (blockEmbedding e A B hmap) := by
  rw [SimpleGraph.map_map,SimpleGraph.map_map]
  congr 1
  funext v
  exact blockEmbedding_commutes e A B hmap hA hB v

theorem packing_mapEmbedding_weight {H : SimpleGraph V} (P : CyclePacking H) (e : V ↪ W) :
    (P.mapEmbedding e).weight=P.weight := by
  change (P.count:ℝ)+(23/42:ℝ)*(P.mapEmbedding e).singles=P.weight
  rw [CyclePacking.singles_mapEmbedding]
  rfl

/-- A local contracted packing can be embedded into the full original
contracted graph at exactly the same cost, regardless of isolated ambient
vertices. No larger-order induction call is made. -/
theorem blockEmbedding_packing (H : SimpleGraph V) (e : V ↪ W) (A : I → Finset V) (B : I → Finset W)
    (hmap : ∀ i,(A i).map e=B i)
    (hA : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hB : Pairwise (fun i j => Disjoint (B i) (B j))) (P : CyclePacking (H.map (contractVertex A))) :
    ∃ T : CyclePacking ((H.map e).map (contractVertex B)),T.weight=P.weight := by
  rw [blockEmbedding_graph H e A B hmap hA hB]
  exact ⟨P.mapEmbedding (blockEmbedding e A B hmap),packing_mapEmbedding_weight P _⟩

theorem blockEmbedding_proper (H : SimpleGraph V) (e : V ↪ W) (A : I → Finset V) (B : I → Finset W)
    (hmap : ∀ i,(A i).map e=B i)
    (hA : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hp : ∀ {x y},H.Adj x y → contractVertex A x ≠ contractVertex A y) :
    ∀ {x y},(H.map e).Adj x y → contractVertex B x ≠ contractVertex B y := by
  rintro x y ⟨_,u,v,hu,rfl,rfl⟩ he
  rw [blockEmbedding_commutes e A B hmap hA hB,blockEmbedding_commutes e A B hmap hA hB] at he
  exact hp hu ((blockEmbedding e A B hmap).injective he)

theorem blockEmbedding_unique (H : SimpleGraph V) (e : V ↪ W) (A : I → Finset V) (B : I → Finset W)
    (hmap : ∀ i,(A i).map e=B i)
    (hA : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hu : Set.InjOn (Sym2.map (contractVertex A)) H.edgeSet) :
    Set.InjOn (Sym2.map (contractVertex B)) (H.map e).edgeSet := by
  intro x hx y hy he
  rw [edgeSet_map] at hx hy
  obtain ⟨x,hx,rfl⟩ := hx
  obtain ⟨y,hy,rfl⟩ := hy
  have hcomm (f : Sym2 V) :
      Sym2.map (contractVertex B) (Sym2.map e f)=
        Sym2.map (blockEmbedding e A B hmap) (Sym2.map (contractVertex A) f) := by
    induction f using Sym2.inductionOn with
    | _ a b =>
      simp only [Sym2.map_mk,blockEmbedding_commutes e A B hmap hA hB]
  change Sym2.map (contractVertex B) (Sym2.map e x)=Sym2.map (contractVertex B) (Sym2.map e y) at he
  rw [hcomm,hcomm] at he
  have hf := (Sym2.map.injective (blockEmbedding e A B hmap).injective) he
  exact congrArg (Sym2.map e) (hu hx hy hf)

end
end Cycle12
