import Cycle12.BlockEmbedding12
import Cycle12.ActualFoldQuotients12

namespace Cycle12
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem verticesWithin_map (W A : Finset V) (hA : A⊆W) :
    (verticesWithin W A).map (Function.Embedding.subtype _)=A := by
  ext v
  simp only [mem_map,mem_verticesWithin,Function.Embedding.subtype_apply]
  exact ⟨fun ⟨x,hx,he⟩ => he ▸ hx,fun hv => ⟨⟨v,hA hv⟩,hv,rfl⟩⟩

end
end Cycle12

namespace Cycle12.Even12
open Cycle12.Global12 Cycle13 SimpleGraph Finset Real
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]
namespace ActualFoldStage12
variable {G : SimpleGraph V} {L : EvenScaleLayers12 G} {i : ℕ}

def ambientBatchActive (F : ActualFoldStage12 L i) (t : F.BatchIndex) : (F.active t.1).Index t.2 → Finset V :=
  (F.active t.1).vertices t.2

def ambientBatchRetained (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t) (t : F.BatchIndex) :
    SimpleGraph V := (P t).retained.map (Function.Embedding.subtype _ : F.batchVertices t ↪ V)

theorem batchActive_embedding (F : ActualFoldStage12 L i) (t : F.BatchIndex)
    (r : (F.active t.1).Index t.2) :
    (F.batchActive t r).map (Function.Embedding.subtype _)=F.ambientBatchActive t r :=
  verticesWithin_map _ _ ((F.active t.1).subset_batch t.2 r)

theorem ambient_retained_le (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t) (t : F.BatchIndex) :
    F.ambientBatchRetained P t ≤ F.batchGraph t := by
  rintro x y ⟨_,u,v,h,rfl,rfl⟩
  exact (P t).quotient_unique (F.batchActive_disjoint t) |>.1 h

theorem ambient_quotient_proper (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t) (t : F.BatchIndex) :
    ∀ {x y},(F.ambientBatchRetained P t).Adj x y →
      contractVertex (F.ambientBatchActive t) x ≠ contractVertex (F.ambientBatchActive t) y :=
  blockEmbedding_proper (P t).retained (Function.Embedding.subtype _) (F.batchActive t) (F.ambientBatchActive t)
    (F.batchActive_embedding t) (F.batchActive_disjoint t) ((F.active t.1).disjoint t.2)
    ((P t).quotient_unique (F.batchActive_disjoint t)).2.1

theorem ambient_quotient_unique (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t) (t : F.BatchIndex) :
    Set.InjOn (Sym2.map (contractVertex (F.ambientBatchActive t))) (F.ambientBatchRetained P t).edgeSet :=
  blockEmbedding_unique (P t).retained (Function.Embedding.subtype _) (F.batchActive t) (F.ambientBatchActive t)
    (F.batchActive_embedding t) (F.batchActive_disjoint t) ((F.active t.1).disjoint t.2)
    ((P t).quotient_unique (F.batchActive_disjoint t)).2.2

/-- Restore every local quotient packing to the original vertex set.
The strict smaller-order induction was already applied locally, and the
embedding preserves both cycle count and singleton weight exactly. -/
theorem ambient_quotient_family (F : ActualFoldStage12 L i) (hi : i ≤ L.stopIndex)
    (ih : PotentialBelow (Fintype.card V)) :
    ∃ P : ∀ t : F.BatchIndex,F.BatchPreparation t,
      ∃ pack : ∀ t,CyclePacking ((F.ambientBatchRetained P t).map (contractVertex (F.ambientBatchActive t))),
        (∀ t,(pack t).weight ≤ C*globalPhi (b*logScale (originalLog V) L.stopIndex i)*
          (((F.batchVertices t).card:ℝ)-kappa*∑ j,(((F.active t.1).vertices t.2 j).card:ℝ))) ∧
        (∑ t,(pack t).weight) ≤ C*globalPhi (b*logScale (originalLog V) L.stopIndex i)*
          (F.batchMass-kappa*F.activeMass) := by
  obtain ⟨P,Q,_,hq,hsum⟩ := F.prepared_quotient_family hi ih
  have hp (t : F.BatchIndex) : ∃ T : CyclePacking
      ((F.ambientBatchRetained P t).map (contractVertex (F.ambientBatchActive t))),T.weight=(Q t).weight :=
    blockEmbedding_packing (P t).retained (Function.Embedding.subtype _) (F.batchActive t) (F.ambientBatchActive t)
      (F.batchActive_embedding t) (F.batchActive_disjoint t) ((F.active t.1).disjoint t.2) (Q t)
  choose pack hpack using hp
  refine ⟨P,pack,fun t => (hpack t).trans_le (hq t),?_⟩
  simpa only [hpack] using hsum

end ActualFoldStage12
end
end Cycle12.Even12
