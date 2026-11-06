import Cycle12.PreparedMatchingClosure12
import Cycle12.ActualQuotientRouting12

namespace Cycle12.Even12
open Cycle12.Global12 Cycle13 SimpleGraph Finset Real
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000
variable {V : Type} [Fintype V] [DecidableEq V]
namespace ActualFoldStage12
variable {G : SimpleGraph V} {L : EvenScaleLayers12 G} {i : ℕ}
variable (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t)
  (Q : ∀ t,F.AmbientQuotientPacking P t) (D : ∀ t,F.AmbientOutlineData P Q t)

abbrev ClassMatchingIndex (t : F.BatchIndex) (label : Sym2 (Option ((F.active t.1).Index t.2))) :=
  ((P t).classes label).ledger.matchingFamily (F.batchActive_disjoint t) |>.Index

def classMatchingRoute (hi : i≤L.stopIndex) (t : F.BatchIndex)
    (label : Sym2 (Option ((F.active t.1).Index t.2))) (j : F.ClassMatchingIndex P t label) :
    G.Walk (((P t).classes label).ledger.matchingFamily (F.batchActive_disjoint t) |>.left j).val
      (((P t).classes label).ledger.matchingFamily (F.batchActive_disjoint t) |>.right j).val :=
  F.boxRoute P Q D hi t.1 (Sum.inr (Sum.inl ⟨t.2,⟨label,j⟩⟩))

theorem localBatchEdges_ambient (t : F.BatchIndex) :
    Sym2.map (Function.Embedding.subtype _ : F.batchVertices t ↪ V) '' (F.localBatchGraph t).edgeSet⊆
      (L.foldDescendantGraph i t.1).edgeSet := by
  rintro _ ⟨e,he,rfl⟩
  induction e using Sym2.ind with
  | _ x y => exact (F.batches t.1).graph_le t.2 he

/-- Each actual matching class now closes with the same common routes
already used for low paths and quotient switches. -/
theorem actual_matching_class_closure (hi : i≤L.stopIndex) (t : F.BatchIndex)
    (label : Sym2 (Option ((F.active t.1).Index t.2))) :
    ∃ T : CyclePacking G,
      T.used=Sym2.map (Function.Embedding.subtype _ : F.batchVertices t ↪ V) ''
        ((P t).classes label).ledger.matchingEdges∪
        (⋃ j,(F.classMatchingRoute P Q D hi t label j).edgeSet) ∧
      T.count≤((P t).classes label).ledger.matchingGroupCount := by
  let ledger := ((P t).classes label).ledger
  have hQ := (growing_rounding_bounds (logScale_active L.initial_log_pos.le L.phase_lower hi)).1
  apply ledger.close_matching (F.batchActive_disjoint t) hQ (Function.Embedding.subtype _)
    (F.quotientRoutingCores t) (F.quotientRoutingCores_disjoint hi t)
    (fun r v hv => (F.active t.1).subset_router t.2 r ((mem_verticesWithin _ _ v).mp hv))
    (fun {_ _} h => F.batch_graph_le_original t h)
    (F.classMatchingRoute P Q D hi t label)
  · intro j
    exact F.boxRoute_isPath P Q D hi t.1 _
  · intro j v hv
    exact F.boxRoute_support P Q D hi t.1 _ hv
  · intro j
    exact F.boxRoute_hard P Q D hi t.1 _
  · intro j k hjk ht
    apply F.boxRoute_team_interiors P Q D hi t.1
    · intro he
      have h1 := eq_of_heq (Sigma.mk.inj (Sum.inl.inj (Sum.inr.inj he))).2
      exact hjk (eq_of_heq (Sigma.mk.inj h1).2)
    · exact congrArg (fun x => Sum.inr (Sum.inl
        (⟨t.2,⟨label,x⟩⟩ : (F.boxMatchingTeams P hi t.1).Team))) ht
  · intro j k hjk
    apply F.boxRoute_edges_disjoint P Q D hi t.1
    intro he
    have h1 := eq_of_heq (Sigma.mk.inj (Sum.inl.inj (Sum.inr.inj he))).2
    exact hjk (eq_of_heq (Sigma.mk.inj h1).2)
  · intro j
    exact (F.boxRoute_descendant_disjoint P Q D hi t.1 _ t.1).symm.mono
      (F.localBatchEdges_ambient t) subset_rfl

end ActualFoldStage12
end
end Cycle12.Even12
