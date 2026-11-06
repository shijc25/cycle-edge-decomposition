import Cycle12.ActualCoreRemainder12

namespace Cycle12.Even12
open Cycle12.Global12 Cycle13 SimpleGraph Finset Real
open OAI.ErdosGallai.Scale OAI.ErdosGallai.Sampling
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000
variable {V : Type} [Fintype V] [DecidableEq V]
namespace ActualFoldStage12
variable {G : SimpleGraph V} {L : EvenScaleLayers12 G} {i : ℕ}
variable (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t)
  (Q : ∀ t,F.AmbientQuotientPacking P t) (D : ∀ t,F.AmbientOutlineData P Q t)

theorem coreCompletion_outside_neighbors (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i)
    (v : V) (hv : v∉(L.foldCorePiece i r).vertices) :
    (neighborsIn (F.coreCompletionGraph P Q D hi r) v (L.foldCorePiece i r).vertices).card=
      (F.coreCompletionGraph P Q D hi r).degree v := by
  rw [←card_neighborFinset_eq_degree]
  congr 1
  ext u
  simp only [neighborsIn,mem_filter,mem_neighborFinset]
  constructor
  · exact fun h => h.2
  · intro h
    have hh := (F.coreCompletion_outside_adj P Q D hi r hv).mp h
    have he := (F.coreExternalPairs P r).restrict_graph_le _ hh
    rcases F.coreExternal_bipartite P r he with h'|h'
    · exact False.elim (hv h'.1)
    · exact ⟨h'.2,h⟩

theorem coreCompletion_high_degree (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i)
    (v : V) (hw : v∈F.coreCompletionVertices P r) (hv : v∉(L.foldCorePiece i r).vertices) :
    F.coreCenterThreshold r≤
      ((neighborsIn (F.coreCompletionGraph P Q D hi r) v (L.foldCorePiece i r).vertices).card:ℝ) := by
  have hh : v∈F.coreHighCenters P r := (mem_union.mp hw).resolve_left hv
  rw [F.coreCompletion_outside_neighbors P Q D hi r v hv,
    F.coreCompletion_outside_degree P Q D hi r v hv,F.coreHigh_degree P r v hh]
  exact (mem_filter.mp hh).2

theorem coreCompletion_load (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i)
    (v : V) (hv : v∈(L.foldCorePiece i r).vertices) :
    ((neighborsIn (F.coreCompletionGraph P Q D hi r) v (L.foldCorePiece i r).verticesᶜ).card:ℝ)≤
      routingAllowance (logScale (originalLog V) L.stopIndex i) := by
  have hs : neighborsIn (F.coreCompletionGraph P Q D hi r) v (L.foldCorePiece i r).verticesᶜ⊆
      (F.coreExternalPairs P r).graph.neighborFinset v := by
    intro u hu
    have h := mem_filter.mp hu
    have he := (F.coreCompletion_outside_adj P Q D hi r (mem_compl.mp h.1)).mp h.2.symm
    exact ((F.coreExternalPairs P r).graph.mem_neighborFinset v u).mpr
      ((F.coreExternalPairs P r).restrict_graph_le _ he).symm
  have hc := card_le_card hs
  rw [card_neighborFinset_eq_degree] at hc
  exact (show ((neighborsIn (F.coreCompletionGraph P Q D hi r) v
    (L.foldCorePiece i r).verticesᶜ).card:ℝ)≤(F.coreExternalPairs P r).graph.degree v by
      exact_mod_cast hc).trans (F.coreExternal_core_degree P r v hv)

theorem coreCompletion_even (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i)
    (v : V) (hv : v∉(L.foldCorePiece i r).vertices) :
    Even ((F.coreCompletionGraph P Q D hi r).degree v) := by
  rw [F.coreCompletion_outside_degree P Q D hi r v hv]
  exact F.coreHigh_even P r v hv

/-- All high-center hypotheses are now checked on the concrete remainder
from the actual joint routing. No abstract completion premise is assumed. -/
theorem actual_core_completion (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i) {K : ℝ}
    (hK : 0≤K)
    (ih : ∀ m,m<Fintype.card V → ∀ H : SimpleGraph (Fin m),
      ∃ T : CyclePacking H,T.weight≤K*m) :
    ∃ T : CyclePacking (F.coreCompletionGraph P Q D hi r),
      T.weight+F.coreCenterThreshold r/2+2*routingAllowance (logScale (originalLog V) L.stopIndex i)≤
        (1+23/42+K*eta+1/2048)*(L.foldCorePiece i r).vertices.card := by
  let w := logScale (originalLog V) L.stopIndex i
  have data := (L.actual_box_data hi (L.foldParent_mem i r.1) (L.foldBox_mem i r.1)).2.2.2.1 r.2
  have hncore : 2≤(L.foldCorePiece i r).vertices.card := by
    simpa only [Fintype.card_coe] using (L.fold_core_local_data hi r).1
  apply supported_high_center_completion (F.coreCompletionGraph P Q D hi r)
    (F.coreCompletionVertices P r) (L.foldCorePiece i r).vertices
    (subset_union_left) (F.coreCompletion_supported P Q D hi r)
    (logScale_active L.initial_log_pos.le L.phase_lower hi)
    (hncore.trans (card_le_card subset_union_left)) hK data.1.le data.2.1
    (F.coreCompletion_expansion P Q D hi r)
    (F.coreCompletion_high_degree P Q D hi r) (F.coreCompletion_load P Q D hi r)
    (F.coreCenterThreshold_bounds r).1 (F.coreCenterThreshold_bounds r).2
    (fun v _ hv => F.coreCompletion_even P Q D hi r v hv) ih

end ActualFoldStage12
end
end Cycle12.Even12
