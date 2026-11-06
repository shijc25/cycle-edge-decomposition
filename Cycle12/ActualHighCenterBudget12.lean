import Cycle12.ActualCorePairSplit12

namespace Cycle12.Even12
open Cycle12.Global12 Cycle13 SimpleGraph Finset Real
open OAI.ErdosGallai.Scale OAI.ErdosGallai.Sampling
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]
namespace ActualFoldStage12
variable {G : SimpleGraph V} {L : EvenScaleLayers12 G} {i : ℕ}

def coreHighCenters (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t) (r : L.FoldCoreIndex i) : Finset V :=
  (L.foldCorePiece i r).verticesᶜ.filter (fun v =>
    F.coreCenterThreshold r ≤ ((F.coreExternalPairs P r).graph.degree v:ℝ))

def coreHighPairs (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t) (r : L.FoldCoreIndex i) :=
  (F.coreExternalPairs P r).restrict (fun j =>
    ¬(((F.coreExternalPairs P r).graph.degree ((F.coreExternalPairs P r).center j):ℝ) < F.coreCenterThreshold r))

theorem core_low_high_partition (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t)
    (r : L.FoldCoreIndex i) :
    ((F.coreExternalPairs P r).low (F.coreCenterThreshold r)).used∪(F.coreHighPairs P r).used=
      (F.coreExternalPairs P r).used ∧
    Disjoint ((F.coreExternalPairs P r).low (F.coreCenterThreshold r)).used (F.coreHighPairs P r).used :=
  (F.coreExternalPairs P r).restrict_partition _

theorem coreExternal_neighbors_degree (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t)
    (r : L.FoldCoreIndex i) (v : V) (hv : v∉(L.foldCorePiece i r).vertices) :
    (neighborsIn (F.coreExternalPairs P r).graph v (L.foldCorePiece i r).vertices).card=
      (F.coreExternalPairs P r).graph.degree v := by
  have he : neighborsIn (F.coreExternalPairs P r).graph v (L.foldCorePiece i r).vertices=
      (F.coreExternalPairs P r).graph.neighborFinset v := by
    ext u
    simp only [neighborsIn,mem_filter,mem_neighborFinset]
    constructor
    · exact fun h => h.2
    · intro h
      rcases F.coreExternal_bipartite P r h with hh|hh
      · exact False.elim (hv hh.1)
      · exact ⟨hh.2,h⟩
  rw [he,card_neighborFinset_eq_degree]

/-- High centers are counted in the actual aggregated original graph. -/
theorem core_high_incidence_budget (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t)
    (r : L.FoldCoreIndex i) :
    ((F.coreHighCenters P r).card:ℝ)*F.coreCenterThreshold r ≤
      routingAllowance (logScale (originalLog V) L.stopIndex i)*(L.foldCorePiece i r).vertices.card := by
  have hh := high_centers_incidence_budget (F.coreExternalPairs P r).graph (L.foldCorePiece i r).vertices
    (F.coreHighCenters P r) (a:=routingAllowance (logScale (originalLog V) L.stopIndex i))
    (d:=F.coreCenterThreshold r) (by
      intro v hv
      have hv' := mem_filter.mp hv
      rw [F.coreExternal_neighbors_degree P r v (mem_compl.mp hv'.1)]
      exact hv'.2) (by
      intro v hv
      have hs : neighborsIn (F.coreExternalPairs P r).graph v (F.coreHighCenters P r)⊆
          (F.coreExternalPairs P r).graph.neighborFinset v := by
        intro u hu
        exact (mem_neighborFinset _ _ _).mpr (mem_filter.mp hu).2
      have hc := card_le_card hs
      rw [card_neighborFinset_eq_degree] at hc
      exact (show ((neighborsIn (F.coreExternalPairs P r).graph v (F.coreHighCenters P r)).card:ℝ) ≤
        (F.coreExternalPairs P r).graph.degree v by exact_mod_cast hc).trans (F.coreExternal_core_degree P r v hv))
  simpa only [mul_comm] using hh

/-- The actual high-center vertex count and actual low-path palette
ceiling together fit the single 1/2048 core-order fee. -/
theorem core_high_palette_budget (F : ActualFoldStage12 L i) (hi : i ≤ L.stopIndex)
    (P : ∀ t,F.BatchPreparation t) (r : L.FoldCoreIndex i) :
    ((F.coreHighCenters P r).card:ℝ) ≤ (L.foldCorePiece i r).vertices.card/2048 ∧
      ((F.coreHighCenters P r).card:ℝ)+F.coreCenterThreshold r/2+
        2*routingAllowance (logScale (originalLog V) L.stopIndex i) ≤ (L.foldCorePiece i r).vertices.card/2048 := by
  let w := logScale (originalLog V) L.stopIndex i
  let R : ℝ := (L.foldCorePiece i r).vertices.card
  have data := (L.actual_box_data hi (L.foldParent_mem i r.1) (L.foldBox_mem i r.1)).2.2.2.1 r.2
  have hlo : (2:ℝ)^(s*w) ≤ R := data.1.le
  have hhi : R ≤ (2:ℝ)^(rho*w) := data.2.1
  have hR : 0<R := (rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _).trans_le hlo
  have hw : wA ≤ w := logScale_active L.initial_log_pos.le L.phase_lower hi
  have hs := high_center_scale_bounds (n:=R) hw hlo hhi (by nlinarith only [hR]) hR
  exact high_center_rounding_budget hs.1 hs.2.1 (Nat.cast_nonneg _)
    (F.coreCenterThreshold_bounds r).1 (F.coreCenterThreshold_bounds r).2 (F.core_high_incidence_budget P r)

theorem coreHigh_supported (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t)
    (r : L.FoldCoreIndex i) : SupportedOn (F.coreHighPairs P r).graph
      ((L.foldCorePiece i r).vertices∪F.coreHighCenters P r) := by
  intro x y hxy
  have h := ((F.coreHighPairs P r).graph_adj x y).mp hxy
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp h
  have hz : (F.coreHighPairs P r).center j∈F.coreHighCenters P r :=
    mem_filter.mpr ⟨mem_compl.mpr (F.coreExternal_outside P r j.val),le_of_not_gt j.property⟩
  have ha := (F.coreExternal_endpoints P r j.val).1
  have hb := (F.coreExternal_endpoints P r j.val).2
  rcases hj with he|he <;> rcases Sym2.eq_iff.mp he with ⟨hx,hy⟩|⟨hx,hy⟩
  · exact ⟨mem_union_right _ (hx.symm ▸ hz),mem_union_left _ (hy.symm ▸ ha)⟩
  · exact ⟨mem_union_left _ (hx.symm ▸ ha),mem_union_right _ (hy.symm ▸ hz)⟩
  · exact ⟨mem_union_right _ (hx.symm ▸ hz),mem_union_left _ (hy.symm ▸ hb)⟩
  · exact ⟨mem_union_left _ (hx.symm ▸ hb),mem_union_right _ (hy.symm ▸ hz)⟩

theorem coreHigh_degree (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t)
    (r : L.FoldCoreIndex i) (v : V) (hv : v∈F.coreHighCenters P r) :
    (F.coreHighPairs P r).graph.degree v=(F.coreExternalPairs P r).graph.degree v := by
  have hv' := mem_filter.mp hv
  exact (F.coreExternalPairs P r).restrict_center_degree (L.foldCorePiece i r).vertices
    (fun j => (F.coreExternal_endpoints P r j).1) (fun j => (F.coreExternal_endpoints P r j).2)
    (fun v => ¬((F.coreExternalPairs P r).graph.degree v:ℝ) < F.coreCenterThreshold r) v
    (mem_compl.mp hv'.1) (not_lt.mpr hv'.2)

theorem coreHigh_even (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t)
    (r : L.FoldCoreIndex i) (v : V) (hv : v∉(L.foldCorePiece i r).vertices) :
    Even ((F.coreHighPairs P r).graph.degree v) :=
  (F.coreHighPairs P r).exterior_even (L.foldCorePiece i r).vertices
    (fun j => (F.coreExternal_endpoints P r j.val).1) (fun j => (F.coreExternal_endpoints P r j.val).2) v hv

end ActualFoldStage12
end
end Cycle12.Even12
