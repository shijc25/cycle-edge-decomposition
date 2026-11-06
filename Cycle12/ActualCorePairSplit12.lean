import Cycle12.ActualFoldPairs12
import Cycle12.OwnedLowPathRequests12
import Cycle12.GlobalHighCenterCompletion12

namespace Cycle12.Even12
open Cycle12.Global12 Cycle13 SimpleGraph Finset Real
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]
namespace ActualFoldStage12
variable {G : SimpleGraph V} {L : EvenScaleLayers12 G} {i : ℕ}

def coreExternalPairs (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t) (r : L.FoldCoreIndex i) :=
  (F.corePairs P r).restrict (fun j => (F.corePairs P r).center j∉(L.foldCorePiece i r).vertices)

theorem coreExternal_endpoints (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t)
    (r : L.FoldCoreIndex i) (j : (F.coreExternalPairs P r).Index) :
    (F.coreExternalPairs P r).left j∈(L.foldCorePiece i r).vertices ∧
      (F.coreExternalPairs P r).right j∈(L.foldCorePiece i r).vertices := F.corePairs_endpoints P r j.val

theorem coreExternal_outside (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t)
    (r : L.FoldCoreIndex i) (j : (F.coreExternalPairs P r).Index) :
    (F.coreExternalPairs P r).center j∉(L.foldCorePiece i r).vertices := j.property

theorem coreExternal_good (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t)
    (r : L.FoldCoreIndex i) (j : (F.coreExternalPairs P r).Index) :
    (F.coreExternalPairs P r).left j∈F.activeVertices r.1 ∧
      (F.coreExternalPairs P r).right j∈F.activeVertices r.1 := F.boxPairs_good P r.1 j.val.val

/-- Every original pair graph used in the high-center branch is an actual
bipartite subgraph between the selected core and its exterior centers. -/
theorem coreExternal_bipartite (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t)
    (r : L.FoldCoreIndex i) {x y : V} (hxy : (F.coreExternalPairs P r).graph.Adj x y) :
    (x∈(L.foldCorePiece i r).vertices ∧ y∉(L.foldCorePiece i r).vertices) ∨
      (x∉(L.foldCorePiece i r).vertices ∧ y∈(L.foldCorePiece i r).vertices) := by
  have h := ((F.coreExternalPairs P r).graph_adj x y).mp hxy
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp h
  have hz := F.coreExternal_outside P r j
  have ha := (F.coreExternal_endpoints P r j).1
  have hb := (F.coreExternal_endpoints P r j).2
  rcases hj with he|he <;> rcases Sym2.eq_iff.mp he with ⟨hx,hy⟩|⟨hx,hy⟩
  · exact Or.inr ⟨hx.symm ▸ hz,hy.symm ▸ ha⟩
  · exact Or.inl ⟨hx.symm ▸ ha,hy.symm ▸ hz⟩
  · exact Or.inr ⟨hx.symm ▸ hz,hy.symm ▸ hb⟩
  · exact Or.inl ⟨hx.symm ▸ hb,hy.symm ▸ hz⟩

/-- The high-center graph has the required core-degree bound even at core
vertices which were not active in any batch: their degree here is zero. -/
theorem coreExternal_core_degree (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t)
    (r : L.FoldCoreIndex i) (v : V) (hv : v∈(L.foldCorePiece i r).vertices) :
    ((F.coreExternalPairs P r).graph.degree v:ℝ) ≤
      routingAllowance (logScale (originalLog V) L.stopIndex i) := by
  let E := F.coreExternalPairs P r
  by_cases hg : v∈F.activeVertices r.1
  · have hh : (E.graph.degree v:ℝ) ≤ (L.foldDescendantGraph i r.1).degree v := by
      exact_mod_cast E.graph.degree_le_of_le E.graph_le (v:=v)
    exact hh.trans (F.activeVertices_good r.1 hg)
  · have hIso : E.graph.IsIsolated v := by
      intro u hu
      have hs := (E.graph_adj v u).mp hu
      obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hs
      have hz := F.coreExternal_outside P r j
      have hl := (F.coreExternal_good P r j).1
      have hr := (F.coreExternal_good P r j).2
      have hvm : v∈s(v,u) := Sym2.mem_mk_left v u
      rcases hj with he|he
      · have he' : v∈s(E.center j,E.left j) := he ▸ hvm
        rcases Sym2.mem_iff.mp he' with hh|hh
        · exact hz (hh ▸ hv)
        · exact hg (hh.symm ▸ hl)
      · have he' : v∈s(E.center j,E.right j) := he ▸ hvm
        rcases Sym2.mem_iff.mp he' with hh|hh
        · exact hz (hh ▸ hv)
        · exact hg (hh.symm ▸ hr)
    rw [hIso.degree_eq_zero,Nat.cast_zero]
    exact (routingAllowance_pos _).le

theorem coreExternal_even (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t)
    (r : L.FoldCoreIndex i) (v : V) (hv : v∉(L.foldCorePiece i r).vertices) :
    Even ((F.coreExternalPairs P r).graph.degree v) :=
  (F.coreExternalPairs P r).exterior_even (L.foldCorePiece i r).vertices
    (fun j => (F.coreExternal_endpoints P r j).1) (fun j => (F.coreExternal_endpoints P r j).2) v hv

def coreCenterThreshold (F : ActualFoldStage12 L i) (r : L.FoldCoreIndex i) : ℝ :=
  ⌈sqrt (2*routingAllowance (logScale (originalLog V) L.stopIndex i)*(L.foldCorePiece i r).vertices.card)⌉₊

theorem coreCenterThreshold_bounds (F : ActualFoldStage12 L i) (r : L.FoldCoreIndex i) :
    let x := sqrt (2*routingAllowance (logScale (originalLog V) L.stopIndex i)*(L.foldCorePiece i r).vertices.card)
    x ≤ F.coreCenterThreshold r ∧ F.coreCenterThreshold r ≤ x+1 := by
  exact ⟨Nat.le_ceil _,(Nat.ceil_lt_add_one (sqrt_nonneg _)).le⟩

/-- The actual low families have palettes paid by 2a+d/2, after paths
were aggregated across all batches of the selected core. -/
theorem core_low_coloring (F : ActualFoldStage12 L i) (hi : i ≤ L.stopIndex)
    (P : ∀ t,F.BatchPreparation t) (r : L.FoldCoreIndex i) :
    let E := F.coreExternalPairs P r
    let d := F.coreCenterThreshold r
    let a := routingAllowance (logScale (originalLog V) L.stopIndex i)
    Nonempty ((lowPathConflict (E.low d).left (E.low d).right (E.low d).center).Coloring
      (Fin (2*⌊a⌋₊+⌊d/2⌋₊))) := by
  dsimp only
  have hw := logScale_active L.initial_log_pos.le L.phase_lower hi
  have hw0 : 0 ≤ logScale (originalLog V) L.stopIndex i :=
    (by norm_num [wA] : (0:ℝ) ≤ wA).trans hw
  have ha : 1 ≤ routingAllowance (logScale (originalLog V) L.stopIndex i) := by
    unfold routingAllowance
    exact one_le_rpow (by norm_num) (mul_nonneg (by norm_num [alpha]) hw0)
  apply (F.coreExternalPairs P r).low_coloring (F.activeVertices r.1) ha
    (show 0 ≤ F.coreCenterThreshold r from Nat.cast_nonneg _)
    (fun j => (F.coreExternal_good P r j).1) (fun j => (F.coreExternal_good P r j).2)
  exact fun _ hv => F.activeVertices_good r.1 hv

end ActualFoldStage12
end
end Cycle12.Even12
