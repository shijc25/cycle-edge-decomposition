import Cycle12.ActualCoreBanks12

namespace Cycle12.Even12
open Cycle12.Global12 Cycle13 SimpleGraph Finset Real
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

namespace ActualFoldStage12
variable {G : SimpleGraph V} {L : EvenScaleLayers12 G} {i : ℕ}

def activeVertices (F : ActualFoldStage12 L i) (z : L.FoldBoxIndex i) : Finset V :=
  univ.biUnion (fun t => univ.biUnion ((F.active z).vertices t))

theorem activeVertices_good (F : ActualFoldStage12 L i) (z : L.FoldBoxIndex i)
    {v : V} (hv : v∈F.activeVertices z) :
    ((L.foldDescendantGraph i z).degree v:ℝ) ≤ routingAllowance (logScale (originalLog V) L.stopIndex i) := by
  obtain ⟨t,_,ht⟩ := mem_biUnion.mp hv
  obtain ⟨j,_,hj⟩ := mem_biUnion.mp ht
  exact (F.active z).degree_le t j v hj

/-- Use the actual stage's good vertices and the actual selected core's
prepared routing bank in the single combined routing call. -/
theorem route_actual_core {R T : Type} [Fintype R] [Fintype T] [DecidableEq R]
    (F : ActualFoldStage12 L i) (hi : i ≤ L.stopIndex) (r : L.FoldCoreIndex i)
    (B : AssignedCoreBanks12 (L.foldCorePiece i r) (logScale (originalLog V) L.stopIndex i))
    (a b : R → (L.foldCorePiece i r).vertices) (team : R → T)
    (hard : R → Finset (L.foldCorePiece i r).vertices)
    (weight : R → (L.foldCorePiece i r).vertices → ℝ)
    (S : Set (Sym2 V))
    (cert : OriginalEndpointCertificate (L.foldDescendantGraph i r.1)
      (fun j => (a j).val) (fun j => (b j).val) S)
    (hgood : ∀ k : R × Bool,(if k.2 then b k.1 else a k.1).val∈F.activeVertices r.1)
    (hteam : ∀ t,teamLoad team t ≤ routingTeamSize (logScale (originalLog V) L.stopIndex i))
    (hhard : ∀ j,(hard j).card ≤ 2*routingTeamSize (logScale (originalLog V) L.stopIndex i))
    (hweight : ∀ j v,0 ≤ weight j v) :
    let H := splitBank ((L.foldCorePiece i r).graph.induce ((L.foldCorePiece i r).vertices:Set V)) B.coloring true
    ∃ p : ∀ j,H.Walk (a j) (b j),
      (∀ j,(p j).IsPath ∧ (p j).length ≤
        globalRoutingLength (Fintype.card (L.foldCorePiece i r).vertices) (logScale (originalLog V) L.stopIndex i) ∧
        Disjoint (routeInterior (p j)) (hard j) ∧
        (∑ v∈routeInterior (p j),weight j v) ≤
          (gamma/(routingTeamSize (logScale (originalLog V) L.stopIndex i):ℝ))*∑ v,weight j v) ∧
      (∀ j k,j ≠ k → Disjoint (p j).edges.toFinset (p k).edges.toFinset) ∧
      (∀ j k,j ≠ k → team j=team k → Disjoint (routeInterior (p j)) (routeInterior (p k))) := by
  dsimp only
  have hd := L.fold_core_local_data hi r
  let core := (L.foldCorePiece i r).graph.induce ((L.foldCorePiece i r).vertices:Set V)
  let H := splitBank core B.coloring true
  have hH : CutExpands H (routingExpansion (logScale (originalLog V) L.stopIndex i)) := by
    apply (cutExpands_iff_legacy _ _).mpr
    convert B.routing using 1
    rfl
  have hh := certificate_routing_at_scale (L.foldDescendantGraph i r.1) core H
    (Function.Embedding.subtype _) (logScale_active L.initial_log_pos.le L.phase_lower hi)
    hd.1 hd.2.1 (by convert hd.2.2 using 1) hH a b team hard weight S cert
    (fun k => F.activeVertices_good r.1 (hgood k)) hteam hhard hweight
  convert hh using 1
  congr!

end ActualFoldStage12
end
end Cycle12.Even12
