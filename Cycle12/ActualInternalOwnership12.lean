import Cycle12.ActualBoxRoutes12

namespace Cycle12.PreparedBlockBatch12
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]
  {G : SimpleGraph V} {A : I → Finset V} {Q : ℕ}

theorem internalEdges_subset (P : PreparedBlockBatch12 G A Q) : P.internalEdges⊆G.edgeSet := by
  intro e he
  obtain ⟨label,hl⟩ := Set.mem_iUnion.mp he
  exact edgeSet_mono (show edgeLabelGraph G (blockLabel A) label≤G from fun {_ _} h => h.1)
    ((P.classes label).ledger.internal_subset hl)

theorem internalEdges_owner (P : PreparedBlockBatch12 G A Q)
    (hd : Pairwise (fun r t => Disjoint (A r) (A t))) {x y : V}
    (hxy : s(x,y)∈P.internalEdges) : ∃ r,x∈A r ∧ y∈A r := by
  obtain ⟨label,hl⟩ := Set.mem_iUnion.mp hxy
  rcases (P.classes label).ledger.internal_owner hd with he|⟨r,hr⟩
  · rw [he] at hl
    exact False.elim hl
  · exact ⟨r,hr hl⟩

end
end Cycle12.PreparedBlockBatch12

namespace Cycle12.Even12
open Cycle12.Global12 Cycle13 SimpleGraph Finset Real
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]
namespace ActualFoldStage12
variable {G : SimpleGraph V} {L : EvenScaleLayers12 G} {i : ℕ}
variable (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t)

def ambientInternalEdges (t : F.BatchIndex) : Set (Sym2 V) :=
  Sym2.map (Function.Embedding.subtype _ : F.batchVertices t ↪ V) '' (P t).internalEdges

theorem ambientInternal_subset (t : F.BatchIndex) : F.ambientInternalEdges P t⊆(F.batchGraph t).edgeSet := by
  rintro _ ⟨e,he,rfl⟩
  have hh := (P t).internalEdges_subset he
  induction e using Sym2.ind with
  | _ x y => exact hh

theorem ambientInternal_owner (t : F.BatchIndex) {x y : V}
    (hxy : s(x,y)∈F.ambientInternalEdges P t) :
    ∃ r : Fin (L.foldCores i t.1).length,
      x∈((L.foldCores i t.1).get r).vertices ∧ y∈((L.foldCores i t.1).get r).vertices := by
  obtain ⟨e,he,hmap⟩ := hxy
  induction e using Sym2.ind with
  | _ u v =>
    obtain ⟨r,hu,hv⟩ := (P t).internalEdges_owner (F.batchActive_disjoint t) he
    have hu' := (F.active t.1).subset_router t.2 r ((mem_verticesWithin _ _ u).mp hu)
    have hv' := (F.active t.1).subset_router t.2 r ((mem_verticesWithin _ _ v).mp hv)
    refine ⟨(F.active t.1).router t.2 r,?_⟩
    rcases Sym2.eq_iff.mp hmap with ⟨hx,hy⟩|⟨hx,hy⟩
    · exact ⟨hx ▸ hu',hy ▸ hv'⟩
    · exact ⟨hy ▸ hv',hx ▸ hu'⟩

def boxInternalEdges (z : L.FoldBoxIndex i) : Set (Sym2 V) := ⋃ t,F.ambientInternalEdges P ⟨z,t⟩

theorem boxInternal_subset (z : L.FoldBoxIndex i) :
    F.boxInternalEdges P z⊆(L.foldDescendantGraph i z).edgeSet := by
  intro e he
  obtain ⟨t,ht⟩ := Set.mem_iUnion.mp he
  exact edgeSet_mono ((F.batches z).graph_le t) (F.ambientInternal_subset P ⟨z,t⟩ ht)

theorem boxInternal_owner (z : L.FoldBoxIndex i) {x y : V}
    (hxy : s(x,y)∈F.boxInternalEdges P z) :
    ∃ r : Fin (L.foldCores i z).length,
      x∈((L.foldCores i z).get r).vertices ∧ y∈((L.foldCores i z).get r).vertices := by
  obtain ⟨t,ht⟩ := Set.mem_iUnion.mp hxy
  exact F.ambientInternal_owner P ⟨z,t⟩ ht

def coreInternalEdges (r : L.FoldCoreIndex i) : Set (Sym2 V) :=
  F.boxInternalEdges P r.1∩{e | ∀ v∈e,v∈(L.foldCorePiece i r).vertices}

def coreInternalGraph (r : L.FoldCoreIndex i) : SimpleGraph V := fromEdgeSet (F.coreInternalEdges P r)

theorem coreInternalGraph_edges (r : L.FoldCoreIndex i) :
    (F.coreInternalGraph P r).edgeSet=F.coreInternalEdges P r := by
  rw [coreInternalGraph,edgeSet_fromEdgeSet]
  apply Set.Subset.antisymm Set.sdiff_subset
  intro e he
  exact ⟨he,(L.foldDescendantGraph i r.1).edgeSet_subset_compl_diagSet
    (F.boxInternal_subset P r.1 he.1)⟩

theorem coreInternal_supported (r : L.FoldCoreIndex i) :
    SupportedOn (F.coreInternalGraph P r) (L.foldCorePiece i r).vertices := by
  intro x y hxy
  have hh : s(x,y)∈F.coreInternalEdges P r := by
    rw [←F.coreInternalGraph_edges P r]
    exact hxy
  exact ⟨hh.2 x (Sym2.mem_mk_left _ _),hh.2 y (Sym2.mem_mk_right _ _)⟩

/-- Every original internal edge is assigned to an actual selected core.
The assignment concerns original edges, not artificial quotient loops. -/
theorem coreInternal_cover (z : L.FoldBoxIndex i) :
    (⋃ r : Fin (L.foldCores i z).length,F.coreInternalEdges P ⟨z,r⟩)=F.boxInternalEdges P z := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset (fun _ => Set.inter_subset_left)
  · intro e he
    induction e using Sym2.ind with
    | _ x y =>
      obtain ⟨r,hx,hy⟩ := F.boxInternal_owner P z he
      refine Set.mem_iUnion.mpr ⟨r,he,?_⟩
      intro v hv
      rcases Sym2.mem_iff.mp hv with h|h
      · exact h.symm ▸ hx
      · exact h.symm ▸ hy

theorem coreInternal_disjoint (hi : i≤L.stopIndex) :
    Pairwise (fun r t : L.FoldCoreIndex i => Disjoint (F.coreInternalEdges P r) (F.coreInternalEdges P t)) := by
  intro r t hrt
  by_cases h : r.1=t.1
  · rcases r with ⟨z,r⟩
    rcases t with ⟨y,t⟩
    dsimp only at h
    subst y
    have hne : r≠t := by intro he; subst t; exact hrt rfl
    apply Set.disjoint_left.mpr
    intro e he hf
    induction e using Sym2.ind with
    | _ x y =>
      exact Finset.disjoint_left.mp (L.fold_core_vertices_disjoint hi z hne)
        (he.2 x (Sym2.mem_mk_left _ _)) (hf.2 x (Sym2.mem_mk_left _ _))
  · exact (L.fold_descendants_disjoint i h).mono
      (Set.inter_subset_left.trans (F.boxInternal_subset P r.1))
      (Set.inter_subset_left.trans (F.boxInternal_subset P t.1))

end ActualFoldStage12
end
end Cycle12.Even12
