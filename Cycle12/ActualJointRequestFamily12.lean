import Cycle12.ActualMatchingFamily12
import Cycle12.OwnedLowPathRequests12

namespace Cycle12.OwnedEndpointFamily12
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {A : I → Finset V} {S T : Set (Sym2 V)}

def sum (P : OwnedEndpointFamily12 G A S) (Q : OwnedEndpointFamily12 G A T)
    (hd : Disjoint S T) : OwnedEndpointFamily12 G A (S∪T) where
  Index := P.Index ⊕ Q.Index
  finite := inferInstance
  owner := Sum.elim P.owner Q.owner
  left := Sum.elim P.left Q.left
  right := Sum.elim P.right Q.right
  left_mem := by
    intro j
    cases j with
    | inl j => exact P.left_mem j
    | inr j => exact Q.left_mem j
  right_mem := by
    intro j
    cases j with
    | inl j => exact P.right_mem j
    | inr j => exact Q.right_mem j
  certificate := P.certificate.sum Q.certificate hd

/-- Permute the incoming endpoints within their actual owner cores.
The same original incidence, rather than a virtual edge, pays each port. -/
def reconnectPairs (P : OwnedTwoEdgeFamily12 G A) (next : Equiv.Perm P.Index)
    (hn : ∀ j,P.owner (next j)=P.owner j) : OwnedEndpointFamily12 G A P.used where
  Index := P.Index
  finite := P.finite
  owner := P.owner
  left := P.right
  right := fun j => P.left (next j)
  left_mem := P.right_mem
  right_mem := fun j => by simpa only [hn j] using P.left_mem (next j)
  certificate := Classical.choice (P.reconnection_certificate_exists next)

end
end Cycle12.OwnedEndpointFamily12

namespace Cycle12.Even12
open Cycle12.Global12 Cycle13 SimpleGraph Finset
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]
namespace ActualFoldStage12
variable {G : SimpleGraph V} {L : EvenScaleLayers12 G} {i : ℕ}
variable (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t)
  (Q : ∀ t,F.AmbientQuotientPacking P t) (D : ∀ t,F.AmbientOutlineData P Q t)

def ambientQuotientEdges (t : F.BatchIndex) : Set (Sym2 V) := ⋃ j,((D t).outline j).edges

def ambientQuotientFamily (t : F.BatchIndex) : OwnedEndpointFamily12
    (L.foldDescendantGraph i t.1)
    (fun r : Fin (L.foldCores i t.1).length => ((L.foldCores i t.1).get r).vertices)
    (F.ambientQuotientEdges P Q D t) where
  Index := (D t).RequestIndex
  finite := inferInstance
  owner := fun j => F.quotientSwitchCore (D t) j.1 j.2
  left := fun j => ((D t).outline j.1).start j.2
  right := fun j => ((D t).outline j.1).finish j.2
  left_mem := fun j => (F.quotientSwitch_endpoints (D t) j.1 j.2).1
  right_mem := fun j => (F.quotientSwitch_endpoints (D t) j.1 j.2).2.1
  certificate := F.quotient_certificate (D t)

theorem ambientQuotient_retained (t : F.BatchIndex) :
    F.ambientQuotientEdges P Q D t⊆(F.ambientBatchRetained P t).edgeSet := by
  intro e he
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp he
  exact (D t).outline_subset (F.ambient_quotient_unique P t) j hj

theorem ambientQuotient_subset (t : F.BatchIndex) :
    F.ambientQuotientEdges P Q D t⊆(F.batchGraph t).edgeSet :=
  (F.ambientQuotient_retained P Q D t).trans (edgeSet_mono (F.ambient_retained_le P t))

def boxQuotientEdges (z : L.FoldBoxIndex i) : Set (Sym2 V) :=
  ⋃ t,F.ambientQuotientEdges P Q D ⟨z,t⟩

theorem ambientQuotient_disjoint (z : L.FoldBoxIndex i) : Pairwise (fun t u =>
    Disjoint (F.ambientQuotientEdges P Q D ⟨z,t⟩) (F.ambientQuotientEdges P Q D ⟨z,u⟩)) := by
  intro t u htu
  exact ((F.batches z).disjoint htu).mono (F.ambientQuotient_subset P Q D ⟨z,t⟩)
    (F.ambientQuotient_subset P Q D ⟨z,u⟩)

def boxQuotientFamily (z : L.FoldBoxIndex i) : OwnedEndpointFamily12 (L.foldDescendantGraph i z)
    (fun r : Fin (L.foldCores i z).length => ((L.foldCores i z).get r).vertices)
    (F.boxQuotientEdges P Q D z) :=
  OwnedEndpointFamily12.sigma (fun t => F.ambientQuotientFamily P Q D ⟨z,t⟩)
    (F.ambientQuotient_disjoint P Q D z)

theorem boxQuotient_good (z : L.FoldBoxIndex i) (j : (F.boxQuotientFamily P Q D z).Index) :
    (F.boxQuotientFamily P Q D z).left j∈F.activeVertices z ∧
      (F.boxQuotientFamily P Q D z).right j∈F.activeVertices z :=
  (F.quotientSwitch_endpoints (D ⟨z,j.1⟩) j.2.1 j.2.2).2.2

theorem box_pairs_quotient (z : L.FoldBoxIndex i) :
    Disjoint (F.boxPairs P z).used (F.boxQuotientEdges P Q D z) := by
  rw [boxPairs,OwnedTwoEdgeFamily12.sigma_used,boxQuotientEdges]
  apply disjoint_classwise_unions (fun t => (F.batchGraph ⟨z,t⟩).edgeSet) _ _
    (F.batches z).disjoint (fun t => F.ambientBatchPairs_used_subset P ⟨z,t⟩)
    (fun t => F.ambientQuotient_subset P Q D ⟨z,t⟩)
  intro t
  exact (F.ambient_pairs_retained P ⟨z,t⟩).mono subset_rfl (F.ambientQuotient_retained P Q D ⟨z,t⟩)

theorem box_matching_quotient (z : L.FoldBoxIndex i) :
    Disjoint (F.boxMatchingEdges P z) (F.boxQuotientEdges P Q D z) := by
  rw [boxMatchingEdges,boxQuotientEdges]
  apply disjoint_classwise_unions (fun t => (F.batchGraph ⟨z,t⟩).edgeSet) _ _
    (F.batches z).disjoint (fun t => F.ambientMatching_subset P ⟨z,t⟩)
    (fun t => F.ambientQuotient_subset P Q D ⟨z,t⟩)
  intro t
  exact (F.ambient_matching_retained P ⟨z,t⟩).mono subset_rfl (F.ambientQuotient_retained P Q D ⟨z,t⟩)

/-- A parent-wide incidence envelope for all three actual origins.
Path subfamilies can later be restricted without increasing this joint load. -/
def jointFamily (z : L.FoldBoxIndex i) (next : Equiv.Perm (F.boxPairs P z).Index)
    (hn : ∀ j,(F.boxPairs P z).owner (next j)=(F.boxPairs P z).owner j) :
    OwnedEndpointFamily12 (L.foldDescendantGraph i z)
      (fun r : Fin (L.foldCores i z).length => ((L.foldCores i z).get r).vertices)
      ((F.boxPairs P z).used∪(F.boxMatchingEdges P z∪F.boxQuotientEdges P Q D z)) :=
  (OwnedEndpointFamily12.reconnectPairs (F.boxPairs P z) next hn).sum
    ((F.boxMatchingFamily P z).sum (F.boxQuotientFamily P Q D z) (F.box_matching_quotient P Q D z))
    (Set.disjoint_union_right.mpr ⟨F.box_pairs_matching P z,F.box_pairs_quotient P Q D z⟩)

theorem jointFamily_good (z : L.FoldBoxIndex i) (next : Equiv.Perm (F.boxPairs P z).Index)
    (hn : ∀ j,(F.boxPairs P z).owner (next j)=(F.boxPairs P z).owner j)
    (j : (F.jointFamily P Q D z next hn).Index) :
    (F.jointFamily P Q D z next hn).left j∈F.activeVertices z ∧
      (F.jointFamily P Q D z next hn).right j∈F.activeVertices z := by
  cases j with
  | inl j => exact ⟨(F.boxPairs_good P z j).2,(F.boxPairs_good P z (next j)).1⟩
  | inr j =>
    cases j with
    | inl j => exact F.boxMatching_good P z j
    | inr j => exact F.boxQuotient_good P Q D z j

/-- The three origins share one degree allowance; their separate degree
upper bounds are never added. -/
theorem jointFamily_endpoint_load (z : L.FoldBoxIndex i)
    (next : Equiv.Perm (F.boxPairs P z).Index)
    (hn : ∀ j,(F.boxPairs P z).owner (next j)=(F.boxPairs P z).owner j)
    (v : V) (hv : v∈F.activeVertices z) :
    (endpointLoad (F.jointFamily P Q D z next hn).left
      (F.jointFamily P Q D z next hn).right v:ℝ) ≤
        routingAllowance (logScale (originalLog V) L.stopIndex i) := by
  have hh : (endpointLoad (F.jointFamily P Q D z next hn).left
      (F.jointFamily P Q D z next hn).right v:ℝ) ≤ (L.foldDescendantGraph i z).degree v := by
    exact_mod_cast (F.jointFamily P Q D z next hn).load_le v
  exact hh.trans (F.activeVertices_good z hv)

end ActualFoldStage12
end
end Cycle12.Even12
