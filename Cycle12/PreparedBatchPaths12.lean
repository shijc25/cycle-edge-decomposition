import Cycle12.PreparedClassPaths12

namespace Cycle12
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

/-- Local disjointness inside disjoint original classes survives union. -/
theorem disjoint_classwise_unions {X J : Type} (E S T : J → Set X)
    (hd : Pairwise (fun j k => Disjoint (E j) (E k)))
    (hS : ∀ j,S j⊆E j) (hT : ∀ j,T j⊆E j)
    (hlocal : ∀ j,Disjoint (S j) (T j)) : Disjoint (⋃ j,S j) (⋃ j,T j) := by
  apply Set.disjoint_left.mpr
  intro e he hf
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp he
  obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hf
  by_cases hjk : j=k
  · subst k
    exact Set.disjoint_left.mp (hlocal j) hj hk
  · exact Set.disjoint_left.mp (hd hjk) (hS j hj) (hT k hk)

namespace PreparedBlockBatch12
variable {G : SimpleGraph V} {A : I → Finset V} {Q : ℕ}

def classPairs (P : PreparedBlockBatch12 G A Q) (e : Sym2 (Option I)) :
    OwnedTwoEdgeFamily12 G A := (P.classes e).ledger.pairs.enlarge (fun _ _ h => h.1)

theorem classPairs_subset (P : PreparedBlockBatch12 G A Q) (e : Sym2 (Option I)) :
    (P.classPairs e).used⊆(edgeLabelGraph G (blockLabel A) e).edgeSet :=
  (P.classes e).ledger.pairs.used_subset

theorem classPairs_disjoint (P : PreparedBlockBatch12 G A Q) :
    Pairwise (fun e f => Disjoint (P.classPairs e).used (P.classPairs f).used) := by
  intro e f hef
  exact ((edgeLabelGraph_partition G (blockLabel A)).1 hef).mono (P.classPairs_subset e) (P.classPairs_subset f)

def pairs (P : PreparedBlockBatch12 G A Q) : OwnedTwoEdgeFamily12 G A :=
  OwnedTwoEdgeFamily12.sigma P.classPairs P.classPairs_disjoint

theorem pairs_used (P : PreparedBlockBatch12 G A Q) :
    P.pairs.used=⋃ e,(P.classes e).ledger.pairs.used := by
  simp only [pairs,OwnedTwoEdgeFamily12.sigma_used,classPairs,OwnedTwoEdgeFamily12.enlarge_used]

def internalEdges (P : PreparedBlockBatch12 G A Q) : Set (Sym2 V) :=
  ⋃ e,(P.classes e).ledger.internalEdges

def matchingEdges (P : PreparedBlockBatch12 G A Q) : Set (Sym2 V) :=
  ⋃ e,(P.classes e).ledger.matchingEdges

theorem retained_edges (P : PreparedBlockBatch12 G A Q) :
    P.retained.edgeSet=⋃ e,(P.classes e).retained.edgeSet := by
  ext d
  induction d using Sym2.inductionOn with
  | _ x y => simp only [Set.mem_iUnion,SimpleGraph.mem_edgeSet,retained,iSup_adj]

theorem original_cover (P : PreparedBlockBatch12 G A Q) :
    P.internalEdges∪P.pairs.used∪P.matchingEdges∪P.retained.edgeSet=G.edgeSet := by
  rw [internalEdges,P.pairs_used,matchingEdges,P.retained_edges,
    ←Set.iUnion_union_distrib,←Set.iUnion_union_distrib,←Set.iUnion_union_distrib]
  simp_rw [PreparedClassLedger12.cover]
  exact (edgeLabelGraph_partition G (blockLabel A)).2

theorem pairs_matching (P : PreparedBlockBatch12 G A Q) : Disjoint P.pairs.used P.matchingEdges := by
  rw [P.pairs_used]
  exact disjoint_classwise_unions _ _ _ (edgeLabelGraph_partition G (blockLabel A)).1
    (fun e => (P.classes e).ledger.pairs.used_subset)
    (fun e => (P.classes e).ledger.matching_subset)
    (fun e => (P.classes e).ledger.pairs_matching)

theorem pairs_retained (P : PreparedBlockBatch12 G A Q) : Disjoint P.pairs.used P.retained.edgeSet := by
  rw [P.pairs_used,P.retained_edges]
  exact disjoint_classwise_unions _ _ _ (edgeLabelGraph_partition G (blockLabel A)).1
    (fun e => (P.classes e).ledger.pairs.used_subset)
    (fun e => edgeSet_mono (P.classes e).subset)
    (fun e => (P.classes e).ledger.pairs_retained)

theorem matching_retained (P : PreparedBlockBatch12 G A Q) :
    Disjoint P.matchingEdges P.retained.edgeSet := by
  rw [P.retained_edges]
  exact disjoint_classwise_unions _ _ _ (edgeLabelGraph_partition G (blockLabel A)).1
    (fun e => (P.classes e).ledger.matching_subset)
    (fun e => edgeSet_mono (P.classes e).subset)
    (fun e => (P.classes e).ledger.matching_retained)

theorem internal_disjoint (P : PreparedBlockBatch12 G A Q) :
    Disjoint P.internalEdges (P.pairs.used∪P.matchingEdges∪P.retained.edgeSet) := by
  rw [P.pairs_used,matchingEdges,P.retained_edges,←Set.iUnion_union_distrib,←Set.iUnion_union_distrib]
  apply disjoint_classwise_unions _ _ _ (edgeLabelGraph_partition G (blockLabel A)).1
    (fun e => (P.classes e).ledger.internal_subset)
  · intro e
    exact Set.union_subset (Set.union_subset (P.classes e).ledger.pairs.used_subset
      (P.classes e).ledger.matching_subset) (edgeSet_mono (P.classes e).subset)
  · exact fun e => (P.classes e).ledger.internal_disjoint

end PreparedBlockBatch12
end
end Cycle12
