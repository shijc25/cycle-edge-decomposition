import Cycle12.OwnedTwoEdgeFamily12
import Cycle12.PreparedBlockClasses12

namespace Cycle12
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

/-- The constructive data behind a prepared class, including the exact
pairings already used to produce its retained graph. -/
inductive PreparedClassLedger12 (G : SimpleGraph V) (A : I → Finset V) (Q : ℕ)
    (e : Sym2 (Option I)) (H : SimpleGraph V) : Type
  | internal (i : I) (label : e=s(some i,some i)) (retained : H=⊥)
  | external (label : e=s(none,none)) (retained : H=edgeLabelGraph G (blockLabel A) e)
  | outside (i : I) (label : e=s(some i,none))
      (data : OutsideLedger12 (edgeLabelGraph G (blockLabel A) e) (A i))
      (retained : H=data.pairs.residue)
  | crossing (i j : I) (distinct : i ≠ j) (label : e=s(some i,some j))
      (data : CrossingLedger12 (edgeLabelGraph G (blockLabel A) e) (A i) (A j) Q)
      (retained : H=matchingRetainedGraph data.second.residue data.matching)

variable {G : SimpleGraph V} {A : I → Finset V} {Q : ℕ} {e : Sym2 (Option I)} {H : SimpleGraph V}

theorem PreparedBlockClass12.ledger_exists (P : PreparedBlockClass12 G A Q e) :
    Nonempty (PreparedClassLedger12 G A Q e P.retained) := by
  rcases P.origin with ⟨i,he,hh⟩|⟨he,hh⟩|⟨i,he,D,hh⟩|⟨i,j,hij,he,D,hh⟩
  · exact ⟨.internal i he hh⟩
  · exact ⟨.external he hh⟩
  · exact ⟨.outside i he D hh⟩
  · exact ⟨.crossing i j hij he D hh⟩

def PreparedBlockClass12.ledger (P : PreparedBlockClass12 G A Q e) :
    PreparedClassLedger12 G A Q e P.retained := Classical.choice P.ledger_exists

namespace PreparedClassLedger12

def pairs (D : PreparedClassLedger12 G A Q e H) :
    OwnedTwoEdgeFamily12 (edgeLabelGraph G (blockLabel A) e) A :=
  match D with
  | .internal _ _ _ => .empty _ _
  | .external _ _ => .empty _ _
  | .outside r _ P _ => OwnedTwoEdgeFamily12.ofPairing P.pairs le_rfl r
      (fun j => ⟨j.2.val.out.1.property.1,j.2.val.out.2.property.1⟩)
  | .crossing r t _ _ P _ =>
      (OwnedTwoEdgeFamily12.ofPairing P.first le_rfl r P.first_endpoints).sum
        (OwnedTwoEdgeFamily12.ofPairing P.second (fun _ _ h => h.1) t P.second_endpoints)
        (by simpa only [OwnedTwoEdgeFamily12.ofPairing_used] using P.first_second)

def internalEdges (D : PreparedClassLedger12 G A Q e H) : Set (Sym2 V) :=
  match D with
  | .internal _ _ _ => (edgeLabelGraph G (blockLabel A) e).edgeSet
  | _ => ∅

def matchingEdges (D : PreparedClassLedger12 G A Q e H) : Set (Sym2 V) :=
  match D with
  | .crossing _ _ _ _ P _ => ⋃ t,matchingOriginalGroup P.second.residue P.matching Q t
  | _ => ∅

theorem internal_subset (D : PreparedClassLedger12 G A Q e H) :
    D.internalEdges⊆(edgeLabelGraph G (blockLabel A) e).edgeSet := by
  cases D <;> simp only [internalEdges,Set.empty_subset,subset_refl]

theorem matching_subset (D : PreparedClassLedger12 G A Q e H) :
    D.matchingEdges⊆(edgeLabelGraph G (blockLabel A) e).edgeSet := by
  cases D with
  | crossing r t hrt he P hh =>
    intro f hf
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hf
    exact edgeSet_mono (show P.second.residue ≤ edgeLabelGraph G (blockLabel A) e from
      fun _ _ h => h.1.1) (originalEdgeSet_subset P.second.residue _ hj)
  | _ => exact Set.empty_subset _

/-- Exact original-edge cover, before any path routing or completion. -/
theorem cover (D : PreparedClassLedger12 G A Q e H) :
    D.internalEdges∪D.pairs.used∪D.matchingEdges∪H.edgeSet=
      (edgeLabelGraph G (blockLabel A) e).edgeSet := by
  cases D with
  | internal r he hh => simp [internalEdges,pairs,matchingEdges,hh]
  | external he hh => simp [internalEdges,pairs,matchingEdges,hh]
  | outside r he P hh =>
    simpa only [internalEdges,pairs,matchingEdges,OwnedTwoEdgeFamily12.ofPairing_used,
      Set.empty_union,Set.union_empty,hh] using P.cover
  | crossing r t hrt he P hh =>
    simpa only [internalEdges,pairs,matchingEdges,OwnedTwoEdgeFamily12.sum_used,
      OwnedTwoEdgeFamily12.ofPairing_used,Set.empty_union,hh] using P.cover

theorem pairs_matching (D : PreparedClassLedger12 G A Q e H) :
    Disjoint D.pairs.used D.matchingEdges := by
  cases D with
  | crossing r t hrt he P hh =>
    simp only [pairs,matchingEdges,OwnedTwoEdgeFamily12.sum_used,OwnedTwoEdgeFamily12.ofPairing_used,
      Set.disjoint_union_left,Set.disjoint_iUnion_right]
    exact fun t => ⟨P.first_groups t,P.second_groups t⟩
  | _ => simp [pairs,matchingEdges]

theorem pairs_retained (D : PreparedClassLedger12 G A Q e H) : Disjoint D.pairs.used H.edgeSet := by
  cases D with
  | internal r he hh => simp [pairs]
  | external he hh => simp [pairs]
  | outside r he P hh => simpa only [pairs,OwnedTwoEdgeFamily12.ofPairing_used,hh] using P.disjoint
  | crossing r t hrt he P hh =>
    simpa only [pairs,OwnedTwoEdgeFamily12.sum_used,OwnedTwoEdgeFamily12.ofPairing_used,
      Set.disjoint_union_left,hh] using And.intro P.first_retained P.second_retained

theorem matching_retained (D : PreparedClassLedger12 G A Q e H) :
    Disjoint D.matchingEdges H.edgeSet := by
  cases D with
  | crossing r t hrt he P hh =>
    simpa only [matchingEdges,hh,Set.disjoint_iUnion_left] using P.groups_retained
  | _ => simp [matchingEdges]

theorem internal_disjoint (D : PreparedClassLedger12 G A Q e H) :
    Disjoint D.internalEdges (D.pairs.used∪D.matchingEdges∪H.edgeSet) := by
  cases D with
  | internal r he hh => simp [internalEdges,pairs,matchingEdges,hh]
  | _ => simp [internalEdges]

/-- Every edge set assigned directly to completion lies inside one
actual active block, hence inside its assigned core. -/
theorem internal_owner (D : PreparedClassLedger12 G A Q e H)
    (hd : Pairwise (fun r t => Disjoint (A r) (A t))) :
    D.internalEdges=∅ ∨ ∃ r : I,∀ {x y},s(x,y)∈D.internalEdges → x∈A r ∧ y∈A r := by
  cases D with
  | internal r he hh =>
    right
    refine ⟨r,?_⟩
    intro x y hxy
    change (edgeLabelGraph G (blockLabel A) e).Adj x y at hxy
    rw [he,block_internal_graph G A hd r] at hxy
    exact ⟨hxy.2.1,hxy.2.2⟩
  | _ => exact Or.inl rfl

end PreparedClassLedger12
end
end Cycle12
