import Cycle12.PreparedCrossingLedger12

namespace Cycle12
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Retain both actual pairing passes and the actual even matching
groups, together with their complete original-edge ledger. -/
structure CrossingLedger12 (G : SimpleGraph V) (U T : Finset V) (Q : ℕ) where
  first : CenterPairings G U
  second : CenterPairings first.residue Uᶜ
  matching : (⊤ : SimpleGraph second.residue.edgeSet).Subgraph
  first_endpoints : ∀ e : first.Index,first.left e∈U ∧ first.right e∈U
  second_endpoints : ∀ e : second.Index,second.left e∈T ∧ second.right e∈T
  residue_degree : ∀ v,second.residue.degree v ≤ 1
  isMatching : matching.IsMatching
  retained_le : matchingRetainedGraph second.residue matching ≤ G
  retained_small : (matchingRetainedGraph second.residue matching).edgeSet.ncard ≤ 1
  first_second : Disjoint first.used second.used
  first_groups : ∀ t,Disjoint first.used (matchingOriginalGroup second.residue matching Q t)
  second_groups : ∀ t,Disjoint second.used (matchingOriginalGroup second.residue matching Q t)
  first_retained : Disjoint first.used (matchingRetainedGraph second.residue matching).edgeSet
  second_retained : Disjoint second.used (matchingRetainedGraph second.residue matching).edgeSet
  groups_retained : ∀ t,Disjoint (matchingOriginalGroup second.residue matching Q t)
    (matchingRetainedGraph second.residue matching).edgeSet
  groups_disjoint : Pairwise (fun t u => Disjoint (matchingOriginalGroup second.residue matching Q t)
    (matchingOriginalGroup second.residue matching Q u))
  cover : first.used∪second.used∪(⋃ t,matchingOriginalGroup second.residue matching Q t)∪
    (matchingRetainedGraph second.residue matching).edgeSet=G.edgeSet
  group_sizes : ∀ t,Even (matchingOriginalGroup second.residue matching Q t).ncard ∧
    (matchingOriginalGroup second.residue matching Q t).ncard ≤ 2*Q
  group_count : (Fintype.card (Fin (Fintype.card matching.edgeSet/Q+1)):ℝ) ≤
    (second.residue.edgeSet.ncard:ℝ)/(2*Q)+1

theorem crossingLedger_exists (G : SimpleGraph V) (U T : Finset V)
    (hUT : Disjoint U T)
    (hcross : ∀ {x y},G.Adj x y → (x∈U ∧ y∈T) ∨ (x∈T ∧ y∈U))
    {Q : ℕ} (hQ : 0 < Q) : Nonempty (CrossingLedger12 G U T Q) := by
  obtain ⟨P,S,M,hP,hS,hD,hM,hR,hsmall,hPS,hPG,hSG,hPR,hSR,hGR,hGG,hcover,hsizes,hcount⟩ :=
    prepare_crossing_with_groups G U T hUT hcross hQ
  exact ⟨⟨P,S,M,hP,hS,hD,hM,hR,hsmall,hPS,hPG,hSG,hPR,hSR,hGR,hGG,hcover,hsizes,hcount⟩⟩

structure OutsideLedger12 (G : SimpleGraph V) (U : Finset V) where
  pairs : CenterPairings G U
  degree : ∀ v,v∉U → pairs.residue.degree v ≤ 1
  disjoint : Disjoint pairs.used pairs.residue.edgeSet
  cover : pairs.used∪pairs.residue.edgeSet=G.edgeSet
  count : pairs.residue.edgeSet.ncard+2*Fintype.card pairs.Index=G.edgeSet.ncard

theorem outsideLedger_exists (G : SimpleGraph V) (U T : Finset V)
    (hUT : Disjoint U T)
    (hcross : ∀ {x y},G.Adj x y → (x∈U ∧ y∈T) ∨ (x∈T ∧ y∈U)) :
    Nonempty (OutsideLedger12 G U) := by
  obtain ⟨P,hd,hdisj,hcover,hcount⟩ := prepare_block_outside G U T hUT hcross
  exact ⟨⟨P,hd,hdisj,hcover,hcount⟩⟩

end
end Cycle12
