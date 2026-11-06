import Cycle12.TerminalInductiveTemplates

namespace Cycle12
open SimpleGraph Finset

def mixedPairBase : Finset (Sym2 (Fin 6)) :=
  {s(0,2),s(2,3),s(1,3),s(0,4),s(4,5),s(1,5)}

def mixedPairOptional : Fin 4 → Sym2 (Fin 6) := ![s(1,2),s(0,3),s(1,4),s(0,5)]

def mixedPairEdges (S : Finset (Fin 4)) : Finset (Sym2 (Fin 6)) :=
  mixedPairBase ∪ S.image mixedPairOptional

def mixedPairWords : Fin 1 → CycleWord (Fin 6) := ![⟨0,[2,3,1,5,4]⟩]

def mixedPairRemoved : Finset (Fin 6) := {2,3,4,5}

theorem mixed_pair_valid : ∀ S : Finset (Fin 4),
    TerminalCert.Valid (mixedPairEdges S) mixedPairWords := by decide +kernel

/-- Even the densest choice costs 134, within the budget 136. All sixteen
combinations, including mixtures of paths, triangle legs, and diamonds, pass. -/
theorem mixed_pair_budget : ∀ S : Finset (Fin 4),
    42*1+23*(mixedPairEdges S\TerminalCert.covered mixedPairWords).card ≤
      19*mixedPairRemoved.card+6*(mixedPairEdges S).card := by decide +kernel

theorem mixed_pair_incident : ∀ S : Finset (Fin 4), ∀ i j,
    (TerminalCert.graph (mixedPairEdges S)).Adj i j → i∈mixedPairRemoved ∨ j∈mixedPairRemoved := by
  decide +kernel

noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem terminal_induction_mixed_pair (G : SimpleGraph V) (ih : TerminalProperInduction G)
    (S : Finset (Fin 4)) (f : Fin 6 ↪ V)
    (hneighbors : ∀ i∈mixedPairRemoved, ∀ v,
      G.Adj (f i) v ↔ ∃ j, (TerminalCert.graph (mixedPairEdges S)).Adj i j ∧ f j=v) :
    ∃ P : Cycle13.CyclePacking G,
      P.cost ≤ 19*(Fintype.card V-1)+6*G.edgeSet.ncard := by
  exact terminal_neighborhood_induction G ih (mixedPairEdges S) mixedPairWords mixedPairRemoved
    (by decide +kernel) 0 (by decide +kernel) f (mixed_pair_valid S) (mixed_pair_budget S)
    (mixed_pair_incident S) hneighbors

end
end Cycle12
