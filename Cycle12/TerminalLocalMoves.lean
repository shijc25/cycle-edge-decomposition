import Cycle12.TerminalNeighborhoodReduction
import Cycle12.TerminalTemplates

namespace Cycle12
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def terminalRemoved0 : Finset (Fin 4) := {2,3}
/-- Remove the degree two twins template in a graph of arbitrary order. -/
theorem terminal_remove_degree_two_twins (G : SimpleGraph V) (f : Fin 4 ↪ V)
    (hneighbors : ∀ i ∈ terminalRemoved0, ∀ v,
      G.Adj (f i) v ↔ ∃ j, (TerminalCert.graph TerminalTemplates.edges0).Adj i j ∧ f j=v)
    (P : Cycle13.CyclePacking (G.induce (((terminalRemoved0.map f)ᶜ : Finset V):Set V)))
    (hP : P.cost ≤ 19*((terminalRemoved0.map f)ᶜ.card-1)+
      6*(G.induce (((terminalRemoved0.map f)ᶜ : Finset V):Set V)).edgeSet.ncard) :
    ∃ Q : Cycle13.CyclePacking G, Q.cost ≤ 19*(Fintype.card V-1)+6*G.edgeSet.ncard := by
  exact terminal_neighborhood_reduction G TerminalTemplates.edges0 TerminalTemplates.words0 terminalRemoved0
    0 (by decide +kernel) f TerminalTemplates.valid0 (by decide +kernel)
    (by decide +kernel) hneighbors P hP

def terminalRemoved1 : Finset (Fin 6) := {3,4,5}
/-- Remove the degree three triples template in a graph of arbitrary order. -/
theorem terminal_remove_degree_three_triples (G : SimpleGraph V) (f : Fin 6 ↪ V)
    (hneighbors : ∀ i ∈ terminalRemoved1, ∀ v,
      G.Adj (f i) v ↔ ∃ j, (TerminalCert.graph TerminalTemplates.edges1).Adj i j ∧ f j=v)
    (P : Cycle13.CyclePacking (G.induce (((terminalRemoved1.map f)ᶜ : Finset V):Set V)))
    (hP : P.cost ≤ 19*((terminalRemoved1.map f)ᶜ.card-1)+
      6*(G.induce (((terminalRemoved1.map f)ᶜ : Finset V):Set V)).edgeSet.ncard) :
    ∃ Q : Cycle13.CyclePacking G, Q.cost ≤ 19*(Fintype.card V-1)+6*G.edgeSet.ncard := by
  exact terminal_neighborhood_reduction G TerminalTemplates.edges1 TerminalTemplates.words1 terminalRemoved1
    0 (by decide +kernel) f TerminalTemplates.valid1 (by decide +kernel)
    (by decide +kernel) hneighbors P hP

def terminalRemoved2 : Finset (Fin 6) := {2,3,4,5}
/-- Remove the two diamonds template in a graph of arbitrary order. -/
theorem terminal_remove_two_diamonds (G : SimpleGraph V) (f : Fin 6 ↪ V)
    (hneighbors : ∀ i ∈ terminalRemoved2, ∀ v,
      G.Adj (f i) v ↔ ∃ j, (TerminalCert.graph TerminalTemplates.edges2).Adj i j ∧ f j=v)
    (P : Cycle13.CyclePacking (G.induce (((terminalRemoved2.map f)ᶜ : Finset V):Set V)))
    (hP : P.cost ≤ 19*((terminalRemoved2.map f)ᶜ.card-1)+
      6*(G.induce (((terminalRemoved2.map f)ᶜ : Finset V):Set V)).edgeSet.ncard) :
    ∃ Q : Cycle13.CyclePacking G, Q.cost ≤ 19*(Fintype.card V-1)+6*G.edgeSet.ncard := by
  exact terminal_neighborhood_reduction G TerminalTemplates.edges2 TerminalTemplates.words2 terminalRemoved2
    0 (by decide +kernel) f TerminalTemplates.valid2 (by decide +kernel)
    (by decide +kernel) hneighbors P hP

def terminalRemoved3 : Finset (Fin 6) := {2,3,4,5}
/-- Remove the two three edge paths template in a graph of arbitrary order. -/
theorem terminal_remove_two_three_edge_paths (G : SimpleGraph V) (f : Fin 6 ↪ V)
    (hneighbors : ∀ i ∈ terminalRemoved3, ∀ v,
      G.Adj (f i) v ↔ ∃ j, (TerminalCert.graph TerminalTemplates.edges3).Adj i j ∧ f j=v)
    (P : Cycle13.CyclePacking (G.induce (((terminalRemoved3.map f)ᶜ : Finset V):Set V)))
    (hP : P.cost ≤ 19*((terminalRemoved3.map f)ᶜ.card-1)+
      6*(G.induce (((terminalRemoved3.map f)ᶜ : Finset V):Set V)).edgeSet.ncard) :
    ∃ Q : Cycle13.CyclePacking G, Q.cost ≤ 19*(Fintype.card V-1)+6*G.edgeSet.ncard := by
  exact terminal_neighborhood_reduction G TerminalTemplates.edges3 TerminalTemplates.words3 terminalRemoved3
    0 (by decide +kernel) f TerminalTemplates.valid3 (by decide +kernel)
    (by decide +kernel) hneighbors P hP

def terminalRemoved4 : Finset (Fin 5) := {2,3,4}
/-- Remove the double star template in a graph of arbitrary order. -/
theorem terminal_remove_double_star (G : SimpleGraph V) (f : Fin 5 ↪ V)
    (hneighbors : ∀ i ∈ terminalRemoved4, ∀ v,
      G.Adj (f i) v ↔ ∃ j, (TerminalCert.graph TerminalTemplates.edges4).Adj i j ∧ f j=v)
    (P : Cycle13.CyclePacking (G.induce (((terminalRemoved4.map f)ᶜ : Finset V):Set V)))
    (hP : P.cost ≤ 19*((terminalRemoved4.map f)ᶜ.card-1)+
      6*(G.induce (((terminalRemoved4.map f)ᶜ : Finset V):Set V)).edgeSet.ncard) :
    ∃ Q : Cycle13.CyclePacking G, Q.cost ≤ 19*(Fintype.card V-1)+6*G.edgeSet.ncard := by
  exact terminal_neighborhood_reduction G TerminalTemplates.edges4 TerminalTemplates.words4 terminalRemoved4
    0 (by decide +kernel) f TerminalTemplates.valid4 (by decide +kernel)
    (by decide +kernel) hneighbors P hP

def terminalRemoved5 : Finset (Fin 5) := {2,3,4}
/-- Remove the double star with chord template in a graph of arbitrary order. -/
theorem terminal_remove_double_star_with_chord (G : SimpleGraph V) (f : Fin 5 ↪ V)
    (hneighbors : ∀ i ∈ terminalRemoved5, ∀ v,
      G.Adj (f i) v ↔ ∃ j, (TerminalCert.graph TerminalTemplates.edges5).Adj i j ∧ f j=v)
    (P : Cycle13.CyclePacking (G.induce (((terminalRemoved5.map f)ᶜ : Finset V):Set V)))
    (hP : P.cost ≤ 19*((terminalRemoved5.map f)ᶜ.card-1)+
      6*(G.induce (((terminalRemoved5.map f)ᶜ : Finset V):Set V)).edgeSet.ncard) :
    ∃ Q : Cycle13.CyclePacking G, Q.cost ≤ 19*(Fintype.card V-1)+6*G.edgeSet.ncard := by
  exact terminal_neighborhood_reduction G TerminalTemplates.edges5 TerminalTemplates.words5 terminalRemoved5
    0 (by decide +kernel) f TerminalTemplates.valid5 (by decide +kernel)
    (by decide +kernel) hneighbors P hP

def terminalRemoved6 : Finset (Fin 8) := {2,3,4,5,6,7}
/-- Remove the three triangle legs template in a graph of arbitrary order. -/
theorem terminal_remove_three_triangle_legs (G : SimpleGraph V) (f : Fin 8 ↪ V)
    (hneighbors : ∀ i ∈ terminalRemoved6, ∀ v,
      G.Adj (f i) v ↔ ∃ j, (TerminalCert.graph TerminalTemplates.edges6).Adj i j ∧ f j=v)
    (P : Cycle13.CyclePacking (G.induce (((terminalRemoved6.map f)ᶜ : Finset V):Set V)))
    (hP : P.cost ≤ 19*((terminalRemoved6.map f)ᶜ.card-1)+
      6*(G.induce (((terminalRemoved6.map f)ᶜ : Finset V):Set V)).edgeSet.ncard) :
    ∃ Q : Cycle13.CyclePacking G, Q.cost ≤ 19*(Fintype.card V-1)+6*G.edgeSet.ncard := by
  exact terminal_neighborhood_reduction G TerminalTemplates.edges6 TerminalTemplates.words6 terminalRemoved6
    0 (by decide +kernel) f TerminalTemplates.valid6 (by decide +kernel)
    (by decide +kernel) hneighbors P hP

end
end Cycle12
