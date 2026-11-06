import Cycle12.TemplateApplication
import Cycle12.TerminalTemplates

/-! An unconditional local reduction on arbitrary finite graphs, not a
finite-order experiment: remove two degree-two twins and their entire stars. -/
namespace Cycle12
open SimpleGraph Finset Cycle13
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem degree_two_twins_incident_edges (G : SimpleGraph V) (a b x y : V)
    (hab : a ≠ b) (hxy : x ≠ y) (hax : a ≠ x) (hay : a ≠ y)
    (hbx : b ≠ x) (hby : b ≠ y)
    (hx : ∀ v, G.Adj x v ↔ v=a ∨ v=b)
    (hy : ∀ v, G.Adj y v ↔ v=a ∨ v=b) :
    (incidentRemainder G ({x,y}:Finset V)ᶜ).edgeSet=
      ({s(a,x),s(a,y),s(b,x),s(b,y)}:Set (Sym2 V)) := by
  have hx' : ∀ v, G.Adj v x ↔ v=a ∨ v=b := by intro v; rw [G.adj_comm]; exact hx v
  have hy' : ∀ v, G.Adj v y ↔ v=a ∨ v=b := by intro v; rw [G.adj_comm]; exact hy v
  ext e
  induction e using Sym2.ind with
  | _ u v =>
    simp only [incidentRemainder,SimpleGraph.edgeSet_deleteEdges,
      reservoirLift_induce,Set.mem_sdiff,SimpleGraph.mem_edgeSet,
      ReservoirPorts.internalGraph,mem_compl,mem_insert,mem_singleton,
      Set.mem_insert_iff,Set.mem_singleton_iff,Sym2.eq_iff]
    by_cases hux : u=x <;> by_cases huy : u=y <;>
      by_cases hvx : v=x <;> by_cases hvy : v=y <;>
      simp_all [hx,hy,hx',hy'] <;> aesop

theorem terminal_delete_degree_two_twins (G : SimpleGraph V) (a b x y : V)
    (hab : a ≠ b) (hxy : x ≠ y) (hax : a ≠ x) (hay : a ≠ y)
    (hbx : b ≠ x) (hby : b ≠ y)
    (hx : ∀ v, G.Adj x v ↔ v=a ∨ v=b)
    (hy : ∀ v, G.Adj y v ↔ v=a ∨ v=b)
    (P : Cycle13.CyclePacking (G.induce ((({x,y}:Finset V)ᶜ : Finset V):Set V)))
    (hP : P.cost ≤ 19*((({x,y}:Finset V)ᶜ).card-1)+
      6*(G.induce ((({x,y}:Finset V)ᶜ : Finset V):Set V)).edgeSet.ncard) :
    ∃ Q : Cycle13.CyclePacking G, Q.cost ≤ 19*(Fintype.card V-1)+6*G.edgeSet.ncard := by
  let f : Fin 4 ↪ V := ⟨![a,b,x,y],by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all⟩
  have hmodel : (TerminalCert.graph TerminalTemplates.edges0).map f=
      incidentRemainder G ({x,y}:Finset V)ᶜ := by
    apply SimpleGraph.edgeSet_injective
    rw [SimpleGraph.edgeSet_map,
      TerminalCert.edgeSet_graph _ TerminalTemplates.valid0.1,
      degree_two_twins_incident_edges G a b x y hab hxy hax hay hbx hby hx hy]
    simp [TerminalTemplates.edges0,f] <;> rfl
  have hS : (({x,y}:Finset V)ᶜ).Nonempty := ⟨a,by simp [hax,hay]⟩
  have hcard : Fintype.card V-(({x,y}:Finset V)ᶜ).card=2 := by
    have hc := Finset.card_add_card_compl ({x,y}:Finset V)
    rw [Finset.card_pair hxy] at hc
    omega
  have hb : 42*1+23*(TerminalTemplates.edges0\TerminalCert.covered TerminalTemplates.words0).card ≤
      19*(Fintype.card V-(({x,y}:Finset V)ᶜ).card)+6*TerminalTemplates.edges0.card := by
    rw [hcard]
    decide +kernel
  have main := terminal_template_vertex_reduction G _ hS TerminalTemplates.edges0
    TerminalTemplates.words0 TerminalTemplates.valid0 hb f hmodel
  exact main P hP

end
end Cycle12
