import Cycle12.TemplateApplication

/-! A finite removal template is valid in every ambient order when the
neighborhood of each removed vertex agrees with the template. No assumptions
are made about edges among the retained vertices. -/
namespace Cycle12
open SimpleGraph Finset Cycle13
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

theorem incidentRemainder_adj (G : SimpleGraph V) (S : Finset V) (u v : V) :
    (incidentRemainder G S).Adj u v ↔ G.Adj u v ∧ (u ∉ S ∨ v ∉ S) := by
  rw [incidentRemainder,SimpleGraph.deleteEdges_adj,reservoirLift_induce]
  change (G.Adj u v ∧ ¬(G.Adj u v ∧ u ∈ S ∧ v ∈ S)) ↔ _
  tauto

theorem incidentRemainder_eq_template (G : SimpleGraph V) (H : SimpleGraph W)
    (D : Finset W) (f : W ↪ V)
    (hincident : ∀ i j, H.Adj i j → i ∈ D ∨ j ∈ D)
    (hneighbors : ∀ i ∈ D, ∀ v, G.Adj (f i) v ↔ ∃ j, H.Adj i j ∧ f j=v) :
    H.map f=incidentRemainder G (D.map f)ᶜ := by
  ext u v
  rw [SimpleGraph.map_adj,incidentRemainder_adj]
  simp only [Finset.mem_compl,not_not]
  constructor
  · rintro ⟨i,j,hij,rfl,rfl⟩
    rcases hincident i j hij with hi | hj
    · exact ⟨(hneighbors i hi (f j)).mpr ⟨j,hij,rfl⟩,
        Or.inl (Finset.mem_map.mpr ⟨i,hi,rfl⟩)⟩
    · exact ⟨((hneighbors j hj (f i)).mpr ⟨i,hij.symm,rfl⟩).symm,
        Or.inr (Finset.mem_map.mpr ⟨j,hj,rfl⟩)⟩
  · rintro ⟨huv,hu | hv⟩
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hu
      obtain ⟨j,hij,rfl⟩ := (hneighbors i hi v).mp huv
      exact ⟨i,j,hij,rfl,rfl⟩
    · obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hv
      obtain ⟨i,hji,rfl⟩ := (hneighbors j hj u).mp huv.symm
      exact ⟨i,j,hji.symm,rfl,rfl⟩

/-- The actual arbitrary-order induction step associated to a checked local
template. Its hypotheses specify full neighborhoods, so all incident edges
and their costs are accounted for, including edges going to the boundary. -/
theorem terminal_neighborhood_reduction {d : ℕ} (G : SimpleGraph V)
    (E : Finset (Sym2 W)) (words : Fin d → CycleWord W) (D : Finset W)
    (a : W) (ha : a ∉ D) (f : W ↪ V)
    (hc : TerminalCert.Valid E words)
    (hb : 42*d+23*(E\TerminalCert.covered words).card ≤ 19*D.card+6*E.card)
    (hincident : ∀ i j, (TerminalCert.graph E).Adj i j → i ∈ D ∨ j ∈ D)
    (hneighbors : ∀ i ∈ D, ∀ v,
      G.Adj (f i) v ↔ ∃ j, (TerminalCert.graph E).Adj i j ∧ f j=v)
    (P : Cycle13.CyclePacking (G.induce (((D.map f)ᶜ : Finset V):Set V)))
    (hP : P.cost ≤ 19*((D.map f)ᶜ.card-1)+
      6*(G.induce (((D.map f)ᶜ : Finset V):Set V)).edgeSet.ncard) :
    ∃ Q : Cycle13.CyclePacking G, Q.cost ≤ 19*(Fintype.card V-1)+6*G.edgeSet.ncard := by
  have hS : ((D.map f)ᶜ : Finset V).Nonempty := by
    refine ⟨f a,?_⟩
    simpa only [Finset.mem_compl,Finset.mem_map,f.injective.eq_iff,exists_eq_right] using ha
  have hcard : Fintype.card V-(D.map f)ᶜ.card=D.card := by
    have hh := Finset.card_add_card_compl (D.map f)
    rw [Finset.card_map] at hh
    omega
  apply terminal_template_vertex_reduction G _ hS E words hc _ f
    (incidentRemainder_eq_template G _ D f hincident hneighbors) P hP
  simpa only [hcard] using hb

end
end Cycle12
