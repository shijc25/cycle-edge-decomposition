import Cycle12.Foundations.Wedge
import Cycle12.Foundations.PackingPartition
import Cycle12.Foundations.Components

/-! Exact finite amplification. Since the scaled weighted cost is an integer,
528 copies suffice to remove the additive 527; no limiting argument is required.
The global weighted order bound is still a premise, not an assumed axiom. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable

def WeightedOrderBound : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    ∃ P : CyclePacking G, P.cost ≤ 527 * Fintype.card V

theorem wedge_packing_cost_lower_bound {W I : Type} [Fintype W] [Fintype I]
    (G : SimpleGraph (Option W)) (M : ℕ)
    (hM : ∀ Q : CyclePacking G, M ≤ Q.cost) (P : CyclePacking (Wedge.graph G I)) :
    Fintype.card I * M ≤ P.cost := by
  exact packing_cost_copies_lower_bound G (Wedge.graph G I) (Wedge.embedHom G)
    (fun i => Wedge.embed_injective i) (Wedge.copy_edges_disjoint G)
    (Wedge.copy_edges_cover G) (Wedge.cycle_lifts_from_copy G) M hM P

theorem rooted_weighted_predecessor_bound (hglobal : WeightedOrderBound)
    {W : Type} [Fintype W] (G : SimpleGraph (Option W)) :
    ∃ P : CyclePacking G, P.cost ≤ 527 * Fintype.card W := by
  obtain ⟨P, hmin⟩ := CyclePacking.exists_minimum G
  obtain ⟨Q, hQ⟩ := hglobal (Option (Fin 528 × W)) (Wedge.graph G (Fin 528))
  have hlower := wedge_packing_cost_lower_bound G P.cost hmin Q
  simp only [Fintype.card_option, Fintype.card_prod, Fintype.card_fin] at hQ hlower
  refine ⟨P, ?_⟩
  omega

theorem weighted_predecessor_bound (hglobal : WeightedOrderBound)
    {V : Type} [Fintype V] [Nonempty V] (G : SimpleGraph V) :
    ∃ P : CyclePacking G, P.cost ≤ 527 * (Fintype.card V - 1) := by
  classical
  let r : V := Classical.choice inferInstance
  let W := {v : V // v ≠ r}
  let e : Option W ≃ V := ((Equiv.optionSubtype r).symm (Equiv.refl W)).1
  let H := G.comap e
  obtain ⟨P, hP⟩ := rooted_weighted_predecessor_bound hglobal H
  have hcard := Fintype.card_congr e
  simp only [Fintype.card_option] at hcard
  refine ⟨P.mapIso (SimpleGraph.Iso.comap e G), ?_⟩
  rw [CyclePacking.cost_mapIso]
  have hpred : Fintype.card V - 1 = Fintype.card W := by omega
  rw [hpred]
  exact hP

theorem connected_componentCount_eq_one {V : Type} (G : SimpleGraph V)
    (hG : G.Connected) : componentCount G = 1 := by
  have : Subsingleton G.ConnectedComponent := hG.preconnected.subsingleton_connectedComponent
  have : Nonempty G.ConnectedComponent := ⟨G.connectedComponentMk hG.nonempty.some⟩
  exact Nat.card_unique

/-- A complete reduction of the final exact graph statement to the still-open
weighted order bound. This declaration is deliberately not the final theorem. -/
theorem coefficient13_from_weighted_order_bound (hglobal : WeightedOrderBound) :
    Coefficient13Statement := by
  intro n G
  have hcomponents : ∀ c : G.ConnectedComponent,
      ∃ k, EdgeDecomposition c.toSimpleGraph k ∧ k ≤ 13 * (Fintype.card c - 1) := by
    intro c
    have : Nonempty c := c.connected_toSimpleGraph.nonempty
    obtain ⟨P, hP⟩ := weighted_predecessor_bound hglobal c.toSimpleGraph
    have hcc := connected_componentCount_eq_one c.toSimpleGraph c.connected_toSimpleGraph
    have hweighted : ∃ Q : CyclePacking c.toSimpleGraph,
        Q.cost ≤ 527 * (Fintype.card c - componentCount c.toSimpleGraph) :=
      ⟨P, by simpa only [hcc] using hP⟩
    simpa only [hcc] using coefficient13_of_weighted_packing c.toSimpleGraph hweighted
  simpa only [Fintype.card_fin] using coefficient13_of_component_bounds G hcomponents

end
end Cycle13
