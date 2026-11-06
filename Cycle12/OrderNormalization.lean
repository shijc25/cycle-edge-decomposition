import Cycle12.Foundations.Amplification
import Cycle12.Target

/-! Reuse the proved one-vertex gluing and component partition. The only
unproved input in this reduction is the global weighted order bound itself. -/
namespace Cycle12
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Exact finite amplification for any integral weighted cost bound. -/
theorem rooted_weighted_order_to_predecessor {C : ℕ}
    (hglobal : ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∃ P : Cycle13.CyclePacking G, P.cost ≤ C * Fintype.card V)
    {W : Type} [Fintype W] (G : SimpleGraph (Option W)) :
    ∃ P : Cycle13.CyclePacking G, P.cost ≤ C * Fintype.card W := by
  obtain ⟨P, hmin⟩ := Cycle13.CyclePacking.exists_minimum G
  obtain ⟨Q, hQ⟩ := hglobal (Option (Fin (C+1) × W))
    (Cycle13.Wedge.graph G (Fin (C+1)))
  have hlower := Cycle13.wedge_packing_cost_lower_bound G P.cost hmin Q
  simp only [Fintype.card_option, Fintype.card_prod, Fintype.card_fin] at hQ hlower
  refine ⟨P, ?_⟩
  by_contra! hbad
  have hstep : C * Fintype.card W + 1 ≤ P.cost := hbad
  have hmul := Nat.mul_le_mul_left (C+1) hstep
  nlinarith only [hlower,hQ,hmul]

theorem weighted_order_to_predecessor {C : ℕ}
    (hglobal : ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∃ P : Cycle13.CyclePacking G, P.cost ≤ C * Fintype.card V)
    {V : Type} [Fintype V] [Nonempty V] (G : SimpleGraph V) :
    ∃ P : Cycle13.CyclePacking G, P.cost ≤ C * (Fintype.card V - 1) := by
  classical
  let r : V := Classical.choice inferInstance
  let W := {v : V // v ≠ r}
  let e : Option W ≃ V := ((Equiv.optionSubtype r).symm (Equiv.refl W)).1
  obtain ⟨P,hP⟩ := rooted_weighted_order_to_predecessor hglobal (G.comap e)
  have hcard := Fintype.card_congr e
  simp only [Fintype.card_option] at hcard
  refine ⟨P.mapIso (SimpleGraph.Iso.comap e G), ?_⟩
  rw [Cycle13.CyclePacking.cost_mapIso]
  have hpred : Fintype.card V - 1 = Fintype.card W := by omega
  simpa only [hpred] using hP

def WeightedOrderBound : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    ∃ P : Cycle13.CyclePacking G, P.cost ≤ 485 * Fintype.card V

theorem coefficient12_of_indexed_weighted_packing {V : Type} [Fintype V]
    (G : SimpleGraph V)
    (hweighted : ∃ P : Cycle13.CyclePacking G,
      P.cost ≤ 485 * (Fintype.card V - Cycle13.componentCount G)) :
    ∃ k : ℕ, Cycle13.EdgeDecomposition G k ∧
      k ≤ 12 * (Fintype.card V - Cycle13.componentCount G) := by
  obtain ⟨Q,hQ⟩ := hweighted
  obtain ⟨P,hmin⟩ := Cycle13.CyclePacking.exists_minimum G
  have hcost := (hmin Q).trans hQ
  have hforest := P.minimum_singletons_le_rank hmin
  exact ⟨P.count+P.singles,P.decomposition,count_from_weighted_bound hcost hforest⟩

theorem coefficient12_of_component_bounds {V : Type} [Fintype V]
    (G : SimpleGraph V)
    (h : ∀ c : G.ConnectedComponent, ∃ k,
      Cycle13.EdgeDecomposition c.toSimpleGraph k ∧ k ≤ 12 * (Fintype.card c - 1)) :
    ∃ k, Cycle13.EdgeDecomposition G k ∧
      k ≤ 12 * (Fintype.card V - Cycle13.componentCount G) := by
  choose k hdec hbound using h
  refine ⟨∑ c, k c, Cycle13.decomposition_from_components G k hdec, ?_⟩
  calc
    _ ≤ ∑ c : G.ConnectedComponent, 12 * (Fintype.card c - 1) :=
      sum_le_sum (fun c _ => hbound c)
    _ = _ := by rw [← mul_sum, Cycle13.sum_component_ranks]

/-- This is a proved reduction, not the unconditional coefficient-12 theorem.
With C=485 the preceding finite amplification uses exactly 486 copies. -/
theorem coefficient12_from_weighted_order_bound (hglobal : WeightedOrderBound) :
    Coefficient12Statement := by
  intro n G
  have hcomponents : ∀ c : G.ConnectedComponent, ∃ k,
      Cycle13.EdgeDecomposition c.toSimpleGraph k ∧ k ≤ 12 * (Fintype.card c - 1) := by
    intro c
    have : Nonempty c := c.connected_toSimpleGraph.nonempty
    obtain ⟨P,hP⟩ := weighted_order_to_predecessor hglobal c.toSimpleGraph
    have hcc := Cycle13.connected_componentCount_eq_one c.toSimpleGraph
      c.connected_toSimpleGraph
    have hweighted : ∃ Q : Cycle13.CyclePacking c.toSimpleGraph,
        Q.cost ≤ 485 * (Fintype.card c - Cycle13.componentCount c.toSimpleGraph) :=
      ⟨P,by simpa only [hcc] using hP⟩
    simpa only [hcc] using coefficient12_of_indexed_weighted_packing c.toSimpleGraph hweighted
  simpa only [Fintype.card_fin] using coefficient12_of_component_bounds G hcomponents

end
end Cycle12
