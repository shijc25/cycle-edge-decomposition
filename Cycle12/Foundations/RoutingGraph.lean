import Cycle12.Foundations.ReservoirCutAssembly

/-! Actual graph assembly for the routing bank and the source attachments. -/
namespace Cycle13.ReservoirPorts
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def routingGraph (G F : SimpleGraph V) (A U : Finset V) : SimpleGraph V :=
  internalGraph F U ⊔ G.between A U

theorem routingGraph_le {G F : SimpleGraph V} (hFG : F ≤ G) (A U : Finset V) :
    routingGraph G F A U ≤ G :=
  sup_le ((internalGraph_le F U).trans hFG) SimpleGraph.between_le

theorem internal_routingGraph (G F : SimpleGraph V) (A U : Finset V)
    (hAU : Disjoint A U) :
    internalGraph (routingGraph G F A U) U = internalGraph F U := by
  ext x y
  change (((F.Adj x y ∧ x ∈ U ∧ y ∈ U) ∨
      (G.Adj x y ∧ (x ∈ A ∧ y ∈ U ∨ x ∈ U ∧ y ∈ A))) ∧ x ∈ U ∧ y ∈ U) ↔
    (F.Adj x y ∧ x ∈ U ∧ y ∈ U)
  constructor
  · rintro ⟨h, hx, hy⟩
    rcases h with h | ⟨_, h | h⟩
    · exact h
    · exact (Finset.disjoint_left.mp hAU h.1 hx).elim
    · exact (Finset.disjoint_left.mp hAU h.2 hy).elim
  · exact fun h => ⟨Or.inl h, h.2⟩

theorem routingGraph_interedges (G F : SimpleGraph V) (A U Y S : Finset V)
    (hFG : F ≤ G) (hYA : Y ⊆ A) :
    (routingGraph G F A U).interedges Y (U \ S) = G.interedges Y (U \ S) := by
  ext e
  simp only [SimpleGraph.interedges, Rel.mem_interedges_iff]
  constructor
  · rintro ⟨hy, hu, h⟩
    exact ⟨hy, hu, routingGraph_le hFG A U h⟩
  · rintro ⟨hy, hu, h⟩
    exact ⟨hy, hu, Or.inr ⟨h, Or.inl ⟨hYA hy, (mem_sdiff.mp hu).1⟩⟩⟩

/-- The actual union graph retains all source attachments while reserving
only `F` for internal routing. The conclusion has no abstract max-flow
premise: all paths, capacities and reservoir interiors are constructed. -/
theorem exists_routing_in_bank (G F : SimpleGraph V) (A U B : Finset V) (c : ℕ)
    (hFG : F ≤ G) (hAU : Disjoint A U) (hBU : B ⊆ U)
    (hcap : A.card ≤ c * B.card) {f L : ℝ}
    (hf₀ : 0 ≤ f) (hf₁ : f ≤ 1) (hL : 1 ≤ f * L)
    (hretain : ∀ S : Finset V, S ⊆ U →
      f * cutSize (internalGraph G U) S ≤ (cutSize (internalGraph F U) S : ℝ))
    (hanchor : ∀ Y : Finset V, Y ⊆ A → ∀ S : Finset V, S ⊆ U →
      2 * S.card ≤ U.card →
      L * Y.card ≤ (cutSize (internalGraph G U) S : ℝ) + (G.interedges Y (U \ S)).card)
    (hbranch : ∀ S : Finset V, S ⊆ U → 2 * S.card ≤ U.card →
      c * (B ∩ S).card ≤ cutSize (internalGraph F U) S) :
    Nonempty (Routing (routingGraph G F A U) A U B c) := by
  have hir := internal_routingGraph G F A U hAU
  have ha := retained_anchor G (routingGraph G F A U) A U hf₀ hf₁ hL
    (fun Y hYA S _ => congrArg Finset.card (routingGraph_interedges G F A U Y S hFG hYA).symm)
    (by intro S hSU; rw [hir]; exact hretain S hSU) hanchor
  apply exists_routing_of_small_sides _ A U B c hAU hBU hcap ha
  intro S hSU hsmall
  rw [hir]
  exact hbranch S hSU hsmall

end
end Cycle13.ReservoirPorts
