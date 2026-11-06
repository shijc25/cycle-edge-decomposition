import Cycle12.TerminalHFamily
import Cycle12.TerminalNoFiveCycle

namespace Cycle12
open SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Closed terminal theorem for circumference at most five. The infinite
classification, twin-removal induction, and every finite H core are proved. -/
theorem terminal_affine_no_six_cycle {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) (hshort : Cycle13.NoCycleAtLeast G 6) :
    ∃ P : Cycle13.CyclePacking G,
      P.cost ≤ 19*(Fintype.card V-1)+6*G.edgeSet.ncard := by
  apply terminal_affine_from_blocks (threshold:=6) _ G hshort
  intro W _ _ H _ hconn hrobust hshort
  have : Nonempty W := hconn.nonempty
  by_cases hsmall : Cycle13.NoCycleAtLeast H 5
  · exact terminal_affine_no_five_cycle H hsmall
  · obtain ⟨u,c,hc,hlen⟩ : ∃ u, ∃ c : H.Walk u u, c.IsCycle ∧ c.length=5 := by
      by_contra hn
      apply hsmall
      intro u c hc
      have h₁ := hshort u c hc
      have h₂ : c.length≠5 := fun he => hn ⟨u,c,hc,he⟩
      omega
    obtain ⟨f,hf⟩ := h_frame_of_five_cycle H hconn hrobust hshort c hc hlen
    exact terminal_affine_h_frame H f hf

/-- The terminal rank bound for every finite graph without cycles of
length at least six, including the empty graph and all isolated vertices. -/
theorem terminal_rank_no_six_cycle {V : Type} [Fintype V]
    (G : SimpleGraph V) (hshort : Cycle13.NoCycleAtLeast G 6) :
    ∃ P : Cycle13.CyclePacking G,
      P.cost ≤ 19*(Fintype.card V-Cycle13.componentCount G)+6*G.edgeSet.ncard := by
  apply terminal_affine_from_components G
  intro c
  have : Nonempty c := c.connected_toSimpleGraph.nonempty
  have hc : Cycle13.NoCycleAtLeast c.toSimpleGraph 6 := by
    intro v p hp
    have hh := hshort v.val (p.map c.toSimpleGraph_hom) (hp.map Subtype.val_injective)
    erw [Walk.length_map] at hh
    exact hh
  exact terminal_affine_no_six_cycle c.toSimpleGraph hc

theorem terminal_affine_card_le_five {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) (hn : Fintype.card V ≤ 5) :
    ∃ P : Cycle13.CyclePacking G,
      P.cost ≤ 19*(Fintype.card V-1)+6*G.edgeSet.ncard := by
  apply terminal_affine_no_six_cycle G
  intro u c hc
  have hh := Cycle13.cycle_length_le_order hc
  omega

end
end Cycle12
