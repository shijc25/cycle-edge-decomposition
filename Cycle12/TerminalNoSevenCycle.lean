import Cycle12.TerminalSixResidueApplication
import Cycle12.TerminalSixCycleReduction

namespace Cycle12
open SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Closed affine terminal theorem for circumference at most six. The
infinite classification, proper induced-graph reductions, parameter
coverage, finite witnesses, and actual vertex labelings are all proved. -/
theorem terminal_affine_no_seven_cycle {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) (hshort : Cycle13.NoCycleAtLeast G 7) :
    ∃ P : Cycle13.CyclePacking G,
      P.cost ≤ 19*(Fintype.card V-1)+6*G.edgeSet.ncard := by
  apply terminal_affine_block_induction (threshold:=7) _ G hshort
  intro W _ _ H _ hconn hrobust hshort ih
  have : Nonempty W := hconn.nonempty
  by_cases hsmall : Cycle13.NoCycleAtLeast H 6
  · exact terminal_affine_no_six_cycle H hsmall
  · by_contra hbad
    have htwin := (terminal_induction_twins_or_bound H ih).resolve_right hbad
    obtain ⟨u,c,hc,hlen⟩ : ∃ u, ∃ c : H.Walk u u, c.IsCycle ∧ c.length=6 := by
      by_contra hn
      apply hsmall
      intro u c hc
      have h₁ := hshort u c hc
      have h₂ : c.length≠6 := fun he => hn ⟨u,c,hc,he⟩
      omega
    obtain ⟨f,hcycle,_,hf | hf⟩ :=
      six_cycle_twin_free_classification H hconn hrobust htwin c hc hlen hshort
    · exact hbad (terminal_affine_six_independent H hshort f hcycle hf
        (six_attachment_fiber_bound H ih hbad f))
    · exact hbad (terminal_affine_six_matching H ih hshort f hcycle hf)

/-- The exact terminal rank bound for all finite graphs without cycles
of length at least seven, including the empty graph and isolated vertices. -/
theorem terminal_rank_no_seven_cycle {V : Type} [Fintype V]
    (G : SimpleGraph V) (hshort : Cycle13.NoCycleAtLeast G 7) :
    ∃ P : Cycle13.CyclePacking G,
      P.cost ≤ 19*(Fintype.card V-Cycle13.componentCount G)+6*G.edgeSet.ncard := by
  apply terminal_affine_from_components G
  intro c
  have : Nonempty c := c.connected_toSimpleGraph.nonempty
  have hc : Cycle13.NoCycleAtLeast c.toSimpleGraph 7 :=
    noLongCycle_of_injective_hom hshort c.toSimpleGraph_hom Subtype.val_injective
  exact terminal_affine_no_seven_cycle c.toSimpleGraph hc

end
end Cycle12
