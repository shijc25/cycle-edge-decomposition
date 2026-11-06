import Cycle12.SixCycleResidueOrder
import Cycle12.TerminalSixVertices

namespace Cycle12
open SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Every vertex-robust minimal counterexample to the terminal bound has
at most eleven vertices. Both infinite six-cycle families and all exterior
components are covered by actual full-neighborhood reductions. -/
theorem terminal_no_seven_counterexample_order (G : SimpleGraph V)
    (hconn : G.Connected) (hrobust : ∀ a, (G.induce ({a}ᶜ : Set V)).Preconnected)
    (hshort : Cycle13.NoCycleAtLeast G 7) (ih : TerminalProperInduction G)
    (hbad : ¬∃ P : Cycle13.CyclePacking G,
      P.cost ≤ 19*(Fintype.card V-1)+6*G.edgeSet.ncard) : Fintype.card V≤11 := by
  have : Nonempty V := hconn.nonempty
  have htwin := (terminal_induction_twins_or_bound G ih).resolve_right hbad
  have hlong : ¬Cycle13.NoCycleAtLeast G 6 := by
    intro h
    exact hbad (terminal_affine_no_six_cycle G h)
  obtain ⟨u,c,hc,hlen⟩ : ∃ u, ∃ c : G.Walk u u, c.IsCycle ∧ c.length=6 := by
    by_contra hn
    apply hlong
    intro u c hc
    have h₁ := hshort u c hc
    have h₂ : c.length≠6 := fun he => hn ⟨u,c,hc,he⟩
    omega
  obtain ⟨f,_,_,hf | hf⟩ := six_cycle_twin_free_classification G hconn hrobust htwin c hc hlen hshort
  · exact six_independent_frame_counterexample_order G ih hbad f hf
  · exact six_matching_frame_counterexample_order G ih hbad f hf

/-- The terminal induction step is closed for every block of order at
least twelve. The finite orders seven through eleven remain separate. -/
theorem terminal_no_seven_large_block (G : SimpleGraph V)
    (hconn : G.Connected) (hrobust : ∀ a, (G.induce ({a}ᶜ : Set V)).Preconnected)
    (hshort : Cycle13.NoCycleAtLeast G 7) (ih : TerminalProperInduction G)
    (hn : 12≤Fintype.card V) :
    ∃ P : Cycle13.CyclePacking G,
      P.cost ≤ 19*(Fintype.card V-1)+6*G.edgeSet.ncard := by
  by_contra hbad
  have hh := terminal_no_seven_counterexample_order G hconn hrobust hshort ih hbad
  omega

/-- Exact remaining finite interface for the circumference-six terminal
theorem. This is a reduction with an explicit premise, not its discharge. -/
theorem terminal_affine_no_seven_of_small
    (hsmall : ∀ (W : Type) [Fintype W] [DecidableEq W] [Nonempty W]
      (H : SimpleGraph W), Fintype.card W≤11 → Cycle13.NoCycleAtLeast H 7 →
      ∃ P : Cycle13.CyclePacking H,
        P.cost ≤ 19*(Fintype.card W-1)+6*H.edgeSet.ncard)
    [Nonempty V] (G : SimpleGraph V) (hshort : Cycle13.NoCycleAtLeast G 7) :
    ∃ P : Cycle13.CyclePacking G,
      P.cost ≤ 19*(Fintype.card V-1)+6*G.edgeSet.ncard := by
  apply terminal_affine_block_induction (threshold:=7) _ G hshort
  intro W _ _ H _ hconn hrobust hshort ih
  have : Nonempty W := hconn.nonempty
  by_cases hn : Fintype.card W≤11
  · exact hsmall W H hn hshort
  · exact terminal_no_seven_large_block H hconn hrobust hshort ih (by omega)

end
end Cycle12
