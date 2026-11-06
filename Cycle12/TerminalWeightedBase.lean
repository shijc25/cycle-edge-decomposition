import Cycle12.TerminalNoSevenCycle
import Cycle12.Foundations.FiniteTerminalCertificate

namespace Cycle12
open SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The previously missing unconditional graph-theoretic base for all
finite DFS chains. Long cycles are removed by actual edge-disjoint walks. -/
theorem terminal_weighted_affine_seven : Cycle13.WeightedAffineBound (19/42) 7 := by
  apply Cycle13.weightedAffine_of_short_cycles (T:=7) (by norm_num)
  intro V _ _ G hshort
  obtain ⟨P,hP⟩ := terminal_rank_no_seven_cycle G hshort
  have hb : P.cost ≤ 19*Fintype.card V+6*G.edgeSet.ncard :=
    hP.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) _)
  have hbR : (P.cost:ℝ) ≤ 19*(Fintype.card V:ℝ)+6*(G.edgeSet.ncard:ℝ) := by exact_mod_cast hb
  rw [Cycle13.CyclePacking.cost_eq_weight] at hbR
  refine ⟨P,?_⟩
  norm_num
  linarith

theorem terminal_weighted_harmonic {u : ℕ} (hu : 7 ≤ u) :
    Cycle13.WeightedAffineBound (19/42+((harmonic u:ℝ)-(harmonic 7:ℝ))/2) u :=
  Cycle13.weightedAffine_harmonic (by norm_num) hu terminal_weighted_affine_seven

theorem terminal_weighted_294494 :
    Cycle13.WeightedAffineBound (1435511/250000) 294494 :=
  Cycle13.weightedAffine_terminal_294494 terminal_weighted_affine_seven

end
end Cycle12
