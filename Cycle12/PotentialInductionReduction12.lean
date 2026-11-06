import Cycle12.FinitePotentialBase12
import Cycle12.GlobalNoFoldBranch12
import Cycle12.PotentialSmallerGraph12
import Cycle12.OrderNormalization

namespace Cycle12.Global12
open Cycle13 SimpleGraph Finset Real
open Cycle12.Even12
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The remaining graph-theoretic obligation. This predicate leaves the fold branch as an explicit obligation.
It requires an actual packing under
strictly smaller-order induction at an actual foldable layer. -/
def PotentialFoldBranch : Prop := ∀ (n : ℕ) (G : SimpleGraph (Fin n))
    (L : EvenScaleLayers12 G),PotentialBelow n → hasActiveFold L →
      ∃ P : CyclePacking G,P.weight ≤ C*orderPotential n*n

/-- All induction bookkeeping outside the fold branch is discharged:
finite average degree, the actual stopping phase, and every no-fold case. -/
theorem potential_bound_from_fold_branch (hfold : PotentialFoldBranch) :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)),∃ P : CyclePacking G,
      P.weight ≤ C*orderPotential n*n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro G
    have hbelow : PotentialBelow n := fun m hm H => ih m hm H
    by_cases hbase : 2*(G.edgeSet.ncard:ℝ) ≤ (2:ℝ)^mainDegreeLog*n
    · simpa only [Fintype.card_fin] using finite_degree_potential G (by
        simpa only [Fintype.card_fin] using hbase)
    have hlarge : (2:ℝ)^mainDegreeLog < n := by
      by_contra! hh
      apply hbase
      simpa only [Fintype.card_fin] using simple_graph_degree_cap G (by
        simpa only [Fintype.card_fin] using hh)
    have hnR : (0:ℝ)<n := (rpow_pos_of_pos (by norm_num : (0:ℝ)<2) _).trans hlarge
    have hn : 0<n := by exact_mod_cast hnR
    have hlog : wA ≤ originalLog (Fin n) := by
      have hh : mainDegreeLog ≤ logb 2 (n:ℝ) :=
        (le_logb_iff_rpow_le (by norm_num : (1:ℝ)<2) hnR).mpr hlarge.le
      have ha : wA ≤ mainDegreeLog := by norm_num [wA,mainDegreeLog]
      simpa only [originalLog,Fintype.card_fin] using ha.trans hh
    obtain ⟨L⟩ := Cycle12.Even12.exists_actual_scale_layers G (by simpa using hn) hlog
    by_cases hf : hasActiveFold L
    · exact hfold n G L hbelow hf
    · simpa only [Fintype.card_fin] using terminal_potential_of_no_fold L
        (by simpa only [Fintype.card_fin] using hbelow.unweighted) hf

/-- Conditional reduction to the exact requested coefficient-12 statement.
The sole unproved input remains explicitly visible as hfold. -/
theorem coefficient12_from_potential_fold (hfold : PotentialFoldBranch) :
    Cycle12.Coefficient12Statement := by
  apply Cycle12.coefficient12_from_weighted_order_bound
  intro V inst G
  classical
  have hbound : ∀ H : SimpleGraph (Fin (Fintype.card V)),∃ P : CyclePacking H,
      P.weight ≤ C*Fintype.card V := by
    intro H
    obtain ⟨P,hP⟩ := potential_bound_from_fold_branch hfold (Fintype.card V) H
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (orderPotential_bounds (Fintype.card V)).2
        (show 0 ≤ C by norm_num [C])) (Nat.cast_nonneg (Fintype.card V))
    exact ⟨P,hP.trans (by simpa only [mul_one] using hh)⟩
  obtain ⟨P,hP⟩ := packing_weight_of_fin_bound G hbound
  refine ⟨P,?_⟩
  have hc : (P.cost:ℝ) ≤ 485*(Fintype.card V:ℝ) := by
    rw [CyclePacking.cost_eq_weight]
    have hh := mul_le_mul_of_nonneg_left hP (show (0:ℝ) ≤ 42 by norm_num)
    norm_num only [C] at hh
    linarith only [hh]
  exact_mod_cast hc

end
end Cycle12.Global12
