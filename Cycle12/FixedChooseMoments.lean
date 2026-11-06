import Cycle12.FixedSampleEdgeMoments
import Cycle12.SubsetThreeVote

namespace Cycle12
open Finset
noncomputable section

theorem real_cast_choose_four (n : ℕ) :
    (n.choose 4:ℝ)=(n:ℝ)*(n-1)*(n-2)*(n-3)/24 := by
  induction n with
  | zero => norm_num [Nat.choose]
  | succ n ih =>
    rw [Nat.choose_succ_succ,Nat.cast_add,real_cast_choose_three,ih]
    push_cast
    ring

theorem fixed_choose_ratio_two (n k : ℕ) :
    fixedChooseRatio n k 2=(k:ℝ)*(k-1)/((n:ℝ)*(n-1)) := by
  unfold fixedChooseRatio
  rw [Nat.cast_choose_two,Nat.cast_choose_two]
  simp only [div_div_div_comm]
  norm_num

theorem fixed_choose_ratio_three (n k : ℕ) :
    fixedChooseRatio n k 3=(k:ℝ)*(k-1)*(k-2)/((n:ℝ)*(n-1)*(n-2)) := by
  unfold fixedChooseRatio
  rw [real_cast_choose_three,real_cast_choose_three]
  simp only [div_div_div_comm]
  norm_num

theorem fixed_choose_ratio_four (n k : ℕ) :
    fixedChooseRatio n k 4=(k:ℝ)*(k-1)*(k-2)*(k-3)/((n:ℝ)*(n-1)*(n-2)*(n-3)) := by
  unfold fixedChooseRatio
  rw [real_cast_choose_four,real_cast_choose_four]
  simp only [div_div_div_comm]
  norm_num

theorem fixed_choose_ratio_three_ge_four (n k : ℕ) (hn : 4≤n) (hk : k≤n) :
    fixedChooseRatio n k 4 ≤ fixedChooseRatio n k 3 := by
  have hnR : (4:ℝ)≤n := by exact_mod_cast hn
  have hkR : (k:ℝ)≤n := by exact_mod_cast hk
  have he : fixedChooseRatio n k 4=fixedChooseRatio n k 3*((k:ℝ)-3)/((n:ℝ)-3) := by
    rw [fixed_choose_ratio_three,fixed_choose_ratio_four]
    have h0 : (n:ℝ)≠0 := by linarith
    have h1 : (n:ℝ)-1≠0 := by linarith
    have h2 : (n:ℝ)-2≠0 := by linarith
    have h3 : (n:ℝ)-3≠0 := by linarith
    field_simp
  rw [he]
  apply (div_le_iff₀ (show 0<(n:ℝ)-3 by linarith)).mpr
  exact mul_le_mul_of_nonneg_left (by linarith) (by unfold fixedChooseRatio; positivity)

def fixedEdgeVarianceCap (n k m : ℝ) : ℝ :=
  m*k*(n-k)*(k-1)^2*(n*(n-1)-2*m)/(n^2*(n-2)*(n-1)^2)

theorem fixed_variance_cap_algebra (n k : ℕ) (hn : 4≤n) (m : ℝ) :
    m*(fixedChooseRatio n k 2-2*fixedChooseRatio n k 3+fixedChooseRatio n k 4)+
      m*(2*m/((n:ℝ)-1)+(n:ℝ)-2)*(fixedChooseRatio n k 3-fixedChooseRatio n k 4)+
      m^2*(fixedChooseRatio n k 4-(fixedChooseRatio n k 2)^2)=
        fixedEdgeVarianceCap n k m := by
  have hnR : (4:ℝ)≤n := by exact_mod_cast hn
  have h0 : (n:ℝ)≠0 := by linarith
  have h1 : (n:ℝ)-1≠0 := by linarith
  have h2 : (n:ℝ)-2≠0 := by linarith
  have h3 : (n:ℝ)-3≠0 := by linarith
  rw [fixed_choose_ratio_two,fixed_choose_ratio_three,fixed_choose_ratio_four]
  unfold fixedEdgeVarianceCap
  field_simp
  ring

end
end Cycle12
