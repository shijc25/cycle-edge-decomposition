import Cycle12.CoverBankProbability
import Cycle12.CoverBankAlgebra
import Cycle12.CoverSampleRealization
import Cycle12.Foundations.SharpBanks

namespace Cycle12
open Real Finset SimpleGraph Cycle13
noncomputable section
attribute [local instance] Classical.propDecidable

structure CoverBankParameters where
  sample : CoverSamplingBox
  strong : Bool
  maximumScale : Option ℝ
  dm : ℝ
  beta : ℝ
  L : ℝ
  mean : ℝ
  fan : ℝ
  degreeFraction : ℝ
  gain : ℝ
  coeff : ℝ
  qLower : ℝ
  zLower : ℝ
  cutLog : ℝ
  cutBound : ℝ
  coreBound : ℝ
  branchBound : ℝ

def CoverBankParameters.ac (c : CoverBankParameters) : ℝ := (1-c.mean-1/1000)*(97/100)
def CoverBankParameters.dc (c : CoverBankParameters) : ℝ := c.ac*c.gain
def CoverBankParameters.cost (c : CoverBankParameters) : ℝ := if c.strong then 1 else 11/10
def CoverBankParameters.branch (c : CoverBankParameters) : ℝ :=
  max (c.dc/(1-c.degreeFraction)) (coverBankDegreeRatio c.dm c.sample.xl)-c.cost*c.coeff
def CoverBankParameters.modelSize (c : CoverBankParameters) (T : ℝ) : ℕ :=
  if c.strong then evenFloor T else evenFloor (T-1)

structure CoverBankParameters.Valid (c : CoverBankParameters) : Prop where
  sampling : c.sample.Valid
  sample_two : 2 ≤ c.sample.Nlo
  degree_positive : 0 < c.dm
  beta_positive : 0 < c.beta
  fan_positive : 0 < c.fan
  fan_le_degree : c.fan ≤ c.degreeFraction
  degree_lt_mean : c.degreeFraction < c.mean
  mean_lt_one : c.mean < 999/1000
  coeff_positive : 0 < c.coeff
  gain_positive : 0 < c.gain
  weak_degree : c.strong=false → 7*c.coeff ≤ c.dc
  strong_degree : c.strong=true → c.coeff ≤ c.dc
  dense_size : c.dc/(2*c.sample.s0) ≤ 1
  dense_gain : c.gain=1 ∨ ∃ sh, c.maximumScale=some sh ∧ c.gain-c.gain^2*c.ac/(4*sh) ≤ 1
  strong_stopping : c.strong=true → ∃ sh, c.maximumScale=some sh ∧ c.coeff*(1+log (2*sh/c.coeff)) ≤ 2*c.ac
  q_lower : c.qLower ≤ coverRoutingQ c.sample.xh c.sample.s0 c.sample.Plo
  z_lower : c.zLower ≤ 2*(43/10)^3*c.sample.Plo*coverScaleH c.sample.xl*c.sample.s0/
    (coverScaleW c.sample.xh*coverScaleDen c.sample.xl)
  sample_mincut : 1 ≤ c.beta*c.zLower
  cut_log : log (coverRoutingOrder c.sample.xh c.sample.s0 c.sample.Pu) ≤ c.cutLog
  cut_log_lower : 2 ≤ c.cutLog
  cut_gap : 0 < 2*(c.mean-c.fan)^2*c.dm*c.zLower-2*c.cutLog
  cut_tail :
    (2*(c.mean-c.fan)^2*c.dm*c.zLower)/(2*(c.mean-c.fan)^2*c.dm*c.zLower-2*c.cutLog)*
      exp (-(2*(c.mean-c.fan)^2*c.dm*c.zLower-2*c.cutLog)) ≤ c.cutBound
  core_tail : exp (-2*(1/1000)^2*((97/100)*(2*c.sample.s0*(coverRoutingQ c.sample.xh c.sample.s0 c.sample.Plo)^2))) ≤ c.coreBound
  branch_scale : 2 ≤ 2*c.dc*c.qLower*(c.mean-c.degreeFraction)^2/(1-c.degreeFraction)
  branch_tail : coverRoutingOrder c.sample.xh c.sample.s0 c.sample.Pu*
    exp (-(2*c.dc*c.qLower*(c.mean-c.degreeFraction)^2/(1-c.degreeFraction))) ≤ c.branchBound
  probability_sum : c.cutBound+c.coreBound+c.branchBound < 1

theorem cover_bank_ac_pos (c : CoverBankParameters) (hc : c.Valid) : 0 < c.ac := by
  unfold CoverBankParameters.ac
  have hh : 0 < 1-c.mean-1/1000 := by linarith only [hc.mean_lt_one]
  positivity

theorem cover_bank_dc_pos (c : CoverBankParameters) (hc : c.Valid) : 0 < c.dc :=
  mul_pos (cover_bank_ac_pos c hc) hc.gain_positive

theorem cover_bank_model_size_bounds (c : CoverBankParameters) {T : ℝ} (hT : 24 ≤ T) :
    0 < c.modelSize T ∧ Even (c.modelSize T) ∧ (c.modelSize T:ℝ) ≤ T ∧ T-3 ≤ (c.modelSize T:ℝ) := by
  cases he : c.strong with
  | false =>
    obtain ⟨ht,hu,hl,hEven⟩ := evenFloor_bounds (show 4 ≤ T-1 by linarith only [hT])
    simp only [CoverBankParameters.modelSize,he,Bool.false_eq_true,ite_false]
    exact ⟨by omega,hEven,by linarith only [hu],by linarith only [hl]⟩
  | true =>
    obtain ⟨ht,hu,hl,hEven⟩ := evenFloor_bounds (show 4 ≤ T by linarith only [hT])
    simp only [CoverBankParameters.modelSize,he,ite_true]
    exact ⟨by omega,hEven,hu,by linarith only [hl]⟩

end
end Cycle12
