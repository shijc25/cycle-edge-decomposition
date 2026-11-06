import Cycle12.CoverBankScales
import Cycle12.DirectCapacityAlgebra
import Cycle12.CoverSampleRealization

namespace Cycle12
open Real
noncomputable section

structure DirectBankParameters where
  sample : CoverSamplingBox
  dm : ℝ
  beta : ℝ
  L : ℝ
  mean : ℝ
  fan : ℝ
  router : ℝ
  epsilon : ℝ
  zLower : ℝ
  cutLog : ℝ
  cutBound : ℝ
  rLower : ℝ
  weightLower : ℝ

structure DirectBankParameters.Valid (c : DirectBankParameters) : Prop where
  sampling : c.sample.Valid
  sample_two : 2 ≤ c.sample.Nlo
  dm_pos : 0 < c.dm
  beta_pos : 0 < c.beta
  mean_pos : 0 < c.mean
  mean_lt_one : c.mean < 1
  fan_pos : 0 < c.fan
  router_pos : 0 < c.router
  epsilon_nonneg : 0 ≤ c.epsilon
  fan_le : c.fan ≤ c.mean-c.epsilon
  router_le : c.router ≤ 1-c.mean-c.epsilon
  anchoring : 1 ≤ c.fan*c.L
  z_lower : c.zLower ≤ 2*(43/10)^3*c.sample.Plo*coverScaleH c.sample.xl*c.sample.s0/
    (coverScaleW c.sample.xh*coverScaleDen c.sample.xl)
  mincut : 1 ≤ c.beta*c.zLower
  log_upper : log (coverRoutingOrder c.sample.xh c.sample.s0 c.sample.Pu) ≤ c.cutLog
  log_lower : 2 ≤ c.cutLog
  gap : 0 < 2*c.epsilon^2*c.dm*c.zLower-2*c.cutLog
  cut_tail : (2*c.epsilon^2*c.dm*c.zLower)/(2*c.epsilon^2*c.dm*c.zLower-2*c.cutLog)*
    exp (-(2*c.epsilon^2*c.dm*c.zLower-2*c.cutLog)) ≤ c.cutBound
  failure : 2*c.cutBound < 1
  r_lower : c.rLower ≤ 2*c.sample.s0*coverScaleDen c.sample.xh/(coverScaleH c.sample.xh*coverScaleW c.sample.xh)
  ratio : 4096 ≤ c.rLower/(c.router*c.beta)
  weight_lower : c.weightLower ≤ 2*(43/10)^3*c.sample.Plo^2*coverScaleH c.sample.xl*c.sample.s0/coverScaleDen c.sample.xl
  source_capacity : 1 ≤ c.fan*c.beta*c.weightLower
  routing_capacity : 324 ≤ coverDirectCubic (c.router*c.beta) c.sample.xl c.sample.s0 c.sample.Plo

end
end Cycle12
