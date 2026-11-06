import Cycle12.RationalSamplingBox
import Cycle12.RationalDegreeEnvelope
import Cycle12.CoverBankParameters
import Cycle12.RationalDecay
import Cycle12.RationalLabelEntropy

namespace Cycle12
open Real Cycle13

structure RatBankParameters where
  sample : RatSamplingBox
  strong : Bool
  maximumScale : Option ℚ
  dm : ℚ
  beta : ℚ
  L : ℚ
  mean : ℚ
  fan : ℚ
  degreeFraction : ℚ
  gain : ℚ
  coeff : ℚ
  zLower : ℚ
  orderLog : RatScaledLogUpper
  stopLog : RatScaledLogUpper
  branchLog : RatScaledLogUpper
  cutDecay : RatDecayCertificate
  coreDecay : RatDecayCertificate
  branchBound : ℚ

def ratRoutingQ (x s P : ℚ) : ℚ := 2*(43/10)^3*P*s/(ratCoverW x)^2
def ratRoutingOrder (x s P : ℚ) : ℚ := 4*(43/10)^3*P*s^2/(ratCoverW x)^2
def RatBankParameters.ac (c : RatBankParameters) : ℚ := (1-c.mean-1/1000)*(97/100)
def RatBankParameters.dc (c : RatBankParameters) : ℚ := c.ac*c.gain
def RatBankParameters.qLower (c : RatBankParameters) : ℚ := ratRoutingQ c.sample.xh c.sample.s0 c.sample.Plo
def RatBankParameters.nUpper (c : RatBankParameters) : ℚ := ratRoutingOrder c.sample.xh c.sample.s0 c.sample.Pu
def RatBankParameters.cutExponent (c : RatBankParameters) : ℚ := 2*(c.mean-c.fan)^2*c.dm*c.zLower
def RatBankParameters.cutBound (c : RatBankParameters) : ℚ :=
  c.cutExponent/(c.cutExponent-2*c.orderLog.bound)*c.cutDecay.bound
def RatBankParameters.branchExponent (c : RatBankParameters) : ℚ :=
  2*c.dc*c.qLower*(c.mean-c.degreeFraction)^2/(1-c.degreeFraction)
def RatBankParameters.coreExponent (c : RatBankParameters) : ℚ :=
  2*(1/1000)^2*((97/100)*(2*c.sample.s0*c.qLower^2))

def RatBankParameters.NumericValid (c : RatBankParameters) : Prop :=
  c.sample.Valid ∧ 2 ≤ c.sample.Nlo ∧ 0 < c.dm ∧ 0 < c.beta ∧ 0 < c.fan ∧
  c.fan ≤ c.degreeFraction ∧ c.degreeFraction < c.mean ∧ c.mean < 999/1000 ∧
  0 < c.coeff ∧ 0 < c.gain ∧
  (c.strong=false → 7*c.coeff ≤ c.dc) ∧ (c.strong=true → c.coeff ≤ c.dc) ∧
  c.dc/(2*c.sample.s0) ≤ 1 ∧
  (c.gain=1 ∨ (match c.maximumScale with
    | none => False | some sh => c.gain-c.gain^2*c.ac/(4*sh) ≤ 1)) ∧
  (c.strong=true → match c.maximumScale with
    | none => False
    | some sh => c.stopLog.argument=2*sh/c.coeff ∧ c.coeff*(1+c.stopLog.bound) ≤ 2*c.ac) ∧
  c.zLower ≤ 2*(43/10)^3*c.sample.Plo*ratCoverH c.sample.xl*c.sample.s0/
    (ratCoverW c.sample.xh*ratCoverDen c.sample.xl) ∧
  1 ≤ c.beta*c.zLower ∧
  c.orderLog.argument=c.nUpper ∧ 2 ≤ c.orderLog.bound ∧
  0 < c.cutExponent-2*c.orderLog.bound ∧
  c.cutDecay.exponent=c.cutExponent-2*c.orderLog.bound ∧ c.cutDecay.scaleLower=1 ∧
  c.coreDecay.exponent=c.coreExponent ∧ c.coreDecay.scaleLower=1 ∧
  2 ≤ c.branchExponent ∧ 0 < c.branchBound ∧
  c.branchLog.argument=c.nUpper/c.branchBound ∧ c.branchLog.bound ≤ c.branchExponent ∧
  c.cutBound+c.coreDecay.bound+c.branchBound < 1

instance instDecidableRatBankParametersNumeric (c : RatBankParameters) : Decidable c.NumericValid := by
  unfold RatBankParameters.NumericValid
  cases c.maximumScale <;> infer_instance

theorem rat_routing_q_cast (x s P : ℚ) : (ratRoutingQ x s P:ℝ)=coverRoutingQ x s P := by
  norm_num [ratRoutingQ,coverRoutingQ,rat_cover_w_cast]
theorem rat_routing_order_cast (x s P : ℚ) : (ratRoutingOrder x s P:ℝ)=coverRoutingOrder x s P := by
  norm_num [ratRoutingOrder,coverRoutingOrder,rat_cover_w_cast]

noncomputable section

def RatBankParameters.realParameters (c : RatBankParameters) : CoverBankParameters :=
  ⟨c.sample.realBox,c.strong,c.maximumScale.map (fun q => (q:ℝ)),c.dm,c.beta,c.L,c.mean,c.fan,
    c.degreeFraction,c.gain,c.coeff,c.qLower,c.zLower,c.orderLog.bound,c.cutBound,c.coreDecay.bound,c.branchBound⟩

theorem rat_bank_ac_cast (c : RatBankParameters) : (c.ac:ℝ)=c.realParameters.ac := by
  norm_num [RatBankParameters.ac,CoverBankParameters.ac,RatBankParameters.realParameters]
theorem rat_bank_dc_cast (c : RatBankParameters) : (c.dc:ℝ)=c.realParameters.dc := by
  norm_num [RatBankParameters.dc,CoverBankParameters.dc,rat_bank_ac_cast,RatBankParameters.realParameters]

theorem rat_bank_exp_of_log_bound {N a budget : ℝ} (hN : 0 < N) (hb : 0 < budget)
    (hlog : log (N/budget) ≤ a) : N*exp (-a) ≤ budget := by
  rw [log_div hN.ne' hb.ne'] at hlog
  calc
    _ = exp (log N-a) := by rw [sub_eq_add_neg,exp_add,exp_log hN]
    _ ≤ exp (log budget) := exp_le_exp.mpr (by linarith only [hlog])
    _ = _ := exp_log hb

end
end Cycle12
