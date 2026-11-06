import Cycle12.CoverBankApplication
import Cycle12.CoverRoutingLarge

namespace Cycle12
open Real Finset SimpleGraph Cycle13
noncomputable section

structure CoverCapacityParameters where
  bank : CoverBankParameters
  localCuts : Bool
  routeBeta : ℝ
  pUpper : ℝ
  weightLower : ℝ

def CoverCapacityParameters.sizeLower (c : CoverCapacityParameters) : ℝ :=
  coverRoutingSizeLower c.bank.coeff c.bank.sample.xl c.bank.sample.xh c.bank.sample.s0 c.bank.sample.Plo

def CoverCapacityParameters.factorLower (c : CoverCapacityParameters) : ℝ :=
  coverRoutingFactorLower c.bank.coeff c.bank.fan c.routeBeta c.bank.branch
    c.bank.sample.xl c.bank.sample.xh c.bank.sample.s0 c.bank.sample.Plo

def CoverCapacityParameters.pairBound (c : CoverCapacityParameters) : ℝ :=
  coverRoutingPairBox c.bank.coeff c.bank.sample.xl c.bank.sample.xh c.bank.sample.s0 c.bank.sample.Plo c.pUpper

def CoverCapacityParameters.fanBound (c : CoverCapacityParameters) : ℝ :=
  coverRoutingFanBox c.bank.coeff c.bank.fan c.routeBeta c.bank.branch
    c.bank.sample.xl c.bank.sample.xh c.bank.sample.s0 c.bank.sample.Plo c.pUpper

def CoverCapacityParameters.largeBound (c : CoverCapacityParameters) : ℝ :=
  coverRoutingLargeBox c.bank.coeff c.bank.fan c.bank.beta (1/125) c.weightLower c.pUpper c.bank.sample.s0

structure CoverCapacityParameters.Valid (c : CoverCapacityParameters) : Prop where
  bank_valid : c.bank.Valid
  route_positive : 0 < c.routeBeta
  branch_nonneg : 0 ≤ c.bank.branch
  fan_upper : c.bank.fan ≤ 1
  anchoring : 1 ≤ c.bank.fan*c.bank.L
  p_upper : c.bank.sample.Pu*coverScaleW c.bank.sample.xh ≤ c.pUpper
  weight_lower : c.weightLower ≤ 2*(43/10)^3*c.bank.sample.Plo^2*coverScaleH c.bank.sample.xl*c.bank.sample.s0/coverScaleDen c.bank.sample.xl
  size_lower : 24 ≤ c.sizeLower
  factor_lower : 1 ≤ c.factorLower
  pair_capacity : 1-c.bank.sample.pl ≤ c.pairBound
  fan_capacity : 1-c.bank.sample.pl ≤ c.fanBound
  large_capacity : c.localCuts=true → 1-c.bank.sample.pl ≤ c.largeBound
  global_beta : c.localCuts=false → c.routeBeta=c.bank.beta

end
end Cycle12
