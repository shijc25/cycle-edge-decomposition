import Cycle12.RationalBankSound
import Cycle12.CoverCapacityApplication

namespace Cycle12
open Real

def RatBankParameters.cost (c : RatBankParameters) : ℚ := if c.strong then 1 else 11/10
def RatBankParameters.branch (c : RatBankParameters) : ℚ :=
  max (c.dc/(1-c.degreeFraction)) (c.dm*ratCoverW c.sample.xl*ratCoverH c.sample.xl/ratCoverDen c.sample.xl)-c.cost*c.coeff

def ratRoutingDenom (a f b x : ℚ) : ℚ := a*ratCoverDen x+f*b*ratCoverH x*ratCoverW x
def ratRoutingK (a f b d x : ℚ) : ℚ := f*b*ratCoverH x*ratCoverW x*d/(a*ratRoutingDenom a f b x)

structure RatCapacityParameters where
  bank : RatBankParameters
  localCuts : Bool
  routeBeta : ℚ
  pUpper : ℚ
  weightLower : ℚ

def RatCapacityParameters.sizeLower (c : RatCapacityParameters) : ℚ :=
  2*(43/10)^3*c.bank.coeff*c.bank.sample.Plo*c.bank.sample.s0/(ratCoverW c.bank.sample.xh)^2

def RatCapacityParameters.factorLower (c : RatCapacityParameters) : ℚ :=
  2*(43/10)^3*c.bank.fan*c.routeBeta*ratCoverH c.bank.sample.xl*c.bank.branch*c.bank.sample.Plo*c.bank.sample.s0/
    (ratCoverW c.bank.sample.xh*(c.bank.coeff*ratCoverDen c.bank.sample.xl+c.bank.fan*c.routeBeta*ratCoverH c.bank.sample.xh*ratCoverW c.bank.sample.xh))

def RatCapacityParameters.pairBound (c : RatCapacityParameters) : ℚ :=
  c.bank.coeff^2*(43/10)^3*c.bank.sample.Plo^2/(3*ratCoverW c.bank.sample.xh)-(11/3)*c.bank.coeff*c.pUpper/c.bank.sample.s0

def RatCapacityParameters.fanBound (c : RatCapacityParameters) : ℚ :=
  c.bank.coeff*c.bank.fan*c.routeBeta*ratCoverH c.bank.sample.xl*c.bank.branch*(43/10)^3*c.bank.sample.Plo^2/
    (c.bank.coeff*ratCoverDen c.bank.sample.xl+c.bank.fan*c.routeBeta*ratCoverH c.bank.sample.xh*ratCoverW c.bank.sample.xh)-
    (3*ratRoutingK c.bank.coeff c.bank.fan c.routeBeta c.bank.branch c.bank.sample.xh+1)*c.bank.coeff*c.pUpper/(2*c.bank.sample.s0)

def RatCapacityParameters.largeBound (c : RatCapacityParameters) : ℚ :=
  c.bank.fan*c.bank.beta*(1/125)*c.weightLower-c.bank.coeff*c.pUpper/(2*c.bank.sample.s0)

def RatCapacityParameters.NumericValid (c : RatCapacityParameters) : Prop :=
  0 < c.routeBeta ∧ 0 ≤ c.bank.branch ∧ c.bank.fan ≤ 1 ∧ 1 ≤ c.bank.fan*c.bank.L ∧
  c.bank.sample.Pu*ratCoverW c.bank.sample.xh ≤ c.pUpper ∧
  c.weightLower ≤ 2*(43/10)^3*c.bank.sample.Plo^2*ratCoverH c.bank.sample.xl*c.bank.sample.s0/ratCoverDen c.bank.sample.xl ∧
  24 ≤ c.sizeLower ∧ 1 ≤ c.factorLower ∧ 1-c.bank.sample.pl ≤ c.pairBound ∧
  1-c.bank.sample.pl ≤ c.fanBound ∧
  (c.localCuts=true → 1-c.bank.sample.pl ≤ c.largeBound) ∧
  (c.localCuts=false → c.routeBeta=c.bank.beta)

instance instDecidableRatCapacityNumeric (c : RatCapacityParameters) : Decidable c.NumericValid := by
  unfold RatCapacityParameters.NumericValid
  infer_instance

noncomputable section

def RatCapacityParameters.realParameters (c : RatCapacityParameters) : CoverCapacityParameters :=
  ⟨c.bank.realParameters,c.localCuts,c.routeBeta,c.pUpper,c.weightLower⟩

theorem rat_bank_branch_cast (c : RatBankParameters) : (c.branch:ℝ)=c.realParameters.branch := by
  cases he : c.strong <;>
    norm_num [RatBankParameters.branch,CoverBankParameters.branch,RatBankParameters.cost,
      CoverBankParameters.cost,coverBankDegreeRatio,rat_bank_dc_cast,
      rat_cover_w_cast,rat_cover_h_cast,rat_cover_den_cast,RatBankParameters.realParameters,RatSamplingBox.realBox,he]

theorem rat_routing_denom_cast (a f b x : ℚ) :
    (ratRoutingDenom a f b x:ℝ)=coverRoutingDenom a f b x := by
  norm_num [ratRoutingDenom,coverRoutingDenom,rat_cover_w_cast,rat_cover_h_cast,rat_cover_den_cast]

theorem rat_routing_k_cast (a f b d x : ℚ) :
    (ratRoutingK a f b d x:ℝ)=coverRoutingK a f b d x := by
  norm_num [ratRoutingK,coverRoutingK,rat_routing_denom_cast,rat_cover_w_cast,rat_cover_h_cast]

theorem rat_capacity_size_cast (c : RatCapacityParameters) :
    (c.sizeLower:ℝ)=c.realParameters.sizeLower := by
  norm_num [RatCapacityParameters.sizeLower,CoverCapacityParameters.sizeLower,coverRoutingSizeLower,
    RatCapacityParameters.realParameters,RatBankParameters.realParameters,RatSamplingBox.realBox,rat_cover_w_cast]

theorem rat_capacity_factor_cast (c : RatCapacityParameters) :
    (c.factorLower:ℝ)=c.realParameters.factorLower := by
  norm_num [RatCapacityParameters.factorLower,CoverCapacityParameters.factorLower,coverRoutingFactorLower,coverRoutingDenomBox,
    RatCapacityParameters.realParameters,rat_bank_branch_cast,RatBankParameters.realParameters,RatSamplingBox.realBox,
    rat_cover_w_cast,rat_cover_h_cast,rat_cover_den_cast]

theorem rat_capacity_pair_cast (c : RatCapacityParameters) :
    (c.pairBound:ℝ)=c.realParameters.pairBound := by
  norm_num [RatCapacityParameters.pairBound,CoverCapacityParameters.pairBound,coverRoutingPairBox,
    RatCapacityParameters.realParameters,RatBankParameters.realParameters,RatSamplingBox.realBox,rat_cover_w_cast]

theorem rat_capacity_fan_cast (c : RatCapacityParameters) :
    (c.fanBound:ℝ)=c.realParameters.fanBound := by
  norm_num [RatCapacityParameters.fanBound,CoverCapacityParameters.fanBound,coverRoutingFanBox,coverRoutingDenomBox,
    RatCapacityParameters.realParameters,rat_bank_branch_cast,rat_routing_k_cast,RatBankParameters.realParameters,RatSamplingBox.realBox,
    rat_cover_w_cast,rat_cover_h_cast,rat_cover_den_cast]

theorem rat_capacity_large_cast (c : RatCapacityParameters) :
    (c.largeBound:ℝ)=c.realParameters.largeBound := by
  norm_num [RatCapacityParameters.largeBound,CoverCapacityParameters.largeBound,coverRoutingLargeBox,
    RatCapacityParameters.realParameters,RatBankParameters.realParameters,RatSamplingBox.realBox]

theorem rat_capacity_parameters_sound (c : RatCapacityParameters) (hc : c.NumericValid)
    (hb : c.bank.realParameters.Valid) : c.realParameters.Valid := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11⟩ := hc
  refine ⟨hb,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals dsimp only [RatCapacityParameters.realParameters,RatBankParameters.realParameters,RatSamplingBox.realBox]
  · exact_mod_cast h0
  · simpa only [rat_bank_branch_cast,RatCapacityParameters.realParameters,RatBankParameters.realParameters,RatSamplingBox.realBox] using (Rat.cast_nonneg (K:=ℝ)).mpr h1
  · exact_mod_cast h2
  · exact_mod_cast h3
  · simpa only [Rat.cast_mul,rat_cover_w_cast,RatCapacityParameters.realParameters,RatBankParameters.realParameters,RatSamplingBox.realBox] using (Rat.cast_le (K:=ℝ)).mpr h4
  · simpa only [Rat.cast_mul,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat,rat_cover_h_cast,rat_cover_den_cast,RatCapacityParameters.realParameters,RatBankParameters.realParameters,RatSamplingBox.realBox]
      using (Rat.cast_le (K:=ℝ)).mpr h5
  · simpa only [Rat.cast_ofNat,rat_capacity_size_cast,RatCapacityParameters.realParameters,RatBankParameters.realParameters,RatSamplingBox.realBox] using (Rat.cast_le (K:=ℝ)).mpr h6
  · simpa only [Rat.cast_one,rat_capacity_factor_cast,RatCapacityParameters.realParameters,RatBankParameters.realParameters,RatSamplingBox.realBox] using (Rat.cast_le (K:=ℝ)).mpr h7
  · simpa only [Rat.cast_sub,Rat.cast_one,rat_capacity_pair_cast,RatCapacityParameters.realParameters,RatBankParameters.realParameters,RatSamplingBox.realBox] using (Rat.cast_le (K:=ℝ)).mpr h8
  · simpa only [Rat.cast_sub,Rat.cast_one,rat_capacity_fan_cast,RatCapacityParameters.realParameters,RatBankParameters.realParameters,RatSamplingBox.realBox] using (Rat.cast_le (K:=ℝ)).mpr h9
  · intro he
    simpa only [Rat.cast_sub,Rat.cast_one,rat_capacity_large_cast,RatCapacityParameters.realParameters,RatBankParameters.realParameters,RatSamplingBox.realBox] using (Rat.cast_le (K:=ℝ)).mpr (h10 he)
  · intro he
    exact_mod_cast h11 he

end
end Cycle12
