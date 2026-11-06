import Cycle12.DirectBankParameters
import Cycle12.RationalBankParameters

namespace Cycle12
open Real Cycle13

structure RatDirectParameters where
  sample : RatSamplingBox
  dm : ℚ
  beta : ℚ
  L : ℚ
  mean : ℚ
  fan : ℚ
  router : ℚ
  epsilon : ℚ
  zLower : ℚ
  orderLog : RatScaledLogUpper
  cutDecay : RatDecayCertificate
  rLower : ℚ
  weightLower : ℚ

def ratDirectCubic (b x s P : ℚ) : ℚ :=
  b^3*2*(43/10)^6*P^4*(ratCoverH x)^3*s*ratCoverW x/(ratCoverDen x)^3

def RatDirectParameters.cutExponent (c : RatDirectParameters) : ℚ := 2*c.epsilon^2*c.dm*c.zLower
def RatDirectParameters.cutBound (c : RatDirectParameters) : ℚ :=
  c.cutExponent/(c.cutExponent-2*c.orderLog.bound)*c.cutDecay.bound

def RatDirectParameters.NumericValid (c : RatDirectParameters) : Prop :=
  c.sample.Valid ∧ 2 ≤ c.sample.Nlo ∧ 0 < c.dm ∧ 0 < c.beta ∧
  0 < c.mean ∧ c.mean < 1 ∧ 0 < c.fan ∧ 0 < c.router ∧ 0 ≤ c.epsilon ∧
  c.fan ≤ c.mean-c.epsilon ∧ c.router ≤ 1-c.mean-c.epsilon ∧ 1 ≤ c.fan*c.L ∧
  c.zLower ≤ 2*(43/10)^3*c.sample.Plo*ratCoverH c.sample.xl*c.sample.s0/
    (ratCoverW c.sample.xh*ratCoverDen c.sample.xl) ∧
  1 ≤ c.beta*c.zLower ∧
  c.orderLog.argument=ratRoutingOrder c.sample.xh c.sample.s0 c.sample.Pu ∧
  2 ≤ c.orderLog.bound ∧ 0 < c.cutExponent-2*c.orderLog.bound ∧
  c.cutDecay.exponent=c.cutExponent-2*c.orderLog.bound ∧ c.cutDecay.scaleLower=1 ∧
  2*c.cutBound < 1 ∧
  c.rLower ≤ 2*c.sample.s0*ratCoverDen c.sample.xh/(ratCoverH c.sample.xh*ratCoverW c.sample.xh) ∧
  4096 ≤ c.rLower/(c.router*c.beta) ∧
  c.weightLower ≤ 2*(43/10)^3*c.sample.Plo^2*ratCoverH c.sample.xl*c.sample.s0/ratCoverDen c.sample.xl ∧
  1 ≤ c.fan*c.beta*c.weightLower ∧
  324 ≤ ratDirectCubic (c.router*c.beta) c.sample.xl c.sample.s0 c.sample.Plo

instance instDecidableRatDirectNumeric (c : RatDirectParameters) : Decidable c.NumericValid := by
  unfold RatDirectParameters.NumericValid
  infer_instance

theorem rat_direct_cubic_cast (b x s P : ℚ) :
    (ratDirectCubic b x s P:ℝ)=coverDirectCubic b x s P := by
  norm_num [ratDirectCubic,coverDirectCubic,rat_cover_h_cast,rat_cover_w_cast,rat_cover_den_cast]

noncomputable section

def RatDirectParameters.realParameters (c : RatDirectParameters) : DirectBankParameters :=
  ⟨c.sample.realBox,c.dm,c.beta,c.L,c.mean,c.fan,c.router,c.epsilon,c.zLower,c.orderLog.bound,
    c.cutBound,c.rLower,c.weightLower⟩

theorem rat_direct_parameters_sound (c : RatDirectParameters) (hc : c.NumericValid)
    (hOrder : c.orderLog.Valid) (hCut : c.cutDecay.Valid) : c.realParameters.Valid := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24⟩ := hc
  have hOL := rat_scaled_log_upper_sound c.orderLog hOrder
  rw [h14,rat_routing_order_cast] at hOL
  have hCD := rat_decay_certificate_sound c.cutDecay hCut (1:ℝ) (by rw [h18]; norm_num)
  rw [h17] at hCD
  simp only [mul_one] at hCD
  have hA : (0:ℝ) ≤ (c.cutExponent:ℝ) := by
    have hh : (0:ℚ) < c.cutExponent := by linarith only [h15,h16]
    exact_mod_cast hh.le
  have hgap : (0:ℝ) < ((c.cutExponent-2*c.orderLog.bound:ℚ):ℝ) := by exact_mod_cast h16
  have hcut := mul_le_mul_of_nonneg_left hCD (div_nonneg hA hgap.le)
  have hcut' :
      (c.cutExponent:ℝ)/((c.cutExponent-2*c.orderLog.bound:ℚ):ℝ)*
        exp (-((c.cutExponent-2*c.orderLog.bound:ℚ):ℝ)) ≤ (c.cutBound:ℝ) := by
    simpa only [RatDirectParameters.cutBound,Rat.cast_mul,Rat.cast_div] using hcut
  refine ⟨rat_sampling_box_sound c.sample h0,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,hOL,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals dsimp only [RatDirectParameters.realParameters,RatSamplingBox.realBox]
  · exact_mod_cast h1
  · exact_mod_cast h2
  · exact_mod_cast h3
  · exact_mod_cast h4
  · exact_mod_cast h5
  · exact_mod_cast h6
  · exact_mod_cast h7
  · exact_mod_cast h8
  · exact_mod_cast h9
  · exact_mod_cast h10
  · exact_mod_cast h11
  · have hh := (Rat.cast_le (K:=ℝ)).mpr h12
    simpa only [Rat.cast_div,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat,rat_cover_h_cast,rat_cover_den_cast,rat_cover_w_cast] using hh
  · exact_mod_cast h13
  · exact_mod_cast h15
  · have hh := (Rat.cast_lt (K:=ℝ)).mpr h16
    simpa only [RatDirectParameters.cutExponent,Rat.cast_sub,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_zero] using hh
  · simpa only [RatDirectParameters.cutExponent,Rat.cast_sub,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat] using hcut'
  · exact_mod_cast h19
  · have hh := (Rat.cast_le (K:=ℝ)).mpr h20
    simpa only [Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat,rat_cover_h_cast,rat_cover_den_cast,rat_cover_w_cast] using hh
  · exact_mod_cast h21
  · have hh := (Rat.cast_le (K:=ℝ)).mpr h22
    simpa only [Rat.cast_div,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat,rat_cover_h_cast,rat_cover_den_cast] using hh
  · exact_mod_cast h23
  · have hh := (Rat.cast_le (K:=ℝ)).mpr h24
    simpa only [Rat.cast_ofNat,rat_direct_cubic_cast,Rat.cast_mul] using hh

end
end Cycle12
