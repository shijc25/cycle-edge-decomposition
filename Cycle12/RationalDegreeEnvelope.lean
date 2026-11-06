import Cycle12.RationalMomentCertificate
import Cycle12.CoverDegreeCertificate
import Cycle12.MajorityExponentialCertificate

namespace Cycle12
open Finset Real Cycle13 SimpleGraph
open OAI.ErdosGallai.Sampling

def ratCoverH (x : ℚ) : ℚ := 103/250+351/200*x
def ratCoverDen (x : ℚ) : ℚ := 1-33/125*ratCoverW x
def ratCoverMu (x : ℚ) : ℚ := (1+447/100*x)/ratCoverH x

theorem rat_cover_h_cast (x : ℚ) : (ratCoverH x:ℝ)=coverScaleH (x:ℝ) := by
  norm_num [ratCoverH,coverScaleH]
theorem rat_cover_den_cast (x : ℚ) : (ratCoverDen x:ℝ)=coverScaleDen (x:ℝ) := by
  norm_num [ratCoverDen,rat_cover_w_cast,coverScaleDen]
theorem rat_cover_mu_cast (x : ℚ) : (ratCoverMu x:ℝ)=coverScaleMu (x:ℝ) := by
  norm_num [ratCoverMu,rat_cover_h_cast,coverScaleMu]

structure RatDegreeEnvelope where
  sourceRow : ℕ
  inputs : RatMomentCertificate
  dm : ℚ
  mu : ℚ
  zbase : ℚ
  rate : ℚ
  expPoint : ℚ
  reciprocal : ℚ
  probability : ℚ
  logTerms : ℕ
  expTerms : ℕ

def RatDegreeEnvelope.NumericValid (c : RatDegreeEnvelope) : Prop :=
  0 < c.dm ∧ c.dm < c.mu ∧ c.mu ≤ ratCoverMu c.inputs.xl ∧
  c.zbase ≤ 2*(43/10)^3*c.inputs.Plo*ratCoverH c.inputs.xl*c.inputs.s0/
    (ratCoverW c.inputs.xh*ratCoverDen c.inputs.xl) ∧
  0 ≤ c.rate ∧ 3 ≤ c.rate*c.zbase ∧
  c.rate ≤ c.mu-c.dm-c.dm*ratLogUpper ((c.mu/c.dm-1)/(c.mu/c.dm+1)) c.logTerms ∧
  0 ≤ c.expPoint ∧ 2*c.expPoint ≤ c.rate*c.zbase ∧ 0 ≤ c.reciprocal ∧
  1 ≤ c.reciprocal*ratExpPartial c.expPoint c.expTerms ∧
  (4*(43/10)^3*c.inputs.s0^2/(ratCoverW c.inputs.xh)^3)*c.reciprocal^2 ≤ c.probability

instance instDecidableRatDegreeEnvelopeNumericValid (c : RatDegreeEnvelope) : Decidable c.NumericValid := by
  unfold RatDegreeEnvelope.NumericValid
  infer_instance

theorem rational_degree_rate_lower {mu dm rate : ℚ} (n : ℕ)
    (hdm : 0 < dm) (hgap : dm < mu)
    (hrate : rate ≤ mu-dm-dm*ratLogUpper ((mu/dm-1)/(mu/dm+1)) n) :
    (rate:ℝ) ≤ (mu:ℝ)-(dm:ℝ)-(dm:ℝ)*log ((mu:ℝ)/(dm:ℝ)) := by
  have hq : 1 ≤ mu/dm := (one_le_div hdm).mpr hgap.le
  have hu := (ratLog_argument_bounds hq n).2
  simp only [Rat.cast_div] at hu
  have hm := mul_le_mul_of_nonneg_left hu (show (0:ℝ) ≤ (dm:ℝ) by exact_mod_cast hdm.le)
  have hr := (Rat.cast_le (K:=ℝ)).mpr hrate
  simp only [Rat.cast_sub,Rat.cast_mul] at hr
  linarith only [hr,hm]

noncomputable section
attribute [local instance] Classical.propDecidable

def RatDegreeEnvelope.Sound (c : RatDegreeEnvelope) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    {x s : ℝ} {k : ℕ}, 0 < x → (c.inputs.xl:ℝ) ≤ x → x ≤ (c.inputs.xh:ℝ) →
    (c.inputs.s0:ℝ) ≤ s →
    (Fintype.card V:ℝ)=4*(43/10)^3*s^2/(coverScaleW x)^3 →
    k=⌊coverSampleP x*(Fintype.card V:ℝ)⌋₊ →
    (∀ v, coverScaleMu x*coverScaleZ x s (((k:ℝ)/(Fintype.card V:ℝ))/coverScaleW x) ≤
      ((k:ℝ)/(Fintype.card V:ℝ))*(neighborsIn G v univ).card) →
    (fixedSizeLaw (univ:Finset V) k).prob
      (fun T => ∃ v, ((neighborsIn G v T).card:ℝ) ≤
        (c.dm:ℝ)*coverScaleZ x s (((k:ℝ)/(Fintype.card V:ℝ))/coverScaleW x)) ≤ (c.probability:ℝ)

theorem rat_degree_envelope_sound (c : RatDegreeEnvelope) (hi : c.inputs.Valid)
    (hc : c.NumericValid) : c.Sound := by
  obtain ⟨hdm,hgap,hmu,hz,hr0,hscale,hr,hx0,hxq,hrec,hpartial,hbound⟩ := hc
  have hrR := rational_degree_rate_lower c.logTerms hdm hgap hr
  have he := rational_negative_exp_upper c.expTerms hx0 hxq hrec hpartial
  simp only [Rat.cast_mul] at he
  have hmuR : (c.mu:ℝ) ≤ coverScaleMu (c.inputs.xl:ℝ) := by
    simpa only [rat_cover_mu_cast] using (Rat.cast_le (K:=ℝ)).mpr hmu
  have hzR : (c.zbase:ℝ) ≤ 2*(43/10)^3*(c.inputs.Plo:ℝ)*coverScaleH (c.inputs.xl:ℝ)*(c.inputs.s0:ℝ)/
      (coverScaleW (c.inputs.xh:ℝ)*coverScaleDen (c.inputs.xl:ℝ)) := by
    simpa only [rat_cover_h_cast,rat_cover_w_cast,rat_cover_den_cast,Rat.cast_mul,Rat.cast_div,
      Rat.cast_pow,Rat.cast_ofNat] using (Rat.cast_le (K:=ℝ)).mpr hz
  have hbR : (4*(43/10:ℝ)^3*(c.inputs.s0:ℝ)^2/(coverScaleW (c.inputs.xh:ℝ))^3)*
      exp (-(c.rate:ℝ)*(c.zbase:ℝ)) ≤ (c.probability:ℝ) := by
    have hbase : 0 ≤ 4*(43/10:ℝ)^3*(c.inputs.s0:ℝ)^2/(coverScaleW (c.inputs.xh:ℝ))^3 := by
      unfold coverScaleW
      positivity
    rw [neg_mul]
    apply (mul_le_mul_of_nonneg_left he hbase).trans
    simpa only [rat_cover_w_cast,Rat.cast_mul,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat]
      using (Rat.cast_le (K:=ℝ)).mpr hbound
  intro V _ _ G x s k hxp hxl hxh hs hn hk hmean
  exact cover_degree_certificate_sound c.inputs.realCertificate.box (rat_moment_certificate_valid c.inputs hi).sampling
    (by exact_mod_cast hdm) (by exact_mod_cast hgap) hmuR hzR (by exact_mod_cast hr0) hrR
    (by exact_mod_cast hscale) hbR G hxp hxl hxh hs hn hk hmean

end
end Cycle12
