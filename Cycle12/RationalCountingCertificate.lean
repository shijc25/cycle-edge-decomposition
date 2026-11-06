import Cycle12.CoverCountingExponent
import Cycle12.Foundations.RationalBounds

namespace Cycle12
open Real Cycle13

structure RatCountingCertificate where
  theta : ℚ
  pl : ℚ
  slope : ℚ
  intercept : ℚ
  D : ℚ
  M : ℚ
  aa : ℚ
  expTheta : ℚ
  expCount : ℚ
  logCount : ℚ
  thetaTerms : ℕ
  countTerms : ℕ
  slopeTerms : ℕ
  logTerms : ℕ

def RatCountingCertificate.Valid (c : RatCountingCertificate) : Prop :=
  0 < c.theta ∧ 0 ≤ c.pl ∧ 0 < c.slope ∧ 0 ≤ c.intercept ∧
  0 < c.D ∧ 0 < c.M ∧ 0 < c.aa ∧ 1 ≤ c.expTheta ∧ 0 ≤ c.expCount ∧
  c.theta < c.thetaTerms+2 ∧ ratExpUpper c.theta c.thetaTerms ≤ c.expTheta ∧
  (if c.pl=0 then c.expTheta-1 ≤ c.theta*c.slope else
    ratLogUpper ((c.pl*(c.expTheta-1))/(2+c.pl*(c.expTheta-1))) c.slopeTerms ≤ c.theta*c.pl*c.slope) ∧
  0 ≤ c.theta*(1-c.slope*c.pl) ∧ c.theta*(1-c.slope*c.pl) < c.countTerms+2 ∧
  ratExpUpper (c.theta*(1-c.slope*c.pl)) c.countTerms ≤ c.expCount ∧
  ratLogUpper (c.expCount/(2+c.expCount)) c.logTerms ≤ c.logCount ∧
  c.aa ≤ c.theta*c.intercept*c.D-c.M*c.logCount

instance instDecidableRatCountingValid (c : RatCountingCertificate) : Decidable c.Valid := by
  unfold RatCountingCertificate.Valid
  infer_instance

noncomputable section

def RatCountingCertificate.Sound (c : RatCountingCertificate) : Prop :=
  (∀ p residual : ℝ, 0 ≤ p → (c.pl:ℝ) ≤ p → residual ≤ p →
    1-residual+residual*exp (c.theta:ℝ) ≤ exp ((c.theta:ℝ)*(c.slope:ℝ)*p)) ∧
  ∀ {R z p : ℝ} {t : ℕ}, 0 < R → (c.D:ℝ)*R ≤ z → (c.pl:ℝ) ≤ p →
    (t:ℝ) ≤ (c.M:ℝ)*R →
    2*exp (-(c.theta:ℝ)*((c.intercept:ℝ)*z))*
      (1+exp ((c.theta:ℝ)-(c.theta:ℝ)*(c.slope:ℝ)*p))^t ≤ 2*exp (-(c.aa:ℝ)*R)

theorem rat_counting_certificate_sound (c : RatCountingCertificate) (hc : c.Valid) : c.Sound := by
  obtain ⟨ht,hpl,hs,hi,hD,hM,haa,hE1,hE2,htn,hEt,hsl,hcount0,hcountn,hEc,hlog,hbound⟩ := hc
  have htR : (0:ℝ) < (c.theta:ℝ) := by exact_mod_cast ht
  have htheta := (ratExp_bounds ht.le c.thetaTerms htn).2.trans ((Rat.cast_le (K:=ℝ)).mpr hEt)
  have hlogSlope := (ratLog_argument_bounds
    (show (1:ℚ) ≤ 1+c.pl*(c.expTheta-1) by
      exact le_add_of_nonneg_right (mul_nonneg hpl (sub_nonneg.mpr hE1))) c.slopeTerms).2
  have harg : 0 < 1+(c.pl:ℝ)*(exp (c.theta:ℝ)-1) := by
    have hpR : (0:ℝ) ≤ (c.pl:ℝ) := by exact_mod_cast hpl
    have heR := sub_nonneg.mpr (one_le_exp_iff.mpr htR.le)
    positivity
  have hlogSlopeActual : log (1+(c.pl:ℝ)*(exp (c.theta:ℝ)-1)) ≤
      (ratLogUpper (c.pl*(c.expTheta-1)/(2+c.pl*(c.expTheta-1))) c.slopeTerms:ℝ) := by
    have hargEq : (1+c.pl*(c.expTheta-1)-1)/(1+c.pl*(c.expTheta-1)+1)=
        c.pl*(c.expTheta-1)/(2+c.pl*(c.expTheta-1)) := by ring
    rw [hargEq] at hlogSlope
    apply (log_le_log harg ?_).trans hlogSlope
    push_cast
    gcongr
  have hcount := (ratExp_bounds hcount0 c.countTerms hcountn).2.trans ((Rat.cast_le (K:=ℝ)).mpr hEc)
  have hlogCount := (ratLog_argument_bounds
    (show (1:ℚ) ≤ 1+c.expCount by linarith only [hE2]) c.logTerms).2
  have hcountEq : (1+c.expCount-1)/(1+c.expCount+1)=c.expCount/(2+c.expCount) := by ring
  rw [hcountEq] at hlogCount
  have hlogActual : log (1+exp ((c.theta:ℝ)*(1-(c.slope:ℝ)*(c.pl:ℝ)))) ≤ (c.logCount:ℝ) := by
    have hh := hlogCount.trans ((Rat.cast_le (K:=ℝ)).mpr hlog)
    apply (log_le_log (by positivity) ?_).trans hh
    push_cast at hcount ⊢
    exact add_le_add le_rfl hcount
  constructor
  · intro p residual hp hpp hr
    by_cases hp0 : c.pl=0
    · rw [if_pos hp0] at hsl
      apply fixed_count_mgf_from_zero_lower hp hr htR
      have hh := (Rat.cast_le (K:=ℝ)).mpr hsl
      push_cast at hh
      linarith only [htheta,hh]
    · rw [if_neg hp0] at hsl
      apply fixed_count_mgf_from_lower_sample (by exact_mod_cast lt_of_le_of_ne hpl (Ne.symm hp0)) hpp hr htR
      apply (div_le_iff₀ (mul_pos htR (by exact_mod_cast lt_of_le_of_ne hpl (Ne.symm hp0)))).mpr
      have hh := hlogSlopeActual.trans ((Rat.cast_le (K:=ℝ)).mpr hsl)
      push_cast at hh
      nlinarith only [hh]
  · intro R z p t hR hDz hpp hmarks
    apply counting_union_exponent_bound hR hDz hpp htR.le (by exact_mod_cast hs.le)
      (by exact_mod_cast hi) hmarks hlogActual
    have hh := (Rat.cast_le (K:=ℝ)).mpr hbound
    simpa only [Rat.cast_sub,Rat.cast_mul] using hh

end
end Cycle12
