import Cycle12.CappedLabelEntropy
import Cycle12.Foundations.RationalPowers

namespace Cycle12
open Real Cycle13

structure RatScaledLogUpper where
  argument : ℚ
  split : ℕ
  terms : ℕ
  bound : ℚ

def RatScaledLogUpper.Valid (c : RatScaledLogUpper) : Prop :=
  1 ≤ c.argument/2^c.split ∧
  c.split*logTwoUpper+ratLogUpper ((c.argument/2^c.split-1)/(c.argument/2^c.split+1)) c.terms ≤ c.bound

instance instDecidableRatScaledLogUpperValid (c : RatScaledLogUpper) : Decidable c.Valid := by
  unfold RatScaledLogUpper.Valid
  infer_instance

theorem rat_scaled_log_upper_sound (c : RatScaledLogUpper) (hc : c.Valid) :
    log (c.argument:ℝ) ≤ (c.bound:ℝ) := by
  have hu := (ratLog_argument_bounds hc.1 c.terms).2
  have htwo : log 2 ≤ (logTwoUpper:ℝ) := by simpa [logTwoUpper] using log_two_24_digits.2
  have hy : (0:ℝ) < ((c.argument/2^c.split:ℚ):ℝ) := by
    have hh : (1:ℝ) ≤ ((c.argument/2^c.split:ℚ):ℝ) := by exact_mod_cast hc.1
    linarith only [hh]
  have hid : (2:ℝ)^c.split*((c.argument/2^c.split:ℚ):ℝ)=(c.argument:ℝ) := by
    push_cast
    field_simp
  calc
    _ = log ((2:ℝ)^c.split*((c.argument/2^c.split:ℚ):ℝ)) := by rw [hid]
    _ = (c.split:ℝ)*log 2+log ((c.argument/2^c.split:ℚ):ℝ) := by
      rw [log_mul (by positivity) hy.ne',log_pow]
    _ ≤ (c.split:ℝ)*(logTwoUpper:ℝ)+
        (ratLogUpper ((c.argument/2^c.split-1)/(c.argument/2^c.split+1)) c.terms:ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg _)) hu
    _ ≤ _ := by
      simpa only [Rat.cast_add,Rat.cast_mul,Rat.cast_natCast] using (Rat.cast_le (K:=ℝ)).mpr hc.2

structure RatLabelEntropyCertificate where
  rho : ℚ
  left : RatScaledLogUpper
  right : RatScaledLogUpper
  bound : ℚ

def RatLabelEntropyCertificate.Valid (c : RatLabelEntropyCertificate) : Prop :=
  0 < c.rho ∧
  (if c.rho < 1/2 then
    c.left.Valid ∧ c.right.Valid ∧ c.left.argument=1/c.rho ∧ c.right.argument=1/(1-c.rho) ∧
    c.rho*c.left.bound+(1-c.rho)*c.right.bound ≤ c.bound
  else logTwoUpper ≤ c.bound)

instance instDecidableRatLabelEntropyValid (c : RatLabelEntropyCertificate) : Decidable c.Valid := by
  unfold RatLabelEntropyCertificate.Valid
  infer_instance

noncomputable section

theorem rat_label_entropy_certificate_sound (c : RatLabelEntropyCertificate) (hc : c.Valid) :
    0 ≤ cappedLabelEntropy (c.rho:ℝ) ∧ cappedLabelEntropy (c.rho:ℝ) ≤ (c.bound:ℝ) := by
  have hr : (0:ℝ) < (c.rho:ℝ) := by exact_mod_cast hc.1
  have hn : 0 ≤ cappedLabelEntropy (c.rho:ℝ) := by
    unfold cappedLabelEntropy
    split_ifs with hh
    · exact binEntropy_nonneg hr.le (by linarith only [hh])
    · exact (log_pos (by norm_num : (1:ℝ) < 2)).le
  refine ⟨hn,?_⟩
  by_cases hsmall : c.rho < 1/2
  · have hh := hc.2
    rw [if_pos hsmall] at hh
    obtain ⟨hl,hright,hlarg,hrarg,hbound⟩ := hh
    have hleft := rat_scaled_log_upper_sound c.left hl
    have hright := rat_scaled_log_upper_sound c.right hright
    rw [hlarg] at hleft
    rw [hrarg] at hright
    have hsmallR : (c.rho:ℝ) < 1/2 := by
      have hh := (Rat.cast_lt (K:=ℝ)).mpr hsmall
      norm_num at hh ⊢
      exact hh
    have hcomp : 0 ≤ 1-(c.rho:ℝ) := by linarith only [hsmallR]
    have hsum := add_le_add (mul_le_mul_of_nonneg_left hleft hr.le) (mul_le_mul_of_nonneg_left hright hcomp)
    have hboundR := (Rat.cast_le (K:=ℝ)).mpr hbound
    push_cast at hsum hboundR
    rw [cappedLabelEntropy,if_pos hsmallR.le]
    unfold binEntropy
    simpa only [one_div] using hsum.trans hboundR
  · have hh := hc.2
    rw [if_neg hsmall] at hh
    have htwo : log 2 ≤ (logTwoUpper:ℝ) := by simpa [logTwoUpper] using log_two_24_digits.2
    have hle : cappedLabelEntropy (c.rho:ℝ) ≤ log 2 := by
      unfold cappedLabelEntropy
      split_ifs <;> first | exact binEntropy_le_log_two | exact le_rfl
    exact hle.trans (htwo.trans ((Rat.cast_le (K:=ℝ)).mpr hh))

end
end Cycle12
