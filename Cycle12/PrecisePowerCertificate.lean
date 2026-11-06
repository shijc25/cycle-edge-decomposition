import Cycle12.Foundations.RationalPowers

namespace Cycle12
open Cycle13 Real

structure RatPrecisePowerUpper where
  exponent : ℚ
  integerPart : ℤ
  fraction : ℚ
  logTerms : ℕ
  logBound : ℚ
  expTerms : ℕ
  bound : ℚ
  deriving DecidableEq

def RatPrecisePowerUpper.Valid (c : RatPrecisePowerUpper) : Prop :=
  c.exponent=c.integerPart+c.fraction ∧ 0≤c.fraction ∧ c.fraction≤1 ∧
  ratLogUpper (1/3) c.logTerms≤c.logBound ∧
  c.logBound*c.fraction<c.expTerms+2 ∧
  (2:ℚ)^c.integerPart*ratExpUpper (c.logBound*c.fraction) c.expTerms≤c.bound

instance RatPrecisePowerUpper.instDecidableValid (c : RatPrecisePowerUpper) : Decidable c.Valid := by
  unfold RatPrecisePowerUpper.Valid
  infer_instance

theorem precise_power_upper_sound (c : RatPrecisePowerUpper) (hc : c.Valid) :
    (2:ℝ)^(c.exponent:ℝ)≤(c.bound:ℝ) := by
  obtain ⟨harg,hfraction,hfraction1,hlog,hN,hbound⟩ := hc
  have hl := (ratLog_argument_bounds (q:=2) (by norm_num) c.logTerms).2
  norm_num only [show ((2:ℚ)-1)/(2+1)=1/3 by norm_num,Rat.cast_ofNat] at hl
  have hu : log (2:ℝ)≤(c.logBound:ℝ) := hl.trans (by exact_mod_cast hlog)
  have hh := power_two_rational_bounds (x:=(c.exponent:ℝ)) (l:=0) (u:=c.logBound)
    c.integerPart hfraction (by exact_mod_cast harg) (by norm_num)
    (by simpa using (log_pos (by norm_num : (1:ℝ)<2)).le) hu c.expTerms hN
  exact hh.2.trans (by exact_mod_cast hbound)

end Cycle12
