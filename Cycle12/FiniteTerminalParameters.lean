import Cycle12.TerminalWeightedBase
import Cycle12.RationalLabelEntropy

namespace Cycle12
open Real Cycle13

structure RatTerminalParameters where
  order : ℕ
  orderLog : RatScaledLogUpper
  bound : ℚ

def RatTerminalParameters.NumericValid (c : RatTerminalParameters) : Prop :=
  256 ≤ c.order ∧ c.orderLog.argument=(c.order:ℚ)/256 ∧
  (19/42+(3531487819961/1000000000000+c.orderLog.bound)/2:ℚ) ≤ c.bound

instance instDecidableRatTerminalNumeric (c : RatTerminalParameters) : Decidable c.NumericValid := by
  unfold RatTerminalParameters.NumericValid
  infer_instance

noncomputable section

theorem rat_terminal_parameters_sound (c : RatTerminalParameters) (hc : c.NumericValid)
    (hLog : c.orderLog.Valid) : WeightedAffineBound (c.bound:ℝ) c.order := by
  obtain ⟨h0,h1,h2⟩ := hc
  have hL := rat_scaled_log_upper_sound c.orderLog hLog
  rw [h1] at hL
  have horder : (0:ℝ) < c.order := by exact_mod_cast (show 0 < c.order by omega)
  simp only [Rat.cast_div,Rat.cast_natCast,Rat.cast_ofNat,log_div horder.ne' (by norm_num : (256:ℝ)≠0)] at hL
  have hpay := (Rat.cast_le (K:=ℝ)).mpr h2
  push_cast at hpay
  apply weightedAffine_mono_constant _
    (weightedAffine_harmonic_anchor (a:=256) (by norm_num) h0 terminal_weighted_affine_seven)
  linarith only [hL,harmonic_256_difference,hpay]

/-- A finite affine chain pays any graph whose actual average degree is
bounded by the certified cap. -/
theorem finite_average_bound {cap T : ℕ} {C budget : ℝ} (hT : 0 < T)
    (hchain : WeightedAffineBound C T) (hbudget : C+(cap:ℝ)/(2*T) ≤ budget)
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hdegree : 2*G.edgeSet.ncard ≤ cap*Fintype.card V) :
    ∃ P : CyclePacking G, P.weight ≤ budget*Fintype.card V := by
  obtain ⟨P,hP⟩ := hchain V G
  have hTR : (0:ℝ) < T := by exact_mod_cast hT
  have hd : 2*(G.edgeSet.ncard:ℝ) ≤ (cap:ℝ)*Fintype.card V := by exact_mod_cast hdegree
  have hdiv : (G.edgeSet.ncard:ℝ)/(T:ℝ) ≤ ((cap:ℝ)/(2*T))*(Fintype.card V:ℝ) := by
    apply (div_le_iff₀ hTR).mpr
    field_simp
    linarith only [hd]
  have hh := mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg (α:=ℝ) (Fintype.card V))
  exact ⟨P,by nlinarith only [hP,hdiv,hh]⟩

end
end Cycle12
