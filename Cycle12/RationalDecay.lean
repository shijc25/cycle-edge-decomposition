import Cycle12.MajorityExponentialCertificate

namespace Cycle12
open Real Cycle13

structure RatDecayCertificate where
  exponent : ℚ
  scaleLower : ℚ
  expPoint : ℚ
  reciprocal : ℚ
  bound : ℚ
  terms : ℕ

def RatDecayCertificate.Valid (c : RatDecayCertificate) : Prop :=
  0 ≤ c.exponent ∧ 0 ≤ c.expPoint ∧ 2*c.expPoint ≤ c.exponent*c.scaleLower ∧
  0 ≤ c.reciprocal ∧ 1 ≤ c.reciprocal*ratExpPartial c.expPoint c.terms ∧ c.reciprocal^2 ≤ c.bound

instance instDecidableRatDecayValid (c : RatDecayCertificate) : Decidable c.Valid := by
  unfold RatDecayCertificate.Valid
  infer_instance

noncomputable section

def RatDecayCertificate.Sound (c : RatDecayCertificate) : Prop :=
  ∀ R : ℝ, (c.scaleLower:ℝ) ≤ R → exp (-(c.exponent:ℝ)*R) ≤ (c.bound:ℝ)

theorem rat_decay_certificate_sound (c : RatDecayCertificate) (hc : c.Valid) : c.Sound := by
  obtain ⟨he,hp,hq,hr,hpart,hb⟩ := hc
  have hbase := rational_negative_exp_upper c.terms hp hq hr hpart
  have hbR := (Rat.cast_le (K:=ℝ)).mpr hb
  push_cast at hbase hbR
  intro R hR
  have hmono := mul_le_mul_of_nonneg_left hR (show (0:ℝ) ≤ (c.exponent:ℝ) by exact_mod_cast he)
  apply (exp_le_exp.mpr (show -(c.exponent:ℝ)*R ≤ -((c.exponent:ℝ)*(c.scaleLower:ℝ)) by
    linarith only [hmono])).trans
  exact hbase.trans hbR

end
end Cycle12
