import Cycle12.CoverEntropyExponent
import Cycle12.RationalCutBin

namespace Cycle12
open Real

structure RatCutEntropyCertificate where
  bin : RatCutBinCertificate
  entropy : RatLabelEntropyCertificate
  exponent : ℚ

def RatCutEntropyCertificate.NumericValid (c : RatCutEntropyCertificate) : Prop :=
  0 ≤ c.bin.residual.M ∧ 0 ≤ c.bin.gamma ∧
  c.exponent ≤ c.bin.residual.Dlo*c.bin.gamma-c.bin.residual.M*c.entropy.bound

instance instDecidableRatCutEntropyNumeric (c : RatCutEntropyCertificate) : Decidable c.NumericValid := by
  unfold RatCutEntropyCertificate.NumericValid
  infer_instance

noncomputable section

def RatCutEntropyCertificate.Sound (c : RatCutEntropyCertificate) : Prop :=
  ∀ (R z : ℝ) (t : ℕ), 0 ≤ R → (c.bin.residual.Dlo:ℝ)*R ≤ z →
    (t:ℝ) ≤ (c.bin.residual.M:ℝ)*R →
    exp ((t:ℝ)*cappedLabelEntropy (c.entropy.rho:ℝ))*(2*exp (-(c.bin.gamma:ℝ)*z)) ≤
      2*exp (-(c.exponent:ℝ)*R)

theorem rat_cut_entropy_certificate_sound (c : RatCutEntropyCertificate)
    (he : c.entropy.Valid) (hc : c.NumericValid) : c.Sound := by
  have hentropy := rat_label_entropy_certificate_sound c.entropy he
  intro R z t hR hD ht
  apply cover_entropy_union_exponent_bound hR hD (by exact_mod_cast hc.1)
    (by exact_mod_cast hc.2.1) ht hentropy.1 hentropy.2
  exact_mod_cast hc.2.2

theorem rat_cut_entropy_uniform_raw_tail (c : RatCutEntropyCertificate)
    (hc : c.NumericValid) {R z : ℝ} (hR : 0 ≤ R) (hD : (c.bin.residual.Dlo:ℝ)*R ≤ z) :
    2*exp (-(c.bin.gamma:ℝ)*z) ≤
      2*exp (-((c.exponent:ℝ)+(c.bin.residual.M:ℝ)*(c.entropy.bound:ℝ))*R) := by
  have hgamma : (0:ℝ) ≤ (c.bin.gamma:ℝ) := by exact_mod_cast hc.2.1
  have hb := (Rat.cast_le (K:=ℝ)).mpr hc.2.2
  push_cast at hb
  have hm := mul_le_mul_of_nonneg_right hb hR
  have hz := mul_le_mul_of_nonneg_left hD hgamma
  apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (by norm_num : (0:ℝ) ≤ 2)
  nlinarith only [hm,hz]

theorem rat_cut_entropy_uniform_label_tail (c : RatCutEntropyCertificate)
    (he : c.entropy.Valid) {R : ℝ} {t : ℕ} (hR : 0 ≤ R)
    (ht : (t:ℝ) ≤ (c.bin.residual.M:ℝ)*R) :
    exp ((t:ℝ)*cappedLabelEntropy (c.entropy.rho:ℝ))*
      (2*exp (-((c.exponent:ℝ)+(c.bin.residual.M:ℝ)*(c.entropy.bound:ℝ))*R)) ≤
      2*exp (-(c.exponent:ℝ)*R) := by
  have hentropy := rat_label_entropy_certificate_sound c.entropy he
  have hu := hentropy.1.trans hentropy.2
  have hh := (mul_le_mul_of_nonneg_left hentropy.2 (Nat.cast_nonneg (α:=ℝ) t)).trans
    (mul_le_mul_of_nonneg_right ht hu)
  calc
    _ = 2*exp ((t:ℝ)*cappedLabelEntropy (c.entropy.rho:ℝ)+
        (-((c.exponent:ℝ)+(c.bin.residual.M:ℝ)*(c.entropy.bound:ℝ))*R)) := by rw [exp_add]; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (by norm_num : (0:ℝ) ≤ 2)
      nlinarith only [hh]

end
end Cycle12
