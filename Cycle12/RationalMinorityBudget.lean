import Cycle12.CoverMinorityBudget
import Cycle12.Foundations.RationalBounds

namespace Cycle12
open Real Cycle13

def ratCoverExpOneUpper : ℚ := 679570457114761309/250000000000000000

theorem cover_exp_one_upper : exp 1 ≤ (ratCoverExpOneUpper:ℝ) := by
  have h := (ratExp_bounds (by norm_num : (0:ℚ) ≤ 1) 30 (by norm_num)).2
  have hn : ratExpUpper 1 30 ≤ ratCoverExpOneUpper := by decide +kernel
  simpa only [Rat.cast_one] using h.trans ((Rat.cast_le (K:=ℝ)).mpr hn)

structure RatMinorityBudgetCertificate where
  Rlo : ℚ
  qmark : ℚ
  ymax : ℚ
  slope : ℚ
  intercept : ℚ
  cap : ℚ
  rho : ℚ

def RatMinorityBudgetCertificate.Valid (c : RatMinorityBudgetCertificate) : Prop :=
  0 < c.Rlo ∧ 0 < c.qmark ∧ 0 ≤ c.ymax ∧ 0 ≤ c.slope ∧ 0 ≤ c.intercept ∧ c.cap < 1 ∧
  (ratCoverExpOneUpper-1)*(c.slope*c.ymax+c.intercept/c.Rlo)/(1-c.cap)+6/(c.qmark*c.Rlo) ≤ c.rho

instance instDecidableRatMinorityBudgetValid (c : RatMinorityBudgetCertificate) : Decidable c.Valid := by
  unfold RatMinorityBudgetCertificate.Valid
  infer_instance

noncomputable section

def RatMinorityBudgetCertificate.Sound (c : RatMinorityBudgetCertificate) : Prop :=
  ∀ n N p z R t cutoff frac : ℝ, 0 < n → 0 < p → 0 < z → (c.Rlo:ℝ) ≤ R →
    (c.qmark:ℝ)*R ≤ t → 0 ≤ cutoff → cutoff ≤ (c.ymax:ℝ)*n → N=p*n → N=z*R →
    frac ≤ (c.cap:ℝ) →
    (exp 1-1)*(t/N)*(((c.slope:ℝ)*p*cutoff+(c.intercept:ℝ)*z)/(1-frac))+6 ≤ (c.rho:ℝ)*t

theorem rat_minority_budget_certificate_sound (c : RatMinorityBudgetCertificate) (hc : c.Valid) : c.Sound := by
  obtain ⟨hR,hq,hy,hs,hi,hcap,hbudget⟩ := hc
  intro n N p z R t cutoff frac hn hp hz hRl ht hcut0 hcut hN hNZ hfrac
  apply minority_label_budget_from_scales hn hp hz (by exact_mod_cast hR) hRl
    (by exact_mod_cast hq) ht (by exact_mod_cast hy) (by exact_mod_cast hs) (by exact_mod_cast hi)
    hcut0 hcut hN hNZ hfrac (by exact_mod_cast hcap) cover_exp_one_upper
  exact_mod_cast hbudget

end
end Cycle12
