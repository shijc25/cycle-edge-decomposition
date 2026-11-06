import Cycle12.CoverReverseLocal
import Cycle12.RationalPopulationCertificate
import Cycle12.RationalMarkedGeometry

namespace Cycle12
open Real Cycle13

def ratCoverLogTwoBudget : ℚ := 69314718055994531/100000000000000000

theorem cover_log_two_budget : log 2 ≤ (ratCoverLogTwoBudget:ℝ) := by
  have h : log 2 ≤ (logTwoUpper:ℝ) := by simpa [logTwoUpper] using log_two_24_digits.2
  have hn : logTwoUpper ≤ ratCoverLogTwoBudget := by decide +kernel
  exact h.trans ((Rat.cast_le (K:=ℝ)).mpr hn)

structure RatReverseLocalCertificate where
  geometry : RatMarkedGeometry
  population : RatPopulationCertificate
  exponent : ℚ

def RatReverseLocalCertificate.Valid (c : RatReverseLocalCertificate) : Prop :=
  0 < c.geometry.ps ∧ 0 < c.geometry.zlo ∧ 0 ≤ c.geometry.M ∧
  (c.population.witness.error+2*c.population.witness.beta)/c.population.witness.dm ≤ c.population.cap ∧
  0 < c.geometry.zlo/40-c.geometry.pmax*c.geometry.M ∧ 0 < c.exponent ∧
  c.exponent ≤ c.geometry.ps*(c.geometry.zlo/40-c.geometry.pmax*c.geometry.M)/8-
    c.geometry.M*ratCoverLogTwoBudget ∧
  (1+c.population.cap)/125 ≤ (49/100)*c.geometry.ps*(1/40-c.geometry.M*c.geometry.pmax/c.geometry.zlo)

instance instDecidableRatReverseLocalValid (c : RatReverseLocalCertificate) : Decidable c.Valid := by
  unfold RatReverseLocalCertificate.Valid
  infer_instance

noncomputable section

def RatReverseLocalCertificate.Sound (c : RatReverseLocalCertificate) : Prop :=
  ∀ (n N p z R residual : ℝ) (t : ℕ), 0 < p → 0 < R → p ≤ (c.geometry.pmax:ℝ) →
    (c.geometry.zlo:ℝ) ≤ z → n=R*(z/p) → N=z*R → (t:ℝ) ≤ (c.geometry.M:ℝ)*R →
    (c.geometry.ps:ℝ)*p ≤ residual →
    let mean := (c.geometry.ps:ℝ)*(z/40-p*(c.geometry.M:ℝ))*R
    0 < mean ∧ mean ≤ residual*(n/40-t) ∧
    (1+((c.population.witness.error:ℝ)+2*(c.population.witness.beta:ℝ))/(c.population.witness.dm:ℝ))*
      (1/125)*N < (1/2)*mean ∧
    (2:ℝ)^t*exp (-(1-(1/2:ℝ))^2*mean/2) ≤ exp (-(c.exponent:ℝ)*R)

theorem rat_reverse_local_certificate_sound (c : RatReverseLocalCertificate) (hc : c.Valid) : c.Sound := by
  obtain ⟨hps,hzlo,hM,hcap,hgap,he,hbudget,hlocal⟩ := hc
  have hpsR : (0:ℝ) < (c.geometry.ps:ℝ) := by exact_mod_cast hps
  have hzR : (0:ℝ) < (c.geometry.zlo:ℝ) := by exact_mod_cast hzlo
  have hMR : (0:ℝ) ≤ (c.geometry.M:ℝ) := by exact_mod_cast hM
  have hgapR := (Rat.cast_lt (K:=ℝ)).mpr hgap
  have hbudgetR := (Rat.cast_le (K:=ℝ)).mpr hbudget
  have hlocalR := (Rat.cast_le (K:=ℝ)).mpr hlocal
  push_cast at hgapR hbudgetR hlocalR
  intro n N p z R residual t hp hR hpu hzl hn hN ht hres
  have hz := hzR.trans_le hzl
  have hg := cover_reverse_local_gap_lower (Y:=(1/40:ℝ)) (by norm_num) hMR hpu hzl
  have hga : 0 < (1/40:ℝ)*z-p*(c.geometry.M:ℝ) := by
    have hbase : 0 < (1/40:ℝ)*(c.geometry.zlo:ℝ)-(c.geometry.pmax:ℝ)*(c.geometry.M:ℝ) := by
      nlinarith only [hgapR]
    exact hbase.trans_le hg
  have hmean := cover_reverse_local_mean hp hR hpsR hMR hn ht hres hga
  have hpz : p/z ≤ (c.geometry.pmax:ℝ)/(c.geometry.zlo:ℝ) :=
    (div_le_div_of_nonneg_right hpu hz.le).trans
      (div_le_div_of_nonneg_left (hp.le.trans hpu) hzR hzl)
  have hratio := mul_le_mul_of_nonneg_left hpz hMR
  have hloc : (1+(c.population.cap:ℝ))*(1/125) ≤
      (49/100:ℝ)*(c.geometry.ps:ℝ)*(1/40-(c.geometry.M:ℝ)*p/z) := by
    have hm := mul_le_mul_of_nonneg_left (sub_le_sub_left hratio (1/40:ℝ))
      (show 0 ≤ (49/100:ℝ)*(c.geometry.ps:ℝ) by positivity)
    have hh := hlocalR.trans (by simpa only [mul_div_assoc] using hm)
    convert hh using 1 <;> ring
  have hcut := cover_reverse_local_cutoff hp hz hR hpsR (by norm_num : (0:ℝ) ≤ 1/125)
    hN (show ((c.population.witness.error:ℝ)+2*(c.population.witness.beta:ℝ))/(c.population.witness.dm:ℝ) ≤
      (c.population.cap:ℝ) by exact_mod_cast hcap) hga hloc
  have hcost : (c.exponent:ℝ) ≤ (c.geometry.ps:ℝ)*((1/40:ℝ)*z-p*(c.geometry.M:ℝ))/8-
      (c.geometry.M:ℝ)*(ratCoverLogTwoBudget:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hg (show 0 ≤ (c.geometry.ps:ℝ)/8 by positivity)
    nlinarith only [hbudgetR,hh]
  have htail := cover_reverse_local_tail hR.le ht cover_log_two_budget hcost
  change 0 < _ ∧ _ ≤ _ ∧ _ < _ ∧ _ ≤ _
  convert And.intro hmean.1 (And.intro hmean.2 (And.intro hcut htail)) using 1 <;> ring_nf

end
end Cycle12
