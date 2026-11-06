import Cycle12.CoverCutThresholds
import Cycle12.RationalPopulationCertificate

namespace Cycle12

structure RatCutThresholdCertificate where
  bin : RatCutBinCertificate
  population : RatPopulationCertificate

def RatCutThresholdCertificate.Valid (c : RatCutThresholdCertificate) : Prop :=
  0 ≤ c.population.slope ∧ 0 ≤ c.population.intercept ∧
  match c.population.witness.kind with
  | .globalCut =>
    0 ≤ c.population.witness.factor ∧
    c.population.witness.factor*(c.population.slope+c.population.intercept/c.bin.residual.retention.nu) ≤
      c.bin.tau*c.bin.residual.kappa*c.bin.ps^2
  | .localCut =>
    0 ≤ c.population.witness.beta+c.population.witness.error ∧
    (c.population.witness.error+2*c.population.witness.beta)/c.population.witness.dm ≤ c.population.cap ∧
    c.population.cap < 1 ∧
    (c.population.witness.beta+c.population.witness.error)*
      (c.population.slope+c.population.intercept/c.bin.residual.retention.nu)/(1-c.population.cap) ≤
      c.bin.tau*c.bin.residual.kappa*c.bin.ps^2
  | .anchor =>
    0 < c.population.ce ∧
    (1+c.population.witness.factor)*c.population.witness.L ≤
      c.bin.tau*c.bin.residual.kappa*c.bin.ps^2*c.population.ce*c.population.Wlo

instance instDecidableRatCutThresholdValid (c : RatCutThresholdCertificate) : Decidable c.Valid := by
  unfold RatCutThresholdCertificate.Valid
  cases c.population.witness.kind <;> infer_instance

noncomputable section

def RatCutThresholdCertificate.Bound (c : RatCutThresholdCertificate) (p z residual u : ℝ) : Prop :=
  let target := (c.bin.tau:ℝ)*((c.bin.residual.kappa:ℝ)*(z/p)*u*residual^2)
  match c.population.witness.kind with
  | .globalCut =>
    (c.population.witness.factor:ℝ)*z*((c.population.slope:ℝ)*p*u+(c.population.intercept:ℝ)*z) ≤ target
  | .localCut =>
    ((c.population.witness.beta:ℝ)+(c.population.witness.error:ℝ))*z*
      (((c.population.slope:ℝ)*p*u+(c.population.intercept:ℝ)*z)/
        (1-((c.population.witness.error:ℝ)+2*(c.population.witness.beta:ℝ))/(c.population.witness.dm:ℝ))) ≤ target
  | .anchor =>
    (((1+(c.population.witness.factor:ℝ))*(c.population.witness.L:ℝ))/(c.population.ce:ℝ))*u ≤ target

def RatCutThresholdCertificate.Sound (c : RatCutThresholdCertificate) : Prop :=
  ∀ p z residual u : ℝ, 0 < p → 0 < z →
    (c.bin.residual.retention.nu:ℝ)*(z/p) ≤ u → (c.bin.ps:ℝ)*p ≤ residual →
    (c.population.Wlo:ℝ) ≤ p*z → c.Bound p z residual u

theorem rat_cut_threshold_certificate_sound (c : RatCutThresholdCertificate)
    (hc : c.Valid) (hb : c.bin.Valid) : c.Sound := by
  have hn : (0:ℝ) < (c.bin.residual.retention.nu:ℝ) := by exact_mod_cast hb.2.2.2.1
  have hk : (0:ℝ) ≤ (c.bin.residual.kappa:ℝ) := by exact_mod_cast hb.2.2.1.le
  have hps : (0:ℝ) ≤ (c.bin.ps:ℝ) := by exact_mod_cast hb.2.2.2.2.2.2.1.le
  have ht : (0:ℝ) ≤ (c.bin.tau:ℝ) := by exact_mod_cast hb.2.2.2.2.2.2.2.1.le
  obtain ⟨hs,hi,hbranch⟩ := hc
  intro p z residual u hp hz hside hres hW
  cases he : c.population.witness.kind with
  | globalCut =>
    simp only [he] at hbranch
    rw [RatCutThresholdCertificate.Bound,he]
    apply cover_counting_cut_threshold hp hz hn hside (by exact_mod_cast hi)
      (by exact_mod_cast hbranch.1) hps ht hk hres
    exact_mod_cast hbranch.2
  | localCut =>
    simp only [he] at hbranch
    rw [RatCutThresholdCertificate.Bound,he]
    apply cover_local_cut_threshold (cap:=(c.population.cap:ℝ)) hp hz hn hside
      (by exact_mod_cast hs) (by exact_mod_cast hi) (by exact_mod_cast hbranch.1) hps ht hk hres
      (by exact_mod_cast hbranch.2.1) (by exact_mod_cast hbranch.2.2.1)
    exact_mod_cast hbranch.2.2.2
  | anchor =>
    simp only [he] at hbranch
    rw [RatCutThresholdCertificate.Bound,he]
    apply cover_anchor_cut_threshold hp hz ((mul_pos hn (div_pos hz hp)).le.trans hside)
      hps ht hk hres hW (by exact_mod_cast hbranch.1)
    exact_mod_cast hbranch.2

end
end Cycle12
