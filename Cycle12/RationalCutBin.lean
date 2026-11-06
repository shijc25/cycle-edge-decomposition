import Cycle12.RationalResidualRetention
import Cycle12.RationalCutRate
import Cycle12.FixedCutLabelTail

namespace Cycle12
open Finset SimpleGraph Cycle13 Real

structure RatCutBinCertificate where
  residual : RatResidualRetentionCertificate
  ps : ℚ
  tau : ℚ
  phi : ℚ
  gamma : ℚ

def RatCutBinCertificate.rate (c : RatCutBinCertificate) : RatCutRateCertificate :=
  ⟨c.residual.retention.lambda,c.residual.kappa,c.residual.retention.nu,
    c.residual.pmax,c.residual.zlo,c.ps,c.tau,c.phi,c.gamma⟩

def RatCutBinCertificate.Valid (c : RatCutBinCertificate) : Prop :=
  c.residual.Valid ∧ c.rate.Valid

instance instDecidableRatCutBinValid (c : RatCutBinCertificate) : Decidable c.Valid := by
  unfold RatCutBinCertificate.Valid
  infer_instance

noncomputable section
attribute [local instance] Classical.propDecidable

def RatCutBinCertificate.Sound (c : RatCutBinCertificate) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (S T : Finset V)
    (R z p : ℝ) (pres : unitInterval),
    (0:ℝ) < Fintype.card V → (0:ℝ) < Fintype.card G.edgeSet → CoverSparseCutIrreducible G →
    (c.residual.retention.xl:ℝ) ≤ coverGraphX (Fintype.card V) (Fintype.card G.edgeSet) →
    coverGraphX (Fintype.card V) (Fintype.card G.edgeSet) ≤ (c.residual.retention.xh:ℝ) →
    coverGraphExpansion (Fintype.card V) (Fintype.card G.edgeSet)=z/p →
    0 ≤ R → 0 < p → p ≤ (c.residual.pmax:ℝ) → (c.residual.zlo:ℝ) ≤ z →
    (c.residual.Dlo:ℝ)*R ≤ z → (c.ps:ℝ)*p ≤ (pres:ℝ) →
    (T.card:ℝ) ≤ (c.residual.M:ℝ)*R →
    (c.residual.retention.nu:ℝ)*(z/p) ≤ (S.card:ℝ) →
    (S.card:ℝ) ≤ (c.residual.retention.ymax:ℝ)*Fintype.card V →
    RoundedCutLabelValid G S T pres c.residual.retention.lambda
      ((c.residual.kappa:ℝ)*(z/p)*S.card) c.tau (2*exp (-(c.gamma:ℝ)*z))

theorem rat_cut_bin_certificate_sound (c : RatCutBinCertificate)
    (hp : c.residual.retention.ProfilesValid) (hn : c.residual.retention.NumericValid)
    (hc : c.Valid) : c.Sound := by
  intro V _ _ G S T R z p pres horder hmass hI hxl hxh hcoord hR hp0 hpu hzlo hDz hres hmark hside hupper
  have hret := rat_residual_retention_certificate_sound c.residual hp hn hc.1 G S T R z p
    horder hmass hI hxl hxh hcoord hR hp0 hpu hzlo hDz hmark hside hupper
  have hrate := rat_cut_rate_certificate_sound c.rate hc.2 p z pres S.card hp0 hpu hzlo hres hside
  obtain ⟨hl,hk,hnu,hpmax,hz,hps,ht0,ht1,hphi0,hgamma,hphi,hbudget⟩ := hc.2
  have hnR : (0:ℝ) < (c.residual.retention.nu:ℝ) := by exact_mod_cast hnu
  have hzR : (0:ℝ) < (c.residual.zlo:ℝ) := by exact_mod_cast hz
  have hh : 0 < z/p := div_pos (hzR.trans_le hzlo) hp0
  have hs : (0:ℝ) < S.card := (mul_pos hnR hh).trans_le hside
  have hkp : (0:ℝ) < (c.residual.kappa:ℝ) := by exact_mod_cast hk
  refine ⟨card_pos.mp (by exact_mod_cast hs),?_,mul_pos (mul_pos hkp hh) hs,hret,?_,?_,?_⟩
  · exact_mod_cast hl
  · have htR : (0:ℝ) < (c.tau:ℝ) := by exact_mod_cast ht0
    exact htR.le
  · exact_mod_cast ht1
  · apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (by norm_num : (0:ℝ) ≤ 2)
    have hh' := neg_le_neg hrate
    dsimp only [RatCutBinCertificate.rate] at hh'
    convert hh' using 1 <;> ring

end
end Cycle12
