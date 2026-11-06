import Cycle12.RationalCutRetention
import Cycle12.CoverTruncationCoordinates

namespace Cycle12
open Finset SimpleGraph Cycle13

structure RatResidualRetentionCertificate where
  retention : RatCutRetentionCertificate
  M : ℚ
  pmax : ℚ
  Dlo : ℚ
  zlo : ℚ
  kappa : ℚ

def RatResidualRetentionCertificate.Valid (c : RatResidualRetentionCertificate) : Prop :=
  0 ≤ c.M ∧ 0 < c.Dlo ∧ 0 < c.zlo ∧ 0 < c.retention.nu ∧ 1 ≤ c.retention.lambda ∧
  c.kappa ≤ c.retention.retained-
    (c.M*c.pmax/c.Dlo)*(c.retention.lambda+c.pmax/(c.retention.nu*c.zlo))

instance instDecidableRatResidualRetentionValid (c : RatResidualRetentionCertificate) : Decidable c.Valid := by
  unfold RatResidualRetentionCertificate.Valid
  infer_instance

noncomputable section
attribute [local instance] Classical.propDecidable

def RatResidualRetentionCertificate.Sound (c : RatResidualRetentionCertificate) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (S T : Finset V)
    (R z p : ℝ),
    (0:ℝ) < Fintype.card V → (0:ℝ) < Fintype.card G.edgeSet → CoverSparseCutIrreducible G →
    (c.retention.xl:ℝ) ≤ coverGraphX (Fintype.card V) (Fintype.card G.edgeSet) →
    coverGraphX (Fintype.card V) (Fintype.card G.edgeSet) ≤ (c.retention.xh:ℝ) →
    coverGraphExpansion (Fintype.card V) (Fintype.card G.edgeSet)=z/p →
    0 ≤ R → 0 < p → p ≤ (c.pmax:ℝ) → (c.zlo:ℝ) ≤ z → (c.Dlo:ℝ)*R ≤ z →
    (T.card:ℝ) ≤ (c.M:ℝ)*R → (c.retention.nu:ℝ)*(z/p) ≤ (S.card:ℝ) →
    (S.card:ℝ) ≤ (c.retention.ymax:ℝ)*Fintype.card V →
    (c.kappa:ℝ)*(z/p)*S.card ≤
      (Fintype.card (truncatedResidualGraph G S T (roundedCutCap c.retention.lambda S)).edgeSet:ℝ)

theorem rat_residual_retention_certificate_sound (c : RatResidualRetentionCertificate)
    (hp : c.retention.ProfilesValid) (hnumeric : c.retention.NumericValid) (hc : c.Valid) : c.Sound := by
  obtain ⟨hM,hD,hz,hn,hl,hk⟩ := hc
  have hMR : (0:ℝ) ≤ (c.M:ℝ) := by exact_mod_cast hM
  have hDR : (0:ℝ) < (c.Dlo:ℝ) := by exact_mod_cast hD
  have hzR : (0:ℝ) < (c.zlo:ℝ) := by exact_mod_cast hz
  have hnR : (0:ℝ) < (c.retention.nu:ℝ) := by exact_mod_cast hn
  have hlR : (1:ℝ) ≤ (c.retention.lambda:ℝ) := by exact_mod_cast hl
  have hkR := (Rat.cast_le (K:=ℝ)).mpr hk
  push_cast at hkR
  intro V _ _ G S T R z p horder hmass hI hxl hxh hcoord hR hp0 hpu hzlo hDz hmark hside hupper
  have hh : 0 < z/p := div_pos (hzR.trans_le hzlo) hp0
  have hb := rat_cut_retention_certificate_sound c.retention hp hnumeric G S horder hmass hI
    hxl hxh (by rwa [hcoord]) (by rwa [hcoord]) hupper
  rw [hcoord] at hb
  have hloss := cover_rounded_loss_upper hR hp0 hDR hzR hzlo hDz hpu hMR hnR
    (show (0:ℝ) ≤ (c.retention.lambda:ℝ) by linarith only [hlR])
  apply rounded_residual_from_retained G S T hh hnR hlR hside hmark hb
  exact hkR.trans (sub_le_sub_left hloss _)

end
end Cycle12
