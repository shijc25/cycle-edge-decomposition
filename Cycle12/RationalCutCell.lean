import Cycle12.RationalCutRegion
import Cycle12.RationalCutThreshold
import Cycle12.RationalCutEntropy

namespace Cycle12
open Finset SimpleGraph Cycle13 Real

structure RatCutCellCertificate where
  region : RatCutRegion
  population : RatPopulationCertificate
  entropy : RatLabelEntropyCertificate
  exponent : ℚ

def RatCutCellCertificate.threshold (c : RatCutCellCertificate) : RatCutThresholdCertificate :=
  ⟨c.region.bin,c.population⟩
def RatCutCellCertificate.charge (c : RatCutCellCertificate) : RatCutEntropyCertificate :=
  ⟨c.region.bin,c.entropy,c.exponent⟩
def RatCutCellCertificate.NumericValid (c : RatCutCellCertificate) : Prop :=
  c.region.Valid ∧ c.threshold.Valid ∧ c.charge.NumericValid

instance instDecidableRatCutCellNumeric (c : RatCutCellCertificate) : Decidable c.NumericValid := by
  unfold RatCutCellCertificate.NumericValid
  infer_instance

noncomputable section
attribute [local instance] Classical.propDecidable

def RatCutCellCertificate.Sound (c : RatCutCellCertificate) : Prop :=
  c.region.Valid ∧ c.region.bin.Sound ∧ c.threshold.Sound ∧ c.charge.Sound

theorem rat_cut_cell_certificate_sound (c : RatCutCellCertificate)
    (hb : c.region.bin.Valid) (hs : c.region.bin.Sound) (he : c.entropy.Valid)
    (hc : c.NumericValid) : c.Sound :=
  ⟨hc.1,hs,rat_cut_threshold_certificate_sound c.threshold hc.2.1 hb,
    rat_cut_entropy_certificate_sound c.charge he hc.2.2⟩

theorem rounded_cut_label_valid_mono {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {S T : Finset V} {p : unitInterval} {lambda M fraction eta eta' : ℝ}
    (hc : RoundedCutLabelValid G S T p lambda M fraction eta) (he : eta ≤ eta') :
    RoundedCutLabelValid G S T p lambda M fraction eta' :=
  ⟨hc.1,hc.2.1,hc.2.2.1,hc.2.2.2.1,hc.2.2.2.2.1,hc.2.2.2.2.2.1,hc.2.2.2.2.2.2.trans he⟩

theorem rat_cut_cell_uniform_label_valid (c : RatCutCellCertificate) (hc : c.NumericValid)
    {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {S T : Finset V}
    {pres : unitInterval} {R z p : ℝ} (hR : 0 ≤ R) (hD : (c.region.bin.residual.Dlo:ℝ)*R ≤ z)
    (hcut : RoundedCutLabelValid G S T pres c.region.bin.residual.retention.lambda
      ((c.region.bin.residual.kappa:ℝ)*(z/p)*S.card) c.region.bin.tau (2*exp (-(c.region.bin.gamma:ℝ)*z))) :
    RoundedCutLabelValid G S T pres c.region.bin.residual.retention.lambda
      ((c.region.bin.residual.kappa:ℝ)*(z/p)*S.card) c.region.bin.tau
      (2*exp (-((c.exponent:ℝ)+(c.region.bin.residual.M:ℝ)*(c.entropy.bound:ℝ))*R)) :=
  rounded_cut_label_valid_mono hcut (rat_cut_entropy_uniform_raw_tail c.charge hc.2.2 hR hD)

end
end Cycle12
