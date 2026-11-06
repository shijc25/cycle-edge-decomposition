import Cycle12.RationalCutGroup
import Cycle12.CoverMarkedGraphState

namespace Cycle12
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem cover_group_actual_cut (g : RatCutGroup) (G : SimpleGraph V)
    (st : CoverMarkedGraphState g.geometry G) (hc : g.NumericValid)
    (hs : ∀ c∈g.cells, c.Sound) (hpop : ∀ c∈g.cells, c.population=g.population)
    (hW : g.population.Wlo=g.geometry.Wlo) (hI : CoverSparseCutIrreducible G)
    (S T : Finset V) (hT : T.card=st.t)
    (hside : g.interval.Contains ((S.card:ℝ)/(st.z/st.p)))
    (hcap : (S.card:ℝ) ≤ (g.cap:ℝ)*Fintype.card V) :
    ∃ c∈g.cells,
      RoundedCutLabelValid G S T st.residual c.region.bin.residual.retention.lambda
        ((c.region.bin.residual.kappa:ℝ)*(st.z/st.p)*S.card) c.region.bin.tau
        (2*exp (-(c.region.bin.gamma:ℝ)*st.z)) ∧
      c.threshold.Bound st.p st.z st.residual S.card := by
  apply rat_cut_group_actual_cut g hc hs G S T st.R st.z st.p st.residual
    st.order_pos st.mass_pos hI st.x_lower st.x_upper st.expansion_identity st.order_identity
    st.scale_pos.le st.scale_lower st.fraction_pos st.z_pos st.fraction_upper st.z_lower
    st.scale_ratio st.residual_lower (by rw [hT]; exact st.mark_upper) ?_ hside hcap
  intro c hc
  rw [hpop c hc,hW]
  exact st.weight_lower

theorem cover_group_uniform_actual_cut (g : RatCutGroup) (G : SimpleGraph V)
    (st : CoverMarkedGraphState g.geometry G) (hc : g.NumericValid)
    (hs : ∀ c∈g.cells, c.Sound) (hnum : ∀ c∈g.cells, c.NumericValid)
    (hpop : ∀ c∈g.cells, c.population=g.population)
    (hW : g.population.Wlo=g.geometry.Wlo) (hI : CoverSparseCutIrreducible G)
    {entropy : ℚ} (hentropy : g.entropyBound=some entropy)
    (S T : Finset V) (hT : T.card=st.t)
    (hside : g.interval.Contains ((S.card:ℝ)/(st.z/st.p)))
    (hcap : (S.card:ℝ) ≤ (g.cap:ℝ)*Fintype.card V) :
    ∃ c∈g.cells,
      RoundedCutLabelValid G S T st.residual c.region.bin.residual.retention.lambda
        ((c.region.bin.residual.kappa:ℝ)*(st.z/st.p)*S.card) c.region.bin.tau
        (2*exp (-((g.exponent:ℝ)+(g.geometry.M:ℝ)*(entropy:ℝ))*st.R)) ∧
      c.threshold.Bound st.p st.z st.residual S.card := by
  obtain ⟨c,hmem,hcut,hthreshold⟩ := cover_group_actual_cut g G st hc hs hpop hW hI S T hT hside hcap
  obtain ⟨_,_,hexp,_,_,hM,_,hD,_,_,he,_⟩ := hc.2.2.2 c hmem
  simp only [hentropy] at he
  have hu := rat_cut_cell_uniform_label_valid c (hnum c hmem) st.scale_pos.le
    (by rw [hD]; exact st.scale_ratio) hcut
  rw [hexp,hM,he] at hu
  exact ⟨c,hmem,hu,hthreshold⟩

theorem cover_marked_vote_mean (g : RatMarkedGeometry) (G : SimpleGraph V)
    (st : CoverMarkedGraphState g G) {dm : ℝ} (hdm : 0 ≤ dm) :
    dm*(g.qmark:ℝ) ≤ ((st.t:ℝ)/st.N)*(dm*st.z) := by
  have hq := mul_le_mul_of_nonneg_left st.mark_lower hdm
  have hdiv := (le_div_iff₀ st.scale_pos).mpr (show (dm*(g.qmark:ℝ))*st.R ≤ dm*(st.t:ℝ) by
    simpa only [mul_assoc] using hq)
  have he : (dm*(st.t:ℝ))/st.R=((st.t:ℝ)/st.N)*(dm*st.z) := by
    rw [st.sample_identity]
    field_simp [st.scale_pos.ne',st.z_pos.ne']
  rwa [he] at hdiv

end
end Cycle12
