import Cycle12.CertifiedAnchorFailure
import Cycle12.RationalMinorityBudget

namespace Cycle12
open Finset SimpleGraph Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem cover_group_uniform_actual_cut_of_geometry (g : RatCutGroup) (G : SimpleGraph V)
    {geometry : RatMarkedGeometry} (st : CoverMarkedGraphState geometry G) (heq : g.geometry=geometry)
    (hc : g.NumericValid) (hs : ∀ c∈g.cells, c.Sound) (hnum : ∀ c∈g.cells, c.NumericValid)
    (hpop : ∀ c∈g.cells, c.population=g.population)
    (hW : g.population.Wlo=g.geometry.Wlo) (hI : CoverSparseCutIrreducible G)
    {entropy : ℚ} (hentropy : g.entropyBound=some entropy)
    (S T : Finset V) (hT : T.card=st.t)
    (hside : g.interval.Contains ((S.card:ℝ)/(st.z/st.p)))
    (hcap : (S.card:ℝ) ≤ (g.cap:ℝ)*Fintype.card V) :
    ∃ c∈g.cells,
      RoundedCutLabelValid G S T st.residual c.region.bin.residual.retention.lambda
        ((c.region.bin.residual.kappa:ℝ)*(st.z/st.p)*S.card) c.region.bin.tau
        (2*exp (-((g.exponent:ℝ)+(geometry.M:ℝ)*(entropy:ℝ))*st.R)) ∧
      c.threshold.Bound st.p st.z st.residual S.card := by
  subst geometry
  exact cover_group_uniform_actual_cut g G st hc hs hnum hpop hW hI hentropy S T hT hside hcap

theorem cover_capped_label_uniform_tail {M R exponent upper rho : ℝ} {t : ℕ}
    (ht : (t:ℝ) ≤ M*R) (h0 : 0 ≤ cappedLabelEntropy rho) (hu : cappedLabelEntropy rho ≤ upper) :
    exp ((t:ℝ)*cappedLabelEntropy rho)*(2*exp (-(exponent+M*upper)*R)) ≤ 2*exp (-exponent*R) := by
  have hh := (mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg (α:=ℝ) t)).trans
    (mul_le_mul_of_nonneg_right ht (h0.trans hu))
  calc
    _ = 2*exp ((t:ℝ)*cappedLabelEntropy rho+(-(exponent+M*upper)*R)) := by rw [exp_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by nlinarith only [hh])) (by norm_num)

theorem cover_split_cutoff_upper {n h R Rlo split ymax : ℝ}
    (hh : 0 < h) (hRlo : 0 < Rlo) (hR : Rlo ≤ R) (hn : n=R*h)
    (hsplit : 0 ≤ split) (hy : min (split/Rlo) (1/2) ≤ ymax) :
    0 ≤ min (split*h) (n/2) ∧ min (split*h) (n/2) ≤ ymax*n := by
  have hn0 : 0 ≤ n := by rw [hn]; exact mul_nonneg (hRlo.le.trans hR) hh.le
  have hu : split*h ≤ (split/Rlo)*n := by
    have hm := mul_le_mul_of_nonneg_left hR (div_nonneg hsplit hRlo.le)
    have he : (split/Rlo)*Rlo=split := by field_simp
    rw [he] at hm
    rw [hn]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hm hh.le
  refine ⟨le_min (mul_nonneg hsplit hh.le) (div_nonneg hn0 (by norm_num)),?_⟩
  have hmin : min (split*h) (n/2) ≤ min (split/Rlo) (1/2)*n := by
    rw [min_mul_of_nonneg _ _ hn0]
    apply le_min ((min_le_left _ _).trans hu)
    convert min_le_right (split*h) (n/2) using 1 <;> ring
  exact hmin.trans (mul_le_mul_of_nonneg_right hy hn0)

end
end Cycle12
