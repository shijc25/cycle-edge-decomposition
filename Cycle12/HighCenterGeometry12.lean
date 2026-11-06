import Cycle12.HighCenterCutExtension12
import Cycle12.HighCenterCompletionGates12

namespace Cycle12
open Cycle13 SimpleGraph Finset Real
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The center threshold and core load pay all high-center vertices and
the low-path color overhead inside the existing 1/2048 core budget. -/
theorem high_center_rounding_budget {a r q d : ℝ}
    (ha : 1 ≤ a) (hr : (2:ℝ)^24*a ≤ r) (hq : 0 ≤ q)
    (hd : sqrt (2*a*r) ≤ d) (hdup : d ≤ sqrt (2*a*r)+1) (hqd : q*d ≤ a*r) :
    q ≤ r/2048 ∧ q+d/2+2*a ≤ r/2048 := by
  have ha0 : 0<a := by linarith only [ha]
  have hr0 : 0<r := lt_of_lt_of_le (mul_pos (by norm_num) ha0) hr
  have hx0 : 0<sqrt (2*a*r) := sqrt_pos.2 (by positivity)
  have hx2 := sq_sqrt (show 0 ≤ 2*a*r by positivity)
  have hqmul := mul_le_mul_of_nonneg_left hd hq
  have hqhalf : q ≤ sqrt (2*a*r)/2 := by
    nlinarith only [hqmul,hqd,hx2,hx0]
  have hrmul := mul_le_mul_of_nonneg_right hr hr0.le
  have hx : sqrt (2*a*r) ≤ (3/8192)*r := by
    have hy0 : 0 ≤ (3/8192:ℝ)*r := by positivity
    nlinarith only [hrmul,hx2,hy0]
  norm_num only [Nat.reducePow] at hr
  constructor
  · linarith only [hqhalf,hx,hr0]
  · linarith only [hqhalf,hdup,hx,ha,hr]

/-- If the untouched completion bank is the smaller expansion, its
square determines the usable allowance. This handles biased bank splits. -/
theorem high_center_effective_geometry {a r h d : ℝ}
    (ha : 0 ≤ a) (hr : 0<r) (hh : 0 ≤ h) (hd : 0 ≤ d)
    (hsep : (2:ℝ)^24*a ≤ r) (hthreshold : 2*a*r ≤ d^2) :
    let a₀ := min a (h^2/(2*r))
    let g := min h d/2
    0 ≤ a₀ ∧ a₀ ≤ a ∧ 1024*a₀ ≤ g ∧ a₀*r/2 ≤ g^2 := by
  dsimp only
  let a₀ := min a (h^2/(2*r))
  let g := min h d/2
  have ha₀ : 0 ≤ a₀ := le_min ha (div_nonneg (sq_nonneg _) (by positivity))
  have ha₀a : a₀ ≤ a := min_le_left _ _
  have ha₀h : a₀*(2*r) ≤ h^2 := (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  have hsep₀ : (2:ℝ)^24*a₀ ≤ r := (mul_le_mul_of_nonneg_left ha₀a (by positivity)).trans hsep
  have hmul := mul_le_mul_of_nonneg_right ha₀a hr.le
  have hg0 : 0 ≤ g := div_nonneg (le_min hh hd) (by norm_num)
  have hg2 : a₀*r/2 ≤ g^2 := by
    by_cases hhd : h ≤ d
    · simp only [g,min_eq_left hhd]
      nlinarith only [ha₀h]
    · simp only [g,min_eq_right (le_of_not_ge hhd)]
      nlinarith only [hmul,hthreshold]
  have hmul₀ := mul_le_mul_of_nonneg_right hsep₀ ha₀
  have hlinear : 1024*a₀ ≤ g := by
    by_contra hn
    have hs : 0<(1024*a₀-g)*(1024*a₀+g) :=
      mul_pos (by linarith) (by linarith only [hn,hg0])
    norm_num only [Nat.reducePow] at hmul₀
    nlinarith only [hg2,hmul₀,hs,sq_nonneg a₀]
  exact ⟨ha₀,ha₀a,hlinear,hg2⟩

variable {V : Type} [Fintype V] [DecidableEq V]
open OAI.ErdosGallai.Sampling

/-- Count high exterior centers by actual original incidences at core
vertices. It remains valid when some exterior vertices are unused. -/
theorem high_centers_incidence_budget (B : SimpleGraph V) (U Z : Finset V)
    {a d : ℝ} (hdeg : ∀ v∈Z,d ≤ ((neighborsIn B v U).card:ℝ))
    (hload : ∀ v∈U,((neighborsIn B v Z).card:ℝ) ≤ a) :
    d*(Z.card:ℝ) ≤ a*(U.card:ℝ) := by
  have hl := Finset.sum_le_sum (fun v hv => hdeg v hv)
  have hr := Finset.sum_le_sum (fun v hv => hload v hv)
  have he : (∑ v∈Z,((neighborsIn B v U).card:ℝ))=
      ∑ v∈U,((neighborsIn B v Z).card:ℝ) := by
    rw [←Nat.cast_sum,←card_interedges_eq_sum_neighborsIn,interedges_card_symm,
      card_interedges_eq_sum_neighborsIn,Nat.cast_sum]
  rw [he] at hl
  simpa only [Finset.sum_const,nsmul_eq_mul,mul_comm] using hl.trans hr

end
end Cycle12
