import Cycle12.Foundations.SubsetBernoulliMGF
import Cycle12.Foundations.FiniteSupport

namespace Cycle13
open Finset Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem log_lower_fraction_bound {u : ℝ} (hu : 0<u) (hu1 : u≤1) :
    log u ≤ u-1-(1-u)^2/2 := by
  let f := fun x : ℝ => log x-x+1+(x-1)^2/2
  have hd (x : ℝ) (hx : 0<x) : HasDerivAt f ((x-1)^2/x) x := by
    convert (((Real.hasDerivAt_log hx.ne').sub (hasDerivAt_id x)).add_const 1).add
      ((((hasDerivAt_id x).sub_const 1).pow 2).div_const 2) using 1
      <;> (try funext t) <;> dsimp [f] <;> field_simp <;> ring
  have hm := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioi (0:ℝ))
    (f:=f) (f':=fun x => (x-1)^2/x)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt)
    (fun x hx => div_nonneg (sq_nonneg _) (le_of_lt (interior_subset hx)))
  have hh := hm hu (by norm_num : (1:ℝ)∈Set.Ioi 0) hu1
  dsimp [f] at hh
  rw [log_one] at hh
  nlinarith

theorem subsetBernoulli_card_mgf_le (W : Finset V) (p : unitInterval) (θ : ℝ) :
    (subsetBernoulli W p).expect (fun S => exp (θ*S.card)) ≤
      exp ((p:ℝ)*(exp θ-1)*W.card) := by
  apply le_trans ((subsetBernoulli W p).expect_mono_support
    (Y:=fun S => exp (θ*(S∩W).card)) ?_) (subsetBernoulli_count_mgf_le W p W θ (Subset.refl _))
  intro S hmass
  have hs : S⊆W := by
    by_contra hn
    rw [subsetBernoulli_mass_not_subset W S p hn] at hmass
    exact lt_irrefl _ hmass
  rw [inter_eq_left.mpr hs]

theorem subsetBernoulli_card_upper_tail (W : Finset V) (p : unitInterval)
    {B : ℝ} (hμ : 0<(p:ℝ)*W.card) (hB : (p:ℝ)*W.card≤B) :
    (subsetBernoulli W p).prob (fun S => B≤(S.card:ℝ)) ≤
      exp (-(B-(p:ℝ)*W.card)^2/(2*B)) := by
  let μ := (p:ℝ)*W.card
  have hμ0 : 0<μ := hμ
  have hB0 : 0<B := hμ.trans_le hB
  let θ := log (B/μ)
  have hθ : 0≤θ := Real.log_nonneg ((one_le_div hμ0).mpr hB)
  have heθ : exp θ=B/μ := Real.exp_log (div_pos hB0 hμ0)
  have hh := (subsetBernoulli W p).exp_markov_le (fun S => (S.card:ℝ)) θ B hθ
  apply hh.trans
  apply le_trans (mul_le_mul_of_nonneg_left (subsetBernoulli_card_mgf_le W p θ) (exp_pos _).le)
  rw [← exp_add,heθ]
  apply exp_le_exp.mpr
  have hu : 0<μ/B := div_pos hμ0 hB0
  have hu1 : μ/B≤1 := (div_le_one hB0).mpr hB
  have hlog := mul_le_mul_of_nonneg_left (log_lower_fraction_bound hu hu1) hB0.le
  have hθlog : θ= -log (μ/B) := by
    dsimp [θ]
    rw [log_div hB0.ne' hμ0.ne',log_div hμ0.ne' hB0.ne']
    ring
  rw [hθlog]
  calc
    _ = -(-log (μ/B))*B+μ*(B/μ-1) := by dsimp [μ]; ring
    _ = B*log (μ/B)+B-μ := by field_simp [hμ0.ne']; ring
    _ ≤ B*(μ/B-1-(1-μ/B)^2/2)+B-μ := by linarith
    _ = _ := by
      change _ = -(B-μ)^2/(2*B)
      field_simp [hB0.ne']
      ring

end
end Cycle13
