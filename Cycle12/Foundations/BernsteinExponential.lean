import Cycle12.Foundations.SubsetChernoff

namespace Cycle13
open Real
noncomputable section

theorem exp_le_bernstein_positive {x : ℝ} (hx : 0 ≤ x) (hx3 : x < 3) :
    exp x ≤ 1+x+x^2/(2*(1-x/3)) := by
  let f : ℝ→ℝ := fun t => 1+2*t/3+t^2/6-(1-t/3)*exp t
  have hd (t : ℝ) : HasDerivAt f ((2+t-(2-t)*exp t)/3) t := by
    unfold f
    convert (((hasDerivAt_const t (1:ℝ)).add (((hasDerivAt_id t).const_mul 2).div_const 3)).add
      (((hasDerivAt_id t).pow 2).div_const 6)).sub
        (((hasDerivAt_const t (1:ℝ)).sub ((hasDerivAt_id t).div_const 3)).mul (hasDerivAt_exp t))
      using 1 <;> (try funext y) <;> dsimp <;> ring
  have hdpos (t : ℝ) (ht : 0 ≤ t) : 0 ≤ (2+t-(2-t)*exp t)/3 := by
    by_cases ht2 : t < 2
    · have hh := exp_le_two_add_div_two_sub ht ht2
      have hm := (le_div_iff₀ (show 0 < 2-t by linarith)).mp hh
      nlinarith
    · have hm := mul_nonpos_of_nonpos_of_nonneg (show 2-t ≤ 0 by linarith) (exp_pos t).le
      linarith
  have hm := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (0:ℝ))
    (f:=f) (f':=fun t => (2+t-(2-t)*exp t)/3)
    (by unfold f; fun_prop) (fun t _ => (hd t).hasDerivWithinAt)
    (fun t ht => hdpos t (interior_subset ht))
  have hf := hm (by simp) hx hx
  have hf0 : f 0=0 := by simp [f]
  rw [hf0] at hf
  dsimp [f] at hf
  have hden : 0 < 2*(1-x/3) := by linarith
  apply (mul_le_mul_iff_left₀ hden).mp
  have he : (1+x+x^2/(2*(1-x/3)))*(2*(1-x/3))=
      2*(1+2*x/3+x^2/6) := by
    rw [add_mul,div_mul_cancel₀ _ hden.ne']
    ring
  rw [he]
  nlinarith

theorem exp_le_bernstein_quadratic {x b : ℝ} (hb : 0 ≤ b) (hb3 : b < 3) (hx : x ≤ b) :
    exp x ≤ 1+x+x^2/(2*(1-b/3)) := by
  have hden : 0 < 2*(1-b/3) := by linarith
  by_cases hx0 : 0 ≤ x
  · apply (exp_le_bernstein_positive hx0 (hx.trans_lt hb3)).trans
    have hh := div_le_div_of_nonneg_left (sq_nonneg x) hden (show 2*(1-b/3) ≤ 2*(1-x/3) by linarith)
    linarith
  · have hh := exp_neg_le_quadratic (show 0 ≤ -x by linarith)
    simp only [neg_neg,neg_sq] at hh
    have hd := div_le_div_of_nonneg_left (sq_nonneg x) hden (show 2*(1-b/3) ≤ 2 by linarith)
    linarith

theorem centered_bernoulli_mgf_bound (p : unitInterval) {d r θ : ℝ}
    (hd : 0 ≤ d) (hdr : d ≤ r) (hθ : 0 ≤ θ) (hθr : θ*(1-(p:ℝ))*r < 3) :
    (1-(p:ℝ))*exp (-θ*(p:ℝ)*d)+(p:ℝ)*exp (θ*(1-(p:ℝ))*d) ≤
      exp (θ^2*(p:ℝ)*(1-(p:ℝ))*d^2/(2*(1-θ*(1-(p:ℝ))*r/3))) := by
  have hp0 := p.2.1
  have hp1 : 0 ≤ 1-(p:ℝ) := sub_nonneg.mpr p.2.2
  have hr : 0 ≤ r := hd.trans hdr
  have hb : 0 ≤ θ*(1-(p:ℝ))*r := by positivity
  have hneg : -θ*(p:ℝ)*d ≤ 0 := mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hθ) hp0) hd
  have h₀ := exp_le_bernstein_quadratic hb hθr (x:= -θ*(p:ℝ)*d) (hneg.trans hb)
  have h₁ := exp_le_bernstein_quadratic hb hθr (x:= θ*(1-(p:ℝ))*d) (by
    exact mul_le_mul_of_nonneg_left hdr (mul_nonneg hθ hp1))
  have h₀' := mul_le_mul_of_nonneg_left h₀ hp1
  have h₁' := mul_le_mul_of_nonneg_left h₁ hp0
  have hh := add_le_add h₀' h₁'
  have he : (1-(p:ℝ))*(1+(-θ*(p:ℝ)*d)+(-θ*(p:ℝ)*d)^2/(2*(1-θ*(1-(p:ℝ))*r/3)))+
      (p:ℝ)*(1+θ*(1-(p:ℝ))*d+(θ*(1-(p:ℝ))*d)^2/(2*(1-θ*(1-(p:ℝ))*r/3)))=
      1+θ^2*(p:ℝ)*(1-(p:ℝ))*d^2/(2*(1-θ*(1-(p:ℝ))*r/3)) := by ring
  rw [he] at hh
  apply hh.trans
  simpa only [add_comm (1:ℝ)] using (Real.add_one_le_exp
    (θ^2*(p:ℝ)*(1-(p:ℝ))*d^2/(2*(1-θ*(1-(p:ℝ))*r/3))))

end
end Cycle13
