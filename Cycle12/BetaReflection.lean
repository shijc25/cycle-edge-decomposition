import Cycle12.BetaReflectionAlgebra

namespace Cycle12
open Real
noncomputable section

theorem beta_power_reflection (a b : ℕ) (p q x : ℝ)
    (hp : 0<p) (hpq : p≤q) (hx0 : 0≤x) (hxp : x<p)
    (hab : (b:ℝ)*p≤(a:ℝ)*q) :
    (p-x)^a*(q+x)^b ≤ (p+x)^a*(q-x)^b := by
  let H : ℝ → ℝ := fun t => (a:ℝ)*(log (p+t)-log (p-t))+
    (b:ℝ)*(log (q-t)-log (q+t))
  have hD (t : ℝ) (ht : t∈Set.Icc 0 x) : HasDerivAt H
      ((a:ℝ)*(1/(p+t)+1/(p-t))-(b:ℝ)*(1/(q-t)+1/(q+t))) t := by
    have hpplus : p+t≠0 := by linarith [ht.1]
    have hpminus : p-t≠0 := by linarith [ht.2]
    have hqplus : q+t≠0 := by linarith [ht.1]
    have hqminus : q-t≠0 := by linarith [ht.2]
    have h₁ := ((hasDerivAt_id t).const_add p).log hpplus
    have h₂ := ((hasDerivAt_id t).const_sub p).log hpminus
    have h₃ := ((hasDerivAt_id t).const_sub q).log hqminus
    have h₄ := ((hasDerivAt_id t).const_add q).log hqplus
    convert ((h₁.sub h₂).const_mul (a:ℝ)).add ((h₃.sub h₄).const_mul (b:ℝ)) using 1
    · rfl
    · simp only [id_eq]
      ring
  have hmono : MonotoneOn H (Set.Icc 0 x) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 x)
    · intro t ht
      exact (hD t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hD t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hD t (interior_subset ht)).deriv]
      exact beta_reflection_derivative_nonneg _ _ p q t (Nat.cast_nonneg _) hp hpq
        (interior_subset ht).1 ((interior_subset ht).2.trans_lt hxp) hab
  have hh := hmono (show 0∈Set.Icc (0:ℝ) x from ⟨le_refl _,hx0⟩)
    (show x∈Set.Icc (0:ℝ) x from ⟨hx0,le_refl _⟩) hx0
  have hpx : 0<p-x := by linarith
  have hqx : 0<q-x := by linarith
  have hpx' : 0<p+x := by linarith
  have hqx' : 0<q+x := by linarith
  apply (log_le_log_iff (mul_pos (pow_pos hpx _) (pow_pos hqx' _))
    (mul_pos (pow_pos hpx' _) (pow_pos hqx _))).mp
  rw [log_mul (pow_pos hpx _).ne' (pow_pos hqx' _).ne',
    log_mul (pow_pos hpx' _).ne' (pow_pos hqx _).ne',log_pow,log_pow,log_pow,log_pow]
  dsimp only [H] at hh
  simp only [add_zero,sub_zero,sub_self,mul_zero,zero_add] at hh
  linarith

end
end Cycle12
