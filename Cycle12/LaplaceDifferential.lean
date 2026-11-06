import Cycle12.FiniteLaplace

namespace Cycle12
open Finset Cycle13 Real
noncomputable section
variable {Ω : Type} [Fintype Ω]

/-- Integrating the sharp Janson differential inequality, using a positive
integrating factor and no division by a possibly small Laplace transform. -/
theorem finite_laplace_of_slope (mu : FiniteLaw Ω) (X : Ω → ℝ) (m r : ℝ)
    (hr : 0 < r)
    (hstep : ∀ t : ℝ, 0 ≤ t → m*exp (-r*t)*finiteLaplace mu X t ≤
      mu.expect (fun x => X x*exp (-t*X x)))
    (s : ℝ) (hs : 0 ≤ s) :
    finiteLaplace mu X s ≤ exp ((m/r)*(exp (-r*s)-1)) := by
  let H : ℝ → ℝ := fun t => exp ((m/r)*(1-exp (-r*t)))
  let F : ℝ → ℝ := fun t => finiteLaplace mu X t*H t
  have hH (t : ℝ) : HasDerivAt H (m*exp (-r*t)*H t) t := by
    have he : HasDerivAt (fun x : ℝ => exp (-r*x)) (-r*exp (-r*t)) t := by
      convert (((hasDerivAt_id t).const_mul (-r)).exp) using 1 <;>
        simp only [id_eq,mul_one] <;> ring
    convert ((he.const_sub 1).const_mul (m/r)).exp using 1
    dsimp only [H]
    field_simp
  have hF (t : ℝ) : HasDerivAt F
      (-mu.expect (fun x => X x*exp (-t*X x))*H t+
        finiteLaplace mu X t*(m*exp (-r*t)*H t)) t :=
    (finite_laplace_derivative mu X t).mul (hH t)
  have hanti : AntitoneOn F (Set.Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · exact (continuous_iff_continuousAt.mpr (fun t => (hF t).continuousAt)).continuousOn
    · intro t _
      exact (hF t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hF t).deriv]
      have ht0 : 0 ≤ t := (interior_subset ht)
      have hh := mul_le_mul_of_nonneg_right (hstep t ht0) (show 0 ≤ H t from (exp_pos _).le)
      nlinarith
  have hh := hanti (show 0∈Set.Ici (0:ℝ) by norm_num) hs hs
  have hF0 : F 0=1 := by simp [F,H]
  rw [hF0] at hh
  have hcancel : exp ((m/r)*(exp (-r*s)-1))*H s=1 := by
    dsimp only [H]
    rw [← exp_add]
    convert exp_zero using 1
    ring
  exact (mul_le_mul_iff_left₀ (show 0 < H s from exp_pos _)).mp (hh.trans_eq hcancel.symm)

end
end Cycle12
