import Cycle12.DegreeSquareResidual

namespace Cycle12
open Finset
noncomputable section
variable {V : Type} [Fintype V]

/-- The de Caen estimate is a residual sum of squares for the incidence
matrix of the complete graph; this version exposes the exact scalar input. -/
theorem symmetric_boolean_degree_square_bound (A : V → V → ℝ) (d : V → ℝ)
    (hsym : ∀ i j, A i j=A j i) (hrow : ∀ i, ∑ j, A i j=d i)
    (hsq : ∀ i j, (A i j)^2=A i j) (hdiag : ∀ i, A i i=0)
    (hn : 2 < Fintype.card V) :
    (∑ i, (d i)^2) ≤ ((Fintype.card V:ℝ)-2)*(∑ i, d i)/2+
      (∑ i, d i)^2/(2*((Fintype.card V:ℝ)-1)) := by
  classical
  let n : ℝ := Fintype.card V
  let t : ℝ := ∑ i, d i
  let Q : ℝ := ∑ i, (d i)^2
  let c : ℝ := t/(n-1)
  have hn2 : 2<n := by
    change (2:ℝ)<(Fintype.card V:ℝ)
    exact_mod_cast hn
  have hn1 : n-1≠0 := by linarith
  have hr := symmetric_matrix_residual_identity A d hsym hrow hsq (n-2) c
  have hd : (∑ i, ((n-2)*A i i-d i-d i+c)^2)=4*Q-4*c*t+n*c^2 := by
    simp_rw [hdiag]
    have he (i : V) : ((n-2)*0-d i-d i+c)^2=4*(d i)^2-4*c*d i+c^2 := by ring
    simp_rw [he,sum_add_distrib,sum_sub_distrib]
    simp only [← mul_sum,sum_const,card_univ,nsmul_eq_mul,Q,t,n]
  have hs : (∑ i, ((n-2)*A i i-d i-d i+c)^2) ≤
      ∑ i, ∑ j, ((n-2)*A i j-d i-d j+c)^2 := by
    apply sum_le_sum
    intro i _
    exact single_le_sum (f:=fun j => ((n-2)*A i j-d i-d j+c)^2)
      (fun j _ => sq_nonneg _) (mem_univ i)
  rw [hd,hr] at hs
  change 4*Q-4*c*t+n*c^2 ≤
    (n-2)^2*t+2*n*Q+n^2*c^2-4*(n-2)*Q+2*(n-2)*c*t+2*t^2-4*n*c*t at hs
  have hid : ((n-2)^2*t+2*n*Q+n^2*c^2-4*(n-2)*Q+2*(n-2)*c*t+2*t^2-4*n*c*t)-
      (4*Q-4*c*t+n*c^2)=(n-2)*((n-2)*t-2*Q+t^2/(n-1)) := by
    dsimp only [c]
    field_simp
    ring
  have hp : 0≤(n-2)*((n-2)*t-2*Q+t^2/(n-1)) := by
    rw [← hid]
    exact sub_nonneg.mpr hs
  have hinner : 0≤(n-2)*t-2*Q+t^2/(n-1) :=
    (mul_nonneg_iff_of_pos_left (show 0<n-2 by linarith)).mp hp
  change Q≤(n-2)*t/2+t^2/(2*(n-1))
  have he : t^2/(2*(n-1))=(t^2/(n-1))/2 := by field_simp
  rw [he]
  linarith

end
end Cycle12
