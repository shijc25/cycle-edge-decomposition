import Mathlib

namespace Cycle13
open Real
noncomputable section

/-- A boundary estimate between two successive BFS layers gives a
square-root increment over two steps. This avoids any differential or
asymptotic approximation in the diameter estimate. -/
theorem sqrt_growth_of_layer_product {x y z g : ℝ}
    (hx : 0 ≤ x) (hy : 0 < y) (hz : 0 ≤ z) (hg : 0 ≤ g)
    (hxz : x ≤ z) (hprod : g*y ≤ (y-x)*(z-y)) :
    sqrt x+sqrt g ≤ sqrt z := by
  have hroot : sqrt x ≤ sqrt z := sqrt_le_sqrt hxz
  have hprod' : g*y ≤ (y-(sqrt x)^2)*((sqrt z)^2-y) := by
    simpa only [sq_sqrt hx,sq_sqrt hz] using hprod
  have hsq := sq_nonneg (y-sqrt x*sqrt z)
  have hmul : g*y ≤ (sqrt z-sqrt x)^2*y := by nlinarith only [hprod',hsq]
  have hg' : g ≤ (sqrt z-sqrt x)^2 := by
    exact (mul_le_mul_iff_left₀ hy).mp (by simpa only [mul_comm] using hmul)
  have hgsq := sq_sqrt hg
  have hgn := sqrt_nonneg g
  nlinarith only [hg',hgsq,hgn,hroot]

/-- Complete discrete induction: if every second square root increases
by sqrt g, and the first ball has at least g vertices, the k-th square
root is at least k*sqrt(g)/2. -/
theorem sqrt_growth_induction (B : ℕ → ℝ) {g : ℝ} (hg : 0 ≤ g)
    (hB : ∀ i, 0 ≤ B i) (hfirst : g ≤ B 1)
    (hstep : ∀ i, sqrt (B i)+sqrt g ≤ sqrt (B (i+2))) (k : ℕ) :
    (k:ℝ)/2*sqrt g ≤ sqrt (B k) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases k with _ | (_ | k)
    · simpa using sqrt_nonneg (B 0)
    · have hh := sqrt_le_sqrt hfirst
      have hn := sqrt_nonneg g
      norm_num only [Nat.cast_one]
      linarith
    · have hh := ih k (by omega)
      have hs := hstep k
      push_cast
      nlinarith only [hh,hs]

end
end Cycle13
