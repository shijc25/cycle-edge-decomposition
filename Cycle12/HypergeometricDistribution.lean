import Cycle12.HypergeometricRoots
import Cycle12.FixedSizeLaw

namespace Cycle12
open Polynomial Finset Cycle13
noncomputable section
attribute [local instance] Classical.propDecidable

def normalizedHypergeom (d b t : ℕ) : Polynomial ℂ :=
  C (((d+b).choose t:ℂ)⁻¹)*hypergeomPolynomial d b t

theorem hypergeom_polynomial_coeff (d b t j : ℕ) :
    (hypergeomPolynomial d b t).coeff j=
      if j ≤ t then (d.choose j:ℂ)*(b.choose (t-j):ℂ) else 0 := by
  simp only [hypergeomPolynomial,finsetSum_coeff,coeff_C_mul_X_pow]
  simp [Nat.lt_succ_iff]

theorem normalized_hypergeom_eval_one (d b t : ℕ) (ht : t ≤ d+b) :
    (normalizedHypergeom d b t).eval 1=1 := by
  have hn : ((d+b).choose t:ℂ)≠0 := by exact_mod_cast (Nat.choose_pos ht).ne'
  rw [normalizedHypergeom,eval_mul,eval_C,hypergeom_polynomial_eval_one,inv_mul_cancel₀ hn]

theorem normalized_hypergeom_roots (d b t : ℕ) (ht : t ≤ d+b) {z : ℂ}
    (hz : (normalizedHypergeom d b t).IsRoot z) : z.im=0 ∧ z.re ≤ 0 := by
  have hn : ((d+b).choose t:ℂ)≠0 := by exact_mod_cast (Nat.choose_pos ht).ne'
  change eval z (C (((d+b).choose t:ℂ)⁻¹)*hypergeomPolynomial d b t)=0 at hz
  rw [eval_mul,eval_C] at hz
  have hh := (mul_eq_zero.mp hz).resolve_left (inv_ne_zero hn)
  exact hypergeom_polynomial_roots_real_nonpositive d b t ht hh

variable {V : Type} [Fintype V] [DecidableEq V]

theorem fixed_size_count_probability_zero (D B : Finset V) {k j : ℕ}
    (hk : k ≤ D.card) (hkj : k<j) :
    (fixedSizeLaw D k).prob (fun A => (A∩B).card=j)=0 := by
  have hp : (fixedSizeLaw D k).prob (fun A => (A∩B).card=j) ≤
      (fixedSizeLaw D k).prob (fun _ => False) := by
    apply FiniteLaw.prob_mono_support
    intro A hA hj
    have hc := (fixed_size_support D A hk hA).2
    have hh := card_le_card (inter_subset_left (s₁:=A) (s₂:=B))
    omega
  have hz : (fixedSizeLaw D k).prob (fun _ => False)=0 := by
    simp only [FiniteLaw.prob,ite_false,FiniteLaw.expect_const]
  rw [hz] at hp
  exact le_antisymm hp (FiniteLaw.prob_nonneg _ _)

/-- Coefficients of the normalized real-rooted polynomial are exactly
the actual fixed-sample intersection probabilities, at every natural index. -/
theorem fixed_size_hypergeom_coeff (D B : Finset V) (hB : B⊆D)
    {k : ℕ} (hk : k ≤ D.card) (j : ℕ) :
    (normalizedHypergeom B.card (D.card-B.card) k).coeff j=
      (((fixedSizeLaw D k).prob (fun A => (A∩B).card=j):ℝ):ℂ) := by
  have hn : B.card+(D.card-B.card)=D.card := Nat.add_sub_of_le (card_le_card hB)
  rw [normalizedHypergeom,coeff_C_mul,hypergeom_polynomial_coeff,hn]
  by_cases hj : j ≤ k
  · rw [if_pos hj,fixed_size_intersection_probability D B hB hk hj]
    push_cast
    ring
  · rw [if_neg hj,mul_zero,fixed_size_count_probability_zero D B hk (by omega)]
    norm_num

end
end Cycle12
