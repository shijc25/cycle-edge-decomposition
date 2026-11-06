import Cycle12.HypergeometricDistribution

namespace Cycle12
open Polynomial
noncomputable section

def bernoulliPolynomial (p : ℝ) : Polynomial ℂ := C (1-(p:ℂ))+C (p:ℂ)*X

def rootBernoulliParameter (r : ℂ) : ℝ := (1-r.re)⁻¹

theorem root_bernoulli_parameter_bounds {r : ℂ} (hr : r.re ≤ 0) :
    0<rootBernoulliParameter r ∧ rootBernoulliParameter r ≤ 1 := by
  have hd : 0<1-r.re := by linarith
  refine ⟨inv_pos.mpr hd,?_⟩
  change (1-r.re)⁻¹ ≤ 1
  rw [inv_le_one₀ hd]
  linarith only [hr]

theorem root_bernoulli_factor_eval {r : ℂ} (hi : r.im=0) (hr : r.re ≤ 0) (z : ℂ) :
    z-r=(1-r)*(bernoulliPolynomial (rootBernoulliParameter r)).eval z := by
  have hd : (1-r.re)≠0 := ne_of_gt (by linarith)
  have he : r=(r.re:ℂ) := by apply Complex.ext <;> simp [hi]
  have hp : (1-r)*(rootBernoulliParameter r:ℂ)=1 := by
    unfold rootBernoulliParameter
    rw [he]
    push_cast
    exact mul_inv_cancel₀ (by exact_mod_cast hd)
  simp only [bernoulliPolynomial,eval_add,eval_C,eval_mul,eval_X]
  linear_combination (1-z)*hp

/-- A normalized polynomial with real nonpositive roots is an actual
finite product of Bernoulli probability generating polynomials. Multiplicity
is retained by the root multiset. -/
theorem real_root_bernoulli_factorization (P : Polynomial ℂ) (hP1 : P.eval 1=1)
    (hroots : ∀ z, P.IsRoot z → z.im=0 ∧ z.re ≤ 0) :
    P=(P.roots.map (fun r => bernoulliPolynomial (rootBernoulliParameter r))).prod ∧
      ∀ r∈P.roots, 0<rootBernoulliParameter r ∧ rootBernoulliParameter r ≤ 1 := by
  have hP : P≠0 := by intro h; rw [h,eval_zero] at hP1; exact zero_ne_one hP1
  have hr : ∀ r∈P.roots, r.im=0 ∧ r.re ≤ 0 := by
    intro r hr
    exact hroots r ((mem_roots hP).mp hr)
  refine ⟨?_,fun r h => root_bernoulli_parameter_bounds (hr r h).2⟩
  apply Polynomial.funext
  intro z
  rw [(IsAlgClosed.splits P).eval_eq_prod_roots]
  have hmap : P.roots.map (fun r => z-r)=P.roots.map
      (fun r => (1-r)*(bernoulliPolynomial (rootBernoulliParameter r)).eval z) := by
    exact Multiset.map_congr rfl (fun r h => root_bernoulli_factor_eval (hr r h).1 (hr r h).2 z)
  rw [hmap,Multiset.prod_map_mul,← mul_assoc]
  have hn : P.leadingCoeff*(P.roots.map (fun r => 1-r)).prod=1 := by
    rw [← (IsAlgClosed.splits P).eval_eq_prod_roots,hP1]
  rw [hn,one_mul,eval_multiset_prod,Multiset.map_map]
  rfl

/-- The hypergeometric probability polynomial admits Bernoulli factors.
This is a one-variable distribution representation, not an assertion that
different vertices' marked-neighbor counts are independent. -/
theorem hypergeom_bernoulli_factorization (d b t : ℕ) (ht : t ≤ d+b) :
    normalizedHypergeom d b t=
      ((normalizedHypergeom d b t).roots.map
        (fun r => bernoulliPolynomial (rootBernoulliParameter r))).prod ∧
      ∀ r∈(normalizedHypergeom d b t).roots,
        0<rootBernoulliParameter r ∧ rootBernoulliParameter r ≤ 1 :=
  real_root_bernoulli_factorization _ (normalized_hypergeom_eval_one d b t ht)
    (fun _ hz => normalized_hypergeom_roots d b t ht hz)

end
end Cycle12
