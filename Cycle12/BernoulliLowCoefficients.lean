import Mathlib

namespace Cycle12
open Polynomial Finset
noncomputable section

def realBernoulliPolynomial (p : ℝ) : Polynomial ℝ := C (1-p)+C p*X

def bernoulliPGF {I : Type} (S : Finset I) (p : I → ℝ) : Polynomial ℝ :=
  ∏ i∈S, realBernoulliPolynomial (p i)

def bernoulliOdds (p : ℝ) : ℝ := p/(1-p)

theorem bernoulli_step_coeff_zero (p : ℝ) (Q : Polynomial ℝ) :
    (realBernoulliPolynomial p*Q).coeff 0=(1-p)*Q.coeff 0 := by
  simp [realBernoulliPolynomial,add_mul,mul_assoc,coeff_C_mul,coeff_X_mul_zero]

theorem bernoulli_step_coeff_succ (p : ℝ) (Q : Polynomial ℝ) (n : ℕ) :
    (realBernoulliPolynomial p*Q).coeff (n+1)=
      (1-p)*Q.coeff (n+1)+p*Q.coeff n := by
  simp only [realBernoulliPolynomial,add_mul,mul_assoc,coeff_add,coeff_C_mul,coeff_X_mul]

theorem bernoulli_odds_balance {p : ℝ} (hp : p<1) :
    (1-p)*bernoulliOdds p=p := by
  have h : 1-p≠0 := ne_of_gt (sub_pos.mpr hp)
  unfold bernoulliOdds
  field_simp

theorem bernoulli_odds_decomposition {p : ℝ} (hp : p<1) :
    bernoulliOdds p=p+p*bernoulliOdds p := by
  have hh := bernoulli_odds_balance hp
  nlinarith only [hh]

theorem bernoulli_odds_nonneg {p : ℝ} (h0 : 0 ≤ p) (h1 : p<1) :
    0 ≤ bernoulliOdds p := div_nonneg h0 (sub_pos.mpr h1).le

theorem bernoulli_probability_le_odds {p : ℝ} (h0 : 0 ≤ p) (h1 : p<1) :
    p ≤ bernoulliOdds p := by
  have hh := bernoulli_odds_decomposition h1
  have hn := mul_nonneg h0 (bernoulli_odds_nonneg h0 h1)
  linarith only [hh,hn]

variable {I : Type} [DecidableEq I]

theorem bernoulli_pgf_insert (S : Finset I) (p : I → ℝ) {i : I} (hi : i∉S) :
    bernoulliPGF (insert i S) p=realBernoulliPolynomial (p i)*bernoulliPGF S p := by
  exact prod_insert hi

theorem bernoulli_pgf_erase_factor (S : Finset I) (p : I → ℝ) {i : I} (hi : i∈S) :
    bernoulliPGF S p=realBernoulliPolynomial (p i)*bernoulliPGF (S.erase i) p := by
  have hh := bernoulli_pgf_insert (S.erase i) p (notMem_erase i S)
  simpa only [insert_erase hi] using hh

theorem bernoulli_pgf_coeff_nonneg (S : Finset I) (p : I → ℝ)
    (hp : ∀ i∈S, 0 ≤ p i ∧ p i ≤ 1) (n : ℕ) :
    0 ≤ (bernoulliPGF S p).coeff n := by
  induction S using Finset.induction_on generalizing n with
  | empty => simp [bernoulliPGF,coeff_one]; split_ifs <;> norm_num
  | @insert i S hi ih =>
    have hpS : ∀ j∈S, 0 ≤ p j ∧ p j ≤ 1 := fun j hj => hp j (mem_insert_of_mem hj)
    have hpi := hp i (mem_insert_self _ _)
    rw [bernoulli_pgf_insert S p hi]
    cases n with
    | zero =>
      rw [bernoulli_step_coeff_zero]
      exact mul_nonneg (sub_nonneg.mpr hpi.2) (ih hpS 0)
    | succ n =>
      rw [bernoulli_step_coeff_succ]
      exact add_nonneg (mul_nonneg (sub_nonneg.mpr hpi.2) (ih hpS (n+1)))
        (mul_nonneg hpi.1 (ih hpS n))

/-- Exact first three coefficients, including the square-sum correction
for the coefficient of degree two. -/
theorem bernoulli_low_coefficients (S : Finset I) (p : I → ℝ)
    (hp : ∀ i∈S, p i<1) :
    (bernoulliPGF S p).coeff 0=(∏ i∈S, (1-p i)) ∧
    (bernoulliPGF S p).coeff 1=(∏ i∈S, (1-p i))*(∑ i∈S, bernoulliOdds (p i)) ∧
    2*(bernoulliPGF S p).coeff 2=(∏ i∈S, (1-p i))*
      ((∑ i∈S, bernoulliOdds (p i))^2-∑ i∈S, (bernoulliOdds (p i))^2) := by
  induction S using Finset.induction_on with
  | empty => simp [bernoulliPGF,coeff_one]
  | @insert i S hi ih =>
    obtain ⟨h₀,h₁,h₂⟩ := ih (fun j hj => hp j (mem_insert_of_mem hj))
    have hbal := bernoulli_odds_balance (hp i (mem_insert_self _ _))
    rw [bernoulli_pgf_insert S p hi]
    simp only [prod_insert hi,sum_insert hi]
    refine ⟨?_,?_,?_⟩
    · rw [bernoulli_step_coeff_zero,h₀]
    · rw [bernoulli_step_coeff_succ _ _ 0,h₀,h₁]
      linear_combination -(∏ j∈S, (1-p j))*hbal
    · rw [bernoulli_step_coeff_succ _ _ 1]
      have hnew : 2*((1-p i)*(bernoulliPGF S p).coeff 2+p i*(bernoulliPGF S p).coeff 1)=
          (1-p i)*(2*(bernoulliPGF S p).coeff 2)+2*p i*(bernoulliPGF S p).coeff 1 := by ring
      rw [hnew,h₂,h₁]
      linear_combination -(2*(∏ j∈S, (1-p j))*(∑ j∈S, bernoulliOdds (p j)))*hbal

end
end Cycle12
