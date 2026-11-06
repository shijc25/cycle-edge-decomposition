import Cycle12.BernoulliLowCoefficients

namespace Cycle12
open Polynomial Finset
noncomputable section
variable {I : Type} [DecidableEq I]

theorem bernoulli_odds_second_sum_lower (S : Finset I) (p : I → ℝ)
    (hp : ∀ i∈S, 0 ≤ p i ∧ p i<1) (hmean : 2 ≤ ∑ i∈S, p i) :
    2*(∑ i∈S, bernoulliOdds (p i)) ≤
      (∑ i∈S, bernoulliOdds (p i))^2-∑ i∈S, (bernoulliOdds (p i))^2 := by
  let B := ∑ i∈S, bernoulliOdds (p i)
  let M := ∑ i∈S, p i
  have hBn : 0 ≤ B := sum_nonneg (fun i hi => bernoulli_odds_nonneg (hp i hi).1 (hp i hi).2)
  have hidentity : B^2-(∑ i∈S, (bernoulliOdds (p i))^2)-M*B=
      ∑ i∈S, p i*bernoulliOdds (p i)*(B-bernoulliOdds (p i)-1) := by
    calc
      _ = ∑ i∈S, (bernoulliOdds (p i)*(B-bernoulliOdds (p i))-p i*B) := by
        simp only [mul_sub,sum_sub_distrib,← sum_mul,← pow_two]
        dsimp [B,M]
        ring
      _ = _ := by
        apply sum_congr rfl
        intro i hi
        have hb := bernoulli_odds_decomposition (hp i hi).2
        linear_combination (B-bernoulliOdds (p i))*hb
  have hnonneg : 0 ≤ ∑ i∈S, p i*bernoulliOdds (p i)*(B-bernoulliOdds (p i)-1) := by
    apply sum_nonneg
    intro i hi
    apply mul_nonneg (mul_nonneg (hp i hi).1 (bernoulli_odds_nonneg (hp i hi).1 (hp i hi).2))
    have hh : (∑ j∈S.erase i, p j) ≤ ∑ j∈S.erase i, bernoulliOdds (p j) :=
      sum_le_sum (fun j hj => bernoulli_probability_le_odds
        (hp j (mem_of_mem_erase hj)).1 (hp j (mem_of_mem_erase hj)).2)
    have h₁ := sum_erase_add S p hi
    have h₂ := sum_erase_add S (fun j => bernoulliOdds (p j)) hi
    have hpi := (hp i hi).2
    change _=B at h₂
    linarith only [hh,h₁,h₂,hmean,hpi]
  have hscale := mul_le_mul_of_nonneg_right hmean hBn
  change 2*B ≤ _
  change 2*B ≤ M*B at hscale
  linarith only [hidentity,hnonneg,hscale]

theorem bernoulli_coeff_one_ge_zero_strict (S : Finset I) (p : I → ℝ)
    (hp : ∀ i∈S, 0 ≤ p i ∧ p i<1) (hmean : 1 ≤ ∑ i∈S, p i) :
    (bernoulliPGF S p).coeff 0 ≤ (bernoulliPGF S p).coeff 1 := by
  obtain ⟨h₀,h₁,_⟩ := bernoulli_low_coefficients S p (fun i hi => (hp i hi).2)
  have hs := sum_le_sum (fun i hi => bernoulli_probability_le_odds (hp i hi).1 (hp i hi).2)
  have hprod : 0 ≤ ∏ i∈S, (1-p i) := prod_nonneg (fun i hi => (sub_pos.mpr (hp i hi).2).le)
  have hh := mul_le_mul_of_nonneg_left (hmean.trans hs) hprod
  rw [h₀,h₁]
  simpa only [mul_one] using hh

theorem bernoulli_coeff_two_ge_one_strict (S : Finset I) (p : I → ℝ)
    (hp : ∀ i∈S, 0 ≤ p i ∧ p i<1) (hmean : 2 ≤ ∑ i∈S, p i) :
    (bernoulliPGF S p).coeff 1 ≤ (bernoulliPGF S p).coeff 2 := by
  obtain ⟨_,h₁,h₂⟩ := bernoulli_low_coefficients S p (fun i hi => (hp i hi).2)
  have hh := bernoulli_odds_second_sum_lower S p hp hmean
  have hprod : 0 ≤ ∏ i∈S, (1-p i) := prod_nonneg (fun i hi => (sub_pos.mpr (hp i hi).2).le)
  have hm := mul_le_mul_of_nonneg_left hh hprod
  rw [← h₂] at hm
  nlinarith only [hm,h₁]

/-- Includes deterministic Bernoulli parameters p=1, which occur at the
endpoint roots of the hypergeometric polynomial. -/
theorem bernoulli_coeff_one_ge_zero (S : Finset I) (p : I → ℝ)
    (hp : ∀ i∈S, 0 ≤ p i ∧ p i ≤ 1) (hmean : 1 ≤ ∑ i∈S, p i) :
    (bernoulliPGF S p).coeff 0 ≤ (bernoulliPGF S p).coeff 1 := by
  by_cases he : ∃ i∈S, p i=1
  · obtain ⟨i,hi,he⟩ := he
    have hf := bernoulli_pgf_erase_factor S p hi
    rw [he] at hf
    simp only [realBernoulliPolynomial,sub_self,map_zero,map_one,one_mul,zero_add] at hf
    rw [hf,coeff_X_mul_zero,coeff_X_mul]
    exact bernoulli_pgf_coeff_nonneg (S.erase i) p (fun j hj => hp j (mem_of_mem_erase hj)) 0
  · apply bernoulli_coeff_one_ge_zero_strict S p _ hmean
    intro i hi
    refine ⟨(hp i hi).1,lt_of_le_of_ne (hp i hi).2 ?_⟩
    intro hh
    exact he ⟨i,hi,hh⟩

theorem bernoulli_coeff_two_ge_one (S : Finset I) (p : I → ℝ)
    (hp : ∀ i∈S, 0 ≤ p i ∧ p i ≤ 1) (hmean : 2 ≤ ∑ i∈S, p i) :
    (bernoulliPGF S p).coeff 1 ≤ (bernoulliPGF S p).coeff 2 := by
  by_cases he : ∃ i∈S, p i=1
  · obtain ⟨i,hi,he⟩ := he
    have hf := bernoulli_pgf_erase_factor S p hi
    rw [he] at hf
    simp only [realBernoulliPolynomial,sub_self,map_zero,map_one,one_mul,zero_add] at hf
    rw [hf,coeff_X_mul _ 0,coeff_X_mul _ 1]
    apply bernoulli_coeff_one_ge_zero (S.erase i) p (fun j hj => hp j (mem_of_mem_erase hj))
    have hh := sum_erase_add S p hi
    rw [he] at hh
    linarith only [hh,hmean]
  · apply bernoulli_coeff_two_ge_one_strict S p _ hmean
    intro i hi
    refine ⟨(hp i hi).1,lt_of_le_of_ne (hp i hi).2 ?_⟩
    intro hh
    exact he ⟨i,hi,hh⟩

end
end Cycle12
