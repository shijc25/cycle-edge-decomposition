/-
Copyright (c) 2026 Jiacheng Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Cycle12.Independent.SetIndicators
import Cycle12.Independent.LaplaceSummand

/-!
The lower tail for a family of distinct two-element sets in a Bernoulli
sample. A supplied dependency neighborhood has at most D elements; every
other set is disjoint from the chosen set. The proof combines a direct
Laplace estimate, finite-coordinate independence and Mathlib's FKG theorem.
-/
namespace Cycle12.Independent
open Finset Real Cycle13
noncomputable section
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

omit [Fintype V] in
theorem indicatorCount_split (B : I → Finset V) (i : I) (R : Finset I) (hi : i ∉ R)
    (S : Finset V) :
    indicatorCount B univ S = containsIndicator (B i) S +
      indicatorCount B R S + indicatorCount B (univ \ insert i R) S := by
  have h := sum_sdiff (f := fun j => containsIndicator (B j) S)
    (subset_univ (insert i R))
  rw [sum_insert hi] at h
  dsimp [indicatorCount]
  linarith

theorem dependency_laplace_bound (p : unitInterval) (B : I → Finset V)
    (i : I) (R Z : Finset I) {D : ℕ} (hcard : R.card ≤ D)
    (hpair : ∀ j ∈ R, 3 ≤ (B i ∪ B j).card) {s : ℝ} (hs : 0 ≤ s) :
    (bernoulliSubset p).expect (fun S => containsIndicator (B i) S *
      indicatorCount B R S * exp (-s*indicatorCount B Z S)) ≤
      ((D:ℝ)*(p:ℝ)^3) *
        (bernoulliSubset p).expect (fun S => exp (-s*indicatorCount B Z S)) := by
  let E := (bernoulliSubset p).expect (fun S => exp (-s*indicatorCount B Z S))
  have hE : 0 ≤ E := (bernoulliSubset p).expect_nonneg (fun _ => (exp_pos _).le)
  have hterm : ∀ j ∈ R,
      (bernoulliSubset p).expect (fun S => containsIndicator (B i) S *
        containsIndicator (B j) S * exp (-s*indicatorCount B Z S)) ≤ (p:ℝ)^3*E := by
    intro j hj
    apply (indicator_pair_laplace_bound p (B i) (B j) B Z hs).trans
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_of_le_one p.2.1 p.2.2 (hpair j hj)) hE
  calc
    _ = ∑ j ∈ R, (bernoulliSubset p).expect (fun S => containsIndicator (B i) S *
        containsIndicator (B j) S * exp (-s*indicatorCount B Z S)) := by
      simp only [FiniteLaw.expect, indicatorCount, mul_sum, sum_mul]
      rw [sum_comm]
    _ ≤ ∑ _j ∈ R, (p:ℝ)^3*E := sum_le_sum hterm
    _ = (R.card:ℝ)*(p:ℝ)^3*E := by simp; ring
    _ ≤ (D:ℝ)*(p:ℝ)^3*E := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (pow_nonneg p.2.1 _)) hE
    _ = _ := rfl

theorem setFamily_laplace_local (p : unitInterval) (B : I → Finset V)
    (R : I → Finset I) {D : ℕ}
    (hB : ∀ i, (B i).card = 2)
    (hself : ∀ i, i ∉ R i) (hcard : ∀ i, (R i).card ≤ D)
    (hpair : ∀ i j, j ∈ R i → 3 ≤ (B i ∪ B j).card)
    (hdis : ∀ i j, j ∈ univ \ insert i (R i) → Disjoint (B i) (B j))
    {s : ℝ} (hs : 0 ≤ s) (hsa : s*(1+(D:ℝ)*(p:ℝ)) ≤ 1) :
    ((Fintype.card I:ℝ)*(p:ℝ)^2 -
        ((Fintype.card I:ℝ)*(p:ℝ)^2+(Fintype.card I:ℝ)*D*(p:ℝ)^3)*s) *
      (bernoulliSubset p).expect (fun S => exp (-s*indicatorCount B univ S)) ≤
        (bernoulliSubset p).expect (fun S =>
          indicatorCount B univ S * exp (-s*indicatorCount B univ S)) := by
  have hp0 : 0 ≤ (p:ℝ) := p.2.1
  have hD0 : 0 ≤ (D:ℝ) := Nat.cast_nonneg _
  have ha0 : 0 ≤ (D:ℝ)*(p:ℝ) := mul_nonneg hD0 hp0
  have hsq : 0 ≤ (p:ℝ)^2 := sq_nonneg _
  have hremain : 0 ≤ 1-s*((D:ℝ)*(p:ℝ)) := by nlinarith
  have hqr : 0 ≤ (p:ℝ)^2-s*((D:ℝ)*(p:ℝ)^3) := by
    nlinarith [mul_nonneg hsq hremain]
  let L := (bernoulliSubset p).expect (fun S => exp (-s*indicatorCount B univ S))
  have hL : 0 ≤ L := (bernoulliSubset p).expect_nonneg (fun _ => (exp_pos _).le)
  have hi : ∀ i : I,
      exp (-s)*((p:ℝ)^2-s*((D:ℝ)*(p:ℝ)^3))*L ≤
        (bernoulliSubset p).expect (fun S =>
          containsIndicator (B i) S * exp (-s*indicatorCount B univ S)) := by
    intro i
    apply laplace_indicator_summand (bernoulliSubset p) (containsIndicator (B i))
      (indicatorCount B (R i)) (indicatorCount B (univ \ insert i (R i)))
      (indicatorCount B univ) hs hqr (indicator_zero_or_one (B i))
      (indicatorCount_nonneg B (R i)) (indicatorCount_split B i (R i) (hself i))
    · simpa [hB i] using indicator_laplace_independent p (B i) B
        (univ \ insert i (R i)) s (hdis i)
    · exact dependency_laplace_bound p B i (R i) (univ \ insert i (R i))
        (hcard i) (hpair i) hs
  have hsum := sum_le_sum (fun i (_ : i ∈ (univ : Finset I)) => hi i)
  have hsumexp : (∑ i : I, (bernoulliSubset p).expect (fun S =>
      containsIndicator (B i) S * exp (-s*indicatorCount B univ S))) =
      (bernoulliSubset p).expect (fun S =>
        indicatorCount B univ S * exp (-s*indicatorCount B univ S)) := by
    rw [← FiniteLaw.expect_sum]
    congr 1
    funext S
    simp only [indicatorCount, sum_mul]
  rw [hsumexp] at hsum
  simp only [sum_const, card_univ, nsmul_eq_mul] at hsum
  have hexp : 1-s ≤ exp (-s) := by linarith [add_one_le_exp (-s)]
  have hsingle : (p:ℝ)^2*(1-s*(1+(D:ℝ)*(p:ℝ))) ≤
      exp (-s)*((p:ℝ)^2-s*((D:ℝ)*(p:ℝ)^3)) := by
    have he := mul_le_mul_of_nonneg_right hexp hqr
    have hpos := mul_nonneg (sq_nonneg s) (mul_nonneg hD0 (pow_nonneg hp0 3))
    nlinarith
  have hcoeff := mul_le_mul_of_nonneg_left hsingle (Nat.cast_nonneg (Fintype.card I) :
    (0:ℝ) ≤ (Fintype.card I:ℝ))
  have hh := mul_le_mul_of_nonneg_right hcoeff hL
  apply le_trans _ hsum
  convert hh using 1 <;> dsimp [L] <;> ring

theorem setFamily_lower_tail (p : unitInterval) (B : I → Finset V)
    (R : I → Finset I) {D : ℕ}
    (hB : ∀ i, (B i).card = 2)
    (hself : ∀ i, i ∉ R i) (hcard : ∀ i, (R i).card ≤ D)
    (hpair : ∀ i j, j ∈ R i → 3 ≤ (B i ∪ B j).card)
    (hdis : ∀ i j, j ∈ univ \ insert i (R i) → Disjoint (B i) (B j))
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ (Fintype.card I:ℝ)*(p:ℝ)^2) :
    (bernoulliSubset p).prob (fun S =>
      indicatorCount B univ S ≤ (Fintype.card I:ℝ)*(p:ℝ)^2-t) ≤
      exp (-t^2/(2*((Fintype.card I:ℝ)*(p:ℝ)^2+(Fintype.card I:ℝ)*D*(p:ℝ)^3))) := by
  rcases ht0.eq_or_lt with htzero | htpos
  · subst t
    simpa using (bernoulliSubset p).prob_le_one (fun S =>
      indicatorCount B univ S ≤ (Fintype.card I:ℝ)*(p:ℝ)^2)
  have hμ : 0 < (Fintype.card I:ℝ)*(p:ℝ)^2 := htpos.trans_le ht
  have hv : 0 < (Fintype.card I:ℝ)*(p:ℝ)^2+(Fintype.card I:ℝ)*D*(p:ℝ)^3 := by
    exact add_pos_of_pos_of_nonneg hμ (mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (pow_nonneg p.2.1 _))
  apply finite_laplace_lower_tail (bernoulliSubset p) (indicatorCount B univ) hv ht0 ht
  intro s hs
  apply setFamily_laplace_local p B R hB hself hcard hpair hdis hs.1
  have h := (le_div_iff₀ hv).mp hs.2
  have heq : (Fintype.card I:ℝ)*(p:ℝ)^2+(Fintype.card I:ℝ)*D*(p:ℝ)^3 =
      ((Fintype.card I:ℝ)*(p:ℝ)^2)*(1+(D:ℝ)*(p:ℝ)) := by ring
  rw [heq] at h
  nlinarith

end
end Cycle12.Independent
