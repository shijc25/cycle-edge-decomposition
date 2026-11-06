import Cycle12.ThreeVoteBound
import Cycle12.FixedIntersectionDisintegration

namespace Cycle12
open Finset Cycle13
noncomputable section
attribute [local instance] Classical.propDecidable

theorem real_cast_choose_three (n : ℕ) :
    (n.choose 3:ℝ)=(n:ℝ)*(n-1)*(n-2)/6 := by
  by_cases hn : 2 ≤ n
  · have hh := congrArg (fun a : ℕ => (a:ℝ)) (Nat.descFactorial_eq_factorial_mul_choose n 3)
    rw [Nat.descFactorial_succ,Nat.cast_mul,Nat.cast_sub hn,Nat.cast_descFactorial_two] at hh
    norm_num at hh
    linarith only [hh]
  · interval_cases n <;> norm_num [Nat.choose]

variable {V : Type} [Fintype V] [DecidableEq V]

theorem three_subset_majority_probability (D B : Finset V)
    (hD : 3 ≤ D.card) (hB : B⊆D) :
    (fixedSizeLaw D 3).prob (fun S => 2 ≤ (S∩B).card)=
      ((B.card.choose 2:ℝ)*(D.card-B.card)+(B.card.choose 3:ℝ))/(D.card.choose 3:ℝ) := by
  have he : (fixedSizeLaw D 3).prob (fun S => 2 ≤ (S∩B).card)=
      (fixedSizeLaw D 3).prob (fun S => (S∩B).card=2)+
      (fixedSizeLaw D 3).prob (fun S => (S∩B).card=3) := by
    rw [FiniteLaw.prob,FiniteLaw.prob,FiniteLaw.prob,← FiniteLaw.expect_add]
    apply finite_expect_congr_support
    intro S hS
    have hc := (fixed_size_support D S hD hS).2
    have hb := card_le_card (inter_subset_left (s₁:=S) (s₂:=B))
    split_ifs <;> norm_num <;> omega
  rw [he,fixed_size_intersection_probability D B hB hD (by omega : 2 ≤ 3),
    fixed_size_intersection_probability D B hB hD (le_refl 3)]
  norm_num
  rw [Nat.cast_sub (card_le_card hB)]
  ring

/-- The unordered three-subset rule has the same conservative cubic
bound as ordered distinct three-vote sampling. -/
theorem three_subset_majority_bound (D B : Finset V)
    (hD : 3 ≤ D.card) (hB : B⊆D) :
    (fixedSizeLaw D 3).prob (fun S => 2 ≤ (S∩B).card) ≤
      majorityCorrection D.card*majorityPolynomial ((B.card:ℝ)/D.card) := by
  rw [three_subset_majority_probability D B hD hB,Nat.cast_choose_two,
    real_cast_choose_three B.card,real_cast_choose_three D.card]
  have hd : (2:ℝ)<D.card := by exact_mod_cast (show 2<D.card by omega)
  have hb : (B.card:ℝ) ≤ D.card := by exact_mod_cast card_le_card hB
  have hbc : (0:ℝ) ≤ B.card := Nat.cast_nonneg _
  have hden : (0:ℝ)<(D.card:ℝ)*(D.card-1)*(D.card-2) :=
    mul_pos (mul_pos (by linarith only [hd]) (by linarith only [hd])) (by linarith only [hd])
  have hd0 : (D.card:ℝ)≠0 := ne_of_gt (by linarith only [hd])
  have hd1 : (D.card:ℝ)-1≠0 := ne_of_gt (by linarith only [hd])
  have hd2 : (D.card:ℝ)-2≠0 := ne_of_gt (by linarith only [hd])
  have hid :
      majorityCorrection D.card*majorityPolynomial ((B.card:ℝ)/D.card)-
        (((B.card:ℝ)*(B.card-1)/2)*((D.card:ℝ)-B.card)+
          (B.card:ℝ)*(B.card-1)*(B.card-2)/6)/
          ((D.card:ℝ)*(D.card-1)*(D.card-2)/6)=
      (B.card:ℝ)*(3*(D.card:ℝ)-2)/((D.card:ℝ)*(D.card-1)*(D.card-2)) := by
    unfold majorityCorrection majorityPolynomial
    field_simp
    <;> ring
  apply sub_nonneg.mp
  rw [hid]
  exact div_nonneg (mul_nonneg hbc (by linarith only [hd])) hden.le

end
end Cycle12
