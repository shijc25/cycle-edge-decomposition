import Cycle12.Foundations.SubsetBernoulliMGF

namespace Cycle13
open Finset Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exp_neg_le_quadratic {x : ℝ} (hx : 0 ≤ x) :
    exp (-x) ≤ 1-x+x^2/2 := by
  have hd (y : ℝ) : HasDerivAt (fun t : ℝ => 1-t+t^2/2-exp (-t))
      (-1+y+exp (-y)) y := by
    convert (((hasDerivAt_const y (1:ℝ)).sub (hasDerivAt_id y)).add
      (((hasDerivAt_id y).pow 2).div_const 2)).sub
        (((hasDerivAt_id y).neg).exp) using 1 <;> (try funext t) <;> dsimp <;> ring
  have hm := monotone_of_hasDerivAt_nonneg hd (fun y => by
    change 0 ≤ -1+y+exp (-y)
    have hh := Real.add_one_le_exp (-y)
    linarith)
  have hh := hm hx
  simpa only [neg_zero,exp_zero,sub_zero,zero_pow (by omega : 2≠0),zero_div,
    add_zero,sub_self,sub_nonneg] using hh

theorem subsetBernoulli_lower_tail (W : Finset V) (p : unitInterval)
    (D : Finset V) (hD : D⊆W) {ν : ℝ} (hν : ν ≤ 1) :
    (subsetBernoulli W p).prob (fun S => ((S∩D).card:ℝ) ≤ ν*(p:ℝ)*D.card) ≤
      exp (-(1-ν)^2*(p:ℝ)*D.card/2) := by
  let μ := (p:ℝ)*D.card
  let δ := 1-ν
  have hδ : 0 ≤ δ := by dsimp [δ]; linarith
  have hh := (subsetBernoulli W p).exp_markov_le
    (fun S => -((S∩D).card:ℝ)) δ (-ν*μ) hδ
  have hbad : (fun S : Finset V => ((S∩D).card:ℝ) ≤ ν*(p:ℝ)*D.card)=
      (fun S => -ν*μ ≤ -((S∩D).card:ℝ)) := by
    funext S; apply propext; dsimp [μ]; constructor <;> intro h <;> nlinarith
  rw [hbad]
  apply hh.trans
  have he : (fun S : Finset V => exp (δ*-((S∩D).card:ℝ)))=
      (fun S => exp (-δ*((S∩D).card:ℝ))) := by funext S; congr 1; ring
  rw [he]
  apply le_trans (mul_le_mul_of_nonneg_left
    (subsetBernoulli_count_mgf_le W p D (-δ) hD) (exp_pos _).le)
  rw [← exp_add]
  apply exp_le_exp.mpr
  have hnon : 0 ≤ μ := mul_nonneg p.2.1 (Nat.cast_nonneg _)
  have hs := mul_le_mul_of_nonneg_right (exp_neg_le_quadratic hδ) hnon
  calc
    _ = -δ*(-ν*μ)+μ*(exp (-δ)-1) := by dsimp [μ]; ring
    _ ≤ -δ*(-ν*μ)+μ*((1-δ+δ^2/2)-1) := by nlinarith
    _ = _ := by dsimp [δ,μ]; ring

theorem exp_neg_half_le_five_eighths : exp (-(1/2:ℝ)) ≤ 5/8 := by
  have hh := Real.quadratic_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)
  rw [Real.exp_neg]
  rw [inv_eq_one_div]
  apply (div_le_iff₀ (exp_pos _)).mpr
  nlinarith

theorem subsetBernoulli_lower_half (W : Finset V) (p : unitInterval) (D : Finset V) (hD : D⊆W) :
    (subsetBernoulli W p).prob (fun S => ((S∩D).card:ℝ) ≤ (p:ℝ)*D.card/2) ≤
      exp (-(p:ℝ)*D.card/8) := by
  let μ := (p:ℝ)*D.card
  have hh := (subsetBernoulli W p).exp_markov_le
    (fun S => -((S∩D).card:ℝ)) (1/2) (-μ/2) (by norm_num)
  have hbad : (fun S : Finset V => ((S∩D).card:ℝ) ≤ μ/2)=
      (fun S => -μ/2 ≤ -((S∩D).card:ℝ)) := by funext S; apply propext; constructor <;> intro h <;> linarith
  change (subsetBernoulli W p).prob (fun S => ((S∩D).card:ℝ) ≤ μ/2) ≤ _
  rw [hbad]
  apply hh.trans
  have he : (fun S : Finset V => exp ((1/2)*-((S∩D).card:ℝ)))=
      (fun S => exp (-(1/2)*((S∩D).card:ℝ))) := by funext S; congr 1; ring
  rw [he]
  apply le_trans (mul_le_mul_of_nonneg_left
    (subsetBernoulli_count_mgf_le W p D (-(1/2)) hD) (exp_pos _).le)
  rw [← exp_add]
  apply exp_le_exp.mpr
  have hnon : 0 ≤ (p:ℝ)*D.card := mul_nonneg p.2.1 (Nat.cast_nonneg _)
  have hs := mul_le_mul_of_nonneg_right exp_neg_half_le_five_eighths hnon
  dsimp [μ]
  nlinarith

end
end Cycle13
