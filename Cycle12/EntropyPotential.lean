import Mathlib

namespace Cycle12
open Real Set
noncomputable section

/-- Twice the normalized sparse-cut remainder potential. -/
def rawEntropy (x : ℝ) : ℝ := x*(1+log x/log 2)
def truncatedEntropy (x : ℝ) : ℝ := if x ≤ 1 then x^2 else rawEntropy x

theorem raw_entropy_hasDeriv {x : ℝ} (hx : 0 < x) :
    HasDerivAt rawEntropy (1+(log x+1)/log 2) x := by
  have h := (hasDerivAt_id x).mul
    ((hasDerivAt_const x (1:ℝ)).add ((hasDerivAt_log hx.ne').div_const (log 2)))
  convert h using 1
  · funext y
    simp [rawEntropy]
  · have hl : log (2:ℝ)≠0 := (log_pos (by norm_num : (1:ℝ)<2)).ne'
    simp only [Pi.add_apply,id_eq]
    field_simp
    <;> ring

theorem raw_entropy_increment_mono {x : ℝ} (hx : 0 ≤ x) :
    MonotoneOn (fun y => rawEntropy (x+y)-rawEntropy y) (Ioi 0) := by
  have hder (y : ℝ) (hy : 0 < y) :
      HasDerivAt (fun z => rawEntropy (x+z)-rawEntropy z)
        ((1+(log (x+y)+1)/log 2)-(1+(log y+1)/log 2)) y := by
    have h := ((raw_entropy_hasDeriv (show 0 < x+y by linarith)).comp y
      ((hasDerivAt_id y).const_add x)).sub (raw_entropy_hasDeriv hy)
    convert h using 1 <;> simp only [Function.comp_def,mul_one]
    funext z
    rfl
  apply monotoneOn_of_deriv_nonneg (convex_Ioi (0:ℝ))
    (fun y hy => (hder y hy).continuousAt.continuousWithinAt)
    (fun y hy => (hder y (interior_subset hy)).differentiableAt.differentiableWithinAt)
  intro y hy
  have hyp : 0 < y := interior_subset hy
  rw [(hder y hyp).deriv]
  have hl := log_le_log hyp (show y ≤ x+y by linarith)
  have hd := div_le_div_of_nonneg_right (add_le_add_right hl 1)
    (log_pos (by norm_num : (1:ℝ)<2)).le
  convert sub_nonneg.mpr (add_le_add_left hd 1) using 1 <;> ring

theorem log_two_secant {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    x ≤ log (1+x)/log 2 := by
  have hh := strictConcaveOn_log_Ioi.concaveOn.2
    (show (1:ℝ)∈Ioi 0 by norm_num) (show (2:ℝ)∈Ioi 0 by norm_num)
    (show 0 ≤ 1-x by linarith) hx (show (1-x)+x=1 by ring)
  simp only [smul_eq_mul,log_one,mul_zero,zero_add] at hh
  have he : (1-x)*1+x*2=1+x := by ring
  rw [he] at hh
  exact (le_div_iff₀ (log_pos (by norm_num : (1:ℝ)<2))).mpr hh

theorem raw_entropy_above_square {x : ℝ} (hx : 1 ≤ x) (hx2 : x ≤ 2) :
    x^2 ≤ rawEntropy x := by
  have hh := log_two_secant (show 0 ≤ x-1 by linarith) (show x-1 ≤ 1 by linarith)
  rw [show 1+(x-1)=x by ring] at hh
  have hm := mul_le_mul_of_nonneg_left hh (show 0 ≤ x by linarith)
  unfold rawEntropy
  nlinarith only [hm]

theorem raw_entropy_double {x : ℝ} (hx : 0 < x) :
    rawEntropy (2*x)-2*rawEntropy x=2*x := by
  unfold rawEntropy
  rw [log_mul (by norm_num) hx.ne']
  have hlog : log (2:ℝ)≠0 := (log_pos (by norm_num : (1:ℝ)<2)).ne'
  field_simp
  <;> ring

/-- The exact cut payment, with the simple-graph cap retained below the
truncation scale. It holds uniformly across the transition at x+y=1. -/
theorem truncated_entropy_split {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    2*min (x*y) x ≤ truncatedEntropy (x+y)-truncatedEntropy x-truncatedEntropy y := by
  have hy := hx.trans hxy
  by_cases hx1 : x ≤ 1
  · by_cases hy1 : y ≤ 1
    · have hm : x*y ≤ x := by nlinarith [mul_le_mul_of_nonneg_left hy1 hx]
      rw [min_eq_left hm]
      by_cases hs : x+y ≤ 1
      · simp only [truncatedEntropy,if_pos hs,if_pos hx1,if_pos hy1]
        nlinarith
      · have hb := raw_entropy_above_square (le_of_not_ge hs)
          (show x+y ≤ 2 by linarith)
        simp only [truncatedEntropy,if_neg hs,if_pos hx1,if_pos hy1]
        nlinarith only [hb]
    · have hygt : 1 < y := lt_of_not_ge hy1
      have hsum : ¬x+y ≤ 1 := by linarith
      have hm : x ≤ x*y := by nlinarith [mul_le_mul_of_nonneg_left hygt.le hx]
      have hinc := raw_entropy_increment_mono hx
        (show (1:ℝ)∈Ioi 0 by norm_num) (show 0 < y by linarith) hygt.le
      have hb := raw_entropy_above_square (x:=x+1) (by linarith) (by linarith)
      norm_num [rawEntropy] at hinc
      rw [min_eq_right hm]
      simp only [truncatedEntropy,if_neg hsum,if_pos hx1,if_neg hy1]
      dsimp only [rawEntropy] at hb ⊢
      nlinarith only [hinc,hb]
  · have hxgt : 1 < x := lt_of_not_ge hx1
    have hy1 : ¬y ≤ 1 := by linarith
    have hsum : ¬x+y ≤ 1 := by linarith
    have hm : x ≤ x*y := by nlinarith [mul_le_mul_of_nonneg_left (show 1 ≤ y by linarith) hx]
    have hinc := raw_entropy_increment_mono hx
      (show 0 < x by linarith) (show 0 < y by linarith) hxy
    have he := raw_entropy_double (show 0 < x by linarith)
    rw [show 2*x=x+x by ring] at he
    rw [min_eq_right hm]
    simp only [truncatedEntropy,if_neg hsum,if_neg hx1,if_neg hy1]
    linarith only [hinc,he]

def entropyPotential (h n : ℝ) : ℝ := h^2/2*truncatedEntropy (n/h)

theorem entropy_potential_small {h n : ℝ} (hh : 0 < h) (hn : n ≤ h) :
    entropyPotential h n=n^2/2 := by
  have he : n/h ≤ 1 := (div_le_one hh).mpr hn
  simp only [entropyPotential,truncatedEntropy,if_pos he]
  field_simp

theorem entropy_potential_large {h n : ℝ} (hh : 0 < h) (hn : h ≤ n) :
    entropyPotential h n=h*n/2*(1+log (n/h)/log 2) := by
  rcases hn.eq_or_lt with he | he
  · subst n
    simp [entropyPotential,truncatedEntropy,hh.ne']
    ring
  · have he' : ¬n/h ≤ 1 := not_le.mpr ((one_lt_div hh).mpr he)
    simp only [entropyPotential,truncatedEntropy,if_neg he',rawEntropy]
    field_simp
    <;> ring

theorem entropy_potential_nonneg {h n : ℝ} (hh : 0 < h) (hn : 0 ≤ n) :
    0 ≤ entropyPotential h n := by
  by_cases hnh : n ≤ h
  · rw [entropy_potential_small hh hnh]
    positivity
  · rw [entropy_potential_large hh (le_of_not_ge hnh)]
    have he : 1 ≤ n/h := (one_le_div hh).mpr (le_of_not_ge hnh)
    have hl := log_nonneg he
    positivity [log_pos (by norm_num : (1:ℝ)<2)]

theorem entropy_potential_split {h a b : ℝ} (hh : 0 < h) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    min (a*b) (h*min a b)+entropyPotential h a+entropyPotential h b ≤ entropyPotential h (a+b) := by
  wlog hab : a ≤ b generalizing a b
  · have h := this hb ha (le_of_not_ge hab)
    simpa only [mul_comm b a,min_comm b a,add_comm b a,add_right_comm] using h
  have hs := truncated_entropy_split (div_nonneg ha hh.le) (div_le_div_of_nonneg_right hab hh.le)
  have hmul := mul_le_mul_of_nonneg_left hs (sq_nonneg h)
  have he : h^2*min (a/h*(b/h)) (a/h)=min (a*b) (h*a) := by
    rw [mul_min_of_nonneg _ _ (sq_nonneg h)]
    congr 1 <;> field_simp
  rw [show a/h+b/h=(a+b)/h by ring] at hmul
  rw [min_eq_left hab]
  unfold entropyPotential
  nlinarith only [hmul,he]

end
end Cycle12
