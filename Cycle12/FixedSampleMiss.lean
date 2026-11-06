import Cycle12.FixedSizeLaw

namespace Cycle12
open Finset Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The exact without-replacement avoidance ratio is bounded by the
corresponding independent power. This does not assume independent membership. -/
theorem choose_ratio_le_power {a n k : ℕ} (han : a ≤ n) (hn : 0<n) (hk : k ≤ n) :
    (a.choose k:ℝ)/(n.choose k:ℝ) ≤ ((a:ℝ)/n)^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hkn : k ≤ n := by omega
    have ih := ih hkn
    by_cases hka : k+1 ≤ a
    · have ha0 : k ≤ a := by omega
      have hnR : (0:ℝ)<n := by exact_mod_cast hn
      have haR : (a:ℝ) ≤ n := by exact_mod_cast han
      have hnk : (0:ℝ)<(n:ℝ)-k := sub_pos.mpr (by exact_mod_cast (show k<n by omega))
      have hak : (0:ℝ) ≤ (a:ℝ)-k := sub_nonneg.mpr (by exact_mod_cast ha0)
      have hpos : (0:ℝ)<(n.choose k:ℝ) := by exact_mod_cast Nat.choose_pos hkn
      have hpos' : (0:ℝ)<(n.choose (k+1):ℝ) := by exact_mod_cast Nat.choose_pos hk
      have hc₁ : (a.choose (k+1):ℝ)*(k+1)=(a.choose k:ℝ)*((a:ℝ)-k) := by
        have hh := congrArg (fun r : ℕ => (r:ℝ)) (Nat.choose_succ_right_eq a k)
        simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_sub ha0] using hh
      have hc₂ : (n.choose (k+1):ℝ)*(k+1)=(n.choose k:ℝ)*((n:ℝ)-k) := by
        have hh := congrArg (fun r : ℕ => (r:ℝ)) (Nat.choose_succ_right_eq n k)
        simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_sub hkn] using hh
      have hratio : (a.choose (k+1):ℝ)/(n.choose (k+1):ℝ)=
          ((a.choose k:ℝ)/(n.choose k:ℝ))*(((a:ℝ)-k)/((n:ℝ)-k)) := by
        apply (div_eq_iff hpos'.ne').mpr
        field_simp
        nlinarith only [hc₁,hc₂]
      have hstep : ((a:ℝ)-k)/((n:ℝ)-k) ≤ (a:ℝ)/n := by
        apply (div_le_div_iff₀ hnk hnR).mpr
        have hh := mul_le_mul_of_nonneg_left haR (Nat.cast_nonneg (α:=ℝ) k)
        nlinarith only [hh]
      rw [hratio,pow_succ]
      exact mul_le_mul ih hstep (div_nonneg hak hnk.le) (pow_nonneg (div_nonneg (Nat.cast_nonneg _) hnR.le) _)
    · rw [Nat.choose_eq_zero_of_lt (by omega : a<k+1),Nat.cast_zero,zero_div]
      exact pow_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _

variable {V : Type} [Fintype V] [DecidableEq V]

theorem fixed_sample_miss_probability (D B : Finset V) (hB : B⊆D)
    {k : ℕ} (hk : k ≤ D.card) :
    (fixedSizeLaw D k).prob (fun A => A∩B=∅)=
      ((D.card-B.card).choose k:ℝ)/(D.card.choose k:ℝ) := by
  have hh := fixed_size_intersection_probability D B hB hk (Nat.zero_le k)
  simpa only [card_eq_zero,Nat.choose_zero_right,Nat.cast_one,one_mul,Nat.sub_zero] using hh

theorem fixed_sample_miss_exponential (D B : Finset V) (hD : D.Nonempty)
    (hB : B⊆D) {k : ℕ} (hk : k ≤ D.card) :
    (fixedSizeLaw D k).prob (fun A => A∩B=∅) ≤ exp (-(k:ℝ)*B.card/D.card) := by
  rw [fixed_sample_miss_probability D B hB hk]
  have hbound := choose_ratio_le_power (Nat.sub_le D.card B.card) (card_pos.mpr hD) hk
  have hn : (0:ℝ)<D.card := by exact_mod_cast card_pos.mpr hD
  have hb : (B.card:ℝ) ≤ D.card := by exact_mod_cast card_le_card hB
  have he : ((D.card-B.card:ℕ):ℝ)/(D.card:ℝ)=1-(B.card:ℝ)/D.card := by
    rw [Nat.cast_sub (card_le_card hB)]
    field_simp
  rw [he] at hbound
  have hbase := Real.add_one_le_exp (-(B.card:ℝ)/D.card)
  rw [neg_div] at hbase
  have hnonneg : 0 ≤ 1-(B.card:ℝ)/D.card := sub_nonneg.mpr ((div_le_one hn).mpr hb)
  have hp := pow_le_pow_left₀ hnonneg (show 1-(B.card:ℝ)/D.card ≤ exp (-(B.card:ℝ)/D.card) by
    simpa only [neg_div,sub_eq_add_neg,add_comm] using hbase) k
  apply hbound.trans
  apply hp.trans_eq
  rw [← exp_nat_mul]
  congr 1
  ring

end
end Cycle12
