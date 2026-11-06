import Mathlib

/-! A falling-factorial potential for contraction with a real cut-size
ratio. Keeping the fractional exponent removes the extra factor of n
caused by integer cut buckets. -/
namespace Cycle13
open Real
noncomputable section

theorem proper_subsets_le_factorial {n : ℕ} (hn : 2 ≤ n) : 2^n-2 ≤ n.factorial := by
  induction n,hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hp : 2 ≤ 2^n := by
      calc
        2 = 2^1 := by norm_num
        _ ≤ 2^n := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hf : 2 ≤ n.factorial := (by norm_num : 2 ≤ Nat.factorial 2).trans (Nat.factorial_le hn)
    rw [pow_succ,Nat.factorial_succ]
    have hs := Nat.sub_add_cancel hp
    have hp' : 2 ≤ 2^n*2 := by omega
    have hs' := Nat.sub_add_cancel hp'
    nlinarith

def fractionalCutPotential (n k : ℕ) (θ : ℝ) : ℝ :=
  (n.descFactorial k:ℝ)*((n:ℝ)-k)^θ

theorem fractionalCutPotential_base (k : ℕ) (θ : ℝ) :
    fractionalCutPotential (k+1) k θ=((k+1).factorial:ℝ) := by
  have hh := Nat.factorial_mul_descFactorial (show k ≤ k+1 by omega)
  simp only [Nat.add_sub_cancel_left,Nat.factorial_one,one_mul] at hh
  simp only [fractionalCutPotential,Nat.cast_add,Nat.cast_one,add_sub_cancel_left,one_rpow,mul_one,hh]

theorem fractional_power_step {b θ : ℝ} (hb : 1 < b) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    b*(b-1)^θ ≤ (b-θ)*b^θ := by
  have hb0 : 0 < b := by linarith
  have hbin := rpow_one_add_le_one_add_mul_self
    (show (-1:ℝ) ≤ -1/b by apply (le_div_iff₀ hb0).mpr; linarith) hθ₀ hθ₁
  have hrat : (b-1)^θ/b^θ ≤ (b-θ)/b := by
    rw [← div_rpow (by linarith : 0 ≤ b-1) hb0.le]
    convert hbin using 1 <;> congr 1 <;> field_simp <;> ring
  simpa only [mul_comm] using (div_le_div_iff₀ (rpow_pos_of_pos hb0 θ) hb0).mp hrat

theorem fractionalCutPotential_step {n k : ℕ} {θ : ℝ}
    (hn : k+1 < n) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    (n:ℝ)*fractionalCutPotential (n-1) k θ ≤
      ((n:ℝ)-((k:ℝ)+θ))*fractionalCutPotential n k θ := by
  have hn1 : 1 ≤ n := by omega
  have hk : k ≤ n := by omega
  have hh := Nat.succ_descFactorial (n-1) k
  rw [Nat.sub_add_cancel hn1] at hh
  have hid : ((n:ℝ)-k)*(n.descFactorial k:ℝ)=(n:ℝ)*((n-1).descFactorial k:ℝ) := by
    exact_mod_cast hh
  have hb : 1 < (n:ℝ)-k := by
    have hh : (k:ℝ)+1 < n := by exact_mod_cast hn
    linarith
  have hp := mul_le_mul_of_nonneg_left (fractional_power_step hb hθ₀ hθ₁)
    (Nat.cast_nonneg (α:=ℝ) (n.descFactorial k))
  unfold fractionalCutPotential
  rw [Nat.cast_sub hn1,Nat.cast_one]
  have hbase : (n:ℝ)-1-k=((n:ℝ)-k)-1 := by ring
  rw [hbase]
  calc
    _ = (n.descFactorial k:ℝ)*(((n:ℝ)-k)*((n:ℝ)-k-1)^θ) := by
      rw [← mul_assoc,← hid]
      ring
    _ ≤ _ := hp
    _ = _ := by ring

theorem fractionalCutPotential_le_rpow {n k : ℕ} {θ : ℝ}
    (hkn : k ≤ n) (hθ : 0 ≤ θ) (hn : 0 < n) :
    fractionalCutPotential n k θ ≤ (n:ℝ)^((k:ℝ)+θ) := by
  have hp : (n.descFactorial k:ℝ) ≤ (n:ℝ)^k := by exact_mod_cast Nat.descFactorial_le_pow n k
  have hb : 0 ≤ (n:ℝ)-k := sub_nonneg.mpr (by exact_mod_cast hkn)
  have hθp := rpow_le_rpow hb (sub_le_self (n:ℝ) (Nat.cast_nonneg k)) hθ
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  calc
    _ ≤ (n:ℝ)^k*(n:ℝ)^θ := mul_le_mul hp hθp (rpow_nonneg hb _) (by positivity)
    _ = _ := by rw [rpow_add hnR, rpow_natCast]

theorem real_contraction_arithmetic {n a K l m C B : ℝ}
    (hl : 0 < l) (ha : 0 ≤ a) (hn : 0 ≤ n) (hC : 0 ≤ C)
    (hK : 2*K ≤ a*l) (hhand : n*l ≤ 2*m)
    (hcount : m*C ≤ m*B+K*C) : (n-a)*C ≤ n*B := by
  by_cases hCB : C ≤ B
  · nlinarith [mul_nonneg ha hC,mul_le_mul_of_nonneg_left hCB hn]
  · have hdiff : 0 ≤ C-B := by linarith
    have hhand' := mul_le_mul_of_nonneg_right hhand hdiff
    have hK' := mul_le_mul_of_nonneg_right hK hC
    have hh : l*((n-a)*C-n*B) ≤ 0 := by nlinarith
    nlinarith

end
end Cycle13
