import Cycle12.Foundations.ClosedPrefix

/-! An infinite positive recurrence tail with arbitrary positive starting values.
This supplies the infinite part of a variable-prefix certificate. -/
namespace Cycle122
open Finset Filter
open scoped Topology
noncomputable section

def tailPair (r x y : ℝ) : ℕ → ℝ × ℝ
  | 0 => (x,y)
  | n+1 => ((tailPair r x y n).2,
      (1-r)*(tailPair r x y n).2+r*(1-r)*(tailPair r x y n).1)

def tailTerm (r x y : ℝ) (n : ℕ) : ℝ := (tailPair r x y n).1

@[simp] theorem tailTerm_zero (r x y : ℝ) : tailTerm r x y 0=x := rfl
@[simp] theorem tailTerm_one (r x y : ℝ) : tailTerm r x y 1=y := rfl

theorem tailTerm_recurrence (r x y : ℝ) (n : ℕ) :
    tailTerm r x y (n+2)=(1-r)*tailTerm r x y (n+1)+r*(1-r)*tailTerm r x y n := rfl

theorem tailTerm_pos {r x y : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hx : 0 < x) (hy : 0 < y) (n : ℕ) : 0 < tailTerm r x y n := by
  have h : ∀ n, 0 < (tailPair r x y n).1 ∧ 0 < (tailPair r x y n).2 := by
    intro n
    induction n with
    | zero => exact ⟨hx,hy⟩
    | succ n ih =>
      constructor
      · exact ih.2
      · change 0 < (1-r)*(tailPair r x y n).2+r*(1-r)*(tailPair r x y n).1
        exact add_pos (mul_pos (sub_pos.mpr hr1) ih.2)
          (mul_pos (mul_pos hr (sub_pos.mpr hr1)) ih.1)
  exact (h n).1

theorem tailTerm_balance (r x y : ℝ) (n : ℕ) :
    Cycle1249.prefixH r*tailTerm r x y n =
      tailTerm r x y (n+2)-tailTerm r x y (n+3) := by
  have h1 := tailTerm_recurrence r x y (n+1)
  simp only [show n+1+1=n+2 by omega, show n+1+2=n+3 by omega] at h1
  rw [h1,tailTerm_recurrence r x y n]
  unfold Cycle1249.prefixH
  ring

theorem tail_partial_sum_balance (r x y : ℝ) (a n : ℕ) :
    Cycle1249.prefixH r*(∑ k ∈ range n, tailTerm r x y (k+a)) =
      tailTerm r x y (a+2)-tailTerm r x y (n+a+2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ,mul_add,ih,tailTerm_balance]
    have hn : n+1+a+2=n+a+3 := by omega
    rw [hn]
    ring

theorem tailTerm_summable {r x y : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hx : 0 < x) (hy : 0 < y) : Summable (tailTerm r x y) := by
  apply summable_of_sum_range_le (fun n => (tailTerm_pos hr hr1 hx hy n).le)
    (c := tailTerm r x y 2/Cycle1249.prefixH r)
  intro n
  apply (le_div_iff₀ (Cycle1249.prefixH_pos hr hr1)).mpr
  have h := tail_partial_sum_balance r x y 0 n
  simp only [Nat.add_zero,zero_add] at h
  have hp := tailTerm_pos hr hr1 hx hy (n+2)
  nlinarith

theorem tail_infinite_balance {r x y : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hx : 0 < x) (hy : 0 < y) (a : ℕ) :
    Cycle1249.prefixH r*(∑' k : ℕ, tailTerm r x y (k+a))=tailTerm r x y (a+2) := by
  have hs := tailTerm_summable hr hr1 hx hy
  have ha := (summable_nat_add_iff a).mpr hs
  have hleft := ha.hasSum.tendsto_sum_nat.const_mul (Cycle1249.prefixH r)
  have hz := hs.tendsto_atTop_zero.comp (tendsto_add_atTop_nat (a+2))
  have hright : Tendsto (fun n : ℕ => tailTerm r x y (a+2)-tailTerm r x y (n+(a+2)))
      atTop (𝓝 (tailTerm r x y (a+2)-0)) := tendsto_const_nhds.sub hz
  have heq : (fun n : ℕ => Cycle1249.prefixH r*(∑ k ∈ range n, tailTerm r x y (k+a))) =
      (fun n : ℕ => tailTerm r x y (a+2)-tailTerm r x y (n+(a+2))) := by
    funext n
    simpa only [Nat.add_assoc] using tail_partial_sum_balance r x y a n
  rw [heq] at hleft
  simpa using tendsto_nhds_unique hleft hright

theorem tail_total_mass {r x y : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hx : 0 < x) (hy : 0 < y) :
    (∑' k : ℕ, tailTerm r x y k)=(r*x+y)/r^2 := by
  have h := tail_infinite_balance hr hr1 hx hy 0
  simp only [Nat.add_zero,zero_add] at h
  rw [tailTerm_recurrence r x y 0] at h
  simp only [Nat.zero_add,tailTerm_one,tailTerm_zero,Cycle1249.prefixH] at h
  apply (eq_div_iff (ne_of_gt (sq_pos_of_pos hr))).mpr
  apply mul_right_cancel₀ (ne_of_gt (sub_pos.mpr hr1))
  nlinarith [h]

theorem tail_majorant {r x y P : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hx : 0 < x) (hy : 0 < y) (hP : 1 ≤ P*Cycle1249.prefixH r) (a : ℕ) :
    (∑' k : ℕ, tailTerm r x y (k+a)) ≤ P*tailTerm r x y (a+2) := by
  have hb := tail_infinite_balance hr hr1 hx hy a
  have hn : 0 ≤ ∑' k : ℕ, tailTerm r x y (k+a) :=
    tsum_nonneg (fun k => (tailTerm_pos hr hr1 hx hy _).le)
  have hm := mul_le_mul_of_nonneg_right hP hn
  rw [← hb]
  simpa only [one_mul,mul_assoc] using hm

end
end Cycle122
