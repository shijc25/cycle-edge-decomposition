import Cycle12.Foundations.PrefixSupersolution

/-! An infinite positive prefix supersolution with an exact total mass.
The argument uses telescoping and nonnegative partial sums, with no finite
enumeration or assumed summability. Indices in `term` start at zero. -/
namespace Cycle1249
open Finset Filter
open scoped Topology
noncomputable section

def prefixPair (r : ℝ) : ℕ → ℝ × ℝ
  | 0 => (1, 1)
  | n + 1 => ((prefixPair r n).2,
      (1-r) * (prefixPair r n).2 + r*(1-r) * (prefixPair r n).1)

def term (r : ℝ) (n : ℕ) : ℝ := (prefixPair r n).1
def prefixH (r : ℝ) : ℝ := r^2*(1-r)

@[simp] theorem term_zero (r : ℝ) : term r 0 = 1 := rfl
@[simp] theorem term_one (r : ℝ) : term r 1 = 1 := rfl

theorem term_recurrence (r : ℝ) (n : ℕ) :
    term r (n+2) = (1-r)*term r (n+1) + r*(1-r)*term r n := rfl

theorem term_pos {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (n : ℕ) : 0 < term r n := by
  have h : ∀ n, 0 < (prefixPair r n).1 ∧ 0 < (prefixPair r n).2 := by
    intro n
    induction n with
    | zero => norm_num [prefixPair]
    | succ n ih =>
      constructor
      · exact ih.2
      · change 0 < (1-r)*(prefixPair r n).2 + r*(1-r)*(prefixPair r n).1
        exact add_pos (mul_pos (sub_pos.mpr hr1) ih.2)
          (mul_pos (mul_pos hr (sub_pos.mpr hr1)) ih.1)
  exact (h n).1

theorem prefixH_pos {r : ℝ} (hr : 0 < r) (hr1 : r < 1) : 0 < prefixH r :=
  mul_pos (sq_pos_of_pos hr) (sub_pos.mpr hr1)

theorem term_balance (r : ℝ) (n : ℕ) :
    prefixH r * term r n = term r (n+2) - term r (n+3) := by
  have h1 := term_recurrence r (n+1)
  simp only [show n+1+1=n+2 by omega, show n+1+2=n+3 by omega] at h1
  rw [h1, term_recurrence r n]
  unfold prefixH
  ring

theorem partial_sum_balance (r : ℝ) (a n : ℕ) :
    prefixH r * (∑ k ∈ range n, term r (k+a)) =
      term r (a+2) - term r (n+a+2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih, term_balance]
    have hn : n+1+a+2 = n+a+3 := by omega
    rw [hn]
    ring

theorem summable_term {r : ℝ} (hr : 0 < r) (hr1 : r < 1) : Summable (term r) := by
  apply summable_of_sum_range_le (fun n => (term_pos hr hr1 n).le)
    (c := term r 2 / prefixH r)
  intro n
  apply (le_div_iff₀ (prefixH_pos hr hr1)).mpr
  have h := partial_sum_balance r 0 n
  simp only [Nat.add_zero, zero_add] at h
  have hp := term_pos hr hr1 (n+2)
  nlinarith

theorem tail_balance {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (a : ℕ) :
    prefixH r * (∑' k : ℕ, term r (k+a)) = term r (a+2) := by
  have hs := summable_term hr hr1
  have ha := (summable_nat_add_iff a).mpr hs
  have hleft := ha.hasSum.tendsto_sum_nat.const_mul (prefixH r)
  have hz := hs.tendsto_atTop_zero.comp (tendsto_add_atTop_nat (a+2))
  have hright : Tendsto (fun n : ℕ => term r (a+2) - term r (n+(a+2)))
      atTop (𝓝 (term r (a+2)-0)) := tendsto_const_nhds.sub hz
  have heq : (fun n : ℕ => prefixH r * (∑ k ∈ range n, term r (k+a))) =
      (fun n : ℕ => term r (a+2) - term r (n+(a+2))) := by
    funext n
    simpa only [Nat.add_assoc] using partial_sum_balance r a n
  rw [heq] at hleft
  simpa using tendsto_nhds_unique hleft hright

theorem total_mass {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    (∑' k : ℕ, term r k) = (1+r)/r^2 := by
  have h := tail_balance hr hr1 0
  simp only [Nat.add_zero, zero_add] at h
  have htwo : term r 2 = 1-r^2 := by
    rw [term_recurrence r 0]
    simp
    ring
  rw [htwo] at h
  apply (eq_div_iff (ne_of_gt (sq_pos_of_pos hr))).mpr
  unfold prefixH at h
  have hne : 1-r ≠ 0 := ne_of_gt (sub_pos.mpr hr1)
  apply mul_right_cancel₀ hne
  nlinarith [h]

theorem tail_two_mass {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    (∑' k : ℕ, term r (k+2)) = (1+r)/r^2-2 := by
  have h := (summable_term hr hr1).sum_add_tsum_nat_add 2
  rw [total_mass hr hr1] at h
  norm_num [sum_range_succ] at h
  linarith

theorem tail_majorant {r P : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hP : 1 ≤ P * prefixH r) (a : ℕ) :
    (∑' k : ℕ, term r (k+a)) ≤ P * term r (a+2) := by
  have hb := tail_balance hr hr1 a
  have hn : 0 ≤ ∑' k : ℕ, term r (k+a) :=
    tsum_nonneg (fun k => (term_pos hr hr1 _).le)
  have hm := mul_le_mul_of_nonneg_right hP hn
  rw [← hb]
  simpa only [one_mul, mul_assoc] using hm

/-- One-indexed form used by the graph-layer selection theorem. -/
def sequence (r : ℝ) : ℕ → ℝ
  | 0 => 0
  | n+1 => term r n

theorem sequence_nonneg {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (n : ℕ) :
    0 ≤ sequence r n := by
  cases n with
  | zero => rfl
  | succ n => exact (term_pos hr hr1 n).le

theorem sequence_pos {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (n : ℕ) (hn : 1 ≤ n) :
    0 < sequence r n := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  exact term_pos hr hr1 k

theorem sequence_summable {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    Summable (sequence r) := by
  apply (summable_nat_add_iff 1).mp
  exact summable_term hr hr1

theorem sequence_last (r : ℝ) (k : ℕ) (hk : 1 ≤ k) (hk2 : k ≤ 2) :
    1 ≤ sequence r k := by
  interval_cases k <;> norm_num [sequence]

theorem sequence_majorant {r P : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hP : 1 ≤ P*prefixH r) (k : ℕ) (hk : 2 < k) :
    (∑' j : ℕ, sequence r (j+(k-2))) ≤ P*sequence r k := by
  have hleft : (fun j : ℕ => sequence r (j+(k-2))) =
      (fun j : ℕ => term r (j+(k-3))) := by
    funext j
    have he : j+(k-2) = (j+(k-3))+1 := by omega
    rw [he]
    rfl
  have hright : sequence r k = term r ((k-3)+2) := by
    have he : k = ((k-3)+2)+1 := by omega
    conv_lhs => rw [he]
    rfl
  rw [hleft, hright]
  exact tail_majorant hr hr1 hP (k-3)

theorem sequence_tail {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    (∑' j : ℕ, sequence r (j+3)) = (1+r)/r^2-2 :=
  tail_two_mass hr hr1

/-- The new closed-form witness applies to arbitrarily many graph layers. -/
theorem terminal_layer_mass_closed {r P L : ℝ} {m : ℕ}
    (hr : 0 < r) (hr1 : r < 1) (hP : 1 ≤ P*prefixH r) (hL : 0 ≤ L)
    (S : Fin m → ℝ) (hS : ∀ i, 0 ≤ S i) (hSL : ∀ i, S i ≤ L)
    (hfold : ¬∃ i : Fin m, 0 < S i ∧ i.val+2 < m ∧
      (∑ j : Fin m with j.val ≤ i.val+2, S j) ≤ P*S i) :
    (∑ i : Fin m with i.val+2 < m, S i) ≤ L*((1+r)/r^2-2) := by
  exact Cycle13.terminal_layer_mass_of_supersolution hL S hS hSL (sequence r)
    (sequence_nonneg hr hr1) (sequence_pos hr hr1) (sequence_summable hr hr1)
    (sequence_last r) (sequence_majorant hr hr1 hP) hfold (sequence_tail hr hr1).le

end
end Cycle1249
