import Cycle12.Foundations.ClosedPrefix

/-! Retain the unused finite-prefix mass and use it to pay a faster-decaying
terminal potential loss. The all-indices proof is a two-step induction. -/
namespace Cycle124
open Finset Cycle1249
noncomputable section

def prefixTail (r : ℝ) (m : ℕ) : ℝ := ∑' k : ℕ, term r (k+m)

theorem prefixTail_nonneg {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (m : ℕ) :
    0 ≤ prefixTail r m := tsum_nonneg (fun _ => (term_pos hr hr1 _).le)

theorem prefixTail_two_step {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (m : ℕ) :
    r*(1-r)*prefixTail r m ≤ prefixTail r (m+2) := by
  unfold prefixTail
  rw [← tsum_mul_left]
  apply Summable.tsum_le_tsum
  · intro k
    have he := term_recurrence r (k+m)
    have hp := mul_nonneg (sub_pos.mpr hr1).le (term_pos hr hr1 (k+m+1)).le
    have hi : k+(m+2) = k+m+2 := by omega
    rw [hi,he]
    linarith
  · exact ((summable_nat_add_iff m).mpr (summable_term hr hr1)).mul_left _
  · exact (summable_nat_add_iff (m+2)).mpr (summable_term hr hr1)

theorem partial_prefix_add_tail {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    {m : ℕ} (hm : 2 ≤ m) :
    (∑ k ∈ range (m-2), term r (k+2)) + prefixTail r m = (1+r)/r^2-2 := by
  have hs := (summable_nat_add_iff 2).mpr (summable_term hr hr1)
  have hsplit := hs.sum_add_tsum_nat_add (m-2)
  have he : (fun k : ℕ => term r (k+(m-2)+2)) = (fun k : ℕ => term r (k+m)) := by
    funext k
    congr 1
    omega
  rw [he, tail_two_mass hr hr1] at hsplit
  exact hsplit

theorem reverse_prefix_mass_le {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (m : ℕ) :
    (∑ i : Fin m with i.val+2 < m, sequence r (m-i.val)) ≤
      ∑ k ∈ range (m-2), term r (k+2) := by
  classical
  let A := univ.filter (fun i : Fin m => i.val+2 < m)
  let f : Fin m → ℕ := fun i => m-i.val-3
  have hinj : Set.InjOn f (A : Set (Fin m)) := by
    intro i hi j hj he
    have hi' := (mem_filter.mp hi).2
    have hj' := (mem_filter.mp hj).2
    apply Fin.ext
    dsimp only [f] at he
    omega
  have hsum : (∑ i ∈ A, sequence r (m-i.val)) = ∑ k ∈ A.image f, term r (k+2) := by
    rw [sum_image hinj]
    apply sum_congr rfl
    intro i hi
    have hi' := (mem_filter.mp hi).2
    have he : m-i.val=(f i+2)+1 := by dsimp only [f]; omega
    rw [he]
    rfl
  have hsub : A.image f ⊆ range (m-2) := by
    intro k hk
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hk
    have hi' := (mem_filter.mp hi).2
    rw [mem_range]
    dsimp only [f]
    omega
  change (∑ i ∈ A, sequence r (m-i.val)) ≤ _
  rw [hsum]
  exact sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => (term_pos hr hr1 _).le)

/-- The terminal bound keeps its dependence on the actual finite layer count. -/
theorem terminal_layer_mass_truncated {r P L : ℝ} {m : ℕ}
    (hr : 0 < r) (hr1 : r < 1) (hP : 1 ≤ P*prefixH r) (hL : 0 ≤ L) (hm : 2 ≤ m)
    (S : Fin m → ℝ) (hS : ∀ i, 0 ≤ S i) (hSL : ∀ i, S i ≤ L)
    (hfold : ¬∃ i : Fin m, 0 < S i ∧ i.val+2 < m ∧
      (∑ j : Fin m with j.val ≤ i.val+2, S j) ≤ P*S i) :
    (∑ i : Fin m with i.val+2 < m, S i) ≤ L*((1+r)/r^2-2-prefixTail r m) := by
  let U : Fin m → ℝ := fun i => sequence r (m-i.val)
  have hU : ∀ i, 0 < U i := by
    intro i
    exact sequence_pos hr hr1 _ (by have hi := i.isLt; omega)
  have hlast : ∀ i : Fin m, m ≤ i.val+2 → 1 ≤ U i := by
    intro i hi
    exact sequence_last r _ (by have hi' := i.isLt; omega) (by omega)
  have hmajor : ∀ i : Fin m, i.val+2 < m →
      (∑ j : Fin m with j.val ≤ i.val+2, U j) ≤ P*U i := by
    intro i hi
    apply (Cycle13.reverse_indexed_sum_le_tail (sequence r) (sequence_nonneg hr hr1)
      (sequence_summable hr hr1) (univ.filter (fun j : Fin m => j.val ≤ i.val+2))
      (a := m-i.val-2) ?_).trans (sequence_majorant hr hr1 hP _ (by omega))
    intro j hj
    have hji := (mem_filter.mp hj).2
    omega
  have hpoint := (Cycle13.prefix_majorant_dichotomy hL S U hU hS hSL hlast hmajor).resolve_left hfold
  have hmass := reverse_prefix_mass_le hr hr1 m
  have htail := partial_prefix_add_tail hr hr1 hm
  calc
    _ ≤ ∑ i : Fin m with i.val+2 < m, L*U i := sum_le_sum (fun i _ => hpoint i)
    _ = L*(∑ i : Fin m with i.val+2 < m, U i) := by rw [mul_sum]
    _ ≤ L*(∑ k ∈ range (m-2), term r (k+2)) := mul_le_mul_of_nonneg_left hmass hL
    _ = _ := by congr 1; linarith

theorem two_step_comparison {A B : ℕ → ℝ} {beta : ℝ} (hb : 0 ≤ beta)
    (h0 : A 0 ≤ B 0) (h1 : A 1 ≤ B 1)
    (hA : ∀ n, A (n+2) ≤ beta*A n) (hB : ∀ n, beta*B n ≤ B (n+2)) :
    ∀ n, A n ≤ B n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => exact h0
  | one => exact h1
  | more n ih _ => exact (hA n).trans ((mul_le_mul_of_nonneg_left ih hb).trans (hB n))

theorem prefix_tail_absorbs {r C K : ℝ} {loss : ℕ → ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (h0 : C*loss 0 ≤ K*prefixTail r 3) (h1 : C*loss 1 ≤ K*prefixTail r 4)
    (hdec : ∀ n, loss (n+2) ≤ r*(1-r)*loss n) :
    ∀ n, C*loss n ≤ K*prefixTail r (n+3) := by
  apply two_step_comparison (mul_nonneg hr.le (sub_pos.mpr hr1).le) h0 h1
  · intro n
    have h := mul_le_mul_of_nonneg_left (hdec n) hC
    simpa only [mul_assoc, mul_left_comm] using h
  · intro n
    have h := mul_le_mul_of_nonneg_left (prefixTail_two_step hr hr1 (n+3)) hK
    have hi : n+3+2=n+2+3 := by omega
    simpa only [hi,mul_assoc,mul_left_comm] using h

/-- This explicitly pays the potential loss; it does not replace the potential by one. -/
theorem terminal_cost_from_tail {cost f K T J C loss R : ℝ}
    (hcost : cost ≤ f+K*(T-R)+J)
    (hbudget : f+K*T+J ≤ C) (habsorb : C*loss ≤ K*R) :
    cost ≤ C*(1-loss) := by nlinarith

end
end Cycle124
