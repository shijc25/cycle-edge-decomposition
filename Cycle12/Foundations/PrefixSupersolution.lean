import Mathlib

/-! The maximum-ratio argument behind the quantitative terminal-layer bound.
The majorant is independent of the graph-layer masses. -/
namespace Cycle13
open Finset
noncomputable section

theorem prefix_majorant_dichotomy {m K : ℕ} {P L : ℝ} (hL : 0 ≤ L)
    (S U : Fin m → ℝ) (hU : ∀ i, 0 < U i) (hS : ∀ i, 0 ≤ S i)
    (hSL : ∀ i, S i ≤ L)
    (htail : ∀ i : Fin m, m ≤ i.val + K → 1 ≤ U i)
    (hmajor : ∀ i : Fin m, i.val + K < m →
      (∑ j : Fin m with j.val ≤ i.val + K, U j) ≤ P * U i) :
    (∃ i : Fin m, 0 < S i ∧ i.val + K < m ∧
      (∑ j : Fin m with j.val ≤ i.val + K, S j) ≤ P * S i) ∨
      (∀ i : Fin m, S i ≤ L * U i) := by
  classical
  by_cases hfold : ∃ i : Fin m, 0 < S i ∧ i.val + K < m ∧
      (∑ j : Fin m with j.val ≤ i.val + K, S j) ≤ P * S i
  · exact Or.inl hfold
  right
  intro k
  by_contra hk
  have hne : (univ : Finset (Fin m)).Nonempty := ⟨k, mem_univ _⟩
  obtain ⟨i, _, hmax⟩ := exists_max_image univ (fun i : Fin m => S i / U i) hne
  have hrat : L < S i / U i :=
    ((lt_div_iff₀ (hU k)).mpr (lt_of_not_ge hk)).trans_le (hmax k (mem_univ _))
  have hpos : 0 < S i := by
    have h := (lt_div_iff₀ (hU i)).mp hrat
    have hn := mul_nonneg hL (hU i).le
    linarith
  have hnonterminal : i.val + K < m := by
    by_contra hi
    have hu := htail i (by omega)
    have hm := mul_le_mul_of_nonneg_left hu hL
    have hh := (lt_div_iff₀ (hU i)).mp hrat
    have hs := hSL i
    nlinarith
  have hpoint : ∀ j : Fin m, S j ≤ (S i / U i) * U j := by
    intro j
    exact (div_le_iff₀ (hU j)).mp (hmax j (mem_univ _))
  have hbound : (∑ j : Fin m with j.val ≤ i.val + K, S j) ≤ P * S i := by
    calc
      _ ≤ ∑ j : Fin m with j.val ≤ i.val + K, (S i / U i) * U j :=
        sum_le_sum (fun j _ => hpoint j)
      _ = (S i / U i) * (∑ j : Fin m with j.val ≤ i.val + K, U j) := by rw [mul_sum]
      _ ≤ (S i / U i) * (P * U i) :=
        mul_le_mul_of_nonneg_left (hmajor i hnonterminal) (div_nonneg hpos.le (hU i).le)
      _ = P * S i := by field_simp [(hU i).ne']
  exact hfold ⟨i, hpos, hnonterminal, hbound⟩

theorem terminal_layer_mass {m K tail : ℕ} {P L T : ℝ} (hL : 0 ≤ L)
    (S U : Fin m → ℝ) (hU : ∀ i, 0 < U i) (hS : ∀ i, 0 ≤ S i)
    (hSL : ∀ i, S i ≤ L)
    (htail : ∀ i : Fin m, m ≤ i.val + K → 1 ≤ U i)
    (hmajor : ∀ i : Fin m, i.val + K < m →
      (∑ j : Fin m with j.val ≤ i.val + K, U j) ≤ P * U i)
    (hfold : ¬∃ i : Fin m, 0 < S i ∧ i.val + K < m ∧
      (∑ j : Fin m with j.val ≤ i.val + K, S j) ≤ P * S i)
    (hmass : (∑ i : Fin m with i.val + tail < m, U i) ≤ T) :
    (∑ i : Fin m with i.val + tail < m, S i) ≤ L * T := by
  have hpoint := (prefix_majorant_dichotomy hL S U hU hS hSL htail hmajor).resolve_left hfold
  calc
    _ ≤ ∑ i : Fin m with i.val + tail < m, L * U i := sum_le_sum (fun i _ => hpoint i)
    _ = L * (∑ i : Fin m with i.val + tail < m, U i) := by rw [mul_sum]
    _ ≤ L * T := mul_le_mul_of_nonneg_left hmass hL

theorem reverse_indexed_sum_le_tail {m a : ℕ} (u : ℕ → ℝ)
    (hu : ∀ k, 0 ≤ u k) (hs : Summable u) (A : Finset (Fin m))
    (hA : ∀ i ∈ A, a ≤ m - i.val) :
    (∑ i ∈ A, u (m - i.val)) ≤ ∑' k : ℕ, u (k + a) := by
  classical
  let f : Fin m → ℕ := fun i => m - i.val - a
  have hinj : Set.InjOn f (A : Set (Fin m)) := by
    intro i hi j hj he
    have hi' := hA i hi
    have hj' := hA j hj
    dsimp only [f] at he
    apply Fin.ext
    have hii := i.isLt
    have hjj := j.isLt
    omega
  have he : (∑ i ∈ A, u (m - i.val)) = ∑ k ∈ A.image f, u (k + a) := by
    rw [sum_image hinj]
    apply sum_congr rfl
    intro i hi
    congr 1
    have ha := hA i hi
    dsimp only [f]
    omega
  rw [he]
  exact ((summable_nat_add_iff a).mpr hs).sum_le_tsum _ (fun k _ => hu _)

/-- A summable positive supersolution controls every finite number of
layers, not just the length of the numerical witness. -/
theorem terminal_layer_mass_of_supersolution {m K tail : ℕ} {P L T : ℝ}
    (hL : 0 ≤ L) (S : Fin m → ℝ) (hS : ∀ i, 0 ≤ S i) (hSL : ∀ i, S i ≤ L)
    (u : ℕ → ℝ) (hu₀ : ∀ k, 0 ≤ u k) (hu : ∀ k, 1 ≤ k → 0 < u k)
    (hs : Summable u) (hlast : ∀ k, 1 ≤ k → k ≤ K → 1 ≤ u k)
    (hss : ∀ k, K < k → (∑' j : ℕ, u (j + (k - K))) ≤ P * u k)
    (hfold : ¬∃ i : Fin m, 0 < S i ∧ i.val + K < m ∧
      (∑ j : Fin m with j.val ≤ i.val + K, S j) ≤ P * S i)
    (htotal : (∑' j : ℕ, u (j + (tail + 1))) ≤ T) :
    (∑ i : Fin m with i.val + tail < m, S i) ≤ L * T := by
  let U : Fin m → ℝ := fun i => u (m - i.val)
  have hU : ∀ i, 0 < U i := by
    intro i
    exact hu _ (by have hi := i.isLt; omega)
  have htail : ∀ i : Fin m, m ≤ i.val + K → 1 ≤ U i := by
    intro i hi
    exact hlast _ (by have hii := i.isLt; omega) (by omega)
  have hmajor : ∀ i : Fin m, i.val + K < m →
      (∑ j : Fin m with j.val ≤ i.val + K, U j) ≤ P * U i := by
    intro i hi
    apply (reverse_indexed_sum_le_tail u hu₀ hs
      (univ.filter (fun j : Fin m => j.val ≤ i.val + K)) (a := m - i.val - K) ?_).trans
      (hss _ (by omega))
    intro j hj
    have hji := (mem_filter.mp hj).2
    omega
  have hmass : (∑ i : Fin m with i.val + tail < m, U i) ≤ T := by
    apply (reverse_indexed_sum_le_tail u hu₀ hs
      (univ.filter (fun i : Fin m => i.val + tail < m)) (a := tail + 1) ?_).trans htotal
    intro i hi
    have hii := (mem_filter.mp hi).2
    omega
  exact terminal_layer_mass hL S U hU hS hSL htail hmajor hfold hmass

end
end Cycle13
