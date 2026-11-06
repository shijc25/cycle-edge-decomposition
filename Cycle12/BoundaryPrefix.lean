import Cycle12.Foundations.PrefixSupersolution

/-! The folding threshold is allowed to depend on the selected layer. -/
namespace Cycle12
open Finset
noncomputable section

theorem prefix_majorant_dichotomy {m K : ℕ} {L : ℝ} (P : Fin m → ℝ) (hL : 0 ≤ L)
    (S U : Fin m → ℝ) (hU : ∀ i, 0 < U i) (hS : ∀ i, 0 ≤ S i)
    (hboundary : ∀ i : Fin m, m ≤ i.val + K → S i ≤ L * U i)
    (hmajor : ∀ i : Fin m, i.val + K < m →
      (∑ j : Fin m with j.val ≤ i.val + K, U j) ≤ P i * U i) :
    (∃ i : Fin m, 0 < S i ∧ i.val + K < m ∧
      (∑ j : Fin m with j.val ≤ i.val + K, S j) ≤ P i * S i) ∨
      (∀ i : Fin m, S i ≤ L * U i) := by
  classical
  by_cases hfold : ∃ i : Fin m, 0 < S i ∧ i.val + K < m ∧
      (∑ j : Fin m with j.val ≤ i.val + K, S j) ≤ P i * S i
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
    have hh := (lt_div_iff₀ (hU i)).mp hrat
    have hs := hboundary i (by omega)
    linarith
  have hpoint : ∀ j : Fin m, S j ≤ (S i / U i) * U j := by
    intro j
    exact (div_le_iff₀ (hU j)).mp (hmax j (mem_univ _))
  have hbound : (∑ j : Fin m with j.val ≤ i.val + K, S j) ≤ P i * S i := by
    calc
      _ ≤ ∑ j : Fin m with j.val ≤ i.val + K, (S i / U i) * U j :=
        sum_le_sum (fun j _ => hpoint j)
      _ = (S i / U i) * (∑ j : Fin m with j.val ≤ i.val + K, U j) := by rw [mul_sum]
      _ ≤ (S i / U i) * (P i * U i) :=
        mul_le_mul_of_nonneg_left (hmajor i hnonterminal) (div_nonneg hpos.le (hU i).le)
      _ = P i * S i := by field_simp [(hU i).ne']
  exact hfold ⟨i, hpos, hnonterminal, hbound⟩

theorem terminal_layer_mass {m K tail : ℕ} {L T : ℝ} (P : Fin m → ℝ) (hL : 0 ≤ L)
    (S U : Fin m → ℝ) (hU : ∀ i, 0 < U i) (hS : ∀ i, 0 ≤ S i)
    (hboundary : ∀ i : Fin m, m ≤ i.val + K → S i ≤ L * U i)
    (hmajor : ∀ i : Fin m, i.val + K < m →
      (∑ j : Fin m with j.val ≤ i.val + K, U j) ≤ P i * U i)
    (hfold : ¬∃ i : Fin m, 0 < S i ∧ i.val + K < m ∧
      (∑ j : Fin m with j.val ≤ i.val + K, S j) ≤ P i * S i)
    (hmass : (∑ i : Fin m with i.val + tail < m, U i) ≤ T) :
    (∑ i : Fin m with i.val + tail < m, S i) ≤ L * T := by
  have hpoint := (prefix_majorant_dichotomy P hL S U hU hS hboundary hmajor).resolve_left hfold
  calc
    _ ≤ ∑ i : Fin m with i.val + tail < m, L * U i := sum_le_sum (fun i _ => hpoint i)
    _ = L * (∑ i : Fin m with i.val + tail < m, U i) := by rw [mul_sum]
    _ ≤ L * T := mul_le_mul_of_nonneg_left hmass hL


end
end Cycle12
