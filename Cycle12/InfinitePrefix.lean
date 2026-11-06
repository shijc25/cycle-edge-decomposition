import Cycle12.BoundaryPrefix
import Cycle12.SplicedTail

namespace Cycle12
open Finset
noncomputable section

def sequenceTail (u : ℕ → ℝ) (a : ℕ) : ℝ := ∑' j : ℕ, u (j+a)

theorem reverse_prefix_interval {m : ℕ} (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) :
    (∑ i : Fin m with i.val+2 < m, u (m-i.val)) ≤
      ∑ k ∈ range (m-2), u (k+3) := by
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
  have hsum : (∑ i ∈ A, u (m-i.val)) = ∑ k ∈ A.image f, u (k+3) := by
    rw [sum_image hinj]
    apply sum_congr rfl
    intro i hi
    have hi' := (mem_filter.mp hi).2
    have he : m-i.val=f i+3 := by dsimp only [f]; omega
    rw [he]
  have hsub : A.image f ⊆ range (m-2) := by
    intro k hk
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hk
    have hi' := (mem_filter.mp hi).2
    rw [mem_range]
    dsimp only [f]
    omega
  change (∑ i ∈ A, u (m-i.val)) ≤ _
  rw [hsum]
  exact sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => hu _)

theorem sequence_prefix_tail_identity {m : ℕ} (hm : 2 ≤ m) (u : ℕ → ℝ)
    (hs : Summable u) :
    (∑ k ∈ range (m-2), u (k+3))+sequenceTail u (m+1)=sequenceTail u 3 := by
  have hh := ((summable_nat_add_iff 3).mpr hs).sum_add_tsum_nat_add (m-2)
  have he : (fun j : ℕ => u (j+(m-2)+3)) = (fun j : ℕ => u (j+(m+1))) := by
    funext j
    congr 1
    omega
  rw [he] at hh
  exact hh

/-- Variable folding thresholds and unequal final-layer bounds imply the exact
truncated mass, including the unused infinite tail. -/
theorem terminal_mass_with_infinite_tail {m : ℕ} (hm : 2 ≤ m) {L : ℝ} (hL : 0 ≤ L)
    (S : Fin m → ℝ) (hS : ∀ i, 0 ≤ S i) (u P : ℕ → ℝ)
    (hu : ∀ n, 0 ≤ u n) (hup : ∀ n, 1 ≤ n → 0 < u n) (hs : Summable u)
    (hboundary : ∀ i : Fin m, m ≤ i.val+2 → S i ≤ L*u (m-i.val))
    (hss : ∀ t, 2 < t → (∑' j : ℕ, u (j+(t-2))) ≤ P t*u t)
    (hfold : ¬∃ i : Fin m, 0 < S i ∧ i.val+2 < m ∧
      (∑ j : Fin m with j.val ≤ i.val+2, S j) ≤ P (m-i.val)*S i) :
    (∑ i : Fin m with i.val+2 < m, S i) ≤
      L*(sequenceTail u 3-sequenceTail u (m+1)) := by
  let U : Fin m → ℝ := fun i => u (m-i.val)
  have hU : ∀ i, 0 < U i := by
    intro i
    exact hup _ (by have hi := i.isLt; omega)
  have hmajor : ∀ i : Fin m, i.val+2 < m →
      (∑ j : Fin m with j.val ≤ i.val+2, U j) ≤ P (m-i.val)*U i := by
    intro i hi
    apply (Cycle13.reverse_indexed_sum_le_tail u hu hs
      (univ.filter (fun j : Fin m => j.val ≤ i.val+2)) (a := m-i.val-2) ?_).trans
      (hss _ (by omega))
    intro j hj
    have hh := (mem_filter.mp hj).2
    omega
  have hpoint := (prefix_majorant_dichotomy (fun i => P (m-i.val)) hL S U hU hS
    hboundary hmajor).resolve_left hfold
  have hmass := reverse_prefix_interval u hu (m := m)
  have hid := sequence_prefix_tail_identity hm u hs
  calc
    _ ≤ ∑ i : Fin m with i.val+2 < m, L*U i := sum_le_sum (fun i _ => hpoint i)
    _ = L*(∑ i : Fin m with i.val+2 < m, U i) := by rw [mul_sum]
    _ ≤ L*(∑ k ∈ range (m-2), u (k+3)) := mul_le_mul_of_nonneg_left hmass hL
    _ = L*(sequenceTail u 3-sequenceTail u (m+1)) := by congr 1; linarith

end
end Cycle12
