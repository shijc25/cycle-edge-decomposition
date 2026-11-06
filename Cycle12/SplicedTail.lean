import Cycle12.Foundations.TailRecurrence

namespace Cycle12
open Finset
noncomputable section

def splice (r : ℝ) (N : ℕ) (u : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n < N then u n else Cycle122.tailTerm r (u (N-2)) (u (N-1)) (n-(N-2))

theorem splice_finite {r : ℝ} {N n : ℕ} {u : ℕ → ℝ} (hn : n < N) :
    splice r N u n = u n := by simp [splice,hn]

theorem splice_shift (r : ℝ) {N : ℕ} (hN : 2 ≤ N) (u : ℕ → ℝ) (n : ℕ) :
    splice r N u (n+(N-2)) = Cycle122.tailTerm r (u (N-2)) (u (N-1)) n := by
  rcases n with _ | n
  · simp [splice,show N-2 < N by omega,Cycle122.tailTerm_zero]
  rcases n with _ | n
  · have he : 1+(N-2)=N-1 := by omega
    simpa [he,splice,show N-1 < N by omega] using
      (Cycle122.tailTerm_one r (u (N-2)) (u (N-1))).symm
  · have hn : ¬(n+1+1+(N-2) < N) := by omega
    simp [splice,hn]

theorem splice_pos {r : ℝ} {N : ℕ} (hN : 2 ≤ N) {u : ℕ → ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hu : ∀ n, n < N → 0 < u n) (n : ℕ) :
    0 < splice r N u n := by
  by_cases hn : n < N
  · simpa [splice,hn] using hu n hn
  · simpa [splice,hn] using Cycle122.tailTerm_pos hr hr1
      (hu (N-2) (by omega)) (hu (N-1) (by omega)) (n-(N-2))

theorem splice_summable {r : ℝ} {N : ℕ} (hN : 2 ≤ N) {u : ℕ → ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hx : 0 < u (N-2)) (hy : 0 < u (N-1)) :
    Summable (splice r N u) := by
  apply (summable_nat_add_iff (N-2)).mp
  have he : (fun n => splice r N u (n+(N-2))) = Cycle122.tailTerm r (u (N-2)) (u (N-1)) := by
    funext n
    exact splice_shift r hN u n
  rw [he]
  exact Cycle122.tailTerm_summable hr hr1 hx hy

theorem splice_total_mass {r : ℝ} {N : ℕ} (hN : 2 ≤ N) {u : ℕ → ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hx : 0 < u (N-2)) (hy : 0 < u (N-1)) :
    (∑' n : ℕ, splice r N u n) =
      (∑ n ∈ range (N-2), u n)+(r*u (N-2)+u (N-1))/r^2 := by
  have hs := splice_summable hN hr hr1 hx hy
  have hh := hs.sum_add_tsum_nat_add (N-2)
  have hf : (∑ n ∈ range (N-2), splice r N u n) = ∑ n ∈ range (N-2), u n := by
    apply sum_congr rfl
    intro n hn
    exact splice_finite (by have := mem_range.mp hn; omega)
  have ht : (fun n => splice r N u (n+(N-2))) = Cycle122.tailTerm r (u (N-2)) (u (N-1)) := by
    funext n
    exact splice_shift r hN u n
  rw [hf,ht,Cycle122.tail_total_mass hr hr1 hx hy] at hh
  exact hh.symm

theorem splice_tail_majorant {r P : ℝ} {N k : ℕ} (hN : 2 ≤ N) {u : ℕ → ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hx : 0 < u (N-2)) (hy : 0 < u (N-1))
    (hP : 1 ≤ P*Cycle1249.prefixH r) (hk : N-2 ≤ k) :
    (∑' j : ℕ, splice r N u (j+k)) ≤ P*splice r N u (k+2) := by
  have he : ∀ j, j+k = (j+(k-(N-2)))+(N-2) := by intro j; omega
  have hrhs : k+2 = (k-(N-2)+2)+(N-2) := by omega
  simp_rw [he,splice_shift r hN u]
  rw [hrhs,splice_shift r hN u]
  exact Cycle122.tail_majorant hr hr1 hx hy hP (k-(N-2))

end
end Cycle12

namespace Cycle12
open Finset
noncomputable section

theorem splice_finite_tail_sum {r : ℝ} {N k : ℕ} (hN : 2 ≤ N) {u : ℕ → ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hx : 0 < u (N-2)) (hy : 0 < u (N-1))
    (hk : k ≤ N-2) :
    (∑' j : ℕ, splice r N u (j+k)) =
      (∑ j ∈ range (N-2-k), u (j+k))+(r*u (N-2)+u (N-1))/r^2 := by
  have hs := (summable_nat_add_iff k).mpr (splice_summable hN hr hr1 hx hy)
  have hh := hs.sum_add_tsum_nat_add (N-2-k)
  have hf : (∑ j ∈ range (N-2-k), splice r N u (j+k)) =
      ∑ j ∈ range (N-2-k), u (j+k) := by
    apply sum_congr rfl
    intro j hj
    exact splice_finite (by have := mem_range.mp hj; omega)
  have ht : (fun j => splice r N u (j+(N-2-k)+k)) =
      Cycle122.tailTerm r (u (N-2)) (u (N-1)) := by
    funext j
    have he : j+(N-2-k)+k=j+(N-2) := by omega
    rw [he,splice_shift r hN u]
  rw [hf,ht,Cycle122.tail_total_mass hr hr1 hx hy] at hh
  exact hh.symm

theorem splice_infinite_majorant {r : ℝ} {N : ℕ} (hN : 4 ≤ N) (u P : ℕ → ℝ)
    (hr : 0 < r) (hr1 : r < 1) (hx : 0 < u (N-2)) (hy : 0 < u (N-1))
    (hP : 1 ≤ P (N-1)*Cycle1249.prefixH r)
    (hmono : ∀ t, N ≤ t → P (N-1) ≤ P t)
    (hfinite : ∀ t, 2 < t → t < N →
      (∑ j ∈ range (N-t), u (j+(t-2)))+(r*u (N-2)+u (N-1))/r^2 ≤ P t*u t)
    (t : ℕ) (ht : 2 < t) :
    (∑' j : ℕ, splice r N u (j+(t-2))) ≤ P t*splice r N u t := by
  have hN2 : 2 ≤ N := by omega
  by_cases htn : t < N
  · rw [splice_finite_tail_sum hN2 hr hr1 hx hy (by omega),splice_finite htn]
    have he : N-2-(t-2)=N-t := by omega
    rw [he]
    exact hfinite t ht htn
  · have hp : 1 ≤ P t*Cycle1249.prefixH r :=
      hP.trans (mul_le_mul_of_nonneg_right (hmono t (by omega))
        (Cycle1249.prefixH_pos hr hr1).le)
    have h := splice_tail_majorant hN2 hr hr1 hx hy hp (k := t-2) (by omega)
    have he : t-2+2=t := by omega
    simpa only [he] using h

end
end Cycle12
