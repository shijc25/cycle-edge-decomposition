/-
Copyright (c) 2026 Jiacheng Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Cycle12.Foundations.BernoulliContainment
import Cycle12.Independent.DisjointCoordinates

namespace Cycle12.Independent
open Finset Real Cycle13
noncomputable section
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

theorem indicator_nonneg (D S : Finset V) : 0 ≤ containsIndicator D S := by
  classical
  simp only [containsIndicator]
  split_ifs <;> norm_num

theorem indicator_zero_or_one (D S : Finset V) :
    containsIndicator D S = 0 ∨ containsIndicator D S = 1 := by
  classical
  simp only [containsIndicator]
  split_ifs <;> simp

theorem indicator_monotone (D : Finset V) : Monotone (containsIndicator D) := by
  classical
  intro A B hAB
  by_cases hD : D ⊆ A
  · simp [containsIndicator, hD, hD.trans hAB]
  · simpa [containsIndicator, hD] using indicator_nonneg D B

theorem indicator_insert (D S : Finset V) {v : V} (hv : v ∉ D) :
    containsIndicator D (insert v S) = containsIndicator D S := by
  classical
  have hsub : D ⊆ insert v S ↔ D ⊆ S := by
    constructor
    · intro h u hu
      rcases mem_insert.mp (h hu) with heq | hmem
      · exact False.elim (hv (heq ▸ hu))
      · exact hmem
    · exact fun h => h.trans (subset_insert _ _)
  simp [containsIndicator, hsub]

def indicatorCount (B : I → Finset V) (R : Finset I) (S : Finset V) : ℝ :=
  ∑ i ∈ R, containsIndicator (B i) S

theorem indicatorCount_nonneg (B : I → Finset V) (R : Finset I) (S : Finset V) :
    0 ≤ indicatorCount B R S := sum_nonneg (fun i _ => indicator_nonneg (B i) S)

theorem indicatorCount_monotone (B : I → Finset V) (R : Finset I) :
    Monotone (indicatorCount B R) := fun _ _ h =>
  sum_le_sum (fun i _ => indicator_monotone (B i) h)

theorem indicatorCount_insert (B : I → Finset V) (R : Finset I) (S : Finset V)
    {v : V} (hv : ∀ i ∈ R, v ∉ B i) :
    indicatorCount B R (insert v S) = indicatorCount B R S := by
  apply sum_congr rfl
  intro i hi
  exact indicator_insert (B i) S (hv i hi)

theorem indicatorCount_exp_antitone (B : I → Finset V) (R : Finset I) {s : ℝ}
    (hs : 0 ≤ s) : Antitone (fun S => exp (-s*indicatorCount B R S)) := by
  intro A C hAC
  apply exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left (indicatorCount_monotone B R hAC) (neg_nonpos.mpr hs)

theorem indicator_laplace_independent (p : unitInterval) (D : Finset V)
    (B : I → Finset V) (R : Finset I) (s : ℝ)
    (hdis : ∀ i ∈ R, Disjoint D (B i)) :
    (bernoulliSubset p).expect (fun S => containsIndicator D S * exp (-s*indicatorCount B R S)) =
      (p:ℝ)^D.card * (bernoulliSubset p).expect (fun S => exp (-s*indicatorCount B R S)) := by
  classical
  rw [bernoulli_independent, bernoulliSubset_contains_expect]
  intro v
  by_cases hv : v ∈ D
  · right
    intro S
    rw [indicatorCount_insert B R S (fun i hi hvi => disjoint_left.mp (hdis i hi) hv hvi)]
  · exact Or.inl (fun S => indicator_insert D S hv)

theorem indicator_pair_laplace_bound (p : unitInterval) (D E : Finset V)
    (B : I → Finset V) (R : Finset I) {s : ℝ} (hs : 0 ≤ s) :
    (bernoulliSubset p).expect (fun S =>
      containsIndicator D S * containsIndicator E S * exp (-s*indicatorCount B R S)) ≤
      (p:ℝ)^(D∪E).card * (bernoulliSubset p).expect (fun S => exp (-s*indicatorCount B R S)) := by
  simp_rw [containsIndicator_mul]
  have h := bernoulli_opposite_association p (fun S => indicator_nonneg (D∪E) S)
    (fun S => (exp_pos (-s*indicatorCount B R S)).le) (indicator_monotone (D∪E))
    (indicatorCount_exp_antitone B R hs)
  rwa [bernoulliSubset_contains_expect] at h

end
end Cycle12.Independent
