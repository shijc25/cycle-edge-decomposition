/-
Copyright (c) 2026 Jiacheng Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Cycle12.Foundations.FiniteBernoulli
import Mathlib.Combinatorics.SetFamily.FourFunctions

/-!
Finite product weights and their association inequalities.

The containment identity is obtained directly from Mathlib's product measure.
The association inequalities instantiate Mathlib's licensed FKG theorem with
the explicit Bernoulli weights. No external correlation library is imported.
-/

namespace Cycle12.Independent
open Finset MeasureTheory ProbabilityTheory
open Cycle13
open scoped ENNReal
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem setBernoulli_contains (p : unitInterval) (D : Finset V) :
    setBernoulli (Set.univ : Set V) p {R : Set V | (D : Set V) ⊆ R} =
      (unitInterval.toNNReal p : ℝ≥0∞) ^ D.card := by
  classical
  rw [setBernoulli_apply']
  have event : (fun f : V → Prop => {i | f i}) ⁻¹'
      {R : Set V | (D : Set V) ⊆ R} =
      Set.pi (D : Set V) (fun _ => {True}) := by
    ext f
    simp [Set.subset_def, Set.mem_pi]
  rw [event]
  simp only [Set.mem_univ]
  rw [Measure.infinitePi_pi (fun _ : V => bernoulliMeasure True False p)
    (s := D) (t := fun _ => ({True} : Set Prop))
    (fun _ _ => MeasurableSet.singleton True)]
  simp

theorem bernoulli_mass_lattice (p : unitInterval) (A B : Finset V) :
    (bernoulliSubset p).mass A * (bernoulliSubset p).mass B =
      (bernoulliSubset p).mass (A ⊓ B) * (bernoulliSubset p).mass (A ⊔ B) := by
  have hc : A.card + B.card = (A ∩ B).card + (A ∪ B).card := by
    have h := card_union_add_card_inter A B
    omega
  have hn : (Fintype.card V - A.card) + (Fintype.card V - B.card) =
      (Fintype.card V - (A ∩ B).card) + (Fintype.card V - (A ∪ B).card) := by
    have ha := card_le_univ A
    have hb := card_le_univ B
    have hi := card_le_univ (A ∩ B)
    have hu := card_le_univ (A ∪ B)
    omega
  change ((p : ℝ)^A.card * (1-(p:ℝ))^(Fintype.card V-A.card)) *
      ((p : ℝ)^B.card * (1-(p:ℝ))^(Fintype.card V-B.card)) =
    ((p : ℝ)^(A∩B).card * (1-(p:ℝ))^(Fintype.card V-(A∩B).card)) *
      ((p : ℝ)^(A∪B).card * (1-(p:ℝ))^(Fintype.card V-(A∪B).card))
  calc
    _ = (p:ℝ)^(A.card+B.card) *
        (1-(p:ℝ))^((Fintype.card V-A.card)+(Fintype.card V-B.card)) := by
      rw [pow_add, pow_add]
      ring
    _ = (p:ℝ)^((A∩B).card+(A∪B).card) *
        (1-(p:ℝ))^((Fintype.card V-(A∩B).card)+(Fintype.card V-(A∪B).card)) := by
      rw [hc, hn]
    _ = _ := by rw [pow_add, pow_add]; ring

theorem bernoulli_association (p : unitInterval) {f g : Finset V → ℝ}
    (hf0 : ∀ S, 0 ≤ f S) (hg0 : ∀ S, 0 ≤ g S)
    (hf : Monotone f) (hg : Monotone g) :
    (bernoulliSubset p).expect f * (bernoulliSubset p).expect g ≤
      (bernoulliSubset p).expect (fun S => f S * g S) := by
  have h := fkg (μ := (bernoulliSubset (V := V) p).mass)
    (f := f) (g := g) (bernoulliSubset p).nonneg hf0 hg0 hf hg
    (fun A B => (bernoulli_mass_lattice p A B).le)
  simpa only [FiniteLaw.expect, (bernoulliSubset (V := V) p).total, one_mul] using h

theorem bernoulli_opposite_association (p : unitInterval) {f g : Finset V → ℝ}
    (hf0 : ∀ S, 0 ≤ f S) (hg0 : ∀ S, 0 ≤ g S)
    (hf : Monotone f) (hg : Antitone g) :
    (bernoulliSubset p).expect (fun S => f S * g S) ≤
      (bernoulliSubset p).expect f * (bernoulliSubset p).expect g := by
  classical
  let M : ℝ := ∑ S : Finset V, g S
  have hgM : ∀ S, g S ≤ M := fun S =>
    single_le_sum (fun T _ => hg0 T) (mem_univ S)
  have h := bernoulli_association p hf0 (fun S => sub_nonneg.mpr (hgM S)) hf
    (show Monotone (fun S => M - g S) from fun A B hAB => sub_le_sub_left (hg hAB) M)
  have hsub : (bernoulliSubset p).expect (fun S => M - g S) =
      M - (bernoulliSubset p).expect g := by
    simp only [FiniteLaw.expect, mul_sub, sum_sub_distrib, ← sum_mul,
      (bernoulliSubset (V := V) p).total, one_mul]
  have hprod : (bernoulliSubset p).expect (fun S => f S * (M - g S)) =
      M * (bernoulliSubset p).expect f -
        (bernoulliSubset p).expect (fun S => f S * g S) := by
    simp only [FiniteLaw.expect, mul_sub, sum_sub_distrib, ← mul_assoc, ← sum_mul]
    ring
  rw [hsub, hprod] at h
  nlinarith

theorem bernoulli_association_real (p : unitInterval) {f g : Finset V → ℝ}
    (hf : Monotone f) (hg : Monotone g) :
    (bernoulliSubset p).expect f * (bernoulliSubset p).expect g ≤
      (bernoulliSubset p).expect (fun S => f S * g S) := by
  have h := bernoulli_association p
    (fun S => sub_nonneg.mpr (hf (empty_subset S)))
    (fun S => sub_nonneg.mpr (hg (empty_subset S)))
    (show Monotone (fun S => f S-f ∅) from fun A B hAB => sub_le_sub_right (hf hAB) _)
    (show Monotone (fun S => g S-g ∅) from fun A B hAB => sub_le_sub_right (hg hAB) _)
  have hsub (F H : Finset V → ℝ) :
      (bernoulliSubset p).expect (fun S => F S-H S) =
        (bernoulliSubset p).expect F - (bernoulliSubset p).expect H := by
    simp only [FiniteLaw.expect, mul_sub, sum_sub_distrib]
  have hprod : (fun S => (f S-f ∅)*(g S-g ∅)) =
      (fun S => (f S*g S - f ∅*g S) - g ∅*f S + f ∅*g ∅) := by
    funext S
    ring
  simp only [hprod, FiniteLaw.expect_add, hsub,
    FiniteLaw.expect_const_mul, FiniteLaw.expect_const] at h
  nlinarith

end
end Cycle12.Independent
