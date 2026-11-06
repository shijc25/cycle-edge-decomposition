/-
Copyright (c) 2026 Jiacheng Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Cycle12.Foundations.SubsetBernoulliRecursion

/-! Independence for observables that use disjoint coordinates, proved by
induction on the finite ground set and the two possible outcomes of its last
coordinate. The hypothesis permits arbitrary real-valued observables. -/

namespace Cycle12.Independent
open Finset
open Cycle13
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem subsetBernoulli_independent (p : unitInterval) (W : Finset V)
    (f g : Finset V → ℝ)
    (hfg : ∀ v ∈ W, (∀ S, f (insert v S) = f S) ∨
      (∀ S, g (insert v S) = g S)) :
    (subsetBernoulli W p).expect (fun S => f S * g S) =
      (subsetBernoulli W p).expect f * (subsetBernoulli W p).expect g := by
  classical
  induction W using Finset.induction_on generalizing f g with
  | empty => simp only [subsetBernoulli_expect_empty]
  | @insert v W hv ih =>
    have hW : ∀ u ∈ W, (∀ S, f (insert u S) = f S) ∨
        (∀ S, g (insert u S) = g S) :=
      fun u hu => hfg u (mem_insert_of_mem hu)
    have hI : ∀ u ∈ W,
        (∀ S, f (insert v (insert u S)) = f (insert v S)) ∨
        (∀ S, g (insert v (insert u S)) = g (insert v S)) := by
      intro u hu
      rcases hW u hu with hf | hg
      · exact Or.inl (fun S => by rw [insert_comm, hf])
      · exact Or.inr (fun S => by rw [insert_comm, hg])
    rw [subsetBernoulli_expect_insert W v hv p,
      subsetBernoulli_expect_insert W v hv p f,
      subsetBernoulli_expect_insert W v hv p g,
      ih f g hW, ih (fun S => f (insert v S)) (fun S => g (insert v S)) hI]
    rcases hfg v (mem_insert_self v W) with hf | hg
    · simp_rw [hf]
      ring
    · simp_rw [hg]
      ring

theorem bernoulli_independent (p : unitInterval) (f g : Finset V → ℝ)
    (hfg : ∀ v, (∀ S, f (insert v S) = f S) ∨
      (∀ S, g (insert v S) = g S)) :
    (bernoulliSubset p).expect (fun S => f S * g S) =
      (bernoulliSubset p).expect f * (bernoulliSubset p).expect g := by
  have h := subsetBernoulli_independent p univ f g (fun v _ => hfg v)
  have hlaw : subsetBernoulli (univ : Finset V) p = bernoulliSubset p := by
    simp [subsetBernoulli, bernoulliSubset]
  rwa [hlaw] at h

end
end Cycle12.Independent
