import Mathlib

namespace Cycle13
open Finset

/-- Group bounded pieces until reaching a target. The upper endpoint is
strict, yielding the DFS core interval k through 2k-1. -/
theorem exists_group_sum_between {I : Type} [DecidableEq I]
    (S : Finset I) (f : I → ℕ) {k : ℕ} (hk : 0 < k)
    (hlarge : k ≤ ∑ i ∈ S, f i) (hsmall : ∀ i ∈ S, f i ≤ k) :
    ∃ U ⊆ S, k ≤ ∑ i ∈ U, f i ∧ ∑ i ∈ U, f i < 2*k := by
  induction S using Finset.induction_on with
  | empty => simp at hlarge; omega
  | @insert a S ha ih =>
    by_cases hS : k ≤ ∑ i ∈ S, f i
    · obtain ⟨U,hU,hlo,hhi⟩ := ih hS (fun i hi => hsmall i (by simp [hi]))
      exact ⟨U,hU.trans (Finset.subset_insert _ _),hlo,hhi⟩
    · refine ⟨insert a S,le_rfl,hlarge,?_⟩
      rw [Finset.sum_insert ha]
      have hh := hsmall a (Finset.mem_insert_self _ _)
      omega

end Cycle13
