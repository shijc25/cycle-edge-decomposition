/-
Copyright (c) 2026 Jiacheng Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-! Counting all edges removed with a vertex set, including its internal
edges exactly once. This is the counting step in the Woodall argument. -/
namespace Cycle12.Independent
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

def intoCount (G : SimpleGraph V) (A : Finset V) (v : V) : ℕ :=
  (A.filter (G.Adj v)).card

omit [Fintype V] [DecidableEq V] in
theorem intoCount_sum (G : SimpleGraph V) (A : Finset V) (v : V) :
    intoCount G A v = ∑ w ∈ A, if G.Adj v w then 1 else 0 := by
  simp [intoCount]

omit [DecidableEq V] in
theorem intoCount_univ (G : SimpleGraph V) (v : V) : intoCount G univ v = G.degree v := by
  simp [intoCount, SimpleGraph.degree, G.neighborFinset_eq_filter]

theorem degree_split (G : SimpleGraph V) (A : Finset V) (v : V) :
    G.degree v = intoCount G A v + intoCount G (univ \ A) v := by
  have h := sum_sdiff (f := fun w => if G.Adj v w then (1:ℕ) else 0) (subset_univ A)
  simp only [← intoCount_sum, intoCount_univ] at h
  omega

theorem intoCount_swap_sum (G : SimpleGraph V) (A B : Finset V) :
    (∑ v ∈ A, intoCount G B v) = ∑ w ∈ B, intoCount G A w := by
  simp only [intoCount_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro w _
  apply sum_congr rfl
  intro v _
  rw [G.adj_comm]

omit [Fintype V] [DecidableEq V] in
theorem induced_degree_intoCount (G : SimpleGraph V) (A : Finset V) (v : (A:Set V)) :
    (G.induce (A:Set V)).degree v = intoCount G A v.val := by
  rw [← (G.induce (A:Set V)).card_neighborSet_eq_degree]
  unfold intoCount
  rw [← Fintype.card_coe]
  apply Fintype.card_congr
  refine {
    toFun := fun w => ⟨w.val.val,mem_filter.mpr ⟨w.val.property,w.property⟩⟩
    invFun := fun w => ⟨⟨w.val,(mem_filter.mp w.property).1⟩,(mem_filter.mp w.property).2⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro w; rfl
  · intro w; rfl

theorem induced_degree_sum (G : SimpleGraph V) (A : Finset V) :
    (∑ v ∈ A, intoCount G A v) = 2*(G.induce (A:Set V)).edgeFinset.card := by
  rw [← (G.induce (A:Set V)).sum_degrees_eq_twice_card_edges]
  simp only [induced_degree_intoCount]
  exact (Finset.sum_coe_sort A (fun v => intoCount G A v)).symm

theorem degree_partitioned_total (G : SimpleGraph V) (W : Finset V) :
    2*G.edgeFinset.card = (∑ v ∈ W, G.degree v) + (∑ v ∈ W, intoCount G (univ \ W) v) +
      2*(G.induce ((univ \ W:Finset V):Set V)).edgeFinset.card := by
  have hsplit := sum_sdiff (f := fun v => G.degree v) (subset_univ W)
  rw [G.sum_degrees_eq_twice_card_edges] at hsplit
  have hrest : (∑ v ∈ univ \ W, G.degree v) =
      (∑ v ∈ W, intoCount G (univ \ W) v) +
        2*(G.induce ((univ \ W:Finset V):Set V)).edgeFinset.card := by
    conv_lhs => arg 2; ext v; rw [degree_split G W v]
    rw [sum_add_distrib, intoCount_swap_sum G (univ \ W) W, induced_degree_sum]
  omega

theorem vertex_deletion_cost (G : SimpleGraph V) (W X : Finset V) {k : ℕ}
    (hWX : W ⊆ X) (hX : X.card ≤ k)
    (hdeg : ∀ v ∈ W, G.degree v ≤ W.card)
    (hnb : ∀ v ∈ W, ∀ w, G.Adj v w → w ∈ X) :
    2*G.edgeFinset.card ≤ W.card*k +
      2*(G.induce ((univ \ W:Finset V):Set V)).edgeFinset.card := by
  have hdegree : (∑ v ∈ W, G.degree v) ≤ W.card*W.card := by
    calc
      _ ≤ ∑ _v ∈ W, W.card := sum_le_sum hdeg
      _ = _ := by simp
  have hone : ∀ v ∈ W, intoCount G (univ \ W) v ≤ X.card-W.card := by
    intro v hv
    rw [← card_sdiff_of_subset hWX]
    apply card_le_card
    intro w hw
    have h := mem_filter.mp hw
    exact mem_sdiff.mpr ⟨hnb v hv w h.2,(mem_sdiff.mp h.1).2⟩
  have hcross : (∑ v ∈ W, intoCount G (univ \ W) v) ≤ W.card*(X.card-W.card) := by
    calc
      _ ≤ ∑ _v ∈ W, (X.card-W.card) := sum_le_sum hone
      _ = _ := by simp
  have hcard := card_le_card hWX
  have hcancel := Nat.sub_add_cancel hcard
  have hmul := Nat.mul_le_mul_left W.card hX
  rw [degree_partitioned_total G W]
  nlinarith

end
end Cycle12.Independent
