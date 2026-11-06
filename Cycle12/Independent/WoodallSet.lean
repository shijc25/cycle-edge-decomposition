/-
Copyright (c) 2026 Jiacheng Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Cycle12.Independent.PathRotation

/-! A nonempty proper set with a small neighborhood obtained by rotating
an optimal longest path, under a bound on all cycle lengths. -/
namespace Cycle12.Independent
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable {a b : V} {k : ℕ}

theorem prefix_chord_index_bound (p : G.Walk a b) (hp : p.IsPath) (hk : 2 ≤ k)
    (hc : ∀ (v : V) (c : G.Walk v v), c.IsCycle → c.length ≤ k)
    {j : ℕ} (hj : j ≤ p.length) (ha : G.Adj a (p.getVert j)) : j < k := by
  by_cases hsmall : j < 2
  · omega
  let c := (p.take j).reverse.cons ha
  have hcycle : c.IsCycle := by
    apply SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    constructor
    · simpa [c] using (hp.take j).reverse
    · simp [c, Nat.min_eq_left hj]
      omega
  have hlen := hc a c hcycle
  simp only [c, SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_reverse,
    SimpleGraph.Walk.take_length, Nat.min_eq_left hj] at hlen
  omega

theorem rotated_neighbor_index_bound (p : G.Walk a b) (hp : p.IsPath) (hk : 2 ≤ k)
    (hc : ∀ (v : V) (c : G.Walk v v), c.IsCycle → c.length ≤ k)
    {i j : ℕ} (hi : i < p.length) (hj : j ≤ p.length)
    (ha : G.Adj a (p.getVert (i+1))) (hij : G.Adj (p.getVert i) (p.getVert j)) : j < k := by
  have hik := prefix_chord_index_bound p hp hk hc (by omega : i+1 ≤ p.length) ha
  by_contra hnot
  have hki : k ≤ j := by omega
  have hij' : i < j := by omega
  have htake : (p.take j).length = j := by simp [Nat.min_eq_left hj]
  have ha' : G.Adj a ((p.take j).getVert (i+1)) := by
    simpa only [SimpleGraph.Walk.take_getVert, Nat.min_eq_right (by omega : i+1 ≤ j)] using ha
  have hj' : G.Adj (p.getVert j) ((p.take j).getVert i) := by
    simpa only [SimpleGraph.Walk.take_getVert, Nat.min_eq_right hij'.le] using hij.symm
  let q := rotatePath (p.take j) i ha'
  have hq : q.IsPath := rotatePath_isPath (p.take j) (hp.take j) (by omega) ha'
  have hqlen : q.length = j := (rotatePath_length (p.take j) (by omega) ha').trans htake
  let c := q.cons hj'
  have hcycle : c.IsCycle := by
    apply SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    constructor
    · simpa [c] using hq
    · simp only [c, SimpleGraph.Walk.length_cons, hqlen]
      omega
  have hlen := hc (p.getVert j) c hcycle
  simp only [c, SimpleGraph.Walk.length_cons, hqlen] at hlen
  omega

def predecessorIndices (p : G.Walk a b) : Finset ℕ :=
  (range p.length).filter (fun i => G.Adj a (p.getVert (i+1)))

def woodallSet (p : G.Walk a b) : Finset V := (predecessorIndices p).image p.getVert

def pathPrefixSet (p : G.Walk a b) (k : ℕ) : Finset V :=
  (range (min k (p.length+1))).image p.getVert

theorem predecessorIndices_card (p : G.Walk a b) (hp : PathOptimal p) :
    (predecessorIndices p).card = G.degree a := by
  rw [← G.card_neighborFinset_eq_degree]
  apply card_bij (fun i _ => p.getVert (i+1))
  · intro i hi
    exact (G.mem_neighborFinset a _).mpr (mem_filter.mp hi).2
  · intro i hi j hj heq
    have hi' := mem_range.mp (mem_filter.mp hi).1
    have hj' := mem_range.mp (mem_filter.mp hj).1
    have he := hp.1.getVert_injOn (by simp only [Set.mem_setOf_eq]; omega)
      (by simp only [Set.mem_setOf_eq]; omega) heq
    omega
  · intro v hv
    have hva := (G.mem_neighborFinset a v).mp hv
    have hmem := longest_start_neighbor_mem p hp.1 hp.2.1 hva
    obtain ⟨j,hjv,hj⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hmem
    have hj0 : j ≠ 0 := by
      intro hzero
      have hav : a = v := by simpa [hzero] using hjv
      exact hva.ne hav
    refine ⟨j-1,?_,?_⟩
    · apply mem_filter.mpr
      constructor
      · apply mem_range.mpr; omega
      · simpa [show j-1+1 = j by omega,hjv] using hva
    · simpa [show j-1+1 = j by omega] using hjv

theorem woodallSet_card (p : G.Walk a b) (hp : PathOptimal p) :
    (woodallSet p).card = G.degree a := by
  rw [woodallSet, card_image_of_injOn, predecessorIndices_card p hp]
  intro i hi j hj heq
  exact hp.1.getVert_injOn (by have := mem_range.mp (mem_filter.mp hi).1; simp; omega)
    (by have := mem_range.mp (mem_filter.mp hj).1; simp; omega) heq

theorem end_not_mem_woodallSet (p : G.Walk a b) (hp : p.IsPath) : b ∉ woodallSet p := by
  intro hb
  obtain ⟨i,hi,hib⟩ := mem_image.mp hb
  have hi' := mem_range.mp (mem_filter.mp hi).1
  have heq := (hp.getVert_eq_end_iff hi'.le).mp hib
  omega

theorem woodallSet_degree (p : G.Walk a b) (hp : PathOptimal p) {v : V}
    (hv : v ∈ woodallSet p) : G.degree v ≤ (woodallSet p).card := by
  obtain ⟨i,hi,rfl⟩ := mem_image.mp hv
  rw [woodallSet_card p hp]
  exact rotated_degree_le p hp (mem_range.mp (mem_filter.mp hi).1) (mem_filter.mp hi).2

theorem woodallSet_subset_prefix (p : G.Walk a b) (hp : PathOptimal p) (hk : 2 ≤ k)
    (hc : ∀ (v : V) (c : G.Walk v v), c.IsCycle → c.length ≤ k) :
    woodallSet p ⊆ pathPrefixSet p k := by
  intro v hv
  obtain ⟨i,hi,rfl⟩ := mem_image.mp hv
  have hi' := mem_range.mp (mem_filter.mp hi).1
  have hik := prefix_chord_index_bound p hp.1 hk hc (by omega : i+1 ≤ p.length)
    (mem_filter.mp hi).2
  apply mem_image.mpr
  exact ⟨i,mem_range.mpr (by omega),rfl⟩

theorem woodallSet_neighbors_subset_prefix (p : G.Walk a b) (hp : PathOptimal p) (hk : 2 ≤ k)
    (hc : ∀ (v : V) (c : G.Walk v v), c.IsCycle → c.length ≤ k)
    {v w : V} (hv : v ∈ woodallSet p) (hvw : G.Adj v w) : w ∈ pathPrefixSet p k := by
  obtain ⟨i,hi,rfl⟩ := mem_image.mp hv
  have hi' := mem_range.mp (mem_filter.mp hi).1
  have ha := (mem_filter.mp hi).2
  have hmem := rotated_neighbor_mem p hp hi' ha hvw
  obtain ⟨j,hjw,hj⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hmem
  have hjk := rotated_neighbor_index_bound p hp.1 hk hc hi' hj ha (by rwa [hjw])
  exact mem_image.mpr ⟨j,mem_range.mpr (by omega),hjw⟩

theorem pathPrefixSet_card (p : G.Walk a b) (k : ℕ) : (pathPrefixSet p k).card ≤ k := by
  exact (card_image_le.trans_eq (card_range _)).trans (Nat.min_le_left _ _)

end
end Cycle12.Independent
