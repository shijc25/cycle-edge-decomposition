import Cycle12.RoutedOutlineTrail12

namespace Cycle12
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency.types false
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Concatenate an arbitrary finite sequence of actual walks. -/
def segmentChain : {n : ℕ} → (v : Fin (n+1) → V) →
    (∀ i : Fin n,G.Walk (v i.castSucc) (v i.succ)) →
    G.Walk (v 0) (v (Fin.last n))
  | 0,_,_ => Walk.nil
  | n+1,v,p => ((p 0).append (segmentChain (fun i => v i.succ)
      (fun i => (p i.succ).copy (congrArg v (Fin.castSucc_succ i)) rfl))).copy
      (congrArg v Fin.castSucc_zero) (congrArg v (Fin.succ_last n))

theorem segmentChain_length {n : ℕ} (v : Fin (n+1) → V)
    (p : ∀ i : Fin n,G.Walk (v i.castSucc) (v i.succ)) :
    (segmentChain v p).length=∑ i,(p i).length := by
  induction n with
  | zero => simp [segmentChain]
  | succ n ih =>
    simp only [segmentChain,Walk.length_copy,Walk.length_append,ih,Fin.sum_univ_succ]

theorem segmentChain_edges {n : ℕ} (v : Fin (n+1) → V)
    (p : ∀ i : Fin n,G.Walk (v i.castSucc) (v i.succ)) :
    (segmentChain v p).edgeSet=⋃ i,(p i).edgeSet := by
  induction n with
  | zero => simp [segmentChain]
  | succ n ih =>
    simp only [segmentChain,Walk.edgeSet_copy,Walk.edgeSet_append,ih]
    ext e
    simp only [Set.mem_union,Set.mem_iUnion,Fin.exists_fin_succ]

theorem segmentChain_support {n : ℕ} (v : Fin (n+1) → V)
    (p : ∀ i : Fin n,G.Walk (v i.castSucc) (v i.succ)) (x : V) :
    x∈(segmentChain v p).support ↔ x=v 0 ∨ ∃ i,x∈(p i).support := by
  induction n with
  | zero => simp [segmentChain]
  | succ n ih =>
    simp only [segmentChain,Walk.support_copy,Walk.mem_support_append_iff,ih,Fin.exists_fin_succ]
    constructor
    · rintro (h | h | h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inl (h.symm ▸ (p 0).end_mem_support))
      · exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exact Or.inl (h.symm ▸ (p 0).start_mem_support)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)

theorem segmentChain_isTrail {n : ℕ} (v : Fin (n+1) → V)
    (p : ∀ i : Fin n,G.Walk (v i.castSucc) (v i.succ))
    (hp : ∀ i,(p i).IsTrail)
    (hd : Pairwise (fun i j => Disjoint (p i).edgeSet (p j).edgeSet)) :
    (segmentChain v p).IsTrail := by
  apply trail_of_edgeSet_card
  rw [segmentChain_edges,disjoint_route_union_card p hp hd,segmentChain_length]

end
end Cycle12
