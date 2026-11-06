import Cycle12.WalkSegmentChain12

namespace Cycle12
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem snoc_succ_rotate {n : ℕ} (x : Fin (n+1) → V) (i : Fin (n+1)) :
    Fin.snoc (α:=fun _ => V) x (x 0) i.succ=x (finRotate (n+1) i) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.succ_last,Fin.snoc_last,finRotate_last]
  · rw [←Fin.castSucc_succ,Fin.snoc_castSucc]
    exact congrArg x (finRotate_of_lt j.isLt).symm

def cyclicSegmentWalk {n : ℕ} (x : Fin (n+1) → V)
    (p : ∀ i,G.Walk (x i) (x (finRotate (n+1) i))) : G.Walk (x 0) (x 0) :=
  (segmentChain (Fin.snoc (α:=fun _ => V) x (x 0)) (fun i =>
    (p i).copy (by simp only [Fin.snoc_castSucc]) (snoc_succ_rotate x i).symm)).copy
    (by simp only [Fin.snoc_apply_zero]) (by simp only [Fin.snoc_last])

theorem cyclicSegmentWalk_length {n : ℕ} (x : Fin (n+1) → V)
    (p : ∀ i,G.Walk (x i) (x (finRotate (n+1) i))) :
    (cyclicSegmentWalk x p).length=∑ i,(p i).length := by
  simp only [cyclicSegmentWalk,Walk.length_copy,segmentChain_length]

theorem cyclicSegmentWalk_edges {n : ℕ} (x : Fin (n+1) → V)
    (p : ∀ i,G.Walk (x i) (x (finRotate (n+1) i))) :
    (cyclicSegmentWalk x p).edgeSet=⋃ i,(p i).edgeSet := by
  simp only [cyclicSegmentWalk,Walk.edgeSet_copy,segmentChain_edges]

theorem cyclicSegmentWalk_support {n : ℕ} (x : Fin (n+1) → V)
    (p : ∀ i,G.Walk (x i) (x (finRotate (n+1) i))) (v : V) :
    v∈(cyclicSegmentWalk x p).support ↔ ∃ i,v∈(p i).support := by
  simp only [cyclicSegmentWalk,Walk.support_copy,segmentChain_support,Fin.snoc_apply_zero]
  constructor
  · rintro (rfl | h)
    · exact ⟨0,(p 0).start_mem_support⟩
    · exact h
  · exact Or.inr

theorem cyclicSegmentWalk_isTrail {n : ℕ} (x : Fin (n+1) → V)
    (p : ∀ i,G.Walk (x i) (x (finRotate (n+1) i)))
    (hp : ∀ i,(p i).IsTrail)
    (hd : Pairwise (fun i j => Disjoint (p i).edgeSet (p j).edgeSet)) :
    (cyclicSegmentWalk x p).IsTrail := by
  apply trail_of_edgeSet_card
  rw [cyclicSegmentWalk_edges,disjoint_route_union_card p hp hd,cyclicSegmentWalk_length]

end
end Cycle12
