/-
Copyright (c) 2026 Jiacheng Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-! The elementary path rotation used in the Woodall proof of the
Erdős--Gallai cycle bound. These constructions use Mathlib walks directly. -/
namespace Cycle12.Independent
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable {a b : V}

def rotatePath (p : G.Walk a b) (i : ℕ) (h : G.Adj a (p.getVert (i+1))) :
    G.Walk (p.getVert i) b :=
  (p.take i).reverse.append ((p.drop (i+1)).cons h)

omit [Fintype V] [DecidableEq V] in
theorem rotatePath_support (p : G.Walk a b) {i : ℕ} (hi : i < p.length)
    (h : G.Adj a (p.getVert (i+1))) :
    (rotatePath p i h).support =
      (p.support.take (i+1)).reverse ++ p.support.drop (i+1) := by
  simp [rotatePath, SimpleGraph.Walk.support_append,
    SimpleGraph.Walk.support_reverse, SimpleGraph.Walk.support_take,
    SimpleGraph.Walk.drop_support_eq_support_drop_min, Nat.min_eq_left (by omega : i+1 ≤ p.length)]

theorem rotatePath_support_perm (p : G.Walk a b) {i : ℕ} (hi : i < p.length)
    (h : G.Adj a (p.getVert (i+1))) :
    (rotatePath p i h).support.Perm p.support := by
  rw [rotatePath_support p hi h]
  have hp := (List.reverse_perm (p.support.take (i+1))).append_right (p.support.drop (i+1))
  simpa using hp

theorem rotatePath_isPath (p : G.Walk a b) (hp : p.IsPath) {i : ℕ}
    (hi : i < p.length) (h : G.Adj a (p.getVert (i+1))) :
    (rotatePath p i h).IsPath :=
  SimpleGraph.Walk.IsPath.mk' ((rotatePath_support_perm p hi h).nodup_iff.mpr hp.support_nodup)

theorem rotatePath_length (p : G.Walk a b) {i : ℕ} (hi : i < p.length)
    (h : G.Adj a (p.getVert (i+1))) : (rotatePath p i h).length = p.length := by
  have hlen := (rotatePath_support_perm p hi h).length_eq
  simp only [SimpleGraph.Walk.length_support] at hlen
  omega

def PathOptimal (p : G.Walk a b) : Prop :=
  p.IsPath ∧
  (∀ (u v : V) (q : G.Walk u v), q.IsPath → q.length ≤ p.length) ∧
  (∀ (u v : V) (q : G.Walk u v), q.IsPath → q.length = p.length → G.degree u ≤ G.degree a)

theorem exists_pathOptimal (G : SimpleGraph V) [Nonempty V] :
    ∃ (a b : V) (p : G.Walk a b), PathOptimal p := by
  classical
  obtain ⟨u,v,p,hp,hmax⟩ := SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length G
  let A := univ.filter (fun x : V => ∃ (y : V) (q : G.Walk x y), q.IsPath ∧ q.length = p.length)
  have hu : u ∈ A := mem_filter.mpr ⟨mem_univ _,v,p,hp,rfl⟩
  obtain ⟨x,hx,hdegree⟩ := exists_max_image A (fun x => G.degree x) ⟨u,hu⟩
  obtain ⟨y,q,hq,hlen⟩ := (mem_filter.mp hx).2
  refine ⟨x,y,q,hq,?_,?_⟩
  · intro u' v' r hr
    rw [hlen]
    exact hmax u' v' r hr
  · intro u' v' r hr heq
    exact hdegree u' (mem_filter.mpr ⟨mem_univ _,v',r,hr,heq.trans hlen⟩)

omit [Fintype V] in
theorem longest_start_neighbor_mem (p : G.Walk a b) (hp : p.IsPath)
    (hmax : ∀ (u v : V) (q : G.Walk u v), q.IsPath → q.length ≤ p.length)
    {v : V} (hv : G.Adj a v) : v ∈ p.support := by
  classical
  by_contra hout
  have hq : (p.cons hv.symm).IsPath := hp.cons hout
  have hlen := hmax v b (p.cons hv.symm) hq
  simp only [SimpleGraph.Walk.length_cons] at hlen
  omega

theorem rotated_degree_le (p : G.Walk a b) (hp : PathOptimal p) {i : ℕ}
    (hi : i < p.length) (h : G.Adj a (p.getVert (i+1))) :
    G.degree (p.getVert i) ≤ G.degree a :=
  hp.2.2 _ _ (rotatePath p i h) (rotatePath_isPath p hp.1 hi h) (rotatePath_length p hi h)

theorem rotated_neighbor_mem (p : G.Walk a b) (hp : PathOptimal p) {i : ℕ}
    (hi : i < p.length) (h : G.Adj a (p.getVert (i+1)))
    {v : V} (hv : G.Adj (p.getVert i) v) : v ∈ p.support := by
  have hlen := rotatePath_length p hi h
  have hmem := longest_start_neighbor_mem (rotatePath p i h) (rotatePath_isPath p hp.1 hi h)
    (fun u w q hq => by rw [hlen]; exact hp.2.1 u w q hq) hv
  exact (rotatePath_support_perm p hi h).mem_iff.mp hmem

end
end Cycle12.Independent
