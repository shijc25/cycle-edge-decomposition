import Cycle12.Foundations.PathClosure
import Cycle12.Foundations.RoutingGraph

/-! Combining source routes and branch connectors into actual cycles.
Branch connectors must still be constructed by a pairing theorem. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] {G : SimpleGraph V}

def EndpointPathPacking.endpoint (P : EndpointPathPacking G) (k : Fin P.count × Bool) : V :=
  if k.2 then (P.paths k.1).start else (P.paths k.1).finish

lemma path_start_not_tail {x y : V} {p : G.Walk x y} (hp : p.IsPath) :
    x ∉ p.support.tail := by
  have h := hp.support_nodup
  rw [← Walk.cons_tail_support] at h
  exact (List.nodup_cons.mp h).1

lemma walk_support_of_tail_inside {x y : V} (p : G.Walk x y) (U : Set V)
    (ht : ∀ v ∈ p.support.tail, v ∈ U) : ∀ v ∈ p.support, v = x ∨ v ∈ U := by
  intro v hv
  rw [← Walk.cons_tail_support, List.mem_cons] at hv
  exact hv.imp id (ht v)

lemma edge_not_both_outside {x y : V} (p : G.Walk x y) (U : Set V)
    (ht : ∀ v ∈ p.support.tail, v ∈ U) {a b : V}
    (ha : a ∉ U) (hb : b ∉ U) (hab : a ≠ b) : s(a,b) ∉ p.edgeSet := by
  intro he
  have ha' := walk_support_of_tail_inside p U ht a (p.fst_mem_support_of_mem_edges he)
  have hb' := walk_support_of_tail_inside p U ht b (p.snd_mem_support_of_mem_edges he)
  exact hab ((ha'.resolve_right ha).trans (hb'.resolve_right hb).symm)

/-- Given actual branch connectors in the reserved edges, all external
paths close to simple, edge-disjoint cycles. Shared routing vertices are
allowed; simplicity is obtained by erasing loops only in the return walk. -/
theorem close_paths_via_reservoir (P : EndpointPathPacking G) (U : Set V)
    (hPU : ∀ i, ∀ v ∈ (P.paths i).walk.support, v ∉ U)
    (branch : Fin P.count × Bool → V)
    (F : ∀ k, G.Walk (P.endpoint k) (branch k))
    (hFU : ∀ k, ∀ v ∈ (F k).support.tail, v ∈ U)
    (hFF : Pairwise (fun k l => Disjoint (F k).edgeSet (F l).edgeSet))
    (Q : ∀ i, G.Walk (branch (i,false)) (branch (i,true)))
    (hQU : ∀ i, ∀ v ∈ (Q i).support, v ∈ U)
    (hQQ : Pairwise (fun i j => Disjoint (Q i).edgeSet (Q j).edgeSet))
    (hFQ : ∀ k i, Disjoint (F k).edgeSet (Q i).edgeSet) :
    ∃ C : CyclePacking G, C.count = P.count ∧ P.used ⊆ C.used ∧
      C.singles ≤ P.singles ∧ C.cost ≤ 42 * P.count + 23 * P.singles := by
  let W := fun i => (F (i,false)).append ((Q i).append (F (i,true)).reverse)
  have hWe : ∀ i, (W i).edgeSet =
      (F (i,false)).edgeSet ∪ (Q i).edgeSet ∪ (F (i,true)).edgeSet := by
    intro i
    simp only [W, Walk.edgeSet_append, Walk.edgeSet_reverse, Set.union_assoc]
  have hWW : Pairwise (fun i j => Disjoint (W i).edgeSet (W j).edgeSet) := by
    intro i j hij
    rw [hWe i, hWe j]
    apply Set.disjoint_left.mpr
    rintro e ((hi | hi) | hi) ((hj | hj) | hj)
    · exact Set.disjoint_left.mp (hFF (by exact fun h => hij (congrArg Prod.fst h))) hi hj
    · exact Set.disjoint_left.mp (hFQ (i,false) j) hi hj
    · exact Set.disjoint_left.mp (hFF (by exact fun h => hij (congrArg Prod.fst h))) hi hj
    · exact Set.disjoint_left.mp (hFQ (j,false) i) hj hi
    · exact Set.disjoint_left.mp (hQQ hij) hi hj
    · exact Set.disjoint_left.mp (hFQ (j,true) i) hj hi
    · exact Set.disjoint_left.mp (hFF (by exact fun h => hij (congrArg Prod.fst h))) hi hj
    · exact Set.disjoint_left.mp (hFQ (i,true) j) hi hj
    · exact Set.disjoint_left.mp (hFF (by exact fun h => hij (congrArg Prod.fst h))) hi hj
  have hno : ∀ i, ∀ x y : V, x ∉ U → y ∉ U → x ≠ y → s(x,y) ∉ (W i).edgeSet := by
    intro i x y hx hy hxy he
    rw [hWe i] at he
    rcases he with (he | he) | he
    · exact edge_not_both_outside (F (i,false)) U (hFU _) hx hy hxy he
    · exact hx (hQU i x ((Q i).fst_mem_support_of_mem_edges he))
    · exact edge_not_both_outside (F (i,true)) U (hFU _) hx hy hxy he
  have hPW : ∀ i j, Disjoint (P.paths i).walk.edgeSet (W j).edgeSet := by
    intro i j
    apply Set.disjoint_left.mpr
    intro e hep hew
    induction e using Sym2.inductionOn with
    | _ x y =>
      exact hno j x y
        (hPU i x ((P.paths i).walk.fst_mem_support_of_mem_edges hep))
        (hPU i y ((P.paths i).walk.snd_mem_support_of_mem_edges hep))
        ((P.paths i).walk.edges_subset_edgeSet hep).ne hew
  have hWs : ∀ i, ∀ v ∈ (W i).support,
      v = (P.paths i).finish ∨ v = (P.paths i).start ∨ v ∈ U := by
    intro i v hv
    simp only [W, Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse] at hv
    rcases hv with hv | hv | hv
    · rcases walk_support_of_tail_inside (F (i,false)) U (hFU _) v hv with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inr (hQU i v hv))
    · rcases walk_support_of_tail_inside (F (i,true)) U (hFU _) v hv with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  let R := fun i => (W i).bypass
  have hR : ∀ i, (R i).IsPath := fun i => Walk.bypass_isPath _
  have hRsub : ∀ i, (R i).edgeSet ⊆ (W i).edgeSet := fun i => Walk.edges_bypass_subset_edges _
  have hlen : ∀ i, 2 ≤ (R i).length := by
    intro i
    have hne : (P.paths i).finish ≠ (P.paths i).start := by
      intro h
      have he := @P.endpoint_injective (i,false) (i,true) (by simpa using h)
      have hb := congrArg Prod.snd he
      cases hb
    have hpos : 0 < (R i).length := by
      exact Nat.pos_of_ne_zero (fun h => hne (Walk.length_eq_zero_iff.mp h).eq)
    by_contra hn
    have h1 : (R i).length = 1 := by omega
    have ha := Walk.adj_of_length_eq_one h1
    have heq : R i = ha.toWalk := Walk.eq_of_length_le_one h1.le (by simp)
    have he : s((P.paths i).finish,(P.paths i).start) ∈ (R i).edgeSet := by
      rw [heq]
      exact List.mem_cons_self
    exact hno i _ _ (hPU i _ (P.paths i).walk.end_mem_support)
      (hPU i _ (P.paths i).walk.start_mem_support) hne (hRsub i he)
  have hsep : ∀ i, (P.paths i).walk.support.tail.Disjoint (R i).support.tail := by
    intro i v hvp hvr
    have hs := hWs i v (Walk.support_bypass_subset_support _ (List.mem_of_mem_tail hvr))
    rcases hs with hs | hs | hs
    · apply path_start_not_tail (hR i)
      change (P.paths i).finish ∈ (R i).support.tail
      exact hs ▸ hvr
    · exact path_start_not_tail (P.paths i).isPath (hs ▸ hvp)
    · exact hPU i v (List.mem_of_mem_tail hvp) hs
  obtain ⟨C, hc, hu, hs, hcost⟩ := cycle_packing_of_disjoint_returns P R hR hlen hsep
    (fun i j hij => (hWW hij).mono (hRsub i) (hRsub j))
    (fun i j => (hPW i j).mono_right (hRsub j))
  refine ⟨C, hc, ?_, hs, hcost⟩
  rw [hu]
  exact Set.subset_union_left

end
end Cycle13
