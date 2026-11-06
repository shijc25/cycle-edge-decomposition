/-
Copyright (c) 2026 Jiacheng Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Cycle12.Independent.WoodallSet
import Cycle12.Independent.VertexDeletionCount

/-!
The precise Erdős--Gallai cycle bound via the classical Woodall rotation
and deletion argument. No Dirac circumference theorem is used. The graph
may be disconnected and may have isolated vertices.
-/
namespace Cycle12.Independent
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

private theorem erdosGallai_aux (k : ℕ) (hk : 2 ≤ k) :
    ∀ (n : ℕ) {U : Type u} [Fintype U] [DecidableEq U], Fintype.card U = n →
      ∀ (G : SimpleGraph U),
      (∀ (v : U) (c : G.Walk v v), c.IsCycle → c.length ≤ k) →
      2*G.edgeFinset.card ≤ k*(Fintype.card U-1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro U _ _ hn G hc
      classical
      by_cases hG : G = ⊥
      · have hempty : G.edgeFinset = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro e he
          have he' := SimpleGraph.mem_edgeFinset.mp he
          simpa only [hG, SimpleGraph.edgeSet_bot, Set.mem_empty_iff_false] using he'
        rw [hempty]
        simp
      obtain ⟨x,y,hxy⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hG
      let : Nonempty U := ⟨x⟩
      obtain ⟨a,b,p,hp⟩ := exists_pathOptimal G
      have hpos : 0 < p.length := by
        have hlen := hp.2.1 x y hxy.toWalk (SimpleGraph.Walk.IsPath.of_adj hxy)
        simp only [SimpleGraph.Adj.length_toWalk] at hlen
        omega
      let W := woodallSet p
      let X := pathPrefixSet p k
      let C := univ \ W
      have hWpos : 0 < W.card := by
        rw [woodallSet_card p hp, ← G.card_neighborFinset_eq_degree]
        apply card_pos.mpr
        refine ⟨p.getVert 1,(G.mem_neighborFinset a _).mpr ?_⟩
        simpa using p.adj_getVert_succ (i := 0) hpos
      have hbC : b ∈ C := mem_sdiff.mpr ⟨mem_univ _,end_not_mem_woodallSet p hp.1⟩
      have hCpos : 0 < C.card := card_pos.mpr ⟨b,hbC⟩
      have hpartition : C.card+W.card = Fintype.card U := by
        simpa [C] using card_sdiff_add_card_eq_card (subset_univ W)
      have hCcard : Fintype.card (C:Set U) = C.card := by
        change Fintype.card C = C.card
        exact Fintype.card_coe C
      have hsmall : Fintype.card (C:Set U) < Fintype.card U := by
        rw [hCcard]
        omega
      have hcost := vertex_deletion_cost G W X (woodallSet_subset_prefix p hp hk hc)
        (pathPrefixSet_card p k) (fun v hv => woodallSet_degree p hp hv)
        (fun v hv w hvw => woodallSet_neighbors_subset_prefix p hp hk hc hv hvw)
      have hcycles : ∀ (v : (C:Set U)) (q : (G.induce (C:Set U)).Walk v v),
          q.IsCycle → q.length ≤ k := by
        intro v q hq
        let emb := SimpleGraph.Embedding.induce (G := G) (C:Set U)
        have h := hc v.val (q.map emb.toHom) (hq.map emb.injective)
        exact (SimpleGraph.Walk.length_map emb.toHom q).symm.le.trans h
      have hind := ih (Fintype.card (C:Set U)) (by omega) rfl
        (G.induce (C:Set U)) hcycles
      have hn : (C.card-1)+W.card = Fintype.card U-1 := by omega
      calc
        _ ≤ W.card*k + 2*(G.induce (C:Set U)).edgeFinset.card := hcost
        _ ≤ W.card*k + k*(Fintype.card (C:Set U)-1) := Nat.add_le_add_left hind _
        _ = k*((C.card-1)+W.card) := by rw [hCcard]; ring
        _ = _ := by rw [hn]

theorem erdosGallai_cycle (G : SimpleGraph V) (k : ℕ) (hk : 2 ≤ k)
    (hc : ∀ (v : V) (c : G.Walk v v), c.IsCycle → c.length ≤ k) :
    2*G.edgeFinset.card ≤ k*(Fintype.card V-1) :=
  erdosGallai_aux k hk (Fintype.card V) rfl G hc

end
end Cycle12.Independent
