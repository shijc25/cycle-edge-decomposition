import Cycle12.Foundations.PackingEraseCycle

namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def NoCycleAtLeast (G : SimpleGraph V) (T : ℕ) : Prop :=
  ∀ v (p : G.Walk v v), p.IsCycle → p.length < T

theorem NoCycleAtLeast.mono {G H : SimpleGraph V} {T : ℕ}
    (h : NoCycleAtLeast G T) (hle : H ≤ G) : NoCycleAtLeast H T := by
  intro v p hp
  simpa only [Walk.length_mapLe] using h v (p.mapLe hle) (hp.mapLe hle)

/-- An actual packing of long cycles with the exact edge payment needed
by the finite-stage affine recurrence. -/
theorem exists_long_cycle_removal (G : SimpleGraph V) (T : ℕ) :
    ∃ P : CyclePacking G, NoCycleAtLeast P.residue T ∧
      P.count*T+P.singles ≤ G.edgeSet.ncard := by
  have main : ∀ n : ℕ, ∀ P : CyclePacking G, P.singles=n →
      ∃ Q : CyclePacking G, NoCycleAtLeast Q.residue T ∧
        Q.count*T+Q.singles ≤ P.count*T+P.singles := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro P hP
      by_cases hstop : NoCycleAtLeast P.residue T
      · exact ⟨P,hstop,le_rfl⟩
      obtain ⟨v,p,hp,hlen⟩ : ∃ v, ∃ p : P.residue.Walk v v,
          p.IsCycle ∧ T ≤ p.length := by
        by_contra hnot
        apply hstop
        intro v p hp
        exact lt_of_not_ge (fun hlen => hnot ⟨v,p,hp,hlen⟩)
      let q := p.mapLe P.residue_le
      have hq : q.IsCycle := hp.mapLe _
      have hsub : q.edgeSet ⊆ P.residue.edgeSet := by
        rw [show q.edgeSet=p.edgeSet from Walk.edgeSet_mapLe_eq_edgeSet _ _]
        exact p.edges_subset_edgeSet
      let Q := P.addCycle q.edgeSet ⟨v,q,hq,rfl⟩ hsub
      have hcount : Q.count=P.count+1 := rfl
      have hs : Q.singles+p.length=P.singles := by
        have hh := P.singles_addCycle q.edgeSet ⟨v,q,hq,rfl⟩ hsub
        simpa only [Q,q,Walk.edgeSet_mapLe_eq_edgeSet,cycle_edgeSet_ncard hp] using hh
      have hsmall : Q.singles < n := by have hh := hp.three_le_length; omega
      obtain ⟨R,hR,hpay⟩ := ih _ hsmall Q rfl
      refine ⟨R,hR,hpay.trans ?_⟩
      rw [hcount]
      nlinarith
  obtain ⟨P,hP,hpay⟩ := main _ (CyclePacking.empty G) rfl
  refine ⟨P,hP,?_⟩
  simpa only [CyclePacking.empty,Nat.zero_mul,Nat.zero_add,CyclePacking.singles,
    CyclePacking.residue,CyclePacking.used,Set.iUnion_of_empty,SimpleGraph.deleteEdges_empty] using hpay

/-- A path whose endpoints are adjacent cannot span more than T tree
edges when the graph has no cycle of length at least T. -/
theorem path_length_le_of_adj_noLongCycle {G : SimpleGraph V} {T : ℕ}
    (hT : 1 ≤ T) (hG : NoCycleAtLeast G T) {u v : V}
    (p : G.Walk u v) (hp : p.IsPath) (huv : G.Adj u v) : p.length ≤ T := by
  by_cases he : p.length=1
  · omega
  have hnot : s(v,u) ∉ p.edges := by
    intro h
    apply he
    exact hp.length_eq_one_of_mem_edges (by simpa only [Sym2.eq_swap] using h)
  have hc : (p.cons huv.symm).IsCycle := (Walk.cons_isCycle_iff p huv.symm).mpr ⟨hp,hnot⟩
  have hl := hG v (p.cons huv.symm) hc
  simp only [Walk.length_cons] at hl
  omega

end
end Cycle13
