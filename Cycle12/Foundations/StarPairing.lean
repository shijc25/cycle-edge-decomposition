import Cycle12.Foundations.RoutedEdges
import Cycle12.Foundations.SplittingMatching

namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

theorem complete_matching_leaves_at_most_one :
    ∃ M : (⊤ : SimpleGraph I).Subgraph, M.IsMatching ∧
      M.vertsᶜ.ncard ≤ 1 ∧ 2*M.edgeSet.ncard+M.vertsᶜ.ncard=Fintype.card I := by
  obtain ⟨M,hM⟩ := exists_maximal_matching (⊤ : SimpleGraph I)
  have hrem : M.vertsᶜ.ncard ≤ 1 := by
    apply Set.ncard_le_one_iff_subsingleton.mpr
    intro i hi j hj
    by_contra hij
    exact maximal_matching_unmatched_nonadjacent _ M hM hi hj hij
  refine ⟨M,hM.prop,hrem,?_⟩
  rw [← matching_matched_vertices_card _ M hM.prop,Set.ncard_add_ncard_compl]
  exact Nat.card_eq_fintype_card

namespace StarPairing
variable (G : SimpleGraph V) (z : V) (port : I ↪ V) (adj : ∀ i,G.Adj z (port i))

def arm (i : I) : G.Walk z (port i) := Walk.cons (adj i) Walk.nil

theorem arm_edges (i : I) : (arm G z port adj i).edgeSet={s(z,port i)} := by
  simp [arm]

theorem arms_disjoint : Pairwise (fun i j => Disjoint (arm G z port adj i).edgeSet
    (arm G z port adj j).edgeSet) := by
  intro i j hij
  rw [arm_edges,arm_edges]
  apply Set.disjoint_singleton.mpr
  intro he
  apply hij
  apply port.injective
  simpa [(adj j).ne] using he

variable (M : (⊤ : SimpleGraph I).Subgraph)

def paired (e : M.edgeSet) : G.Walk (port e.val.out.1) (port e.val.out.2) :=
  MatchingPortFamily.walk M id port z (arm G z port adj) e

theorem paired_edges (e : M.edgeSet) : (paired G z port adj M e).edgeSet=
    {s(z,port e.val.out.1),s(z,port e.val.out.2)} := by
  simp only [paired,MatchingPortFamily.walk,Walk.edgeSet_append,Walk.edgeSet_reverse,arm_edges]
  rfl

theorem paired_isPath (e : M.edgeSet) : (paired G z port adj M e).IsPath := by
  have he : M.Adj e.val.out.1 e.val.out.2 := edge_out_adj M.spanningCoe e
  have hp : port e.val.out.1 ≠ port e.val.out.2 := port.injective.ne (M.adj_sub he)
  apply Walk.IsPath.mk'
  simp [paired,MatchingPortFamily.walk,arm,Walk.support_append,
    hp,(adj e.val.out.1).ne,(adj e.val.out.2).ne,
    (adj e.val.out.1).ne.symm,(adj e.val.out.2).ne.symm]

theorem paired_length (e : M.edgeSet) : (paired G z port adj M e).length=2 := by
  simp [paired,MatchingPortFamily.walk,arm]

theorem paired_disjoint (hM : M.IsMatching) :
    Pairwise (fun e f : M.edgeSet => Disjoint (paired G z port adj M e).edgeSet
      (paired G z port adj M f).edgeSet) :=
  MatchingPortFamily.walk_disjoint M id port z (arm G z port adj) hM
    (arms_disjoint G z port adj)

/-- Every covered port edge occurs in exactly one two-edge path. In
particular, pairing removes no unaccounted original edge. -/
theorem paired_edge_union (hM : M.IsMatching) :
    (⋃ e : M.edgeSet,(paired G z port adj M e).edgeSet)=
      (fun i => s(z,port i)) '' M.verts := by
  ext d
  constructor
  · intro hd
    obtain ⟨e,he⟩ := Set.mem_iUnion.mp hd
    rw [paired_edges] at he
    have ha : M.Adj e.val.out.1 e.val.out.2 := edge_out_adj M.spanningCoe e
    rcases he with rfl | rfl
    · exact ⟨_,ha.fst_mem,rfl⟩
    · exact ⟨_,ha.snd_mem,rfl⟩
  · rintro ⟨i,hi,rfl⟩
    obtain ⟨j,hij,_⟩ := hM hi
    let e : M.edgeSet := ⟨s(i,j),hij⟩
    apply Set.mem_iUnion.mpr
    refine ⟨e,?_⟩
    rw [paired_edges]
    have he : s(e.val.out.1,e.val.out.2)=s(i,j) := e.val.out_eq
    have hor : (e.val.out.1=i ∧ e.val.out.2=j) ∨
        (e.val.out.1=j ∧ e.val.out.2=i) := by
      simpa only [Sym2.eq,Sym2.rel_iff',Prod.mk.injEq,Prod.swap_prod_mk] using he
    rcases hor with h | h
    · have hh : e.val.out.1=i := h.1
      simp [hh]
    · have hh : e.val.out.2=i := h.2
      simp [hh]

end StarPairing
end
end Cycle13
