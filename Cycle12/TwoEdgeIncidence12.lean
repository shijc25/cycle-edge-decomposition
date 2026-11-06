import Cycle12.LowPathColoring12
import Cycle12.GroupedFamilyPacking12

namespace Cycle12
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]
  {G : SimpleGraph V}

def twoEdgeWalk {a b z : V} (ha : G.Adj z a) (hb : G.Adj z b) : G.Walk a b :=
  Walk.cons ha.symm (Walk.cons hb Walk.nil)

theorem twoEdgeWalk_support {a b z : V} (ha : G.Adj z a) (hb : G.Adj z b) :
    (twoEdgeWalk ha hb).support.toFinset={a,b,z} := by
  ext v
  simp only [twoEdgeWalk,Walk.support_cons,Walk.support_nil,List.toFinset_cons,
    List.toFinset_nil,mem_insert,mem_singleton]
  tauto

theorem twoEdgeWalk_length {a b z : V} (ha : G.Adj z a) (hb : G.Adj z b) :
    (twoEdgeWalk ha hb).length=2 := rfl

theorem twoEdgeWalk_edges {a b z : V} (ha : G.Adj z a) (hb : G.Adj z b) :
    (twoEdgeWalk ha hb).edgeSet={s(z,a),s(z,b)} := by
  simp [twoEdgeWalk,Sym2.eq_swap]

theorem twoEdgeWalk_isPath {a b z : V} (ha : G.Adj z a) (hb : G.Adj z b) (hne : a ≠ b) :
    (twoEdgeWalk ha hb).IsPath := by
  apply Walk.IsPath.mk'
  simp [twoEdgeWalk,ha.ne.symm,hb.ne,hne]

/-- Each original two-edge path at a center uses two distinct incident
edges. This bound is valid for a family aggregated across all batches. -/
theorem twoEdge_center_load (a b z : I → V)
    (ha : ∀ i,G.Adj (z i) (a i)) (hb : ∀ i,G.Adj (z i) (b i))
    (hne : ∀ i,a i ≠ b i)
    (hd : Pairwise (fun i j => Disjoint (twoEdgeWalk (ha i) (hb i)).edgeSet
      (twoEdgeWalk (ha j) (hb j)).edgeSet)) (v : V) :
    2*(univ.filter (fun i => z i=v)).card ≤ G.degree v := by
  let J := {i : I // z i=v}
  let S : Set (Sym2 V) := ⋃ i : J,(twoEdgeWalk (ha i.val) (hb i.val)).edgeSet
  have hcard : S.ncard=2*Fintype.card J := by
    rw [show S=⋃ i : J,(twoEdgeWalk (ha i.val) (hb i.val)).edgeSet from rfl,
      ncard_iUnion_disjoint _ (fun i j hij => hd (Subtype.val_injective.ne hij))]
    simp_rw [trail_edgeSet_ncard _ (twoEdgeWalk_isPath _ _ (hne _)).isTrail,twoEdgeWalk_length]
    simp only [sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,mul_comm,J]
  have hs : S ⊆ G.incidenceSet v := by
    intro e he
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp he
    rw [twoEdgeWalk_edges] at hi
    rcases hi with rfl|rfl
    · simpa only [i.property] using G.mk'_mem_incidenceSet_left_iff.mpr (ha i.val)
    · simpa only [i.property] using G.mk'_mem_incidenceSet_left_iff.mpr (hb i.val)
  have hh := Set.ncard_le_ncard hs (Set.toFinite _)
  rw [hcard] at hh
  simpa only [J,Fintype.card_subtype,G.ncard_incidenceSet] using hh

end
end Cycle12
