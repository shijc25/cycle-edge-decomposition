import Cycle12.Foundations.StarPairing
import Cycle12.Foundations.ClosedTrailDecomposition

namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

abbrev OutsideCenter (U : Finset V) := {z : V // z∉U}
abbrev CenterPort (G : SimpleGraph V) (U : Finset V) (z : OutsideCenter U) :=
  {v : V // v∈U ∧ G.Adj z.val v}

/-- Independent pairings at all exterior centers. They are constructed
by maximal matchings, with at most one uncovered original edge per center. -/
structure CenterPairings (G : SimpleGraph V) (U : Finset V) where
  matching : ∀ z : OutsideCenter U,(⊤ : SimpleGraph (CenterPort G U z)).Subgraph
  isMatching : ∀ z,(matching z).IsMatching
  uncovered : ∀ z,(matching z).vertsᶜ.ncard ≤ 1

theorem exists_centerPairings (G : SimpleGraph V) (U : Finset V) :
    Nonempty (CenterPairings G U) := by
  choose M hM hrem hcard using fun z : OutsideCenter U =>
    complete_matching_leaves_at_most_one (I:=CenterPort G U z)
  exact ⟨⟨M,hM,hrem⟩⟩

namespace CenterPairings
variable {G : SimpleGraph V} {U : Finset V} (P : CenterPairings G U)

abbrev Index := Σ z : OutsideCenter U,(P.matching z).edgeSet

abbrev portEmbedding (_P : CenterPairings G U) (z : OutsideCenter U) : CenterPort G U z ↪ V :=
  ⟨Subtype.val,Subtype.val_injective⟩

abbrev left (e : P.Index) : V := e.2.val.out.1.val
abbrev right (e : P.Index) : V := e.2.val.out.2.val

def walk (e : P.Index) : G.Walk (P.left e) (P.right e) :=
  StarPairing.paired G e.1.val (P.portEmbedding e.1) (fun v => v.property.2)
    (P.matching e.1) e.2

theorem walk_isPath (e : P.Index) : (P.walk e).IsPath :=
  StarPairing.paired_isPath G e.1.val (P.portEmbedding e.1) _ _ e.2

theorem walk_length (e : P.Index) : (P.walk e).length=2 :=
  StarPairing.paired_length G e.1.val (P.portEmbedding e.1) _ _ e.2

theorem walk_edge_endpoints (e : P.Index) {d : Sym2 V} (hd : d∈(P.walk e).edgeSet) :
    ∃ v∈U,d=s(e.1.val,v) := by
  rw [walk,StarPairing.paired_edges] at hd
  rcases hd with rfl | rfl
  · exact ⟨_,e.2.val.out.1.property.1,rfl⟩
  · exact ⟨_,e.2.val.out.2.property.1,rfl⟩

theorem walks_disjoint : Pairwise (fun e f : P.Index =>
    Disjoint (P.walk e).edgeSet (P.walk f).edgeSet) := by
  rintro ⟨z,e⟩ ⟨w,f⟩ hne
  by_cases hzw : z=w
  · subst w
    exact StarPairing.paired_disjoint G z.val (P.portEmbedding z) _ (P.matching z)
      (P.isMatching z) (fun hef => hne (by cases hef; rfl))
  · apply Set.disjoint_left.mpr
    intro d he hf
    obtain ⟨v,hv,hev⟩ := P.walk_edge_endpoints ⟨z,e⟩ he
    obtain ⟨u,hu,heu⟩ := P.walk_edge_endpoints ⟨w,f⟩ hf
    have heq : s(z.val,v)=s(w.val,u) := hev.symm.trans heu
    rcases Sym2.eq_iff.mp heq with ⟨hz,_⟩ | ⟨hz,_⟩
    · exact hzw (Subtype.ext hz)
    · exact z.property (hz.symm ▸ hu)

def used : Set (Sym2 V) := ⋃ e : P.Index,(P.walk e).edgeSet
def residue : SimpleGraph V := G.deleteEdges P.used

theorem used_subset : P.used ⊆ G.edgeSet := by
  intro d hd
  obtain ⟨e,he⟩ := Set.mem_iUnion.mp hd
  exact (P.walk e).edges_subset_edgeSet he

theorem paired_port_edge_used (z : OutsideCenter U) (v : CenterPort G U z)
    (hv : v∈(P.matching z).verts) : s(z.val,v.val)∈P.used := by
  have hh : s(z.val,v.val)∈
      (fun i : CenterPort G U z => s(z.val,P.portEmbedding z i)) '' (P.matching z).verts :=
    ⟨v,hv,rfl⟩
  rw [← StarPairing.paired_edge_union G z.val (P.portEmbedding z)
    (fun i => i.property.2) (P.matching z) (P.isMatching z)] at hh
  obtain ⟨e,he⟩ := Set.mem_iUnion.mp hh
  exact Set.mem_iUnion.mpr ⟨⟨z,e⟩,he⟩

/-- Pairing all the stars leaves at most one edge at each exterior
center. The entire retained graph is the original graph minus the actual
two-edge paths, so no edge ownership assumption is hidden in the result. -/
theorem residue_exterior_degree_le_one
    (hside : ∀ {z v},G.Adj z v → z∉U → v∈U) (z : OutsideCenter U) :
    P.residue.degree z.val ≤ 1 := by
  rw [← ncard_neighborSet]
  apply Set.ncard_le_one_iff_subsingleton.mpr
  intro x hx y hy
  have hxG : G.Adj z.val x := hx.1
  have hyG : G.Adj z.val y := hy.1
  let px : CenterPort G U z := ⟨x,hside hxG z.property,hxG⟩
  let py : CenterPort G U z := ⟨y,hside hyG z.property,hyG⟩
  have hpx : px∈(P.matching z).vertsᶜ := by
    intro hv
    exact hx.2 ⟨P.paired_port_edge_used z px hv,hxG.ne⟩
  have hpy : py∈(P.matching z).vertsᶜ := by
    intro hv
    exact hy.2 ⟨P.paired_port_edge_used z py hv,hyG.ne⟩
  have hh := Set.ncard_le_one_iff_subsingleton.mp (P.uncovered z) hpx hpy
  exact congrArg Subtype.val hh

theorem used_card : P.used.ncard=2*Fintype.card P.Index := by
  rw [used,ncard_iUnion_disjoint _ P.walks_disjoint]
  simp_rw [trail_edgeSet_ncard _ (P.walk_isPath _).isTrail,P.walk_length]
  simp [mul_comm]

theorem exact_edge_account : P.residue.edgeSet.ncard+2*Fintype.card P.Index=G.edgeSet.ncard := by
  rw [residue,SimpleGraph.edgeSet_deleteEdges,← P.used_card,
    Set.ncard_sdiff P.used_subset]
  exact Nat.sub_add_cancel (Set.ncard_le_ncard P.used_subset)

end CenterPairings
end
end Cycle13
