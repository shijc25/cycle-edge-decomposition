import Cycle12.Foundations.ForestBound
import Cycle12.Foundations.WeightedConversion
import Cycle12.Foundations.UpstreamBridge

/-! Weighted cycle packings. Their remaining edges are always taken as singletons.
The integer cost `42*cycles + 23*singles` is exactly 42 times the required weight. -/
namespace Cycle13
open Finset SimpleGraph
noncomputable section
variable {V : Type} [Fintype V]
attribute [local instance] Classical.propDecidable

structure CyclePacking (G : SimpleGraph V) where
  count : ℕ
  parts : Fin count → Set (Sym2 V)
  cycles : ∀ i, ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ parts i = p.edgeSet
  disjoint : Pairwise (fun i j => Disjoint (parts i) (parts j))

namespace CyclePacking
variable {G : SimpleGraph V}

def used (P : CyclePacking G) : Set (Sym2 V) := ⋃ i, P.parts i
def residue (P : CyclePacking G) : SimpleGraph V := G.deleteEdges P.used
def singles (P : CyclePacking G) : ℕ := P.residue.edgeSet.ncard
def cost (P : CyclePacking G) : ℕ := 42 * P.count + 23 * P.singles

def empty (G : SimpleGraph V) : CyclePacking G where
  count := 0
  parts := Fin.elim0
  cycles := fun i => Fin.elim0 i
  disjoint := fun i => Fin.elim0 i

theorem residue_le (P : CyclePacking G) : P.residue ≤ G := G.deleteEdges_le _

theorem parts_subset (P : CyclePacking G) (i : Fin P.count) : P.parts i ⊆ G.edgeSet :=
  part_subset (Or.inl (P.cycles i))

theorem used_subset (P : CyclePacking G) : P.used ⊆ G.edgeSet :=
  Set.iUnion_subset P.parts_subset

theorem residue_disjoint_part (P : CyclePacking G) (i : Fin P.count) :
    Disjoint P.residue.edgeSet (P.parts i) := by
  apply Set.disjoint_left.mpr
  intro e he hi
  rw [residue, edgeSet_deleteEdges] at he
  exact he.2 (Set.mem_iUnion.mpr ⟨i, hi⟩)

def addCycle (P : CyclePacking G) (s : Set (Sym2 V))
    (hs : ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ s = p.edgeSet)
    (hsub : s ⊆ P.residue.edgeSet) : CyclePacking G where
  count := P.count + 1
  parts := Fin.cases s P.parts
  cycles := Fin.cases hs P.cycles
  disjoint := by
    intro i j hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact (hij rfl).elim
      | succ j => exact (P.residue_disjoint_part j).mono_left hsub
    | succ i =>
      induction j using Fin.cases with
      | zero => exact ((P.residue_disjoint_part i).mono_left hsub).symm
      | succ j => exact P.disjoint (fun h => hij (congrArg Fin.succ h))

theorem used_addCycle (P : CyclePacking G) (s : Set (Sym2 V))
    (hs : ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ s = p.edgeSet)
    (hsub : s ⊆ P.residue.edgeSet) :
    (P.addCycle s hs hsub).used = s ∪ P.used := by
  ext e
  simp only [used, addCycle, Set.mem_iUnion, Set.mem_union]
  constructor
  · rintro ⟨i, hi⟩
    induction i using Fin.cases with
    | zero => exact Or.inl hi
    | succ i => exact Or.inr ⟨i, hi⟩
  · rintro (he | ⟨i, hi⟩)
    · exact ⟨0, he⟩
    · exact ⟨i.succ, hi⟩

theorem residue_addCycle (P : CyclePacking G) (s : Set (Sym2 V))
    (hs : ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ s = p.edgeSet)
    (hsub : s ⊆ P.residue.edgeSet) :
    (P.addCycle s hs hsub).residue = P.residue.deleteEdges s := by
  apply SimpleGraph.edgeSet_injective
  simp only [residue, edgeSet_deleteEdges, used_addCycle]
  ext e
  simp only [Set.mem_sdiff, Set.mem_union]
  tauto

theorem singles_addCycle (P : CyclePacking G) (s : Set (Sym2 V))
    (hs : ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ s = p.edgeSet)
    (hsub : s ⊆ P.residue.edgeSet) :
    (P.addCycle s hs hsub).singles + s.ncard = P.singles := by
  unfold singles
  rw [residue_addCycle, edgeSet_deleteEdges, Set.ncard_sdiff hsub]
  exact Nat.sub_add_cancel (Set.ncard_le_ncard hsub)

theorem exists_minimum (G : SimpleGraph V) :
    ∃ P : CyclePacking G, ∀ Q : CyclePacking G, P.cost ≤ Q.cost := by
  have h : ∃ n : ℕ, ∃ P : CyclePacking G, P.cost = n := ⟨(empty G).cost, empty G, rfl⟩
  obtain ⟨P, hP⟩ := Nat.find_spec h
  exact ⟨P, fun Q => hP ▸ Nat.find_min' h ⟨Q, rfl⟩⟩

theorem minimum_residue_isAcyclic (P : CyclePacking G)
    (hmin : ∀ Q : CyclePacking G, P.cost ≤ Q.cost) : P.residue.IsAcyclic := by
  classical
  intro v p hp
  let q := p.mapLe P.residue_le
  have hq : q.IsCycle := hp.mapLe _
  have hqedge : q.edgeSet = p.edgeSet := by simp [q]
  have hsub : q.edgeSet ⊆ P.residue.edgeSet := by
    rw [hqedge]
    exact p.edges_subset_edgeSet
  let Q := P.addCycle q.edgeSet ⟨v, q, hq, rfl⟩ hsub
  have hcount : Q.count = P.count + 1 := rfl
  have hs := P.singles_addCycle q.edgeSet ⟨v, q, hq, rfl⟩ hsub
  have hlength : q.edgeSet.ncard = p.length := by
    rw [hqedge, ← p.coe_edges_toFinset, Set.ncard_coe_finset]
    simpa using List.toFinset_card_of_nodup hp.isTrail.edges_nodup
  rw [hlength] at hs
  have hle := hmin Q
  have hl := hp.three_le_length
  change 42 * P.count + 23 * P.singles ≤ 42 * Q.count + 23 * Q.singles at hle
  change Q.singles + p.length = P.singles at hs
  omega

theorem minimum_singletons_le_rank (P : CyclePacking G)
    (hmin : ∀ Q : CyclePacking G, P.cost ≤ Q.cost) :
    P.singles ≤ Fintype.card V - componentCount G := by
  have h := forest_subgraph_edge_bound G P.residue P.residue_le (P.minimum_residue_isAcyclic hmin)
  simpa only [singles, SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card'] using h

theorem decomposition (P : CyclePacking G) : EdgeDecomposition G (P.count + P.singles) := by
  classical
  let I := Fin P.count ⊕ P.residue.edgeSet
  let parts : I → Set (Sym2 V) := Sum.elim P.parts (fun e => {e.1})
  have hp : ∀ i : I, CycleOrSingleEdge G (parts i) := by
    intro i
    cases i with
    | inl i => exact Or.inl (P.cycles i)
    | inr e => exact Or.inr ⟨e.1, SimpleGraph.edgeSet_mono P.residue_le e.2, rfl⟩
  have hd : Pairwise (fun i j : I => Disjoint (parts i) (parts j)) := by
    intro i j hij
    cases i with
    | inl i =>
      cases j with
      | inl j => exact P.disjoint (fun h => hij (congrArg Sum.inl h))
      | inr e =>
        exact (P.residue_disjoint_part i).symm.mono_right (Set.singleton_subset_iff.mpr e.2)
    | inr e =>
      cases j with
      | inl i =>
        exact (P.residue_disjoint_part i).mono_left (Set.singleton_subset_iff.mpr e.2)
      | inr d =>
        exact Set.disjoint_singleton.mpr (fun h => hij (congrArg Sum.inr (Subtype.ext h)))
  have hu : (⋃ i : I, parts i) = G.edgeSet := by
    ext e
    constructor
    · intro he
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp he
      exact part_subset (hp i) hi
    · intro he
      by_cases hused : e ∈ P.used
      · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hused
        exact Set.mem_iUnion.mpr ⟨Sum.inl i, hi⟩
      · have hr : e ∈ P.residue.edgeSet := by
          rw [residue, edgeSet_deleteEdges]
          exact ⟨he, hused⟩
        exact Set.mem_iUnion.mpr ⟨Sum.inr ⟨e, hr⟩, rfl⟩
  have hc : Fintype.card I = P.count + P.singles := by
    simp only [I, Fintype.card_sum, Fintype.card_fin, singles,
      Set.ncard_eq_toFinset_card', Set.toFinset_card]
  rw [← hc]
  exact OAI.ErdosGallai.edgeDecomposition_of_indexed G parts hp hd hu

end CyclePacking

/-- The complete graph-theoretic conversion from the specific weighted bound.
The weighted bound is an explicit premise here and is not yet proved globally. -/
theorem coefficient13_of_weighted_packing (G : SimpleGraph V)
    (hweighted : ∃ P : CyclePacking G,
      P.cost ≤ 527 * (Fintype.card V - componentCount G)) :
    ∃ k : ℕ, EdgeDecomposition G k ∧ k ≤ 13 * (Fintype.card V - componentCount G) := by
  obtain ⟨Q, hQ⟩ := hweighted
  obtain ⟨P, hmin⟩ := CyclePacking.exists_minimum G
  have hcost := (hmin Q).trans hQ
  have hforest := P.minimum_singletons_le_rank hmin
  refine ⟨P.count + P.singles, P.decomposition, ?_⟩
  unfold CyclePacking.cost at hcost
  omega

end
end Cycle13
