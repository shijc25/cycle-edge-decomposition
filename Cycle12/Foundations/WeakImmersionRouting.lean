import Cycle12.Foundations.CliquePairs

/-! Routing through weak clique immersions. No internal-branch avoidance
is assumed; only the actual edge-disjoint immersion paths are used. -/
namespace Cycle13
open SimpleGraph
noncomputable section

structure WeakCliqueImmersion {V : Type} (t : ℕ) (G : SimpleGraph V) where
  branch : Fin t ↪ V
  route : ∀ p : CliquePair t, G.Path (branch p.1.1) (branch p.1.2)
  disjoint : Pairwise (fun p q => Disjoint (route p).val.edgeSet (route q).val.edgeSet)

def StrongCliqueImmersion.toWeak {V : Type} {G : SimpleGraph V} {t : ℕ}
    (M : StrongCliqueImmersion t G) : WeakCliqueImmersion t G :=
  ⟨M.branch, M.route, M.disjoint⟩

namespace CliquePair
variable {t : ℕ}
def ofNe {i j : Fin t} (h : i ≠ j) : CliquePair t :=
  if hij : i < j then ⟨(i,j),hij⟩ else ⟨(j,i),by change j < i; omega⟩

@[simp] theorem edge_ofNe {i j : Fin t} (h : i ≠ j) : (ofNe h).edge = s(i,j) := by
  by_cases hij : i < j <;> simp [ofNe, hij, edge, Sym2.eq_swap]
end CliquePair

namespace WeakCliqueImmersion
variable {V : Type} {G : SimpleGraph V} {t : ℕ}

def used (M : WeakCliqueImmersion t G) : Set (Sym2 V) :=
  ⋃ p : CliquePair t, (M.route p).val.edgeSet

def residue (M : WeakCliqueImmersion t G) : SimpleGraph V := G.deleteEdges M.used

theorem used_subset (M : WeakCliqueImmersion t G) : M.used ⊆ G.edgeSet := by
  intro e he
  obtain ⟨p, hp⟩ := Set.mem_iUnion.mp he
  exact (M.route p).val.edges_subset_edgeSet hp

theorem residue_disjoint_used (M : WeakCliqueImmersion t G) :
    Disjoint M.residue.edgeSet M.used := by
  rw [residue, edgeSet_deleteEdges]
  exact Set.disjoint_sdiff_left

def oriented (M : WeakCliqueImmersion t G) {i j : Fin t} (h : i ≠ j) :
    G.Walk (M.branch i) (M.branch j) :=
  if hij : i < j then (M.route ⟨(i,j),hij⟩).val
  else (M.route ⟨(j,i),by change j < i; omega⟩).val.reverse

theorem oriented_edgeSet (M : WeakCliqueImmersion t G) {i j : Fin t} (h : i ≠ j) :
    (M.oriented h).edgeSet = (M.route (CliquePair.ofNe h)).val.edgeSet := by
  by_cases hij : i < j
  · have hp : CliquePair.ofNe h = ⟨(i,j), hij⟩ := dif_pos hij
    have hw : M.oriented h = (M.route ⟨(i,j),hij⟩).val := dif_pos hij
    rw [hp, hw]
  · have hji : j < i := by omega
    have hp : CliquePair.ofNe h = ⟨(j,i), hji⟩ := dif_neg hij
    have hw : M.oriented h = (M.route ⟨(j,i),hji⟩).val.reverse := dif_neg hij
    rw [hp, hw, Walk.edgeSet_reverse]

def liftWalk (M : WeakCliqueImmersion t G) {i j : Fin t} :
    (completeGraph (Fin t)).Walk i j → G.Walk (M.branch i) (M.branch j)
  | .nil => .nil
  | .cons h p => (M.oriented h).append (M.liftWalk p)

theorem liftWalk_edge_origin (M : WeakCliqueImmersion t G) {i j : Fin t}
    (p : (completeGraph (Fin t)).Walk i j) {e : Sym2 V}
    (he : e ∈ (M.liftWalk p).edgeSet) :
    ∃ q : CliquePair t, q.edge ∈ p.edgeSet ∧ e ∈ (M.route q).val.edgeSet := by
  induction p with
  | nil => simpa [liftWalk] using he
  | @cons i k j h p ih =>
    simp only [liftWalk, Walk.edgeSet_append, Set.mem_union] at he
    rcases he with he | he
    · exact ⟨CliquePair.ofNe h, by simp, by rwa [M.oriented_edgeSet] at he⟩
    · obtain ⟨q, hq, heq⟩ := ih he
      exact ⟨q, by simp [hq], heq⟩

theorem liftWalk_disjoint (M : WeakCliqueImmersion t G) {i j a b : Fin t}
    (p : (completeGraph (Fin t)).Walk i j) (q : (completeGraph (Fin t)).Walk a b)
    (hd : Disjoint p.edgeSet q.edgeSet) :
    Disjoint (M.liftWalk p).edgeSet (M.liftWalk q).edgeSet := by
  apply Set.disjoint_left.mpr
  intro e hep heq
  obtain ⟨r, hrp, her⟩ := M.liftWalk_edge_origin p hep
  obtain ⟨s, hsq, hes⟩ := M.liftWalk_edge_origin q heq
  have hrs : r ≠ s := by
    intro h
    subst s
    exact Set.disjoint_left.mp hd hrp hsq
  exact Set.disjoint_left.mp (M.disjoint hrs) her hes

theorem liftWalk_edges_subset_used (M : WeakCliqueImmersion t G) {i j : Fin t}
    (p : (completeGraph (Fin t)).Walk i j) : (M.liftWalk p).edgeSet ⊆ M.used := by
  intro e he
  obtain ⟨q, _, heq⟩ := M.liftWalk_edge_origin p he
  exact Set.mem_iUnion.mpr ⟨q, heq⟩

theorem liftWalk_inside (M : WeakCliqueImmersion t G) (U : Set V)
    (hb : ∀ i, M.branch i ∈ U)
    (hr : ∀ q : CliquePair t, ∀ v ∈ (M.route q).val.support, v ∈ U)
    {i j : Fin t} (p : (completeGraph (Fin t)).Walk i j) :
    ∀ v ∈ (M.liftWalk p).support, v ∈ U := by
  induction p with
  | @nil i => simpa [liftWalk] using hb i
  | @cons i k j h p ih =>
    intro v hv
    simp only [liftWalk, Walk.mem_support_append_iff] at hv
    rcases hv with hv | hv
    · unfold oriented at hv
      split_ifs at hv with hik
      · exact hr _ v hv
      · exact hr _ v (by simpa using hv)
    · exact ih v hv

/-- Any edge-disjoint complete-graph demand realization lifts to actual
edge-disjoint simple paths, all contained in the reserved immersion edges. -/
theorem realize_paths (M : WeakCliqueImmersion t G) {I : Type}
    (a b : I → Fin t) (p : ∀ i, (completeGraph (Fin t)).Walk (a i) (b i))
    (hd : Pairwise (fun i j => Disjoint (p i).edgeSet (p j).edgeSet)) :
    ∃ Q : ∀ i, G.Walk (M.branch (a i)) (M.branch (b i)),
      (∀ i, (Q i).IsPath) ∧
      Pairwise (fun i j => Disjoint (Q i).edgeSet (Q j).edgeSet) ∧
      ∀ i, (Q i).edgeSet ⊆ M.used := by
  classical
  refine ⟨fun i => (M.liftWalk (p i)).bypass, fun i => Walk.bypass_isPath _, ?_, ?_⟩
  · intro i j hij
    exact (M.liftWalk_disjoint _ _ (hd hij)).mono
      (Walk.edges_bypass_subset_edges _) (Walk.edges_bypass_subset_edges _)
  · intro i e he
    exact M.liftWalk_edges_subset_used _ (Walk.edges_bypass_subset_edges _ he)

end WeakCliqueImmersion
end
end Cycle13
