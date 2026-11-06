import Cycle12.CrossingPairWalk12

namespace Cycle12
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I T : Type} [Fintype V] [Fintype I] [Fintype T]
  [DecidableEq V] [DecidableEq I] [DecidableEq T] {G : SimpleGraph V}

/-- Close paired matching edges by alternating routes in two disjoint
cores. Each group, including a group containing just two original edges,
costs at most one actual simple cycle. -/
theorem alternating_matching_group_closure (U W : Finset V) (hUW : Disjoint U W)
    (group : I → T) (a₀ a₁ b₀ b₁ : I → V)
    (h₀ : ∀ i,G.Adj (a₀ i) (b₀ i)) (h₁ : ∀ i,G.Adj (a₁ i) (b₁ i))
    (ha₀ : ∀ i,a₀ i∈U) (ha₁ : ∀ i,a₁ i∈U) (ha : ∀ i,a₀ i ≠ a₁ i)
    (hA : Pairwise (fun i j => Disjoint ({a₀ i,a₁ i}:Finset V) {a₀ j,a₁ j}))
    (hB : Pairwise (fun i j => Disjoint ({b₀ i,b₁ i}:Finset V) {b₀ j,b₁ j}))
    (r : ∀ i,G.Walk (b₀ i) (b₁ i))
    (s : ∀ i,G.Walk (a₁ i) (a₀ (groupedCycleNext group i)))
    (hr : ∀ i,(r i).IsPath) (hs : ∀ i,(s i).IsPath)
    (hrW : ∀ i v,v∈(r i).support → v∈W) (hsU : ∀ i v,v∈(s i).support → v∈U)
    (hrHard : ∀ i,Disjoint (routeInterior (r i)) (groupPorts group b₀ b₁ (group i)))
    (hsHard : ∀ i,Disjoint (routeInterior (s i)) (groupPorts group a₀ a₁ (group i)))
    (hrInt : ∀ i j,i ≠ j → group i=group j → Disjoint (routeInterior (r i)) (routeInterior (r j)))
    (hsInt : ∀ i j,i ≠ j → group i=group j → Disjoint (routeInterior (s i)) (routeInterior (s j)))
    (hrEdges : Pairwise (fun i j => Disjoint (r i).edgeSet (r j).edgeSet))
    (hsEdges : Pairwise (fun i j => Disjoint (s i).edgeSet (s j).edgeSet))
    (hrs : ∀ i j,Disjoint (r i).edgeSet (s j).edgeSet)
    (hO : Pairwise (fun i j => Disjoint ({s(a₀ i,b₀ i),s(a₁ i,b₁ i)}:Set (Sym2 V))
      {s(a₀ j,b₀ j),s(a₁ j,b₁ j)}))
    (hOr : ∀ i j,Disjoint ({s(a₀ i,b₀ i),s(a₁ i,b₁ i)}:Set (Sym2 V)) (r j).edgeSet)
    (hOs : ∀ i j,Disjoint ({s(a₀ i,b₀ i),s(a₁ i,b₁ i)}:Set (Sym2 V)) (s j).edgeSet) :
    ∃ P : CyclePacking G,
      P.used=(⋃ i,({s(a₀ i,b₀ i),s(a₁ i,b₁ i)}:Set (Sym2 V)))∪
        (⋃ i,(r i).edgeSet)∪(⋃ i,(s i).edgeSet) ∧ P.count ≤ Fintype.card T := by
  let p := fun i => crossingPairWalk (h₀ i) (h₁ i) (r i)
  have hportsU (i) : ({a₀ i,a₁ i}:Finset V) ⊆ U := by
    intro v hv
    simp only [mem_insert,mem_singleton] at hv
    rcases hv with rfl|rfl
    · exact ha₀ i
    · exact ha₁ i
  have hrouteW (i) : (r i).support.toFinset ⊆ W := by
    intro v hv
    exact hrW i v (List.mem_toFinset.mp hv)
  have hp (i) : (p i).IsPath := crossingPairWalk_isPath _ _ _ (hr i) (ha i)
    (fun h => Finset.disjoint_left.mp hUW (ha₀ i) (hrW i _ h))
    (fun h => Finset.disjoint_left.mp hUW (ha₁ i) (hrW i _ h))
  have hv (i j) (hij : i ≠ j) (hg : group i=group j) :
      Disjoint (p i).support.toFinset (p j).support.toFinset := by
    simp only [p,crossingPairWalk_support]
    have hrr := grouped_route_supports_disjoint group b₀ b₁ r hB hrHard hrInt hij hg
    have haj := hUW.mono (hportsU i) (hrouteW j)
    have hai := hUW.mono (hportsU j) (hrouteW i)
    apply Finset.disjoint_left.mpr
    intro v hv hw
    rcases mem_union.mp hv with hv|hv <;> rcases mem_union.mp hw with hw|hw
    · exact Finset.disjoint_left.mp (hA hij) hv hw
    · exact Finset.disjoint_left.mp haj hv hw
    · exact Finset.disjoint_left.mp hai hw hv
    · exact Finset.disjoint_left.mp hrr hv hw
  have hnext : ∀ i,a₁ i ≠ a₀ (groupedCycleNext group i) :=
    grouped_reconnection_distinct group a₀ a₁ ha (by
      intro i j hij _ he
      exact Finset.disjoint_left.mp (hA hij)
        (show a₁ i∈({a₀ i,a₁ i}:Finset V) from by simp) (by simp [he]))
  have hPP : Pairwise (fun i j => Disjoint (p i).edgeSet (p j).edgeSet) := by
    intro i j hij
    simp only [p,crossingPairWalk_edges]
    apply Set.disjoint_left.mpr
    rintro e (he|he) (hf|hf)
    · exact Set.disjoint_left.mp (hO hij) he hf
    · exact Set.disjoint_left.mp (hOr i j) he hf
    · exact Set.disjoint_left.mp (hOr j i) hf he
    · exact Set.disjoint_left.mp (hrEdges hij) he hf
  have hPS (i j) : Disjoint (p i).edgeSet (s j).edgeSet := by
    simp only [p,crossingPairWalk_edges]
    exact Set.disjoint_union_left.mpr ⟨hOs i j,hrs i j⟩
  have hforbid (i j) (hg : group i=group j) :
      Disjoint (routeInterior (s i)) (p j).support.toFinset := by
    simp only [p,crossingPairWalk_support]
    apply Finset.disjoint_left.mpr
    intro v hv hw
    rcases mem_union.mp hw with hw|hw
    · apply Finset.disjoint_left.mp (hsHard i) hv
      apply (mem_groupPorts group a₀ a₁ (group i) v).mpr
      refine ⟨j,hg.symm,?_⟩
      simpa only [mem_insert,mem_singleton,eq_comm] using hw
    · exact Finset.disjoint_left.mp hUW (hsU i _ ((mem_routeInterior_iff _ _).mp hv).1)
        (hrouteW j hw)
  obtain ⟨P,hused,hcount⟩ := grouped_family_cycle_packing group a₀ a₁ p s hp hs hnext
    hv hPP hsEdges hPS hsInt hforbid
  refine ⟨P,?_,hcount⟩
  simpa only [p,crossingPairWalk_edges,Set.iUnion_union_distrib] using hused

end
end Cycle12
