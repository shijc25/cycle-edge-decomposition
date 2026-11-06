import OAI.Combinatorics.CycleDecomposition.ReservoirCycles

namespace Cycle12
open SimpleGraph
open OAI.ErdosGallai
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} {G : SimpleGraph V} {x y a b : V}

/-- Closing an isolated old vertex is permitted when its two connectors
reach distinct reservoir vertices. This is needed for hub-only paths. -/
theorem reservoir_return_cycle (P : G.Walk a b) (hP : P.IsPath)
    (hxP : x ∉ P.support) (hab : a ≠ b)
    (hx : G.Adj x a) (hy : G.Adj x b) :
    (reservoirReturn P hx hy).IsCycle := by
  unfold reservoirReturn
  apply (Walk.cons_isCycle_iff _ hy).mpr
  refine ⟨hP.reverse.concat (by simpa using hxP) hx.symm,?_⟩
  intro he
  simp only [Walk.edges_concat,Walk.edges_reverse,List.concat_eq_append,List.mem_append,List.mem_reverse,
    List.mem_singleton] at he
  rcases he with he | he
  · exact hxP (P.fst_mem_support_of_mem_edges he)
  · rcases Sym2.eq_iff.mp he with ⟨hxa,_⟩ | ⟨_,hba⟩
    · exact hx.ne hxa
    · exact hab hba.symm

/-- Reservoir closure including zero-length exterior paths. Distinct
representatives handle exactly the case of coincident exterior endpoints. -/
theorem reservoir_path_closure_allow_nil (Q : G.Walk x y) (P : G.Walk a b)
    (hQ : Q.IsPath) (hP : P.IsPath)
    (hdisj : Q.support.Disjoint P.support) (hab : x = y → a ≠ b)
    (hx : G.Adj x a) (hy : G.Adj y b) :
    (Q.append (reservoirReturn P hx hy)).IsCycle ∧
    (Q.append (reservoirReturn P hx hy)).edgeSet =
      Q.edgeSet ∪ P.edgeSet ∪ {s(x,a),s(y,b)} ∧
    3 ≤ (Q.append (reservoirReturn P hx hy)).length := by
  by_cases hxy : x = y
  · subst y
    have hnil : Q = Walk.nil := Walk.isPath_iff_eq_nil.mp hQ
    have hcycle : (Q.append (reservoirReturn P hx hy)).IsCycle := by
      rw [hnil,Walk.nil_append]
      exact reservoir_return_cycle P hP (hdisj Q.start_mem_support) (hab rfl) hx hy
    refine ⟨hcycle,?_,hcycle.three_le_length⟩
    ext e
    simp only [Walk.edgeSet_append,reservoirReturn,Walk.edgeSet_cons,
      Walk.edgeSet_concat,Walk.edgeSet_reverse,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff]
    rw [Sym2.eq_swap (a := x) (b := a)]
    tauto
  · have hpos : 0 < Q.length := by
      by_contra! hz
      exact hxy (Walk.eq_of_length_eq_zero (by omega : Q.length = 0))
    exact reservoir_path_closure Q P hQ hpos hP hdisj hx hy

theorem reservoir_cycle_family_allow_nil {J : Type}
    {x y a b : J → V} (Q : ∀ i, G.Walk (x i) (y i)) (P : ∀ i, G.Walk (a i) (b i))
    (hx : ∀ i, G.Adj (x i) (a i)) (hy : ∀ i, G.Adj (y i) (b i))
    (hQ : ∀ i, (Q i).IsPath) (hP : ∀ i, (P i).IsPath)
    (hab : ∀ i, x i = y i → a i ≠ b i)
    (hsep : ∀ i, (Q i).support.Disjoint (P i).support)
    (hQQ : Pairwise (fun i j => Disjoint (Q i).edgeSet (Q j).edgeSet))
    (hPP : Pairwise (fun i j => Disjoint (P i).edgeSet (P j).edgeSet))
    (hspoke : Function.Injective (fun z : J × Fin 2 =>
      if z.2 = 0 then s(x z.1,a z.1) else s(y z.1,b z.1)))
    (hQP : ∀ i j, Disjoint (Q i).edgeSet (P j).edgeSet)
    (hQS : ∀ i j, Disjoint (Q i).edgeSet {s(x j,a j),s(y j,b j)})
    (hPS : ∀ i j, Disjoint (P i).edgeSet {s(x j,a j),s(y j,b j)}) :
    let C := fun i => (Q i).append (reservoirReturn (P i) (hx i) (hy i))
    (∀ i, (C i).IsCycle) ∧
    Pairwise (fun i j => Disjoint (C i).edgeSet (C j).edgeSet) ∧
    (⋃ i, (C i).edgeSet) = (⋃ i, (Q i).edgeSet) ∪ (⋃ i, (P i).edgeSet) ∪
      (⋃ i, ({s(x i,a i),s(y i,b i)} : Set (Sym2 V))) := by
  dsimp only
  have hC := fun i => reservoir_path_closure_allow_nil (Q i) (P i) (hQ i) (hP i)
    (hsep i) (hab i) (hx i) (hy i)
  refine ⟨fun i => (hC i).1,?_,?_⟩
  · have hSS : Pairwise (fun i j => Disjoint
        ({s(x i,a i),s(y i,b i)} : Set (Sym2 V)) {s(x j,a j),s(y j,b j)}) := by
      simpa using spoke_sets_pairwise _ hspoke
    simpa only [fun i => (hC i).2.1] using
      pairwise_union_three (fun i => (Q i).edgeSet) (fun i => (P i).edgeSet)
        (fun i => ({s(x i,a i),s(y i,b i)} : Set (Sym2 V))) hQQ hPP hSS hQP hQS hPS
  · simp only [fun i => (hC i).2.1,Set.iUnion_union_distrib]

end
end Cycle12
