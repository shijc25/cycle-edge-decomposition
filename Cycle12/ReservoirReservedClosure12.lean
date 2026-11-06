import Cycle12.ReservoirPathFamily12

namespace Cycle12
open Cycle13 SimpleGraph Finset
open OAI.ErdosGallai
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

/-- Reserved connectors and the internal reservoir graph account for every
added edge. The entire sampling graph need not survive the first pass. -/
theorem close_reserved_external_paths [Nonempty V]
    (G H R : SimpleGraph V) (hHG : H ≤ G) (U : Finset V) {z upper : ℝ}
    (hU : ReservoirSample H U z upper) (source f : I × Bool → V)
    (Q : ∀ i, G.Walk (source (i,false)) (source (i,true)))
    (hQ : ∀ i, (Q i).IsPath)
    (hQQ : Pairwise (fun i j => Disjoint (Q i).edgeSet (Q j).edgeSet))
    (hout : ∀ i, ∀ v ∈ (Q i).support, v ∉ U)
    (hf : ∀ k, f k ∈ U ∧ H.Adj (source k) (f k))
    (hreserve : ∀ k, R.Adj (source k) (f k))
    (hinside : ∀ x ∈ U, ∀ y ∈ U, H.Adj x y → R.Adj x y)
    (hinj : Function.Injective (fun k => s(source k,f k)))
    (hmates : ∀ i, source (i,false) = source (i,true) → f (i,false) ≠ f (i,true))
    (hz : 8192 ≤ z) (hlog : 8192*Real.log (Fintype.card V:ℝ) ≤ z)
    (hsquare : 2112*(Fintype.card I:ℝ) ≤ z^2)
    (hload : ∀ v, ((univ.filter (fun k => f k = v)).card:ℝ) ≤ z/64) :
    ∃ C : ∀ i, G.Walk (source (i,false)) (source (i,false)),
      (∀ i, (C i).IsCycle) ∧
      Pairwise (fun i j => Disjoint (C i).edgeSet (C j).edgeSet) ∧
      (∀ i, (Q i).edgeSet ⊆ (C i).edgeSet) ∧
      ∀ i, (C i).edgeSet ⊆ (Q i).edgeSet ∪ R.edgeSet := by
  obtain ⟨P,hP,hPU,hPP,hPH⟩ := sampled_routes_ambient G H hHG U hU f
    (fun k => (hf k).1) hz hlog hsquare hload
  have hPR : ∀ i, (P i).edgeSet ⊆ R.edgeSet := by
    intro i e he
    induction e using Sym2.inductionOn with
    | _ x y =>
      exact hinside x (hPU i x ((P i).fst_mem_support_of_mem_edges he))
        y (hPU i y ((P i).snd_mem_support_of_mem_edges he)) (hPH i he)
  have hsep : ∀ i, (Q i).support.Disjoint (P i).support := by
    intro i v hv hw
    exact hout i v hv (hPU i v hw)
  let x := fun i => source (i,false)
  let y := fun i => source (i,true)
  let a := fun i => f (i,false)
  let b := fun i => f (i,true)
  let C := fun i => (Q i).append (reservoirReturn (P i) (hHG (hf (i,false)).2) (hHG (hf (i,true)).2))
  have hC := fun i => reservoir_path_closure_allow_nil (Q i) (P i) (hQ i) (hP i)
    (hsep i) (hmates i) (hHG (hf (i,false)).2) (hHG (hf (i,true)).2)
  have hSS : Pairwise (fun i j => Disjoint
      ({s(x i,a i),s(y i,b i)} : Set (Sym2 V)) {s(x j,a j),s(y j,b j)}) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro e hi hj
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hi hj
    rcases hi with hi | hi <;> rcases hj with hj | hj
    · exact hij (congrArg Prod.fst (hinj (show s(source (i,false),f (i,false)) = s(source (j,false),f (j,false)) from hi.symm.trans hj)))
    · exact hij (congrArg Prod.fst (hinj (show s(source (i,false),f (i,false)) = s(source (j,true),f (j,true)) from hi.symm.trans hj)))
    · exact hij (congrArg Prod.fst (hinj (show s(source (i,true),f (i,true)) = s(source (j,false),f (j,false)) from hi.symm.trans hj)))
    · exact hij (congrArg Prod.fst (hinj (show s(source (i,true),f (i,true)) = s(source (j,true),f (j,true)) from hi.symm.trans hj)))
  have hSH : ∀ i, ({s(x i,a i),s(y i,b i)} : Set (Sym2 V)) ⊆ R.edgeSet := by
    intro i e he
    rcases he with he | he
    · exact he ▸ hreserve (i,false)
    · exact he ▸ hreserve (i,true)
  have hPS : ∀ i j, Disjoint (P i).edgeSet ({s(x j,a j),s(y j,b j)} : Set (Sym2 V)) := by
    intro i j
    apply Set.disjoint_left.mpr
    intro e he hs
    rcases hs with heq | heq
    · rw [heq] at he
      exact hout j _ (Q j).start_mem_support (hPU i _ ((P i).fst_mem_support_of_mem_edges he))
    · rw [heq] at he
      exact hout j _ (Q j).end_mem_support (hPU i _ ((P i).fst_mem_support_of_mem_edges he))
  have hQP : ∀ i j, Disjoint (Q i).edgeSet (P j).edgeSet := by
    intro i j
    apply Set.disjoint_left.mpr
    intro e heQ heP
    induction e using Sym2.inductionOn with
    | _ x y =>
      exact hout i x ((Q i).fst_mem_support_of_mem_edges heQ)
        (hPU j x ((P j).fst_mem_support_of_mem_edges heP))
  have hQS : ∀ i j, Disjoint (Q i).edgeSet ({s(x j,a j),s(y j,b j)} : Set (Sym2 V)) := by
    intro i j
    apply Set.disjoint_left.mpr
    intro e he hs
    rcases hs with heq | heq
    · rw [heq] at he
      exact hout i _ ((Q i).snd_mem_support_of_mem_edges he) (hf (j,false)).1
    · rw [heq] at he
      exact hout i _ ((Q i).snd_mem_support_of_mem_edges he) (hf (j,true)).1
  refine ⟨C,fun i => (hC i).1,?_,?_,?_⟩
  · have hh := pairwise_union_three (fun i => (Q i).edgeSet) (fun i => (P i).edgeSet)
      (fun i => ({s(x i,a i),s(y i,b i)} : Set (Sym2 V))) hQQ hPP hSS
      hQP hQS hPS
    simpa only [C,fun i => (hC i).2.1] using hh
  · intro i
    rw [(hC i).2.1]
    exact Set.subset_union_of_subset_left (Set.subset_union_left) _
  · intro i
    rw [(hC i).2.1]
    exact Set.union_subset (Set.union_subset Set.subset_union_left
      (Set.subset_union_of_subset_right (hPR i) _)) (Set.subset_union_of_subset_right (hSH i) _)


end
end Cycle12
