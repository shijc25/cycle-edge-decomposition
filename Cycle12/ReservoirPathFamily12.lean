import Cycle12.ThreeReservoirSampling12
import Cycle12.EndpointConnectors12
import Cycle12.ReservoirCycleClosure12

namespace Cycle12
open Cycle13 SimpleGraph Finset
open OAI.ErdosGallai
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

theorem sampled_routes_ambient [Nonempty V] (G H : SimpleGraph V) (hHG : H ≤ G)
    (U : Finset V) {z upper : ℝ} (hU : ReservoirSample H U z upper)
    (f : I × Bool → V) (hf : ∀ k, f k ∈ U)
    (hz : 8192 ≤ z) (hlog : 8192*Real.log (Fintype.card V:ℝ) ≤ z)
    (hsquare : 2112*(Fintype.card I:ℝ) ≤ z^2)
    (hload : ∀ v, ((univ.filter (fun k => f k = v)).card:ℝ) ≤ z/64) :
    ∃ P : ∀ i, G.Walk (f (i,false)) (f (i,true)),
      (∀ i, (P i).IsPath) ∧
      (∀ i, ∀ v ∈ (P i).support, v ∈ U) ∧
      Pairwise (fun i j => Disjoint (P i).edgeSet (P j).edgeSet) ∧
      ∀ i, (P i).edgeSet ⊆ H.edgeSet := by
  let fs : I × Bool → U := fun k => ⟨f k,hf k⟩
  have hloads : ∀ v : U, ((univ.filter (fun k => fs k = v)).card:ℝ) ≤ z/64 := by
    intro v
    have he : (univ.filter (fun k => fs k = v)) = (univ.filter (fun k => f k = v.val)) := by
      ext k
      simp [fs,Subtype.ext_iff]
    rw [he]
    exact hload v.val
  obtain ⟨q,hq,hdis⟩ := hU.route fs hz hlog hsquare hloads
  let e : H.induce (U:Set V) →g G := { toFun := Subtype.val, map_rel' := fun h => hHG h }
  let P : ∀ i, G.Walk (f (i,false)) (f (i,true)) := fun i => (q i).map e
  have hsupport : ∀ i, (P i).support = (q i).support.map Subtype.val := by
    intro i
    exact Walk.support_map _ _
  have hedge : ∀ i, (P i).edgeSet = Sym2.map (Subtype.val : U → V) '' (q i).edgeSet := by
    intro i
    exact Walk.edgeSet_map _ _
  refine ⟨P,?_,?_,?_,?_⟩
  · intro i
    exact (hq i).map Subtype.val_injective
  · intro i v hv
    rw [hsupport] at hv
    obtain ⟨w,_,rfl⟩ := List.mem_map.mp hv
    exact w.property
  · intro i j hij
    rw [hedge,hedge]
    exact (Set.disjoint_image_iff (Sym2.map.injective Subtype.val_injective)).mpr (hdis hij)
  · intro i a ha
    rw [hedge] at ha
    obtain ⟨b,hb,rfl⟩ := ha
    have hbH := (q i).edges_subset_edgeSet hb
    induction b using Sym2.inductionOn with
    | _ x y => exact hbH

/-- Fixed representative edges plus actual bank routes close an indexed
family into simple cycles. The statement records the exact original
edges retained and that every added edge belongs to the routing bank. -/
theorem close_external_paths_with_representatives [Nonempty V]
    (G H : SimpleGraph V) (hHG : H ≤ G) (U : Finset V) {z upper : ℝ}
    (hU : ReservoirSample H U z upper) (source f : I × Bool → V)
    (Q : ∀ i, G.Walk (source (i,false)) (source (i,true)))
    (hQ : ∀ i, (Q i).IsPath)
    (hQQ : Pairwise (fun i j => Disjoint (Q i).edgeSet (Q j).edgeSet))
    (hout : ∀ i, ∀ v ∈ (Q i).support, v ∉ U)
    (hf : ∀ k, f k ∈ U ∧ H.Adj (source k) (f k))
    (hinj : Function.Injective (fun k => s(source k,f k)))
    (hmates : ∀ i, source (i,false) = source (i,true) → f (i,false) ≠ f (i,true))
    (hz : 8192 ≤ z) (hlog : 8192*Real.log (Fintype.card V:ℝ) ≤ z)
    (hsquare : 2112*(Fintype.card I:ℝ) ≤ z^2)
    (hload : ∀ v, ((univ.filter (fun k => f k = v)).card:ℝ) ≤ z/64) :
    ∃ C : ∀ i, G.Walk (source (i,false)) (source (i,false)),
      (∀ i, (C i).IsCycle) ∧
      Pairwise (fun i j => Disjoint (C i).edgeSet (C j).edgeSet) ∧
      (∀ i, (Q i).edgeSet ⊆ (C i).edgeSet) ∧
      ∀ i, (C i).edgeSet ⊆ (Q i).edgeSet ∪ H.edgeSet := by
  obtain ⟨P,hP,hPU,hPP,hPH⟩ := sampled_routes_ambient G H hHG U hU f
    (fun k => (hf k).1) hz hlog hsquare hload
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
  have hSH : ∀ i, ({s(x i,a i),s(y i,b i)} : Set (Sym2 V)) ⊆ H.edgeSet := by
    intro i e he
    rcases he with he | he
    · exact he ▸ (hf (i,false)).2
    · exact he ▸ (hf (i,true)).2
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
      (Set.subset_union_of_subset_right (hPH i) _)) (Set.subset_union_of_subset_right (hSH i) _)

/-- A whole family with endpoint load at most two is closed using a sampled
bank. Connector existence and all pair routes are proved internally. -/
theorem close_external_path_family [Nonempty V]
    (G H : SimpleGraph V) (hHG : H ≤ G) (U : Finset V) {z upper : ℝ}
    (hU : ReservoirSample H U z upper) (source : I × Bool → V)
    (Q : ∀ i, G.Walk (source (i,false)) (source (i,true)))
    (hQ : ∀ i, (Q i).IsPath)
    (hQQ : Pairwise (fun i j => Disjoint (Q i).edgeSet (Q j).edgeSet))
    (hout : ∀ i, ∀ v ∈ (Q i).support, v ∉ U)
    (hsource : ∀ v, (univ.filter (fun k => source k = v)).card ≤ 2)
    (hz : 8192 ≤ z) (hzr : z ≤ (Fintype.card V:ℝ))
    (hlog : 8192*Real.log (Fintype.card V:ℝ) ≤ z)
    (hsquare : 2112*(Fintype.card V:ℝ) ≤ z^2) (hcard : Fintype.card I ≤ Fintype.card V) :
    ∃ C : ∀ i, G.Walk (source (i,false)) (source (i,false)),
      (∀ i, (C i).IsCycle) ∧
      Pairwise (fun i j => Disjoint (C i).edgeSet (C j).edgeSet) ∧
      (∀ i, (Q i).edgeSet ⊆ (C i).edgeSet) ∧
      ∀ i, (C i).edgeSet ⊆ (Q i).edgeSet ∪ H.edgeSet := by
  have ho : ∀ k, source k ∉ U := by
    rintro ⟨i,b⟩
    cases b
    · exact hout i _ (Q i).start_mem_support
    · exact hout i _ (Q i).end_mem_support
  obtain ⟨f,hf,hmates,hinj,hcap,hstrict⟩ := choose_endpoint_connectors H U source
    hz hzr hsquare (by exact_mod_cast hcard) hsource ho (fun k => hU.neighbors (source k))
  have hI : 2112*(Fintype.card I:ℝ) ≤ z^2 :=
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) (by norm_num : (0:ℝ) ≤ 2112)).trans hsquare
  exact close_external_paths_with_representatives G H hHG U hU source f Q hQ hQQ hout
    hf hinj (fun i _ => hmates i) hz hlog hI
    (fun v => (show ((univ.filter (fun k => f k = v)).card:ℝ) ≤ (⌈8*(Fintype.card V:ℝ)/z⌉₊:ℝ)
      by exact_mod_cast hcap v).trans hstrict.le)

end
end Cycle12
