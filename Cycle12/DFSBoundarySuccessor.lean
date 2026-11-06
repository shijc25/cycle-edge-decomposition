import Cycle12.Foundations.DFSPartition

/-! A one-unit sharpening of the DFS boundary threshold.  A graph with
no cycle of length at least T+1 has the same T-vertex boundary bound. -/
namespace Cycle13
open SimpleGraph Finset ReservoirPorts
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem path_length_le_of_adj_noLongCycle_successor {G : SimpleGraph V} {T : ℕ}
    (hT : 1 ≤ T) (hG : NoCycleAtLeast G (T+1)) {u v : V}
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

namespace NormalDFSForest

theorem edge_depth_bound_successor (F : NormalDFSForest G) {T : ℕ} (hT : 1 ≤ T)
    (hG : NoCycleAtLeast G (T+1)) {u v : V} (huv : G.Adj u v) (hv : v ∈ F.path u) :
    (F.path u).length ≤ (F.path v).length+T := by
  obtain ⟨p,hp,hlen⟩ := F.exists_ancestor_path hv
  have hh := path_length_le_of_adj_noLongCycle_successor hT hG p hp huv
  omega
theorem child_union_external_near_successor (F : NormalDFSForest G) {T : ℕ} (hT : 1 ≤ T)
    (hG : NoCycleAtLeast G (T+1)) {S C : Finset V} {v : V}
    (hC : ∀ c ∈ C, F.Child v c) {x y : V}
    (hx : x ∈ C.biUnion (F.descendants S)) (hyS : y ∈ S)
    (hy : y ∉ C.biUnion (F.descendants S)) (hxy : G.Adj x y) :
    y ∈ (F.path v).take T := by
  obtain ⟨hyv,hlt⟩ := F.child_union_external_ancestor hC hx hyS hy hxy
  have hyx : y ∈ F.path x := by
    obtain ⟨c,hc,hcx⟩ := Finset.mem_biUnion.mp hx
    exact F.ancestor_trans (F.ancestor_trans hyv (F.child_ancestor (hC c hc)))
      ((F.mem_descendants S c x).mp hcx).2
  have hb := F.edge_depth_bound_successor hT hG hxy hyx
  have hi := F.idxOf_add_path_length hyv
  exact (List.mem_take_iff_idxOf_lt hyv).mpr (by omega)
theorem child_union_external_card_successor (F : NormalDFSForest G) {T : ℕ} (hT : 1 ≤ T)
    (hG : NoCycleAtLeast G (T+1)) {S C : Finset V} {v : V}
    (hC : ∀ c ∈ C, F.Child v c) :
    (externalWithin G S (C.biUnion (F.descendants S))).card ≤ T := by
  have hs : externalWithin G S (C.biUnion (F.descendants S)) ⊆ (F.path v |>.take T).toFinset := by
    intro y hy
    obtain ⟨hyS,hy,x,hx,hxy⟩ := (mem_externalWithin _ _ _ _).mp hy
    exact List.mem_toFinset.mpr (F.child_union_external_near_successor hT hG hC hx hyS hy hxy)
  exact (Finset.card_le_card hs).trans ((List.toFinset_card_le _).trans (by simp))
theorem exists_peel_successor (F : NormalDFSForest G) {S : Finset V}
    (hS : F.AncestorClosed S) (hSne : S.Nonempty) {k T : ℕ}
    (hk : 0 < k) (hT : 1 ≤ T) (hG : NoCycleAtLeast G (T+1)) :
    ∃ U ⊆ S, U.Nonempty ∧ F.AncestorClosed (S \ U) ∧
      ((U.card ≤ k ∧ externalWithin G S U=∅) ∨
       (k ≤ U.card ∧ U.card < 2*k ∧ (externalWithin G S U).card ≤ T)) := by
  let heavy := S.filter (fun v => k < (F.descendants S v).card)
  by_cases hh : heavy.Nonempty
  · obtain ⟨v,hv,hmax⟩ := Finset.exists_max_image heavy (fun v => (F.path v).length) hh
    have hvS := (Finset.mem_filter.mp hv).1
    have hheavy := (Finset.mem_filter.mp hv).2
    have hsmall : ∀ c ∈ F.childSet S v, (F.descendants S c).card ≤ k := by
      intro c hc
      obtain ⟨hcS,hchild⟩ := Finset.mem_filter.mp hc
      by_contra hnot
      have hcH : c ∈ heavy := Finset.mem_filter.mpr ⟨hcS,lt_of_not_ge hnot⟩
      have hle := hmax c hcH
      rw [F.child_length hchild] at hle
      omega
    have hdis : ∀ c ∈ F.childSet S v, ∀ d ∈ F.childSet S v,
        c ≠ d → Disjoint (F.descendants S c) (F.descendants S d) := by
      intro c hc d hd hcd
      exact F.child_subtrees_disjoint S (Finset.mem_filter.mp hc).2 (Finset.mem_filter.mp hd).2 hcd
    have hcard : (F.descendants S v).card=
        (∑ c ∈ F.childSet S v, (F.descendants S c).card)+1 := by
      have hvc : v ∈ F.descendants S v := (F.mem_descendants _ _ _).mpr ⟨hvS,F.self_mem v⟩
      have he := Finset.card_erase_add_one hvc
      rw [F.descendants_erase_self hS,Finset.card_biUnion hdis] at he
      exact he.symm
    have hsum : k ≤ ∑ c ∈ F.childSet S v, (F.descendants S c).card := by omega
    obtain ⟨C,hC,hlo,hhi⟩ := exists_group_sum_between (F.childSet S v)
      (fun c => (F.descendants S c).card) hk hsum hsmall
    let U := C.biUnion (F.descendants S)
    have hUc : U.card=∑ c ∈ C, (F.descendants S c).card :=
      Finset.card_biUnion (fun c hc d hd hcd => hdis c (hC hc) d (hC hd) hcd)
    have hUS : U ⊆ S := by
      intro x hx
      obtain ⟨c,hc,hcx⟩ := Finset.mem_biUnion.mp hx
      exact (F.mem_descendants _ _ _).mp hcx |>.1
    refine ⟨U,hUS,Finset.card_pos.mp (by omega),F.child_union_ancestorClosed_compl hS,
      Or.inr ⟨by omega,by omega,?_⟩⟩
    exact F.child_union_external_card_successor hT hG (fun c hc => (Finset.mem_filter.mp (hC hc)).2)
  · obtain ⟨x,hx⟩ := hSne
    let r := (F.path x).getLast (F.nonempty x)
    have hrx : r ∈ F.path x := List.getLast_mem _
    have hr : F.path r=[r] := F.path_eq_of_head_suffix (L:=[]) ⟨(F.path x).dropLast,
      List.dropLast_concat_getLast (F.nonempty x)⟩
    have hrS := hS x hx r hrx
    let U := F.descendants S r
    have hUS : U ⊆ S := Finset.filter_subset _ _
    have hUn : U.Nonempty := ⟨r,(F.mem_descendants _ _ _).mpr ⟨hrS,F.self_mem r⟩⟩
    have hsmall : U.card ≤ k := by
      by_contra hnot
      exact hh ⟨r,Finset.mem_filter.mpr ⟨hrS,lt_of_not_ge hnot⟩⟩
    have hclosed := F.child_union_ancestorClosed_compl (C:={r}) hS
    simp only [Finset.singleton_biUnion] at hclosed
    exact ⟨U,hUS,hUn,hclosed,Or.inl ⟨hsmall,F.root_subtree_no_external hr⟩⟩

end NormalDFSForest

theorem exists_dfsPartition_on_subset_successor {G : SimpleGraph V} (F : NormalDFSForest G)
    {k T : ℕ} (hk : 0 < k) (hT : 1 ≤ T) (hG : NoCycleAtLeast G (T+1))
    (S : Finset V) (hS : F.AncestorClosed S) :
    ∃ P : DFSPartition G S k T, ∀ i, (P.block i).vertices ⊆ S := by
  induction hn : S.card using Nat.strong_induction_on generalizing S with
  | h n ih =>
    by_cases hSne : S.Nonempty
    · obtain ⟨U,hUS,hUn,hclosed,hsize⟩ := F.exists_peel_successor hS hSne hk hT hG
      have hsmall : (S\U).card < n := by
        rw [Finset.card_sdiff_of_subset hUS]
        have hpos := Finset.card_pos.mpr hUn
        have hle := Finset.card_le_card hUS
        omega
      obtain ⟨P,hP⟩ := ih _ hsmall (S\U) hclosed rfl
      let B : DFSBlock G k T := {
        core := U
        boundary := externalWithin G S U
        graph := peelGraph G S U
        core_nonempty := hUn
        separate := by
          apply Finset.disjoint_left.mpr
          intro x hx he
          exact ((mem_externalWithin _ _ _ _).mp he).2.1 hx
        graph_le := fun _ _ h => h.1
        supported := by
          intro x y hxy
          obtain ⟨hxy,hxS,hyS,hU⟩ := hxy
          constructor
          · by_cases hxU : x∈U
            · exact Finset.mem_union_left _ hxU
            · have hyU : y∈U := hU.resolve_left hxU
              exact Finset.mem_union_right _ ((mem_externalWithin _ _ _ _).mpr
                ⟨hxS,hxU,y,hyU,hxy.symm⟩)
          · by_cases hyU : y∈U
            · exact Finset.mem_union_left _ hyU
            · have hxU : x∈U := hU.resolve_right hyU
              exact Finset.mem_union_right _ ((mem_externalWithin _ _ _ _).mpr
                ⟨hyS,hyU,x,hxU,hxy⟩)
        size := hsize }
      have hcore : ∀ i, Disjoint B.core (P.block i).core := by
        intro i
        apply Finset.disjoint_left.mpr
        intro v hv hi
        exact (Finset.mem_sdiff.mp (P.core_subset i hi)).2 hv
      have hedge : ∀ i, Disjoint B.graph.edgeSet (P.block i).graph.edgeSet :=
        fun i => (peelGraph_disjoint_remainder G S U).mono_right (P.edge_subset i)
      refine ⟨{
        count := P.count+1
        block := Fin.cases B P.block
        core_disjoint := ?_
        core_union := ?_
        edge_disjoint := ?_
        edge_union := ?_ },?_⟩
      · intro i j hij
        induction i using Fin.cases with
        | zero =>
          induction j using Fin.cases with
          | zero => exact (hij rfl).elim
          | succ j => exact hcore j
        | succ i =>
          induction j using Fin.cases with
          | zero => exact (hcore i).symm
          | succ j => exact P.core_disjoint (fun h => hij (congrArg Fin.succ h))
      · rw [Set.iUnion_fin_add_one_eq_iUnion_succ]
        change (U:Set V) ∪ (⋃ i, ((P.block i).core:Set V))=(S:Set V)
        rw [P.core_union]
        ext v
        simp only [Set.mem_union,Finset.mem_coe,Finset.mem_sdiff]
        constructor
        · rintro (h | h)
          · exact hUS h
          · exact h.1
        · intro h
          by_cases hv : v∈U
          · exact Or.inl hv
          · exact Or.inr ⟨h,hv⟩
      · intro i j hij
        induction i using Fin.cases with
        | zero =>
          induction j using Fin.cases with
          | zero => exact (hij rfl).elim
          | succ j => exact hedge j
        | succ i =>
          induction j using Fin.cases with
          | zero => exact (hedge i).symm
          | succ j => exact P.edge_disjoint (fun h => hij (congrArg Fin.succ h))
      · rw [Set.iUnion_fin_add_one_eq_iUnion_succ]
        change (peelGraph G S U).edgeSet ∪ (⋃ i, (P.block i).graph.edgeSet)=_
        rw [P.edge_union]
        exact peelGraph_edge_partition G S U
      · intro i
        induction i using Fin.cases with
        | zero =>
          change U ∪ externalWithin G S U ⊆ S
          exact Finset.union_subset hUS (Finset.filter_subset _ _)
        | succ i => exact (hP i).trans Finset.sdiff_subset
    · have hSe : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hSne
      subst S
      refine ⟨⟨0,Fin.elim0,fun i => Fin.elim0 i,?_,fun i => Fin.elim0 i,?_⟩,fun i => Fin.elim0 i⟩
      · simp
      · simp only [Set.iUnion_of_empty]
        have he : internalGraph G ∅=⊥ := by ext x y; simp [internalGraph]
        rw [he,SimpleGraph.edgeSet_bot]

theorem exists_dfsPartition_successor (G : SimpleGraph V) {k T : ℕ}
    (hk : 0 < k) (hT : 1 ≤ T) (hG : NoCycleAtLeast G (T+1)) :
    Nonempty (DFSPartition G univ k T) := by
  obtain ⟨F⟩ := exists_normalDFSForest G
  obtain ⟨P,_⟩ := exists_dfsPartition_on_subset_successor F hk hT hG univ
    (by intro x hx y hy; exact Finset.mem_univ y)
  exact ⟨P⟩

end
end Cycle13
