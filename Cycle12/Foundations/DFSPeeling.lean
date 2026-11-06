import Cycle12.Foundations.DFSAncestry
import Cycle12.Foundations.FiniteGrouping

namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

def externalWithin (G : SimpleGraph V) (S U : Finset V) : Finset V :=
  S.filter (fun y => y ∉ U ∧ ∃ x ∈ U, G.Adj x y)

@[simp] theorem mem_externalWithin (G : SimpleGraph V) (S U : Finset V) (y : V) :
    y ∈ externalWithin G S U ↔ y ∈ S ∧ y ∉ U ∧ ∃ x ∈ U, G.Adj x y := by
  simp [externalWithin]

namespace NormalDFSForest

theorem child_union_external_card (F : NormalDFSForest G) {T : ℕ} (hT : 1 ≤ T)
    (hG : NoCycleAtLeast G T) {S C : Finset V} {v : V}
    (hC : ∀ c ∈ C, F.Child v c) :
    (externalWithin G S (C.biUnion (F.descendants S))).card ≤ T := by
  have hs : externalWithin G S (C.biUnion (F.descendants S)) ⊆ (F.path v |>.take T).toFinset := by
    intro y hy
    obtain ⟨hyS,hy,x,hx,hxy⟩ := (mem_externalWithin _ _ _ _).mp hy
    exact List.mem_toFinset.mpr (F.child_union_external_near hT hG hC hx hyS hy hxy)
  exact (Finset.card_le_card hs).trans ((List.toFinset_card_le _).trans (by simp))

theorem root_subtree_no_external (F : NormalDFSForest G) {S : Finset V} {r : V}
    (hr : F.path r=[r]) : externalWithin G S (F.descendants S r)=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro y hy
  obtain ⟨hyS,hy,x,hx,hxy⟩ := (mem_externalWithin _ _ _ _).mp hy
  have hrx := (F.mem_descendants _ _ _).mp hx |>.2
  have hnot : r ∉ F.path y := fun h => hy ((F.mem_descendants _ _ _).mpr ⟨hyS,h⟩)
  rcases F.edge_ancestor hxy with h | h
  · exact hnot (F.ancestor_trans hrx h)
  · rcases List.suffix_or_suffix_of_suffix (F.coherent x r hrx) (F.coherent x y h) with h | h
    · exact hnot (h.subset (F.self_mem r))
    · have hyr := h.subset (F.self_mem y)
      rw [hr,List.mem_singleton] at hyr
      subst y
      exact hnot (F.self_mem r)

/-- Peel one nonempty core. Either it is a whole remaining component of
at most k vertices, or its size lies in [k,2k) with at most T boundary
vertices. The remaining vertex set is still closed under ancestors. -/
theorem exists_peel (F : NormalDFSForest G) {S : Finset V}
    (hS : F.AncestorClosed S) (hSne : S.Nonempty) {k T : ℕ}
    (hk : 0 < k) (hT : 1 ≤ T) (hG : NoCycleAtLeast G T) :
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
    exact F.child_union_external_card hT hG (fun c hc => (Finset.mem_filter.mp (hC hc)).2)
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
end
end Cycle13
