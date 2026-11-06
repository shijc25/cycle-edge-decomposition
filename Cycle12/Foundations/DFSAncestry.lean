import Cycle12.Foundations.DFSForest
import Cycle12.Foundations.LongCycleRemoval

namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

namespace NormalDFSForest

theorem head_eq (F : NormalDFSForest G) (v : V) :
    (F.path v).head (F.nonempty v)=v :=
  (List.head_eq_iff_head?_eq_some _).mpr (F.head v)

theorem path_eq_of_head_suffix (F : NormalDFSForest G) {u v : V} {L : List V}
    (hs : v::L <:+ F.path u) : F.path v=v::L := by
  have hv : v ∈ F.path u := hs.subset (by simp)
  have hp := F.coherent u v hv
  rcases List.suffix_or_suffix_of_suffix hp hs with h | h
  · exact List.Nodup.eq_of_head_mem_of_suffix h (hne:=by simp) (by simpa using F.self_mem v)
      (F.nodup u |>.sublist hs.sublist)
  · have he : v::L=F.path v := List.Nodup.eq_of_head_mem_of_suffix h
      (by rw [F.head_eq]; simp) (F.nodup v)
    exact he.symm

theorem idxOf_add_path_length (F : NormalDFSForest G) {u v : V}
    (hv : v ∈ F.path u) : (F.path u).idxOf v+(F.path v).length=(F.path u).length := by
  obtain ⟨A,hA⟩ := F.coherent u v hv
  have hnd : (A++F.path v).Nodup := hA.symm ▸ F.nodup u
  have hnot : v ∉ A := fun h => (List.nodup_append.mp hnd).2.2 v h v (F.self_mem v) rfl
  obtain ⟨B,hB⟩ := List.head?_eq_some_iff.mp (F.head v)
  rw [← hA,List.idxOf_append_of_notMem hnot,hB]
  simp

theorem ancestor_length_lt (F : NormalDFSForest G) {u v : V}
    (h : u ∈ F.path v) (hne : u ≠ v) : (F.path u).length < (F.path v).length := by
  have hs := F.coherent v u h
  apply lt_of_le_of_ne hs.length_le
  intro he
  have hh := congrArg List.head? (hs.eq_of_length he)
  simp only [F.head,Option.some.injEq] at hh
  exact hne hh

/-- The discovery chain gives an actual simple path to every ancestor. -/
theorem exists_ancestor_path (F : NormalDFSForest G) {u v : V}
    (hv : v ∈ F.path u) :
    ∃ p : G.Walk u v, p.IsPath ∧ p.length+(F.path v).length=(F.path u).length := by
  let q := (Walk.ofSupport (F.path u) (F.nonempty u) (F.chain u)).copy (F.head_eq u) rfl
  have hsupport : q.support=F.path u := by simp only [q,Walk.support_copy,Walk.support_ofSupport]
  have hq : q.IsPath := by rw [Walk.isPath_def,hsupport]; exact F.nodup u
  have hmem : v ∈ q.support := hsupport.symm ▸ hv
  refine ⟨q.takeUntil v hmem,hq.takeUntil hmem,?_⟩
  rw [Walk.length_takeUntil,hsupport]
  exact F.idxOf_add_path_length hv

theorem edge_depth_bound (F : NormalDFSForest G) {T : ℕ} (hT : 1 ≤ T)
    (hG : NoCycleAtLeast G T) {u v : V} (huv : G.Adj u v) (hv : v ∈ F.path u) :
    (F.path u).length ≤ (F.path v).length+T := by
  obtain ⟨p,hp,hlen⟩ := F.exists_ancestor_path hv
  have hh := path_length_le_of_adj_noLongCycle hT hG p hp huv
  omega

def AncestorClosed (F : NormalDFSForest G) (S : Finset V) : Prop :=
  ∀ x ∈ S, ∀ y ∈ F.path x, y ∈ S

def descendants (F : NormalDFSForest G) (S : Finset V) (v : V) : Finset V :=
  S.filter (fun x => v ∈ F.path x)

@[simp] theorem mem_descendants (F : NormalDFSForest G) (S : Finset V) (v x : V) :
    x ∈ F.descendants S v ↔ x ∈ S ∧ v ∈ F.path x := by simp [descendants]

def Child (F : NormalDFSForest G) (v c : V) : Prop := F.path c=c::F.path v

theorem child_length (F : NormalDFSForest G) {v c : V} (h : F.Child v c) :
    (F.path c).length=(F.path v).length+1 := by rw [h]; rfl

theorem child_ne (F : NormalDFSForest G) {v c : V} (h : F.Child v c) : c ≠ v := by
  intro he
  have hh := F.child_length h
  subst c
  omega

theorem child_ancestor (F : NormalDFSForest G) {v c : V} (h : F.Child v c) :
    v ∈ F.path c := by rw [h]; exact List.mem_cons_of_mem _ (F.self_mem v)

theorem exists_child_ancestor (F : NormalDFSForest G) {v x : V}
    (hv : v ∈ F.path x) (hne : x ≠ v) :
    ∃ c, F.Child v c ∧ c ∈ F.path x := by
  obtain ⟨A,B,hAB⟩ := List.mem_iff_append.mp hv
  have hvB := F.path_eq_of_head_suffix (u:=x) (L:=B) ⟨A,hAB.symm⟩
  have hA : A ≠ [] := by
    intro h
    have hh := F.head x
    rw [hAB,h] at hh
    simp only [List.nil_append,List.head?_cons,Option.some.injEq] at hh
    exact hne hh.symm
  let c := A.getLast hA
  have hc : c::F.path v <:+ F.path x := by
    refine ⟨A.dropLast,?_⟩
    rw [hvB]
    change A.dropLast++([c]++v::B)=F.path x
    rw [← List.append_assoc,List.dropLast_concat_getLast hA]
    exact hAB.symm
  refine ⟨c,F.path_eq_of_head_suffix hc,hc.subset (by simp)⟩

theorem child_subtrees_disjoint (F : NormalDFSForest G) (S : Finset V) {v c d : V}
    (hc : F.Child v c) (hd : F.Child v d) (hne : c ≠ d) :
    Disjoint (F.descendants S c) (F.descendants S d) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hcx := (F.mem_descendants S c x).mp hx |>.2
  have hdx := (F.mem_descendants S d x).mp hy |>.2
  have he : (F.path c).length=(F.path d).length := by rw [F.child_length hc,F.child_length hd]
  have hp : F.path c=F.path d := by
    rcases List.suffix_or_suffix_of_suffix (F.coherent x c hcx) (F.coherent x d hdx) with h | h
    · exact h.eq_of_length he
    · exact (h.eq_of_length he.symm).symm
  have hh := congrArg List.head? hp
  simp only [F.head,Option.some.injEq] at hh
  exact hne hh

def childSet (F : NormalDFSForest G) (S : Finset V) (v : V) : Finset V :=
  S.filter (F.Child v)

theorem descendants_erase_self (F : NormalDFSForest G) {S : Finset V}
    (hS : F.AncestorClosed S) (v : V) :
    (F.descendants S v).erase v=(F.childSet S v).biUnion (F.descendants S) := by
  ext x
  simp only [Finset.mem_erase,mem_descendants,Finset.mem_biUnion,childSet,Finset.mem_filter]
  constructor
  · rintro ⟨hxv,hxS,hvx⟩
    obtain ⟨c,hc,hcx⟩ := F.exists_child_ancestor hvx hxv
    exact ⟨c,⟨hS x hxS c hcx,hc⟩,hxS,hcx⟩
  · rintro ⟨c,⟨hcS,hc⟩,hxS,hcx⟩
    refine ⟨?_,hxS,F.ancestor_trans (F.child_ancestor hc) hcx⟩
    intro hxv
    subst x
    exact F.child_ne hc (F.ancestor_antisymm hcx (F.child_ancestor hc))

theorem child_union_ancestorClosed_compl (F : NormalDFSForest G) {S C : Finset V}
    (hS : F.AncestorClosed S) :
    F.AncestorClosed (S \ C.biUnion (F.descendants S)) := by
  intro x hx y hy
  obtain ⟨hxS,hxC⟩ := Finset.mem_sdiff.mp hx
  refine Finset.mem_sdiff.mpr ⟨hS x hxS y hy,?_⟩
  intro hyC
  obtain ⟨c,hc,hcy⟩ := Finset.mem_biUnion.mp hyC
  apply hxC
  exact Finset.mem_biUnion.mpr ⟨c,hc,(F.mem_descendants S c x).mpr
    ⟨hxS,F.ancestor_trans ((F.mem_descendants S c y).mp hcy).2 hy⟩⟩

/-- All remaining external neighbors of a union of child subtrees lie on
the parent path. This is the graph-theoretic separator, before its size bound. -/
theorem child_union_external_ancestor (F : NormalDFSForest G) {S C : Finset V} {v : V}
    (hC : ∀ c ∈ C, F.Child v c) {x y : V}
    (hx : x ∈ C.biUnion (F.descendants S)) (hyS : y ∈ S)
    (hy : y ∉ C.biUnion (F.descendants S)) (hxy : G.Adj x y) :
    y ∈ F.path v ∧ (F.path v).length < (F.path x).length := by
  obtain ⟨c,hc,hcx⟩ := Finset.mem_biUnion.mp hx
  have hca := (F.mem_descendants S c x).mp hcx |>.2
  have add_y : c ∈ F.path y → False := fun h =>
    hy (Finset.mem_biUnion.mpr ⟨c,hc,(F.mem_descendants S c y).mpr ⟨hyS,h⟩⟩)
  have hyx : y ∈ F.path x := by
    rcases F.edge_ancestor hxy with h | h
    · exact False.elim (add_y (F.ancestor_trans hca h))
    · exact h
  have hyc : y ∈ F.path c := by
    rcases List.suffix_or_suffix_of_suffix (F.coherent x c hca) (F.coherent x y hyx) with h | h
    · exact False.elim (add_y (h.subset (F.self_mem c)))
    · exact h.subset (F.self_mem y)
  have hyv : y ∈ F.path v := by
    rw [hC c hc] at hyc
    rcases List.mem_cons.mp hyc with he | he
    · subst y; exact False.elim (add_y (F.self_mem c))
    · exact he
  refine ⟨hyv,?_⟩
  have hl := (F.coherent x c hca).length_le
  rw [F.child_length (hC c hc)] at hl
  omega

theorem child_union_external_near (F : NormalDFSForest G) {T : ℕ} (hT : 1 ≤ T)
    (hG : NoCycleAtLeast G T) {S C : Finset V} {v : V}
    (hC : ∀ c ∈ C, F.Child v c) {x y : V}
    (hx : x ∈ C.biUnion (F.descendants S)) (hyS : y ∈ S)
    (hy : y ∉ C.biUnion (F.descendants S)) (hxy : G.Adj x y) :
    y ∈ (F.path v).take T := by
  obtain ⟨hyv,hlt⟩ := F.child_union_external_ancestor hC hx hyS hy hxy
  have hyx : y ∈ F.path x := by
    obtain ⟨c,hc,hcx⟩ := Finset.mem_biUnion.mp hx
    exact F.ancestor_trans (F.ancestor_trans hyv (F.child_ancestor (hC c hc)))
      ((F.mem_descendants S c x).mp hcx).2
  have hb := F.edge_depth_bound hT hG hxy hyx
  have hi := F.idxOf_add_path_length hyv
  exact (List.mem_take_iff_idxOf_lt hyv).mpr (by omega)

end NormalDFSForest
end
end Cycle13
