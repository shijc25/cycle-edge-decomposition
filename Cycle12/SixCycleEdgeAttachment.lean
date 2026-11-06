import Cycle12.ShortCycleExterior

namespace Cycle12
open SimpleGraph
variable {V : Type} [DecidableEq V] {G : SimpleGraph V}

/-- An exterior edge joining two distinct attachment vertices of a six-cycle
forces those two cycle vertices to be opposite. -/
theorem six_cycle_external_edge_opposite {u a b x y : V} {c : G.Walk u u}
    (hc : c.IsCycle) (hlen : c.length=6) (hshort : Cycle13.NoCycleAtLeast G 7)
    (ha : a∈c.support) (hb : b∈c.support) (hab : a≠b)
    (hx : x∉c.support) (hy : y∉c.support)
    (hxa : G.Adj x a) (hxy : G.Adj x y) (hyb : G.Adj y b) :
    (c.rotate a ha).getVert 3=b := by
  let C := c.rotate a ha
  let p : G.Walk a b := Walk.cons hxa.symm (Walk.cons hxy (Walk.cons hyb Walk.nil))
  have hp : p.IsPath := by
    rw [Walk.isPath_def]
    change [a,x,y,b].Nodup
    have hxa' : x≠a := fun he => hx (he ▸ ha)
    have hya' : y≠a := fun he => hy (he ▸ ha)
    have hxb : x≠b := fun he => hx (he ▸ hb)
    have hyb' : y≠b := fun he => hy (he ▸ hb)
    have hxy' := hxy.ne
    simp_all only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true,or_false,ne_comm] <;> tauto
  have hpout : ∀ z∈p.support, z≠a → z≠b → z∉C.support := by
    intro z hz hza hzb hzC
    have hzc : z∈c.support := (c.mem_support_rotate_iff a ha).mp hzC
    change z∈[a,x,y,b] at hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact hza rfl
    · exact hx hzc
    · exact hy hzc
    · exact hzb rfl
  have hbC : b∈C.support := (c.mem_support_rotate_iff a ha).mpr hb
  have hC6 : C.length=6 := by simpa only [C,Walk.length_rotate] using hlen
  have hh := exterior_path_six_cycle_bound (hc.rotate ha) hC6 hbC hab hp
    (by change 2≤3; omega) hpout hshort
  have hthree : (C.takeUntil b hbC).length=3 := (hh.2.1 rfl).1
  have hend := C.getVert_length_takeUntil hbC
  rw [hthree] at hend
  exact hend

/-- If the ends of an exterior edge have distinct cycle attachments a,b,
every cycle neighbor of either endpoint belongs to the same opposite pair. -/
theorem six_cycle_external_edge_attachment_pair {u a b x y : V} {c : G.Walk u u}
    (hc : c.IsCycle) (hlen : c.length=6) (hshort : Cycle13.NoCycleAtLeast G 7)
    (ha : a∈c.support) (hb : b∈c.support) (hab : a≠b)
    (hx : x∉c.support) (hy : y∉c.support)
    (hxa : G.Adj x a) (hxy : G.Adj x y) (hyb : G.Adj y b) :
    (∀ v∈c.support, G.Adj x v → v=a ∨ v=b) ∧
    (∀ v∈c.support, G.Adj y v → v=a ∨ v=b) := by
  constructor
  · intro v hv hxv
    by_cases hvb : v=b
    · exact Or.inr hvb
    · have haopp := six_cycle_external_edge_opposite hc hlen hshort hb ha hab.symm
        hy hx hyb hxy.symm hxa
      have hvopp := six_cycle_external_edge_opposite hc hlen hshort hb hv (Ne.symm hvb)
        hy hx hyb hxy.symm hxv
      exact Or.inl (hvopp.symm.trans haopp)
  · intro v hv hyv
    by_cases hva : v=a
    · exact Or.inl hva
    · have hbopp := six_cycle_external_edge_opposite hc hlen hshort ha hb hab hx hy hxa hxy hyb
      have hvopp := six_cycle_external_edge_opposite hc hlen hshort ha hv (Ne.symm hva) hx hy hxa hxy hyv
      exact Or.inr (hvopp.symm.trans hbopp)

end Cycle12
