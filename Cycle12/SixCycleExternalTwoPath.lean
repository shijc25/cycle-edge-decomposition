import Cycle12.SixCycleEdgeAttachment

namespace Cycle12
open SimpleGraph
variable {V : Type} [DecidableEq V] {G : SimpleGraph V}

/-- The endpoints of a two-edge path outside a six-cycle cannot have
different cycle neighbors: those neighbors would create a four-edge ear. -/
theorem six_cycle_external_two_path_attachment_eq {u a b x y z : V} {c : G.Walk u u}
    (hc : c.IsCycle) (hlen : c.length=6) (hshort : Cycle13.NoCycleAtLeast G 7)
    (ha : a∈c.support) (hb : b∈c.support)
    (hx : x∉c.support) (hy : y∉c.support) (hz : z∉c.support)
    (hn : [x,y,z].Nodup) (hxa : G.Adj x a) (hxy : G.Adj x y)
    (hyz : G.Adj y z) (hzb : G.Adj z b) : a=b := by
  by_contra hab
  let C := c.rotate a ha
  let p : G.Walk a b := Walk.cons hxa.symm
    (Walk.cons hxy (Walk.cons hyz (Walk.cons hzb Walk.nil)))
  have hp : p.IsPath := by
    rw [Walk.isPath_def]
    change [a,x,y,z,b].Nodup
    have hxa' : x≠a := fun he => hx (he ▸ ha)
    have hya' : y≠a := fun he => hy (he ▸ ha)
    have hza' : z≠a := fun he => hz (he ▸ ha)
    have hxb : x≠b := fun he => hx (he ▸ hb)
    have hyb : y≠b := fun he => hy (he ▸ hb)
    have hzb' : z≠b := fun he => hz (he ▸ hb)
    simp_all only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true,or_false,ne_comm] <;> tauto
  have hpout : ∀ v∈p.support, v≠a → v≠b → v∉C.support := by
    intro v hv hva hvb hvC
    have hvc : v∈c.support := (c.mem_support_rotate_iff a ha).mp hvC
    change v∈[a,x,y,z,b] at hv
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · exact hva rfl
    · exact hx hvc
    · exact hy hvc
    · exact hz hvc
    · exact hvb rfl
  have hbC : b∈C.support := (c.mem_support_rotate_iff a ha).mpr hb
  have hC6 : C.length=6 := by simpa only [C,Walk.length_rotate] using hlen
  have hh := exterior_path_six_cycle_bound (hc.rotate ha) hC6 hbC hab hp
    (by change 2≤4; omega) hpout hshort
  have hbad : 4≤3 := hh.1
  omega

/-- In the vertex-biconnected setting, both endpoints of every exterior
two-edge path have the same unique neighbor on the chosen six-cycle. -/
theorem six_cycle_external_two_path_unique_attachment [Fintype V]
    (G : SimpleGraph V) (hconn : G.Connected)
    (hrobust : ∀ a, (G.induce ({a}ᶜ : Set V)).Preconnected)
    {u x y z : V} (c : G.Walk u u) (hc : c.IsCycle) (hlen : c.length=6)
    (hshort : Cycle13.NoCycleAtLeast G 7)
    (hx : x∉c.support) (hy : y∉c.support) (hz : z∉c.support)
    (hn : [x,y,z].Nodup) (hxy : G.Adj x y) (hyz : G.Adj y z) :
    ∃ a∈c.support, (∀ v∈c.support, G.Adj x v ↔ v=a) ∧
      (∀ v∈c.support, G.Adj z v ↔ v=a) := by
  obtain ⟨a,ha,hxa⟩ := six_cycle_dominates G hconn hrobust hshort c hc hlen x hx
  obtain ⟨b,hb,hzb⟩ := six_cycle_dominates G hconn hrobust hshort c hc hlen z hz
  have hab := six_cycle_external_two_path_attachment_eq hc hlen hshort ha hb hx hy hz hn hxa hxy hyz hzb
  subst b
  refine ⟨a,ha,?_,?_⟩
  · intro v hv
    constructor
    · intro hxv
      exact six_cycle_external_two_path_attachment_eq hc hlen hshort hv ha hx hy hz hn hxv hxy hyz hzb
    · rintro rfl
      exact hxa
  · intro v hv
    constructor
    · intro hzv
      exact (six_cycle_external_two_path_attachment_eq hc hlen hshort ha hv hx hy hz hn hxa hxy hyz hzv).symm
    · rintro rfl
      exact hzb

end Cycle12
