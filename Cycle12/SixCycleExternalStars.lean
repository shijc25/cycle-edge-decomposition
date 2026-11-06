import Cycle12.SixCycleComponentPropagation

namespace Cycle12
open SimpleGraph
variable {V : Type} [DecidableEq V] {G : SimpleGraph V}

/-- Every exterior simple path with at least two edges has the same cycle
attachment at both ends, whenever those attachments exist. -/
theorem six_cycle_external_path_attachment_eq {u a b x z : V} {c : G.Walk u u}
    (hc : c.IsCycle) (hlen : c.length=6) (hshort : Cycle13.NoCycleAtLeast G 7)
    (ha : a∈c.support) (hb : b∈c.support)
    {p : G.Walk x z} (hp : p.IsPath) (hp2 : 2≤p.length)
    (hout : ∀ v∈p.support, v∉c.support) (hxa : G.Adj x a) (hzb : G.Adj z b) : a=b := by
  by_contra hab
  let C := c.rotate a ha
  let q := Walk.cons hxa.symm p
  let r := q.concat hzb
  have haq : a∉p.support := fun he => hout a he ha
  have hq : q.IsPath := hp.cons haq
  have hbq : b∉q.support := by
    intro he
    change b∈a::p.support at he
    rcases List.mem_cons.mp he with he | he
    · exact hab he.symm
    · exact hout b he hb
  have hr : r.IsPath := hq.concat hbq hzb
  have hrout : ∀ v∈r.support, v≠a → v≠b → v∉C.support := by
    intro v hv hva hvb hvC
    have hvc : v∈c.support := (c.mem_support_rotate_iff a ha).mp hvC
    simp only [r,q,Walk.support_concat,Walk.support_cons,List.mem_append,
      List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with (he | he) | he
    · exact hva he
    · exact hout v he hvc
    · exact hvb he
  have hbC : b∈C.support := (c.mem_support_rotate_iff a ha).mpr hb
  have hC6 : C.length=6 := by simpa only [C,Walk.length_rotate] using hlen
  have hrlen : r.length=p.length+2 := by simp only [r,q,Walk.length_concat,Walk.length_cons]
  have hh := exterior_path_six_cycle_bound (hc.rotate ha) hC6 hbC hab hr (by omega) hrout hshort
  omega

variable [Fintype V]

/-- There is no triangle entirely outside a six-cycle. -/
theorem six_cycle_no_external_triangle (G : SimpleGraph V)
    (hconn : G.Connected) (hrobust : ∀ a, (G.induce ({a}ᶜ : Set V)).Preconnected)
    {u x y z : V} (c : G.Walk u u) (hc : c.IsCycle) (hlen : c.length=6)
    (hshort : Cycle13.NoCycleAtLeast G 7)
    (hx : x∉c.support) (hy : y∉c.support) (hz : z∉c.support)
    (hn : [x,y,z].Nodup) (hxy : G.Adj x y) (hyz : G.Adj y z) (hzx : G.Adj z x) : False := by
  obtain ⟨a,ha,hX,hZ⟩ := six_cycle_external_two_path_unique_attachment G hconn hrobust
    c hc hlen hshort hx hy hz hn hxy hyz
  exact six_cycle_no_equal_single_attachments G hconn hrobust c hc hlen hshort
    ha hx hz hzx.symm hX hZ

/-- No simple path on four vertices lies entirely outside the six-cycle. -/
theorem six_cycle_no_external_three_path (G : SimpleGraph V)
    (hconn : G.Connected) (hrobust : ∀ a, (G.induce ({a}ᶜ : Set V)).Preconnected)
    {u x y z w : V} (c : G.Walk u u) (hc : c.IsCycle) (hlen : c.length=6)
    (hshort : Cycle13.NoCycleAtLeast G 7)
    (hx : x∉c.support) (hy : y∉c.support) (hz : z∉c.support) (hw : w∉c.support)
    (hn : [x,y,z,w].Nodup) (hxy : G.Adj x y) (hyz : G.Adj y z) (hzw : G.Adj z w) : False := by
  have hn₁ : [x,y,z].Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true,or_false] at *
    tauto
  have hn₂ : [y,z,w].Nodup := hn.of_cons
  obtain ⟨a,ha,hX,hZ⟩ := six_cycle_external_two_path_unique_attachment G hconn hrobust
    c hc hlen hshort hx hy hz hn₁ hxy hyz
  obtain ⟨b,hb,hY,hW⟩ := six_cycle_external_two_path_unique_attachment G hconn hrobust
    c hc hlen hshort hy hz hw hn₂ hyz hzw
  let p : G.Walk x w := Walk.cons hxy (Walk.cons hyz (Walk.cons hzw Walk.nil))
  have hp : p.IsPath := by rw [Walk.isPath_def]; exact hn
  have hpout : ∀ v∈p.support, v∉c.support := by
    intro v hv
    change v∈[x,y,z,w] at hv
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact hx
    · exact hy
    · exact hz
    · exact hw
  have hab := six_cycle_external_path_attachment_eq hc hlen hshort ha hb hp
    (by change 2≤3; omega) hpout ((hX a ha).mpr rfl) ((hW b hb).mpr rfl)
  subst b
  exact six_cycle_no_equal_single_attachments G hconn hrobust c hc hlen hshort ha hx hy hxy hX hY

/-- Every endpoint of an exterior two-edge simple path is an exterior leaf.
This is the local star structure needed to classify exterior components. -/
theorem six_cycle_external_two_path_endpoints_are_leaves (G : SimpleGraph V)
    (hconn : G.Connected) (hrobust : ∀ a, (G.induce ({a}ᶜ : Set V)).Preconnected)
    {u x y z : V} (c : G.Walk u u) (hc : c.IsCycle) (hlen : c.length=6)
    (hshort : Cycle13.NoCycleAtLeast G 7)
    (hx : x∉c.support) (hy : y∉c.support) (hz : z∉c.support)
    (hn : [x,y,z].Nodup) (hxy : G.Adj x y) (hyz : G.Adj y z) :
    (∀ w, w∉c.support → G.Adj x w → w=y) ∧
    (∀ w, w∉c.support → G.Adj z w → w=y) := by
  have first : ∀ {x y z : V}, x∉c.support → y∉c.support → z∉c.support →
      [x,y,z].Nodup → G.Adj x y → G.Adj y z →
      ∀ w, w∉c.support → G.Adj x w → w=y := by
    intro x y z hx hy hz hn hxy hyz w hw hxw
    by_contra hwy
    by_cases hwz : w=z
    · subst w
      exact six_cycle_no_external_triangle G hconn hrobust c hc hlen hshort hx hy hz hn hxy hyz hxw.symm
    · have hwx : w≠x := hxw.ne.symm
      have hnodes : [w,x,y,z].Nodup := by
        simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
          not_or,not_false_eq_true,and_true,or_false] at *
        tauto
      exact six_cycle_no_external_three_path G hconn hrobust c hc hlen hshort hw hx hy hz
        hnodes hxw.symm hxy hyz
  refine ⟨first hx hy hz hn hxy hyz,first hz hy hx ?_ hyz.symm hxy.symm⟩
  simp_all only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true,or_false,ne_comm] <;> tauto

end Cycle12
