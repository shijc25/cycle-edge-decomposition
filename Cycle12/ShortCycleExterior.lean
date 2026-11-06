import Cycle12.CycleFanBounds

namespace Cycle12
open SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- An exterior path between two vertices of a longest cycle has length
at most half the cycle length. This compares both actual comparison cycles. -/
theorem exterior_path_longest_cycle_bound {a b : V} {c : G.Walk a a}
    (hc : c.IsCycle) (hb : b∈c.support) (hab : a≠b) {p : G.Walk a b}
    (hp : p.IsPath) (hp2 : 2 ≤ p.length)
    (hout : ∀ z∈p.support, z≠a → z≠b → z∉c.support)
    (hshort : Cycle13.NoCycleAtLeast G (c.length+1)) :
    2*p.length ≤ c.length := by
  obtain ⟨hA,hB⟩ := exterior_path_arc_lengths hc hb hab hp hp2 hout hshort
  have hsum := congrArg Walk.length (c.take_spec hb)
  rw [Walk.length_append] at hsum
  omega

/-- In a vertex-biconnected graph, the vertices outside a longest cycle
of length at most five form an independent set. -/
theorem short_longest_cycle_outside_independent (G : SimpleGraph V)
    (hconn : G.Connected) (hrobust : ∀ a, (G.induce ({a}ᶜ : Set V)).Preconnected)
    {u : V} (c : G.Walk u u) (hc : c.IsCycle) (hlen : c.length ≤ 5)
    (hshort : Cycle13.NoCycleAtLeast G (c.length+1))
    {x y : V} (hx : x∉c.support) (hy : y∉c.support) : ¬G.Adj x y := by
  intro hxy
  obtain ⟨a,ha,_,_,_,hxa,_⟩ :=
    short_longest_cycle_two_neighbors G hconn hrobust c hc hlen hshort x hx
  obtain ⟨b,hb,d,hd,hbd,hyb,hyd⟩ :=
    short_longest_cycle_two_neighbors G hconn hrobust c hc hlen hshort y hy
  have hchoice : ∃ v∈c.support, a≠v ∧ G.Adj y v := by
    by_cases he : a=b
    · exact ⟨d,hd,by simpa only [he] using hbd,hyd⟩
    · exact ⟨b,hb,he,hyb⟩
  obtain ⟨v,hv,hav,hyv⟩ := hchoice
  let C := c.rotate a ha
  let p : G.Walk a v := Walk.cons hxa.symm (Walk.cons hxy (Walk.cons hyv Walk.nil))
  have hp : p.IsPath := by
    rw [Walk.isPath_def]
    change [a,x,y,v].Nodup
    have hxa' : x≠a := fun he => hx (he ▸ ha)
    have hya' : y≠a := fun he => hy (he ▸ ha)
    have hxv : x≠v := fun he => hx (he ▸ hv)
    have hyv' : y≠v := fun he => hy (he ▸ hv)
    have hxy' := hxy.ne
    simp_all only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true,or_false,ne_comm] <;> tauto
  have hpout : ∀ z∈p.support, z≠a → z≠v → z∉C.support := by
    intro z hz hza hzv hzC
    have hzc : z∈c.support := (c.mem_support_rotate_iff a ha).mp hzC
    change z∈[a,x,y,v] at hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact hza rfl
    · exact hx hzc
    · exact hy hzc
    · exact hzv rfl
  have hvC : v∈C.support := (c.mem_support_rotate_iff a ha).mpr hv
  have hshortC : Cycle13.NoCycleAtLeast G (C.length+1) := by
    simpa only [C,Walk.length_rotate] using hshort
  have hh := exterior_path_longest_cycle_bound (hc.rotate ha) hvC hav hp
    (by change 2≤3; omega) hpout hshortC
  change 2*p.length ≤ C.length at hh
  have hCsize : C.length=c.length := Walk.length_rotate _ _ _
  have hpSize : p.length=3 := rfl
  omega

end
end Cycle12
