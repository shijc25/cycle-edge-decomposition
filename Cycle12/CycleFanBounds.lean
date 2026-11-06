import Cycle12.SixCycleDominating

namespace Cycle12
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- A fan to a longest cycle of length k has total length at most k/2.
Both comparison cycles are actual simple cycles in G. -/
theorem two_fan_longest_cycle_length {u x a b : V} {c : G.Walk u u}
    (hc : c.IsCycle) (ha : a∈c.support) (hb : b∈c.support) (hab : a≠b)
    (hx : x∉c.support) {p : G.Walk x a} {q : G.Walk x b}
    (hp : p.IsPath) (hq : q.IsPath)
    (hpout : ∀ z∈p.support, z≠a → z∉c.support)
    (hqout : ∀ z∈q.support, z≠b → z∉c.support)
    (hcommon : ∀ z∈p.support, z∈q.support → z=x)
    (hshort : Cycle13.NoCycleAtLeast G (c.length+1)) :
    2*(p.length+q.length) ≤ c.length := by
  let r := p.reverse.append q
  let C := c.rotate a ha
  have hC : C.IsCycle := hc.rotate ha
  have hbC : b∈C.support := (c.mem_support_rotate_iff a ha).mpr hb
  have hxa : x≠a := fun he => hx (he ▸ ha)
  have hxb : x≠b := fun he => hx (he ▸ hb)
  have hp₁ : 0 < p.length :=
    Nat.pos_of_ne_zero (fun he => Walk.not_nil_of_ne hxa (Walk.length_eq_zero_iff.mp he))
  have hq₁ : 0 < q.length :=
    Nat.pos_of_ne_zero (fun he => Walk.not_nil_of_ne hxb (Walk.length_eq_zero_iff.mp he))
  have hr : r.IsPath := path_reverse_append_of_common_start hp hq hcommon
  have hrlen : 2 ≤ r.length := by simp only [r,Walk.length_append,Walk.length_reverse]; omega
  have hrout : ∀ z∈r.support, z≠a → z≠b → z∉C.support := by
    intro z hz hza hzb hzC
    have hzc : z∈c.support := (c.mem_support_rotate_iff a ha).mp hzC
    change z∈(p.reverse.append q).support at hz
    rw [Walk.mem_support_append_iff] at hz
    rcases hz with hz | hz
    · exact hpout z (by simpa only [Walk.support_reverse,List.mem_reverse] using hz) hza hzc
    · exact hqout z hz hzb hzc
  obtain ⟨hA,hB⟩ := exterior_path_arc_lengths hC hbC hab hr hrlen hrout hshort
  have hsum := congrArg Walk.length (C.take_spec hbC)
  rw [Walk.length_append] at hsum
  have hClen : C.length=c.length := Walk.length_rotate _ _ _
  have hrsize : r.length=p.length+q.length := by simp only [r,Walk.length_append,Walk.length_reverse]
  omega

/-- For a longest cycle of length four or five, every external vertex
has two distinct neighbors on that cycle. -/
theorem short_longest_cycle_two_neighbors (G : SimpleGraph V) (hconn : G.Connected)
    (hrobust : ∀ a, (G.induce ({a}ᶜ : Set V)).Preconnected)
    {u : V} (c : G.Walk u u) (hc : c.IsCycle) (hlen : c.length ≤ 5)
    (hshort : Cycle13.NoCycleAtLeast G (c.length+1))
    (x : V) (hx : x∉c.support) :
    ∃ a∈c.support, ∃ b∈c.support, a≠b ∧ G.Adj x a ∧ G.Adj x b := by
  have hsize : 2 ≤ c.support.toFinset.card := by
    have hh := cycle_support_card_at_least_three hc
    omega
  obtain ⟨a,ha,b,hb,hab,p,q,hp,hq,hpout,hqout,hcommon⟩ :=
    two_fan_to_set G c.support.toFinset hsize hconn hrobust x (by simpa using hx)
  have ha' : a∈c.support := List.mem_toFinset.mp ha
  have hb' : b∈c.support := List.mem_toFinset.mp hb
  have hpout' : ∀ z∈p.support, z≠a → z∉c.support := by simpa only [List.mem_toFinset] using hpout
  have hqout' : ∀ z∈q.support, z≠b → z∉c.support := by simpa only [List.mem_toFinset] using hqout
  have hfan := two_fan_longest_cycle_length hc ha' hb' hab hx hp hq hpout' hqout' hcommon hshort
  have hxa : x≠a := fun he => hx (he ▸ ha')
  have hxb : x≠b := fun he => hx (he ▸ hb')
  have hp₁ : 0 < p.length :=
    Nat.pos_of_ne_zero (fun he => Walk.not_nil_of_ne hxa (Walk.length_eq_zero_iff.mp he))
  have hq₁ : 0 < q.length :=
    Nat.pos_of_ne_zero (fun he => Walk.not_nil_of_ne hxb (Walk.length_eq_zero_iff.mp he))
  have hpone : p.length=1 := by omega
  have hqone : q.length=1 := by omega
  exact ⟨a,ha',b,hb',hab,Walk.adj_of_length_eq_one hpone,Walk.adj_of_length_eq_one hqone⟩

end
end Cycle12
