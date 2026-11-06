import Cycle12.TwoFan
import Cycle12.CircumferenceEars

namespace Cycle12
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem path_reverse_append_of_common_start {x a b : V}
    {p : G.Walk x a} {q : G.Walk x b} (hp : p.IsPath) (hq : q.IsPath)
    (hcommon : ∀ z∈p.support, z∈q.support → z=x) :
    (p.reverse.append q).IsPath := by
  rw [Walk.isPath_def,Walk.support_append,List.nodup_append]
  refine ⟨hp.reverse.support_nodup,hq.support_nodup.tail,?_⟩
  rintro z hzp w hzq rfl
  have hzP : z∈p.support := by simpa only [Walk.support_reverse,List.mem_reverse] using hzp
  have hzx := hcommon z hzP (List.mem_of_mem_tail hzq)
  have hxnot : x∉q.support.tail := by
    have hh := hq.support_nodup
    rw [← q.cons_tail_support,List.nodup_cons] at hh
    exact hh.1
  exact hxnot (hzx ▸ hzq)

theorem cycle_support_card_at_least_three {u : V} {c : G.Walk u u} (hc : c.IsCycle) :
    3 ≤ c.support.toFinset.card := by
  have ht : c.support.tail.toFinset.card=c.length := by
    rw [List.toFinset_card_of_nodup hc.support_nodup,List.length_tail,c.length_support]
    omega
  have hsub : c.support.tail.toFinset ⊆ c.support.toFinset := by
    intro z hz
    exact List.mem_toFinset.mpr (List.mem_of_mem_tail (List.mem_toFinset.mp hz))
  have hh := Finset.card_le_card hsub
  have hlen := hc.three_le_length
  omega

/-- In a graph of circumference at most six, a two-fan from an outside
vertex to a six-cycle has total length at most three. -/
theorem two_fan_six_cycle_length {u x a b : V} {c : G.Walk u u}
    (hc : c.IsCycle) (hc6 : c.length=6)
    (ha : a∈c.support) (hb : b∈c.support) (hab : a≠b) (hx : x∉c.support)
    {p : G.Walk x a} {q : G.Walk x b} (hp : p.IsPath) (hq : q.IsPath)
    (hpout : ∀ z∈p.support, z≠a → z∉c.support)
    (hqout : ∀ z∈q.support, z≠b → z∉c.support)
    (hcommon : ∀ z∈p.support, z∈q.support → z=x)
    (hshort : Cycle13.NoCycleAtLeast G 7) : p.length+q.length ≤ 3 := by
  let r := p.reverse.append q
  let C := c.rotate a ha
  have hC : C.IsCycle := hc.rotate ha
  have hC6 : C.length=6 := by simpa only [C,Walk.length_rotate] using hc6
  have hbC : b∈C.support := (c.mem_support_rotate_iff a ha).mpr hb
  have hxa : x≠a := fun he => hx (he ▸ ha)
  have hxb : x≠b := fun he => hx (he ▸ hb)
  have hp₁ : 1 ≤ p.length := by
    exact Nat.pos_of_ne_zero (fun he => Walk.not_nil_of_ne hxa (Walk.length_eq_zero_iff.mp he))
  have hq₁ : 1 ≤ q.length := by
    exact Nat.pos_of_ne_zero (fun he => Walk.not_nil_of_ne hxb (Walk.length_eq_zero_iff.mp he))
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
  have hbound := (exterior_path_six_cycle_bound hC hC6 hbC hab hr hrlen hrout hshort).1
  simpa only [r,Walk.length_append,Walk.length_reverse] using hbound

/-- Every six-cycle in a vertex-biconnected graph of circumference at most
six dominates every vertex outside it. This is an arbitrary-order theorem. -/
theorem six_cycle_dominates (G : SimpleGraph V) (hconn : G.Connected)
    (hrobust : ∀ a, (G.induce ({a}ᶜ : Set V)).Preconnected)
    (hshort : Cycle13.NoCycleAtLeast G 7)
    {u : V} (c : G.Walk u u) (hc : c.IsCycle) (hc6 : c.length=6)
    (x : V) (hx : x∉c.support) : ∃ y∈c.support, G.Adj x y := by
  have hsize : 2 ≤ c.support.toFinset.card := by
    have hh := cycle_support_card_at_least_three hc
    omega
  obtain ⟨a,ha,b,hb,hab,p,q,hp,hq,hpout,hqout,hcommon⟩ :=
    two_fan_to_set G c.support.toFinset hsize hconn hrobust x (by simpa using hx)
  have ha' : a∈c.support := List.mem_toFinset.mp ha
  have hb' : b∈c.support := List.mem_toFinset.mp hb
  have hpout' : ∀ z∈p.support, z≠a → z∉c.support := by simpa only [List.mem_toFinset] using hpout
  have hqout' : ∀ z∈q.support, z≠b → z∉c.support := by simpa only [List.mem_toFinset] using hqout
  have hlen := two_fan_six_cycle_length hc hc6 ha' hb' hab hx hp hq hpout' hqout' hcommon hshort
  have hxa : x≠a := fun he => hx (he ▸ ha')
  have hxb : x≠b := fun he => hx (he ▸ hb')
  have hp₁ : 0 < p.length :=
    Nat.pos_of_ne_zero (fun he => Walk.not_nil_of_ne hxa (Walk.length_eq_zero_iff.mp he))
  have hq₁ : 0 < q.length :=
    Nat.pos_of_ne_zero (fun he => Walk.not_nil_of_ne hxb (Walk.length_eq_zero_iff.mp he))
  have he : p.length=1 ∨ q.length=1 := by omega
  rcases he with he | he
  · exact ⟨a,ha',Walk.adj_of_length_eq_one he⟩
  · exact ⟨b,hb',Walk.adj_of_length_eq_one he⟩

end
end Cycle12
