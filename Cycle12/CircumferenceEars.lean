import Cycle12.Foundations.LongCycleRemoval

/-! Structural input for the small-circumference classification: any path
outside a six-cycle, meeting it only at distinct ends, has at most three edges.
The proof constructs both actual longer cycles and uses their lengths. -/
namespace Cycle12
open SimpleGraph
variable {V : Type} {G : SimpleGraph V} {u v : V}

theorem path_tails_disjoint_of_exterior {p : G.Walk u v} {q : G.Walk v u}
    (hp : p.IsPath) (hq : q.IsPath) (C : List V)
    (hqC : ∀ w ∈ q.support, w ∈ C)
    (hout : ∀ w ∈ p.support, w ≠ u → w ≠ v → w ∉ C) :
    p.support.tail.Disjoint q.support.tail := by
  have hpu : u ∉ p.support.tail := by
    have hh := hp.support_nodup
    rw [← p.cons_tail_support,List.nodup_cons] at hh
    exact hh.1
  have hqv : v ∉ q.support.tail := by
    have hh := hq.support_nodup
    rw [← q.cons_tail_support,List.nodup_cons] at hh
    exact hh.1
  rw [List.disjoint_left]
  intro w hwP hwQ
  have hwu : w ≠ u := fun he => hpu (he ▸ hwP)
  have hwv : w ≠ v := fun he => hqv (he ▸ hwQ)
  exact hout w (List.mem_of_mem_tail hwP) hwu hwv
    (hqC w (List.mem_of_mem_tail hwQ))

variable [DecidableEq V]

/-- The two genuine cycles made by adjoining an exterior path to the two
arcs of a cycle each obey the prescribed circumference bound. -/
theorem exterior_path_arc_lengths {T : ℕ} {c : G.Walk u u} (hc : c.IsCycle)
    (hv : v ∈ c.support) (huv : u ≠ v) {p : G.Walk u v}
    (hp : p.IsPath) (hp2 : 2 ≤ p.length)
    (hout : ∀ w ∈ p.support, w ≠ u → w ≠ v → w ∉ c.support)
    (hshort : Cycle13.NoCycleAtLeast G T) :
    p.length+(c.takeUntil v hv).length < T ∧
      p.length+(c.dropUntil v hv).length < T := by
  let A := c.takeUntil v hv
  let B := c.dropUntil v hv
  have hA : A.IsPath := hc.isPath_takeUntil hv
  have hB : B.IsPath := by
    have hc' : (A.append B).IsCycle := by simpa only [A,B,c.take_spec] using hc
    exact hc'.isPath_of_append_right (Walk.not_nil_of_ne huv)
  have hAsub : ∀ w ∈ A.reverse.support, w ∈ c.support := by
    intro w hw
    rw [Walk.support_reverse,List.mem_reverse] at hw
    exact c.support_takeUntil_subset_support hv hw
  have hBsub : ∀ w ∈ B.support, w ∈ c.support := fun _ hw =>
    c.support_dropUntil_subset_support hv hw
  have hcycleA := hp.isCycle_append hA.reverse
    (path_tails_disjoint_of_exterior hp hA.reverse c.support hAsub hout) (Or.inl hp2)
  have hcycleB := hp.isCycle_append hB
    (path_tails_disjoint_of_exterior hp hB c.support hBsub hout) (Or.inl hp2)
  have hlenA := hshort u (p.append A.reverse) hcycleA
  have hlenB := hshort u (p.append B) hcycleB
  simpa only [Walk.length_append,Walk.length_reverse,A,B] using And.intro hlenA hlenB

theorem exterior_path_six_cycle_bound {c : G.Walk u u} (hc : c.IsCycle)
    (hc6 : c.length=6) (hv : v ∈ c.support) (huv : u ≠ v) {p : G.Walk u v}
    (hp : p.IsPath) (hp2 : 2 ≤ p.length)
    (hout : ∀ w ∈ p.support, w ≠ u → w ≠ v → w ∉ c.support)
    (hshort : Cycle13.NoCycleAtLeast G 7) :
    p.length ≤ 3 ∧
      (p.length=3 → (c.takeUntil v hv).length=3 ∧ (c.dropUntil v hv).length=3) ∧
      (2 ≤ (c.takeUntil v hv).length ∧ 2 ≤ (c.dropUntil v hv).length) := by
  obtain ⟨hA,hB⟩ := exterior_path_arc_lengths hc hv huv hp hp2 hout hshort
  have hsum := congrArg Walk.length (c.take_spec hv)
  rw [Walk.length_append,hc6] at hsum
  omega

end Cycle12
