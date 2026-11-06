import Mathlib.Combinatorics.SimpleGraph.Paths

namespace Cycle12
open SimpleGraph
variable {V : Type} [DecidableEq V] {G : SimpleGraph V}

/-- Stop a walk at its first visit to a set. All earlier vertices lie
outside that set. Applying this to a path preserves simplicity. -/
theorem first_hit_takeUntil {u v : V} (p : G.Walk u v) (S : Set V)
    (hex : ∃ w∈p.support, w∈S) :
    ∃ w, ∃ hw : w∈p.support, w∈S ∧
      ∀ z∈(p.takeUntil w hw).support, z≠w → z∉S := by
  classical
  induction p with
  | @nil u =>
    obtain ⟨w,hw,hwS⟩ := hex
    have hwu : w=u := by simpa using hw
    subst w
    refine ⟨u,by simp,hwS,?_⟩
    intro z hz hzu
    have hzu' : z=u := by simpa using hz
    exact (hzu hzu').elim
  | @cons u v t huv p ih =>
    by_cases hu : u∈S
    · refine ⟨u,(p.cons huv).start_mem_support,hu,?_⟩
      intro z hz hzu
      rw [Walk.takeUntil_first] at hz
      have hzu' : z=u := by simpa using hz
      exact (hzu hzu').elim
    · have htail : ∃ w∈p.support, w∈S := by
        obtain ⟨w,hw,hwS⟩ := hex
        rw [Walk.support_cons,List.mem_cons] at hw
        rcases hw with hw | hw
        · exact (hu (hw ▸ hwS)).elim
        · exact ⟨w,hw,hwS⟩
      obtain ⟨w,hw,hwS,hfirst⟩ := ih htail
      have huw : u≠w := fun he => hu (he ▸ hwS)
      refine ⟨w,List.mem_cons_of_mem _ hw,hwS,?_⟩
      intro z hz hzw
      rw [Walk.takeUntil_cons hw huw huv] at hz
      rw [Walk.support_cons,List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact hu
      · exact hfirst z hz hzw

end Cycle12
