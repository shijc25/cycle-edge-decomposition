import Cycle12.CycleWord
import Cycle12.Foundations.LongCycleRemoval

/-! Small explicit cycles are interpreted as genuine simple closed walks.
These obstructions will be used for arbitrary-order classification, not as
tests on a bounded ambient graph. -/
namespace Cycle12
open SimpleGraph
variable {V : Type} {G : SimpleGraph V}

theorem no_five_cycle {a b c d e : V}
    (hshort : Cycle13.NoCycleAtLeast G 5)
    (hn : [a,b,c,d,e].Nodup)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d)
    (hde : G.Adj d e) (hea : G.Adj e a) : False := by
  let w : CycleWord V := ⟨e,[a,b,c,d]⟩
  have hw : w.Valid G := by
    refine ⟨by norm_num [w],hn,?_⟩
    simp [w,CycleWord.support,hea,hab,hbc,hcd,hde]
  have hh := hshort e (w.toWalk G hw) (w.isCycle_toWalk G hw)
  rw [w.length_toWalk] at hh
  norm_num [w] at hh

theorem no_six_cycle {a b c d e f : V}
    (hshort : Cycle13.NoCycleAtLeast G 5)
    (hn : [a,b,c,d,e,f].Nodup)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d)
    (hde : G.Adj d e) (hef : G.Adj e f) (hfa : G.Adj f a) : False := by
  let w : CycleWord V := ⟨f,[a,b,c,d,e]⟩
  have hw : w.Valid G := by
    refine ⟨by norm_num [w],hn,?_⟩
    simp [w,CycleWord.support,hfa,hab,hbc,hcd,hde,hef]
  have hh := hshort f (w.toWalk G hw) (w.isCycle_toWalk G hw)
  rw [w.length_toWalk] at hh
  norm_num [w] at hh

/-- Every actual four-cycle admits an ordered list of four distinct vertices. -/
theorem four_cycle_vertices {a : V} {w : G.Walk a a}
    (hw : w.IsCycle) (hlen : w.length=4) :
    ∃ b c d, [a,b,c,d].Nodup ∧ G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧
      G.Adj d a ∧ w.support=[a,b,c,d,a] := by
  cases w with
  | nil => simp at hlen
  | cons hab p =>
    rename_i b
    cases p with
    | nil => simp at hlen
    | cons hbc q =>
      rename_i c
      cases q with
      | nil => simp at hlen
      | cons hcd r =>
        rename_i d
        cases r with
        | nil => simp at hlen
        | cons hde s =>
          rename_i e
          have hs : s.length=0 := by simpa using hlen
          have hsNil := Walk.length_eq_zero_iff.mp hs
          cases hsNil
          refine ⟨b,c,d,?_,hab,hbc,hcd,hde,rfl⟩
          have hh := hw.support_nodup
          simpa only [Walk.support_cons,Walk.support_nil,List.tail_cons,
            List.nodup_cons,List.mem_cons,List.mem_singleton,List.not_mem_nil,
            List.nodup_nil,not_or,not_false_eq_true,and_true,ne_comm,
            and_assoc,and_left_comm,and_comm] using hh

end Cycle12
