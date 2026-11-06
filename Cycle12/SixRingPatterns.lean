import Cycle12.CycleObstructions

namespace Cycle12
open SimpleGraph Finset

/-- The complete list of independent neighbor sets on a six-cycle that
contain at least two vertices: short diagonals, opposite pairs, or triples. -/
theorem six_ring_independent_sets : ∀ S : Finset (Fin 6),
    (∃ i∈S, ∃ j∈S, i≠j) → (∀ i, i∈S → i+1∉S) →
    ∃ k, S={k,k+2} ∨ S={k,k+3} ∨ S={k,k+2,k+4} := by decide +kernel

variable {V : Type} {G : SimpleGraph V}

theorem no_seven_cycle_circumference_six {a b c d e f g : V}
    (hshort : Cycle13.NoCycleAtLeast G 7) (hn : [a,b,c,d,e,f,g].Nodup)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d)
    (hde : G.Adj d e) (hef : G.Adj e f) (hfg : G.Adj f g)
    (hga : G.Adj g a) : False := by
  let w : CycleWord V := ⟨g,[a,b,c,d,e,f]⟩
  have hw : w.Valid G := by
    refine ⟨by norm_num [w],hn,?_⟩
    simp [w,CycleWord.support,hga,hab,hbc,hcd,hde,hef,hfg]
  have hh := hshort g (w.toWalk G hw) (w.isCycle_toWalk G hw)
  rw [w.length_toWalk] at hh
  norm_num [w] at hh

theorem no_eight_cycle_circumference_six {a b c d e f g h : V}
    (hshort : Cycle13.NoCycleAtLeast G 7) (hn : [a,b,c,d,e,f,g,h].Nodup)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d)
    (hde : G.Adj d e) (hef : G.Adj e f) (hfg : G.Adj f g)
    (hgh : G.Adj g h) (hha : G.Adj h a) : False := by
  let w : CycleWord V := ⟨h,[a,b,c,d,e,f,g]⟩
  have hw : w.Valid G := by
    refine ⟨by norm_num [w],hn,?_⟩
    simp [w,CycleWord.support,hha,hab,hbc,hcd,hde,hef,hfg,hgh]
  have hh := hshort h (w.toWalk G hw) (w.isCycle_toWalk G hw)
  rw [w.length_toWalk] at hh
  norm_num [w] at hh

end Cycle12
