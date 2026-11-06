import Cycle12.CycleObstructions

namespace Cycle12
open SimpleGraph Finset

/-- Independent subsets of a five-cycle of size at least two are precisely
its five diagonal pairs. This is a finite combinatorial fact, kernel checked. -/
theorem five_ring_independent_pairs : ∀ S : Finset (Fin 5),
    (∃ i∈S, ∃ j∈S, i≠j) → (∀ i, i∈S → i+1∉S) →
    ∃ k, S={k,k+2} := by decide +kernel

/-- A pairwise intersecting family of diagonals of a five-cycle has a common
vertex and uses at most the two diagonals through that vertex. -/
theorem five_ring_pairwise_family : ∀ S : Finset (Fin 5),
    (∀ i∈S, ∀ j∈S, i=j ∨ i=j+2 ∨ j=i+2) →
    ∃ h, ∀ i∈S, i=h ∨ i=h+3 := by decide +kernel

theorem five_ring_index_alternatives : ∀ i j : Fin 5,
    i=j ∨ i=j+2 ∨ j=i+2 ∨ j=i+1 ∨ i=j+1 := by decide +kernel

variable {V : Type} {G : SimpleGraph V}

theorem no_six_cycle_circumference_five {a b c d e f : V}
    (hshort : Cycle13.NoCycleAtLeast G 6) (hn : [a,b,c,d,e,f].Nodup)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d)
    (hde : G.Adj d e) (hef : G.Adj e f) (hfa : G.Adj f a) : False := by
  let w : CycleWord V := ⟨f,[a,b,c,d,e]⟩
  have hw : w.Valid G := by
    refine ⟨by norm_num [w],hn,?_⟩
    simp [w,CycleWord.support,hfa,hab,hbc,hcd,hde,hef]
  have hh := hshort f (w.toWalk G hw) (w.isCycle_toWalk G hw)
  rw [w.length_toWalk] at hh
  norm_num [w] at hh

theorem no_seven_cycle_circumference_five {a b c d e f g : V}
    (hshort : Cycle13.NoCycleAtLeast G 6) (hn : [a,b,c,d,e,f,g].Nodup)
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

end Cycle12
