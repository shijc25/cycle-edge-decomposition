import Cycle12.Foundations.PackingExtension

/-! A finite, decidable cycle witness with a proved interpretation as an
actual mathlib simple closed walk. Used to certify the finite terminal graphs. -/
namespace Cycle12
open SimpleGraph Finset

structure CycleWord (V : Type) where
  root : V
  tail : List V

namespace CycleWord
variable {V : Type}

def support (c : CycleWord V) : List V := c.root :: (c.tail++[c.root])

def edges [DecidableEq V] (c : CycleWord V) : Finset (Sym2 V) :=
  (List.zipWith (s(·,·)) c.support c.support.tail).toFinset

def Valid (c : CycleWord V) (G : SimpleGraph V) : Prop :=
  2 ≤ c.tail.length ∧ (c.tail++[c.root]).Nodup ∧ c.support.IsChain G.Adj

instance [DecidableEq V] (c : CycleWord V) (G : SimpleGraph V) [DecidableRel G.Adj] :
    Decidable (c.Valid G) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def toWalk (c : CycleWord V) (G : SimpleGraph V) (hc : c.Valid G) : G.Walk c.root c.root :=
  (Walk.ofSupport c.support (by simp [support]) hc.2.2).copy
    (by simp [support]) (by simp [support])

theorem support_toWalk (c : CycleWord V) (G : SimpleGraph V) (hc : c.Valid G) :
    (c.toWalk G hc).support=c.support := by
  unfold toWalk
  erw [Walk.support_copy,Walk.support_ofSupport]

theorem length_toWalk (c : CycleWord V) (G : SimpleGraph V) (hc : c.Valid G) :
    (c.toWalk G hc).length=c.tail.length+1 := by
  unfold toWalk
  erw [Walk.length_copy,Walk.length_ofSupport]
  simp [support]

theorem isCycle_toWalk (c : CycleWord V) (G : SimpleGraph V) (hc : c.Valid G) :
    (c.toWalk G hc).IsCycle := by
  have hlen : 3 ≤ (c.toWalk G hc).length := by rw [length_toWalk]; have := hc.1; omega
  have hn : ¬(c.toWalk G hc).Nil := by
    intro hz
    have hzero := Walk.length_eq_zero_iff.mpr hz
    omega
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  refine ⟨?_,hlen⟩
  rw [Walk.isPath_def,Walk.support_tail_of_not_nil _ hn,support_toWalk]
  exact hc.2.1

theorem edgeSet_toWalk [DecidableEq V] (c : CycleWord V) (G : SimpleGraph V)
    (hc : c.Valid G) : (c.toWalk G hc).edgeSet=(c.edges:Set (Sym2 V)) := by
  rw [← Walk.coe_edges_toFinset,Walk.edges_eq_zipWith_support,support_toWalk]
  rfl

end CycleWord
end Cycle12
