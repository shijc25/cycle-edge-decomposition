import Cycle12.SixTwoEarModels

namespace Cycle12
open SimpleGraph Finset
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def sixTwoEarWitness : Fin 6 → Fin 6 → CycleWord (Fin 10) :=
  ![![⟨0,[1,2]⟩,⟨0,[5,4,3,2,1,9,8]⟩,⟨0,[5,4,3,2,9,8]⟩,⟨0,[1,2]⟩,⟨0,[1,2,3,4,9,8]⟩,⟨0,[1,2,3,4,5,9,8]⟩],
    ![⟨0,[5,4,3,2,1,8,9]⟩,⟨0,[1,2]⟩,⟨0,[1,8,9,2,3,4,5]⟩,⟨0,[1,8,9,3,4,5]⟩,⟨0,[1,8,9,4,3,7,6]⟩,⟨0,[1,8,9,5,4,3,7,6]⟩],
    ![⟨0,[5,4,3,2,8,9]⟩,⟨0,[1,9,8,2,3,4,5]⟩,⟨0,[1,2]⟩,⟨0,[1,2,8,9,3,4,5]⟩,⟨0,[1,2,8,9,4,3,7,6]⟩,⟨0,[1,2,8,9,5,4,3,7,6]⟩],
    ![⟨0,[1,2]⟩,⟨0,[1,9,8,3,4,5]⟩,⟨0,[1,2,9,8,3,4,5]⟩,⟨0,[1,2]⟩,⟨0,[1,2,3,8,9,4,5]⟩,⟨0,[1,2,3,8,9,5]⟩],
    ![⟨0,[1,2,3,4,8,9]⟩,⟨0,[1,9,8,4,3,7,6]⟩,⟨0,[1,2,9,8,4,3,7,6]⟩,⟨0,[1,2,3,9,8,4,5]⟩,⟨0,[1,2]⟩,⟨0,[1,2,3,4,8,9,5]⟩],
    ![⟨0,[1,2,3,4,5,8,9]⟩,⟨0,[1,9,8,5,4,3,7,6]⟩,⟨0,[1,2,9,8,5,4,3,7,6]⟩,⟨0,[1,2,3,9,8,5]⟩,⟨0,[1,2,3,4,9,8,5]⟩,⟨0,[1,2]⟩]]

theorem six_two_ear_witnesses_checked : ∀ a b : Fin 6,
    (a=b ∨ (a=0 ∧ b=3) ∨ (a=3 ∧ b=0)) ∨
    ((sixTwoEarWitness a b).Valid (TerminalCert.graph (sixTwoEarEdges a b)) ∧
      7≤(sixTwoEarWitness a b).tail.length+1) := by decide +kernel

/-- An arbitrary second disjoint exterior edge has the same two core hubs. -/
theorem six_actual_two_ears_common_hubs {V : Type} {G : SimpleGraph V}
    (f : Fin 6 ↪ V) (hcycle : ∀ i, G.Adj (f i) (f (i+1)))
    (hshort : Cycle13.NoCycleAtLeast G 7)
    {x y z w : V} (hx : ∀ i, x≠f i) (hy : ∀ i, y≠f i)
    (hz : ∀ i, z≠f i) (hw : ∀ i, w≠f i)
    (hxy : x≠y) (hxz : x≠z) (hxw : x≠w)
    (hyz : y≠z) (hyw : y≠w) (hzw : z≠w)
    (hxa : G.Adj x (f 0)) (hxyadj : G.Adj x y) (hyb : G.Adj y (f 3))
    (a b : Fin 6) (hab : a≠b)
    (hza : G.Adj z (f a)) (hzwadj : G.Adj z w) (hwb : G.Adj w (f b)) :
    (a=0 ∧ b=3) ∨ (a=3 ∧ b=0) := by
  rcases six_two_ear_witnesses_checked a b with h | ⟨hc,hlen⟩
  · exact h.resolve_left hab
  · obtain ⟨e,he⟩ := six_two_ear_model_embedding f hcycle hx hy hz hw
      hxy hxz hxw hyz hyw hzw hxa hxyadj hyb a b hza hzwadj hwb
    exact False.elim (noLongCycle_excludes_word_embedding hshort e he _ hc hlen)

end Cycle12
