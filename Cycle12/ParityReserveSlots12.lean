import Cycle12.ReserveSlots12
import Cycle12.PackingCompletionLedger12
import Cycle12.FirstPassLedger12

namespace Cycle12
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V]

def parityDoubleRoots (G : SimpleGraph V) (D O : Finset V) : Finset V :=
  D∪O.filter (fun v => ¬Even (G.degree v))

def paritySingleRoots (G : SimpleGraph V) (O : Finset V) : Finset V :=
  O.filter (fun v => Even (G.degree v))

theorem parity_reserve_roots_disjoint (G : SimpleGraph V) (D O : Finset V)
    (hDO : Disjoint D O) : Disjoint (parityDoubleRoots G D O) (paritySingleRoots G O) := by
  apply Finset.disjoint_left.mpr
  intro v hv hw
  obtain ⟨hvO,he⟩ := mem_filter.mp hw
  rcases mem_union.mp hv with hvD | hvN
  · exact Finset.disjoint_left.mp hDO hvD hvO
  · exact (mem_filter.mp hvN).2 he

theorem parity_reserve_roots_outside (G : SimpleGraph V) (D O C : Finset V)
    (hDC : Disjoint D C) (hOC : Disjoint O C) :
    Disjoint (parityDoubleRoots G D O) C ∧ Disjoint (paritySingleRoots G O) C := by
  exact ⟨Finset.disjoint_union_left.mpr ⟨hDC,hOC.mono_left (filter_subset _ _)⟩,
    hOC.mono_left (filter_subset _ _)⟩

/-- Even outside vertices reserve one spoke, odd outside vertices two.
The total number and local multiplicity still obey the existing bounds. -/
theorem parity_reserve_fiber (G : SimpleGraph V) (D O : Finset V) (v : V)
    (hvD : v∉D) (hvO : v∈O) :
    Fintype.card {j // reserveRoot (parityDoubleRoots G D O) (paritySingleRoots G O) j=v}=
      if Even (G.degree v) then 1 else 2 := by
  rw [reserveRoot_fiber_card]
  by_cases he : Even (G.degree v) <;> simp [parityDoubleRoots,paritySingleRoots,hvD,hvO,he]

theorem parity_reserve_slots_at_least (G : SimpleGraph V) (D O : Finset V) (v : V)
    (hv : v∈D ∨ v∈O) :
    (if v∈D then 2 else 1)≤
      Fintype.card {j // reserveRoot (parityDoubleRoots G D O) (paritySingleRoots G O) j=v} := by
  rw [reserveRoot_fiber_card]
  by_cases hvD : v∈D
  · simp only [parityDoubleRoots,mem_union,hvD,true_or,ite_true]
    omega
  · have hvO := hv.resolve_left hvD
    by_cases he : Even (G.degree v)
    · simp [parityDoubleRoots,paritySingleRoots,hvD,hvO,he]
    · have ho := Nat.not_even_iff_odd.mp he
      simp [parityDoubleRoots,paritySingleRoots,hvD,hvO,he,ho]

theorem parity_first_pass_outside_odd {G R : SimpleGraph V} (U : Finset V)
    (P : CyclePacking G) (hR : R≤P.residue) (v : V) (hv : v∉U)
    (hRv : R.degree v=if Even (G.degree v) then 1 else 2) :
    Odd ((P.residue.deleteEdges (R.edgeSet∪(insideGraph G U).edgeSet)).degree v) := by
  have hp := packing_residue_parity P v
  have hd := delete_reserve_degree P.residue R (insideGraph G U) hR v (fun w h => hv h.2.1)
  rw [hRv] at hd
  by_cases he : Even (G.degree v)
  · have hpE := hp.mpr he
    rw [ite_eq_left he] at hd
    simp only [Nat.even_iff] at hpE
    rw [Nat.odd_iff]
    omega
  · have hpN : ¬Even (P.residue.degree v) := fun h => he (hp.mp h)
    rw [ite_eq_right he] at hd
    simp only [Nat.even_iff] at hpN
    rw [Nat.odd_iff]
    omega

/-- After both passes, outside even vertices disappear and outside odd
vertices have exactly one residual incident edge. -/
theorem parity_graph_outside_degree (G H R : SimpleGraph V) (U : Finset V)
    (hcover : H.edgeSet⊆R.edgeSet∪(insideGraph G U).edgeSet)
    (hR : ∀ v,v∉U → R.degree v=if Even (G.degree v) then 1 else 2)
    (hparity : ∀ v,Even (H.degree v) ↔ Even (G.degree v)) :
    ∀ v,v∉U → H.degree v=if Even (G.degree v) then 0 else 1 := by
  intro v hv
  have hs : H.neighborFinset v⊆R.neighborFinset v := by
    intro w hw
    have hH := (H.mem_neighborFinset v w).mp hw
    rcases hcover (show s(v,w)∈H.edgeSet from hH) with h | h
    · exact (R.mem_neighborFinset v w).mpr h
    · exact False.elim (hv h.2.1)
  have hb := card_le_card hs
  rw [card_neighborFinset_eq_degree,card_neighborFinset_eq_degree,hR v hv] at hb
  by_cases he : Even (G.degree v)
  · have hp := (hparity v).mpr he
    rw [ite_eq_left he] at hb ⊢
    rw [Nat.even_iff] at hp
    omega
  · have hp : ¬Even (H.degree v) := fun h => he ((hparity v).mp h)
    rw [ite_eq_right he] at hb ⊢
    simp only [Nat.even_iff] at hp
    omega

end
end Cycle12
