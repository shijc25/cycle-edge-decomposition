import Cycle12.CycleWord
import Cycle12.Foundations.LongCycleRemoval

namespace Cycle12.TerminalCert
open SimpleGraph Finset Cycle13
variable {V : Type} [Fintype V] [DecidableEq V]

def graph (E : Finset (Sym2 V)) : SimpleGraph V := SimpleGraph.fromEdgeSet E

instance (E : Finset (Sym2 V)) : DecidableRel (graph E).Adj :=
  fun u v => inferInstanceAs (Decidable (s(u,v) ∈ E ∧ u ≠ v))

def covered {d : ℕ} (words : Fin d → CycleWord V) : Finset (Sym2 V) :=
  Finset.univ.biUnion fun i => (words i).edges

def Valid {d : ℕ} (E : Finset (Sym2 V)) (words : Fin d → CycleWord V) : Prop :=
  (∀ e ∈ E, ¬e.IsDiag) ∧ (∀ i, (words i).Valid (graph E)) ∧
    Pairwise (fun i j => Disjoint (words i).edges (words j).edges)

instance {d : ℕ} (E : Finset (Sym2 V)) (words : Fin d → CycleWord V) :
    Decidable (Valid E words) := by
  unfold Valid Pairwise
  infer_instance

theorem edgeSet_graph (E : Finset (Sym2 V)) (hE : ∀ e ∈ E, ¬e.IsDiag) :
    (graph E).edgeSet=(E:Set (Sym2 V)) := by
  rw [graph,SimpleGraph.edgeSet_fromEdgeSet]
  apply sdiff_eq_left.mpr
  exact Set.disjoint_left.mpr (fun e he hd => hE e he hd)

noncomputable def packing {d : ℕ} (E : Finset (Sym2 V)) (words : Fin d → CycleWord V)
    (hc : Valid E words) : Cycle13.CyclePacking (graph E) :=
  Cycle13.CyclePacking.ofIndexed (fun i => ((words i).edges:Set (Sym2 V)))
    (fun i => ⟨(words i).root,(words i).toWalk (graph E) (hc.2.1 i),
      (words i).isCycle_toWalk _ _,((words i).edgeSet_toWalk _ _).symm⟩)
    (fun _ _ hij => Finset.disjoint_coe.mpr (hc.2.2 hij))

theorem packing_used {d : ℕ} (E : Finset (Sym2 V)) (words : Fin d → CycleWord V)
    (hc : Valid E words) : (packing E words hc).used=(covered words:Set (Sym2 V)) := by
  unfold packing
  erw [Cycle13.CyclePacking.used_ofIndexed]
  ext e
  simp [covered]

theorem packing_cost {d : ℕ} (E : Finset (Sym2 V)) (words : Fin d → CycleWord V)
    (hc : Valid E words) :
    (packing E words hc).cost=42*d+23*(E\covered words).card := by
  have hcount : (packing E words hc).count=d := by
    simp [packing,Cycle13.CyclePacking.ofIndexed]
  have hsingles : (packing E words hc).singles=(E\covered words).card := by
    rw [Cycle13.CyclePacking.singles,Cycle13.CyclePacking.residue,
      SimpleGraph.edgeSet_deleteEdges,packing_used,edgeSet_graph E hc.1,
      ← Finset.coe_sdiff,Set.ncard_coe_finset]
  simp only [Cycle13.CyclePacking.cost,hcount,hsingles]

/-- A decidable finite certificate yields a packing of actual simple cycles;
every uncovered edge is counted explicitly with integer weight 23. -/
theorem sound {d b : ℕ} (E : Finset (Sym2 V)) (words : Fin d → CycleWord V)
    (hc : Valid E words) (hcost : 42*d+23*(E\covered words).card ≤ b) :
    ∃ P : Cycle13.CyclePacking (graph E), P.cost ≤ b :=
  ⟨packing E words hc,by rw [packing_cost]; exact hcost⟩

theorem long_cycle_excludes (E : Finset (Sym2 V)) (c : CycleWord V)
    (hc : c.Valid (graph E)) (hlen : 7 ≤ c.tail.length+1) :
    ¬NoCycleAtLeast (graph E) 7 := by
  intro hshort
  have hbad := hshort c.root (c.toWalk (graph E) hc) (c.isCycle_toWalk _ _)
  rw [c.length_toWalk] at hbad
  omega

end Cycle12.TerminalCert
