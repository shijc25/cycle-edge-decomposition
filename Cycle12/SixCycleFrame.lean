import Cycle12.ShortCycleExterior

namespace Cycle12
open SimpleGraph
variable {V : Type} {G : SimpleGraph V}

/-- Six distinct labels in the cyclic order of the actual simple walk. -/
theorem six_cycle_frame_precise {u : V} {c : G.Walk u u} (hc : c.IsCycle) (hlen : c.length=6) :
    ∃ f : Fin 6 ↪ V, (∀ i, G.Adj (f i) (f (i+1))) ∧
      (∀ x, x∈c.support ↔ ∃ i, f i=x) ∧ (∀ i, f i=c.getVert i.val) := by
  let f : Fin 6 ↪ V := ⟨fun i => c.getVert i.val,by
    intro i j he
    apply Fin.ext
    exact hc.getVert_injOn' (by have := i.isLt; simp only [Set.mem_setOf_eq]; omega)
      (by have := j.isLt; simp only [Set.mem_setOf_eq]; omega) he⟩
  refine ⟨f,?_,?_,by intro i; rfl⟩
  · intro i
    fin_cases i
    · exact c.adj_getVert_succ (i:=0) (by omega)
    · exact c.adj_getVert_succ (i:=1) (by omega)
    · exact c.adj_getVert_succ (i:=2) (by omega)
    · exact c.adj_getVert_succ (i:=3) (by omega)
    · exact c.adj_getVert_succ (i:=4) (by omega)
    · have hh := c.adj_getVert_succ (i:=5) (by omega)
      change G.Adj (c.getVert 5) (c.getVert 0)
      simpa only [show 5+1=c.length by omega,Walk.getVert_length,Walk.getVert_zero] using hh
  · intro x
    constructor
    · intro hx
      obtain ⟨i,hi,hbound⟩ := Walk.mem_support_iff_exists_getVert.mp hx
      by_cases hlt : i<6
      · exact ⟨⟨i,hlt⟩,hi⟩
      · have hi6 : i=c.length := by omega
        refine ⟨0,?_⟩
        change c.getVert 0=x
        simpa only [hi6,Walk.getVert_length,Walk.getVert_zero] using hi
    · rintro ⟨i,rfl⟩
      exact c.getVert_mem_support i.val

theorem six_cycle_frame {u : V} {c : G.Walk u u} (hc : c.IsCycle) (hlen : c.length=6) :
    ∃ f : Fin 6 ↪ V, (∀ i, G.Adj (f i) (f (i+1))) ∧
      (∀ x, x∈c.support ↔ ∃ i, f i=x) := by
  obtain ⟨f,hcycle,hsupport,_⟩ := six_cycle_frame_precise hc hlen
  exact ⟨f,hcycle,hsupport⟩

end Cycle12
