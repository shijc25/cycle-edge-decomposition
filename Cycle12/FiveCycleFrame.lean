import Cycle12.ShortCycleExterior

namespace Cycle12
open SimpleGraph
variable {V : Type} {G : SimpleGraph V}

/-- A five-cycle labeled by Fin 5, with the exact support of the original walk. -/
theorem five_cycle_frame {u : V} {c : G.Walk u u} (hc : c.IsCycle) (hlen : c.length=5) :
    ∃ f : Fin 5 ↪ V, (∀ i, G.Adj (f i) (f (i+1))) ∧
      (∀ x, x∈c.support ↔ ∃ i, f i=x) := by
  let f : Fin 5 ↪ V := ⟨fun i => c.getVert i.val,by
    intro i j he
    apply Fin.ext
    exact hc.getVert_injOn' (by have := i.isLt; simp only [Set.mem_setOf_eq]; omega)
      (by have := j.isLt; simp only [Set.mem_setOf_eq]; omega) he⟩
  refine ⟨f,?_,?_⟩
  · intro i
    fin_cases i
    · exact c.adj_getVert_succ (i:=0) (by omega)
    · exact c.adj_getVert_succ (i:=1) (by omega)
    · exact c.adj_getVert_succ (i:=2) (by omega)
    · exact c.adj_getVert_succ (i:=3) (by omega)
    · have hh := c.adj_getVert_succ (i:=4) (by omega)
      change G.Adj (c.getVert 4) (c.getVert 0)
      simpa only [show 4+1=c.length by omega,Walk.getVert_length,Walk.getVert_zero] using hh
  · intro x
    constructor
    · intro hx
      obtain ⟨i,hi,hbound⟩ := Walk.mem_support_iff_exists_getVert.mp hx
      by_cases hlt : i<5
      · exact ⟨⟨i,hlt⟩,hi⟩
      · have hi5 : i=c.length := by omega
        refine ⟨0,?_⟩
        change c.getVert 0=x
        simpa only [hi5,Walk.getVert_length,Walk.getVert_zero] using hi
    · rintro ⟨i,rfl⟩
      exact c.getVert_mem_support i.val

end Cycle12
