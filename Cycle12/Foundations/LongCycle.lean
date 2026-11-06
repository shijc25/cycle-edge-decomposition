import Cycle12.Independent.ErdosGallai
import Cycle12.Foundations.PackingEraseCycle

namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

/-- The sharp Erdős--Gallai long-cycle bound, obtained from the independent
Woodall rotation and deletion proof. Its edge bound uses n-1, which matters
when rounding the n/2 greedy cycle budget. -/
theorem exists_cycle_with_edge_bound (G : SimpleGraph V)
    (hm : Fintype.card V-1 < G.edgeSet.ncard) :
    ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧
      2*G.edgeSet.ncard ≤ p.length*(Fintype.card V-1) := by
  have he : G.edgeFinset.card=G.edgeSet.ncard := by
    rw [G.edgeFinset_card,Set.fintypeCard_eq_ncard]
  have hex : ∃ (v : V) (p : G.Walk v v), p.IsCycle := by
    by_contra hnot
    push_neg at hnot
    have hb := Cycle12.Independent.erdosGallai_cycle G 2 (by omega)
      (fun v p hp => (hnot v p hp).elim)
    rw [he] at hb
    omega
  obtain ⟨v,p,hp⟩ := hex
  let lengths := (range (Fintype.card V+1)).filter
    (fun k => ∃ (u : V) (q : G.Walk u u), q.IsCycle ∧ q.length = k)
  have hmem : ∀ (u : V) (q : G.Walk u u), q.IsCycle → q.length ∈ lengths := by
    intro u q hq
    exact mem_filter.mpr ⟨mem_range.mpr (by have := cycle_length_le_order hq; omega),u,q,hq,rfl⟩
  obtain ⟨k,hk,hmax⟩ := exists_max_image lengths id ⟨p.length,hmem v p hp⟩
  obtain ⟨u,q,hq,hqk⟩ := (mem_filter.mp hk).2
  subst k
  have hb := Cycle12.Independent.erdosGallai_cycle G q.length
    (by have hh := hq.three_le_length; omega) (fun z r hr => by
      simpa only [id_eq] using hmax r.length (hmem z r hr))
  rw [he] at hb
  exact ⟨u,q,hq,hb⟩

end
end Cycle13
