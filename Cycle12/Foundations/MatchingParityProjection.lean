import Cycle12.Foundations.MinimalDegree
import Cycle12.Foundations.MatchingPorts

/-! Project a matching to a simple graph by cancelling pairs of repeated
edges. Loops contribute two incidences and vanish; all degree parities persist. -/
namespace Cycle13
open SimpleGraph Finset
open scoped symmDiff
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem single_edge_degree_at_left (x y : V) (hxy : x≠y) : (edge x y).degree x=1 := by
  rw [← ncard_neighborSet]
  have he : (edge x y).neighborSet x={y} := by
    ext w
    simp only [mem_neighborSet,edge_adj,Set.mem_singleton_iff]
    aesop
  rw [he,Set.ncard_singleton]

theorem single_edge_incidence_balance (x y v : V) :
    (edge x y).degree v+2*(if x=v ∧ y=v then 1 else 0)=
      (if x=v then 1 else 0)+(if y=v then 1 else 0) := by
  by_cases hxy : x=y
  · subst y
    simp only [← ncard_neighborSet,edge_self_eq_bot,neighborSet_bot,Set.ncard_empty,and_self]
    split_ifs <;> omega
  by_cases hx : x=v
  · subst v
    rw [single_edge_degree_at_left x y hxy]
    simp [(Ne.symm hxy)]
  by_cases hy : y=v
  · subst v
    have hd : (edge x y).degree y=1 := by
      simp only [← ncard_neighborSet,edge_comm x y]
      simpa only [← ncard_neighborSet] using single_edge_degree_at_left y x (Ne.symm hxy)
    rw [hd]
    simp [hxy]
  rw [single_edge_degree_zero x y v (Ne.symm hx) (Ne.symm hy)]
  simp [hx,hy]

theorem exists_parity_projection {I : Type} [DecidableEq I] (G : SimpleGraph V)
    (a b : I → V) (S : Finset I) (hedge : ∀ i∈S, a i=b i ∨ G.Adj (a i) (b i)) :
    ∃ F : SimpleGraph V, F ≤ G ∧ ∀ v,
      F.degree v ≤ ∑ i∈S, ((if a i=v then 1 else 0)+(if b i=v then 1 else 0)) ∧
      (Even (F.degree v) ↔
        Even (∑ i∈S, ((if a i=v then 1 else 0)+(if b i=v then 1 else 0)))) := by
  induction S using Finset.induction_on with
  | empty => exact ⟨⊥,bot_le,by simp⟩
  | @insert i S hi ih =>
    obtain ⟨F,hFG,hF⟩ := ih (fun j hj => hedge j (mem_insert_of_mem hj))
    have hE : edge (a i) (b i) ≤ G := G.edge_le_iff.mpr (hedge i (mem_insert_self _ _))
    refine ⟨F ∆ edge (a i) (b i),symmDiff_le_sup.trans (sup_le hFG hE),?_⟩
    intro v
    have hb := graph_symmDiff_degree_balance F (edge (a i) (b i)) v
    have he := single_edge_incidence_balance (a i) (b i) v
    have hf := hF v
    rw [sum_insert hi]
    simp only [← ncard_neighborSet] at hb he hf ⊢
    constructor
    · omega
    · simp only [Nat.even_iff] at hf ⊢
      omega

theorem matching_parity_projection {I : Type} [Fintype I] [DecidableEq I]
    {H : SimpleGraph I} (G : SimpleGraph V) (M : H.Subgraph)
    (hM : M.IsMatching) (hcover : M.verts=Set.univ) (o : I → V)
    (hedge : ∀ x y, M.Adj x y → o x=o y ∨ G.Adj (o x) (o y)) :
    ∃ F : SimpleGraph V, F ≤ G ∧ ∀ v,
      F.degree v ≤ (univ.filter (fun i : I => o i=v)).card ∧
      (Even (F.degree v) ↔ Even ((univ.filter (fun i : I => o i=v)).card)) := by
  obtain ⟨F,hFG,hF⟩ := exists_parity_projection G
    (fun e : M.edgeSet => o e.val.out.1) (fun e : M.edgeSet => o e.val.out.2) univ
    (fun e _ => hedge _ _ (edge_out_adj M.spanningCoe e))
  refine ⟨F,hFG,fun v => ?_⟩
  have hc := matching_output_incidence M hM o v
  have he : (univ.filter (fun i : M.verts => o i.val=v)).card=
      (univ.filter (fun i : I => o i=v)).card := by
    rw [← Fintype.card_subtype,← Fintype.card_subtype]
    apply Fintype.card_congr
    exact {
      toFun i := ⟨i.val.val,i.property⟩
      invFun i := ⟨⟨i.val,by rw [hcover]; trivial⟩,i.property⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  rw [he] at hc
  simpa only [hc] using hF v

end
end Cycle13
