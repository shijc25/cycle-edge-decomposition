import Euler.Orientation
import Cycle12.Foundations.SuppressionCounts

/-! A simple incidence subdivision of an indexed loopless multigraph.
Parallel edges have distinct internal vertices, so their degrees are retained. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

def edgeIncidenceGraph (a b : I → V) : SimpleGraph (V⊕I) where
  Adj
    | .inl v, .inr i => v=a i ∨ v=b i
    | .inr i, .inl v => v=a i ∨ v=b i
    | _,_ => False
  symm := ⟨by intro x y h; cases x <;> cases y <;> exact h⟩
  loopless := ⟨by intro x; cases x <;> exact id⟩

theorem incidence_original_degree (a b : I → V) (hne : ∀ i, a i≠b i) (v : V) :
    (edgeIncidenceGraph a b).degree (.inl v)=Suppression.incidenceDegree a b v := by
  have he : (edgeIncidenceGraph a b).neighborSet (.inl v)=
      Sum.inr '' {i : I | a i=v ∨ b i=v} := by
    ext x
    cases x with
    | inl w => simp [edgeIncidenceGraph,mem_neighborSet]
    | inr i => simp [edgeIncidenceGraph,mem_neighborSet,eq_comm]
  have hd : Disjoint {i : I | a i=v} {i : I | b i=v} := by
    apply Set.disjoint_left.mpr
    intro i hi hj
    exact hne i (hi.trans hj.symm)
  rw [← ncard_neighborSet,he,Set.ncard_image_of_injective _ Sum.inr_injective]
  change ({i : I | a i=v} ∪ {i : I | b i=v}).ncard=_
  rw [Set.ncard_union_eq hd]
  unfold Suppression.incidenceDegree
  rw [sum_add_distrib]
  simp only [sum_boole]
  congr 1 <;> simp only [Set.ncard_eq_toFinset_card',Set.toFinset,Finset.card_map]
  · rw [← Fintype.card_subtype]
    exact Fintype.card_congr (Equiv.refl _)
  · rw [← Fintype.card_subtype]
    exact Fintype.card_congr (Equiv.refl _)

theorem incidence_internal_degree (a b : I → V) (hne : ∀ i, a i≠b i) (i : I) :
    (edgeIncidenceGraph a b).degree (.inr i)=2 := by
  have he : (edgeIncidenceGraph a b).neighborSet (.inr i)=
      {Sum.inl (a i),Sum.inl (b i)} := by
    ext x
    cases x with
    | inl v => simp [edgeIncidenceGraph,mem_neighborSet]
    | inr j => simp [edgeIncidenceGraph,mem_neighborSet]
  rw [← ncard_neighborSet,he,Set.ncard_pair (Sum.inl_injective.ne (hne i))]

theorem incidence_even (a b : I → V) (hne : ∀ i, a i≠b i)
    (heven : ∀ v, Even (Suppression.incidenceDegree a b v)) :
    ∀ x, Even ((edgeIncidenceGraph a b).degree x) := by
  intro x
  cases x with
  | inl v => rw [incidence_original_degree a b hne]; exact heven v
  | inr i => rw [incidence_internal_degree a b hne]; decide

theorem orientation_incidence_count {W : Type} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) (D : Finset G.Dart) (hi : EdgeInj D)
    (hc : ∀ e∈G.edgeSet, ∃ d∈D, d.edge=e) (v : W) :
    (D.filter (fun d => d.fst=v)).card+(D.filter (fun d => d.snd=v)).card=G.degree v := by
  have he : D.image Dart.edge=G.edgeFinset := by
    ext e
    constructor
    · rintro he
      obtain ⟨d,hd,rfl⟩ := mem_image.mp he
      exact G.mem_edgeFinset.mpr d.edge_mem
    · intro he
      obtain ⟨d,hd,hde⟩ := hc e (G.mem_edgeFinset.mp he)
      exact mem_image.mpr ⟨d,hd,hde⟩
  have hh := card_image_edge_filter hi v
  rw [he] at hh
  have heq : (G.edgeFinset.filter (fun e => v∈e))=G.incidenceFinset v := by
    ext e
    simp [mem_filter,mem_incidenceFinset,SimpleGraph.incidenceSet]
  rw [heq,G.card_incidenceFinset_eq_degree] at hh
  exact hh.symm

end
end Cycle13
