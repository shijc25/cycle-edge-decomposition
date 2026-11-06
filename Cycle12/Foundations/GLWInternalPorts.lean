import Cycle12.Foundations.GLWNeighbors

/-! Select the first available internal port. If it is not the root,
the removed vertex was originally nonadjacent to the root, giving the
exact one-unit increase in the remaining non-root double-edge budget. -/
namespace Cycle13
open SimpleGraph Finset PrefixVertices
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RoutedEdges
theorem exists_port_of_adj {I V W : Type} [Fintype I] [DecidableEq I] [DecidableEq V]
    {G : SimpleGraph W} {φ : V ↪ W} (R : RoutedEdges G φ I) (z : V)
    (v : {v : V // v≠z}) (h : R.graph.Adj z v.val) : ∃ i, R.portTip z i=v := by
  have hp := (R.graph_adj_iff_multiplicity _ _).mp h |>.2
  rw [← R.portTip_fiber_card z v] at hp
  obtain ⟨i⟩ := Fintype.card_pos_iff.mp hp
  exact ⟨i.val,i.property⟩
end RoutedEdges

namespace PrefixVertices
theorem exists_internal_index {X : Type} {j : ℕ}
    (v : {v : X ⊕ Fin (j+1) // v≠lastVertex j}) (hv : v∉survivingExternal j) :
    ∃ i : Fin j, v=keep j (Sum.inr i) := by
  obtain ⟨w,rfl⟩ := (keep j).surjective v
  cases w with
  | inl x => exact False.elim (hv ((keep_mem_survivingExternal _).mpr ⟨x,rfl⟩))
  | inr i => exact ⟨i,rfl⟩
end PrefixVertices

namespace GLWState
variable {X : Type} [Fintype X] [DecidableEq X] {p j : ℕ}
    {G : SimpleGraph (X ⊕ Fin p)} {rho : ℕ → ℕ} {hj : j+1≤p}
    (A : GLWState G rho (j+1) hj)

theorem exists_first_internal_port
    (hex : ∃ b : A.routes.Ports (lastVertex j), A.routes.portTip (lastVertex j) b∉survivingExternal j) :
    ∃ s : Fin j, ∃ b : A.routes.Ports (lastVertex j),
      A.routes.portTip (lastVertex j) b=keep j (Sum.inr s) ∧
      ∀ i c, A.routes.portTip (lastVertex j) c=keep j (Sum.inr i) → s ≤ i := by
  let K : Finset (Fin j) := univ.filter (fun i =>
    ∃ b : A.routes.Ports (lastVertex j), A.routes.portTip (lastVertex j) b=keep j (Sum.inr i))
  have hK : K.Nonempty := by
    obtain ⟨b,hb⟩ := hex
    obtain ⟨i,hi⟩ := exists_internal_index (A.routes.portTip (lastVertex j) b) hb
    exact ⟨i,mem_filter.mpr ⟨mem_univ _,b,hi⟩⟩
  obtain ⟨b,hb⟩ := (mem_filter.mp (K.min'_mem hK)).2
  refine ⟨K.min' hK,b,hb,?_⟩
  intro i c hc
  exact K.min'_le i (mem_filter.mpr ⟨mem_univ _,c,hc⟩)

theorem root_nonadj_of_first_internal (hp : 0<p) (s : Fin j)
    (hmin : ∀ i c, A.routes.portTip (lastVertex j) c=keep j (Sum.inr i) → s ≤ i)
    (hs : s.val≠0) :
    ¬G.Adj (Sum.inr ⟨0,hp⟩) (Sum.inr ⟨j,hj⟩) := by
  intro hg
  have hjpos : 0<j := by have h := s.isLt; omega
  let i : Fin j := ⟨0,hjpos⟩
  have hR : A.routes.graph.Adj (lastVertex j) (keep j (Sum.inr i)).val := by
    apply A.originals
    exact hg.symm
  obtain ⟨c,hc⟩ := A.routes.exists_port_of_adj (lastVertex j) (keep j (Sum.inr i)) hR
  have h := hmin i c hc
  have hh : s.val≤0 := h
  omega

theorem stepped_cross_increment
    (N : (⊤ : SimpleGraph (A.routes.Ports (lastVertex j))).Subgraph) (hN : N.IsMatching)
    (x₀ : X) (s : Fin j)
    (hc : ∀ x y, x∈survivingExternal j → y∉survivingExternal j →
      (A.routes.suppress (lastVertex j) N hN).multiplicity x y=
        A.routes.multiplicity x.val y.val+
          (if s(keep j (Sum.inl x₀),keep j (Sum.inr s))=s(x,y) then 1 else 0))
    (x : X) (i : Fin j) :
    (A.stepped N hN).multiplicity (Sum.inl x) (Sum.inr i)=
      A.routes.multiplicity (Sum.inl x) (Sum.inr i.castSucc)+(if x=x₀ ∧ i=s then 1 else 0) := by
  rw [A.stepped_multiplicity N hN,hc]
  · congr 1
    congr 1
    simp only [Sym2.eq_iff,(keep j).injective.eq_iff,Sum.inl.injEq,Sum.inr.injEq,
      Sum.inl_ne_inr,Sum.inr_ne_inl,false_and,or_false]
    simp only [eq_comm]
  · exact (keep_mem_survivingExternal _).mpr ⟨x,rfl⟩
  · simpa only [keep_mem_survivingExternal] using inr_not_mem_external (X:=X) j i

end GLWState
end
end Cycle13
