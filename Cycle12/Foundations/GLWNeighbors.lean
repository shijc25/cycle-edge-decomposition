import Cycle12.Foundations.PrefixRho

/-! The actual external neighborhood used in the clone graph at a state. -/
namespace Cycle13
open SimpleGraph Finset PrefixVertices
noncomputable section
attribute [local instance] Classical.propDecidable

namespace GLWState
variable {X : Type} [Fintype X] [DecidableEq X] {p j : ℕ}
    {G : SimpleGraph (X ⊕ Fin p)} {rho : ℕ → ℕ} {hj : j+1≤p}
    (A : GLWState G rho (j+1) hj)

def neighbors : Set {v : X ⊕ Fin (j+1) // v≠lastVertex j} :=
  {v | v∈survivingExternal j ∧ 0<A.routes.multiplicity (lastVertex j) v.val}

theorem neighbors_subset : A.neighbors⊆survivingExternal j := fun _ h => h.1

theorem port_mem_neighbors (i : A.routes.Ports (lastVertex j))
    (hi : A.routes.portTip (lastVertex j) i∈survivingExternal j) :
    A.routes.portTip (lastVertex j) i∈A.neighbors := by
  refine ⟨hi,?_⟩
  exact (A.routes.multiplicity_pos_iff _ _).mpr
    ⟨i.val,(A.routes.portTip_eq_iff (lastVertex j) i _).mp rfl⟩

theorem neighbor_mult_pos (x : A.neighbors) :
    0<A.routes.multiplicity (lastVertex j) x.val.val := x.property.2

theorem neighbor_mult_le_two (x : A.neighbors) :
    A.routes.multiplicity (lastVertex j) x.val.val≤2 := by
  obtain ⟨v,hv⟩ := x.property.1
  rw [← hv,A.routes.multiplicity_symm]
  exact A.crossing v (Fin.last j)

def cloneAuxiliary : SimpleGraph (A.neighbors ⊕ A.routes.doubleExternal (lastVertex j) A.neighbors) :=
  cloneGraph (A.routes.externalGraph (lastVertex j) A.neighbors)
    (A.routes.doubleExternal (lastVertex j) A.neighbors)

theorem exists_wellStep_of_perfect (hG : ∀ v, Even (G.degree v))
    (hrho : rho j≤rho (j+1))
    (hperfect : GallaiEdmonds.HasPerfectMatchingOn A.cloneAuxiliaryᶜ Set.univ) :
    Nonempty (GLWState G rho j (Nat.le_trans (Nat.le_succ j) hj)) := by
  have heven : Even (A.routes.degree (lastVertex j)) := by rw [A.degrees]; exact hG _
  have hs : A.routes.SimpleOn (Subtype.val '' survivingExternal j) := by
    rw [survivingExternal_image]
    exact A.external_simple
  obtain ⟨N,hN,hcover,hs',hc,_⟩ := A.routes.well_suppression_of_clone_perfect (lastVertex j)
    (survivingExternal j) A.neighbors A.neighbors_subset A.port_mem_neighbors
    A.neighbor_mult_pos A.neighbor_mult_le_two heven hs hperfect
  exact ⟨A.wellStep N hN hcover hs' hc hrho⟩

end GLWState
end
end Cycle13
