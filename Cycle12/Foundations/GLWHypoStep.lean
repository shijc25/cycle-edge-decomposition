import Cycle12.Foundations.GLWInternalPorts

/-! A hypomatchable clone complement cannot stop the process when a fresh
external neighbor exists. This closes the near-well-suppression state step. -/
namespace Cycle13
open SimpleGraph Finset PrefixVertices
noncomputable section
attribute [local instance] Classical.propDecidable

namespace GLWState
variable {X : Type} [Fintype X] [DecidableEq X] {p j : ℕ}
    {G : SimpleGraph (X ⊕ Fin p)} {hj : j+1≤p} (hp : 0<p)
    (A : GLWState G (prefixRho G hp) (j+1) hj)

theorem exists_nearStep_of_hypomatchable (hG : ∀ v, Even (G.degree v))
    (x₀ : X) (hx : keep j (Sum.inl x₀)∈A.neighbors) (hfresh : x₀∉A.used)
    (hhypo : Hypomatchable A.cloneAuxiliaryᶜ) :
    Nonempty (GLWState G (prefixRho G hp) j (Nat.le_trans (Nat.le_succ j) hj)) := by
  let x : A.neighbors := ⟨keep j (Sum.inl x₀),hx⟩
  have hnear := hhypo (Sum.inl x)
  have heven : Even (A.routes.degree (lastVertex j)) := by rw [A.degrees]; exact hG _
  have hs : A.routes.SimpleOn (Subtype.val '' survivingExternal j) := by
    rw [survivingExternal_image]
    exact A.external_simple
  obtain ⟨M,a,hM,hatip,ha,hcov,hends,hloop,hi,habsent⟩ :=
    A.routes.near_port_matching_of_clone_near (lastVertex j) (survivingExternal j) A.neighbors
      A.neighbors_subset A.port_mem_neighbors A.neighbor_mult_pos A.neighbor_mult_le_two x hnear
  have hex := A.routes.exists_internal_port_of_near_matching (lastVertex j) (survivingExternal j)
    M hM a ha hcov heven
  obtain ⟨s,b,hbtip,hmin⟩ := A.exists_first_internal_port hex
  have hb : A.routes.portTip (lastVertex j) b∉survivingExternal j := by
    rw [hbtip,keep_mem_survivingExternal]
    exact inr_not_mem_external j s
  have haS : A.routes.portTip (lastVertex j) a∈survivingExternal j := by
    rw [hatip]
    exact hx.1
  obtain ⟨N,hN,hNv,_,hNs,hcross,_⟩ := A.routes.exists_near_controlled_suppression
    (lastVertex j) (survivingExternal j) M hM a b haS hb ha hcov hends hloop hi habsent heven hs
  have hc : ∀ u v, u∈survivingExternal j → v∉survivingExternal j →
      (A.routes.suppress (lastVertex j) N hN).multiplicity u v=
        A.routes.multiplicity u.val v.val+
          (if s(keep j (Sum.inl x₀),keep j (Sum.inr s))=s(u,v) then 1 else 0) := by
    simpa only [hatip,hbtip] using hcross
  have hinc : s.val≠0 → prefixRho G hp (j+1)=prefixRho G hp j+1 := by
    intro hs0
    exact prefixRho_succ_of_not_adj G hp hj (A.root_nonadj_of_first_internal hp s hmin hs0)
  exact ⟨A.nearStep N hN hNv hNs x₀ s hfresh (A.stepped_cross_increment N hN x₀ s hc)
    (prefixRho_monotone G hp (Nat.le_succ j)) (prefixRho_monotone G hp hj) hinc⟩

end GLWState
end
end Cycle13
