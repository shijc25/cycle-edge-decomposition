import Cycle12.Foundations.GLWNeighborCounts

/-! The finite minimal-state argument and the actual clone obstruction at
the stopping state. Both perfect and hypomatchable alternatives are ruled
out by the proved state transitions. -/
namespace Cycle13
open SimpleGraph Finset PrefixVertices
noncomputable section
attribute [local instance] Classical.propDecidable

namespace GLWState
variable {X : Type} [Fintype X] [DecidableEq X] {p : ℕ}
    {G : SimpleGraph (X ⊕ Fin p)} {rho : ℕ → ℕ}

theorem exists_terminal (hzero : ∀ A : GLWState G rho 0 (Nat.zero_le p), False) :
    ∃ j : ℕ, ∃ hj : j+1≤p, ∃ A : GLWState G rho (j+1) hj,
      ¬Nonempty (GLWState G rho j (Nat.le_trans (Nat.le_succ j) hj)) := by
  let P := fun k => ∃ hk : k≤p, Nonempty (GLWState G rho k hk)
  have hex : ∃ k, P k := ⟨p,Nat.le_refl _,⟨initial G rho⟩⟩
  have hP := Nat.find_spec hex
  have hpos : 0<Nat.find hex := by
    by_contra hn
    have hz : Nat.find hex=0 := by omega
    have hP0 : P 0 := hz ▸ hP
    obtain ⟨_,⟨A⟩⟩ := hP0
    exact hzero A
  obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  have hPj : P (j+1) := Eq.mp (congrArg P hj) hP
  obtain ⟨hk,⟨A⟩⟩ := hPj
  refine ⟨j,hk,A,?_⟩
  intro h
  have hm := Nat.find_min' hex (show P j from ⟨Nat.le_trans (Nat.le_succ j) hk,h⟩)
  omega

theorem no_zero_of_minimality [Nonempty X] (hp : 0<p) {d t : ℕ}
    (hbad : ¬HasBudgetedClique t G) (heven : ∀ v, Even (G.degree v))
    (hdef : degreeDeficiency G d<d)
    (hminimal : ∀ H : SimpleGraph (X ⊕ Fin 0),
      (∀ v, Even (H.degree v)) → degreeDeficiency H d<d → HasBudgetedClique t H)
    (A : GLWState G rho 0 (Nat.zero_le p)) : False := by
  have hsmall : Fintype.card (X ⊕ Fin 0)<Fintype.card (X ⊕ Fin p) := by
    simp only [Fintype.card_sum,Fintype.card_fin]
    omega
  exact no_simple_reduction_of_minimality A.routes hbad heven hdef A.degrees hsmall
    (fun H _ => hminimal H) A.zero_simple

variable {j : ℕ} {hj : j+1≤p} (hp : 0<p)
    (A : GLWState G (prefixRho G hp) (j+1) hj)

theorem no_strong_external {t : ℕ} (hbad : ¬HasBudgetedClique t G) :
    ¬Nonempty (StrongCliqueImmersion t (A.routes.externalGraph (lastVertex j) A.neighbors)) := by
  rintro ⟨M⟩
  let F : (A.routes.externalGraph (lastVertex j) A.neighbors).Copy A.routes.graph := {
    toHom := { toFun := fun x => x.val.val, map_rel' := fun h => h }
    injective' := fun _ _ h => Subtype.ext (Subtype.ext h) }
  obtain ⟨hm⟩ := A.routes.clique_lifts (M.mapCopy F)
  exact hbad (hasBudgetedClique_of_strong hm)

theorem terminal_has_small_block {t : ℕ} (hpt : p<t)
    (hbad : ¬HasBudgetedClique t G) (heven : ∀ v, Even (G.degree v))
    (hstop : ¬Nonempty (GLWState G (prefixRho G hp) j (Nat.le_trans (Nat.le_succ j) hj)))
    (hsize : 3*t+2*(A.routes.doubleExternal (lastVertex j) A.neighbors).card≤
      Fintype.card A.neighbors) :
    ∃ B : Set A.neighbors, B.Nonempty ∧ B.ncard<t ∧
      ∀ v∈B, (A.routes.externalGraph (lastVertex j) A.neighbors)ᶜ.degree v≤
        B.ncard+(A.routes.doubleExternal (lastVertex j) A.neighbors).card := by
  have ht : 0<t := hp.trans hpt
  have hD := A.doubleExternal_card_le_removed
  have hDt : (A.routes.doubleExternal (lastVertex j) A.neighbors).card<t := by omega
  have hperfect : ¬GallaiEdmonds.HasPerfectMatchingOn A.cloneAuxiliaryᶜ Set.univ := by
    intro h
    exact hstop (A.exists_wellStep_of_perfect heven (prefixRho_monotone G hp (Nat.le_succ j)) h)
  have hhypo : ¬Hypomatchable A.cloneAuxiliaryᶜ := by
    intro h
    have hc : A.used.card<Fintype.card A.neighbors := by
      have hu := A.used_card
      omega
    obtain ⟨x,hx,hfresh⟩ := A.exists_fresh_neighbor hc
    exact hstop (A.exists_nearStep_of_hypomatchable hp heven x hx hfresh h)
  exact clone_obstruction_small_block _ _ ht hsize hDt (A.no_strong_external hp hbad) hperfect hhypo

end GLWState
end
end Cycle13
