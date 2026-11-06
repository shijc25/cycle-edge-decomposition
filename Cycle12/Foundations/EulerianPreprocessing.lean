import Cycle12.Foundations.BoundedDegreeReduction
import Cycle12.Foundations.BoundedParity
import Cycle12.Foundations.DeletedComponentCuts
import Cycle12.Foundations.InducedDeficiency

/-! General graphs reduce to Eulerian graphs of small total deficiency.
The parity step uses a proved Tutte blowup, saving one degree and avoiding
the bounded-degree spanning-tree theorem. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable

theorem exists_eulerian_deficiency_reduction {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) {d t : ℕ} (hd : 2*t+10 ≤ d)
    (hmin : ∀ v, d+5 ≤ G.degree v)
    (hno : ¬Nonempty (StrongCliqueImmersion t G)) :
    ∃ m : ℕ, 0 < m ∧ ∃ H : SimpleGraph (Fin m), Nonempty (EdgeRouting H G) ∧
      (∀ v, Even (H.degree v)) ∧ degreeDeficiency H d<d := by
  obtain ⟨n,hn,K,⟨R⟩,hK⟩ := exists_bounded_degree_reduction G
    (by omega : 0<d+5) hmin hno
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  obtain ⟨S,hS,hboundary,hconn,hcut⟩ := exists_small_boundary_connected_core K (by omega : 0<d)
  let J := K.induce (S : Set (Fin n))
  have hJdeg : ∀ v : S, J.degree v ≤ d+5+t := by
    intro v
    exact (comap_degree_le K (Function.Embedding.subtype (· ∈ (S : Set (Fin n)))) v).trans (hK v).2
  have hcomp : ∀ U : Set S, U.Nonempty →
      Nat.card (J.induce Uᶜ).ConnectedComponent ≤ 3*U.ncard :=
    deleted_components_set_bound J (by omega : 0<d) (by omega : 2*(d+5+t) ≤ 3*d) hJdeg hcut
  obtain ⟨H,hHJ,heven,hloss⟩ := exists_even_remainder_loss_four J hconn.preconnected hcomp
  have hdef : degreeDeficiency H d<d := by
    apply (induced_deficiency_le_cut_of_loss K S H (k:=4) ?_ ?_).trans_lt hboundary
    · intro v hv
      have hh := (hK v).1
      omega
    · simpa only [← ncard_neighborSet] using hloss
  let f : H.Copy K := {
    toHom := {
      toFun := Subtype.val
      map_rel' := fun h => hHJ h }
    injective' := Subtype.val_injective }
  let e : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  refine ⟨Fintype.card S,by simpa only [Fintype.card_coe] using card_pos.mpr hS,H.comap e,
    ⟨R.compose ((EdgeRouting.ofCopy f).compose (EdgeRouting.ofCopy (graphRelabelIso H e).toCopy))⟩,?_,?_⟩
  · intro v
    rw [degree_comap_equiv]
    exact heven _
  · rw [deficiency_comap_equiv]
    exact hdef

theorem budgeted_clique_of_min_degree {V : Type} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) {t : ℕ} (ht : 4 ≤ t) (hteven : Even t)
    (hmin : ∀ v, 7*t+5 ≤ G.degree v) : HasBudgetedClique t G := by
  classical
  by_cases hs : Nonempty (StrongCliqueImmersion t G)
  · exact hasBudgetedClique_of_strong hs.some
  obtain ⟨n,hn,H,⟨R⟩,heven,hdef⟩ := exists_eulerian_deficiency_reduction G
    (by omega : 2*t+10 ≤ 7*t) hmin hs
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  exact (budgeted_clique_of_even_deficiency H ht hteven le_rfl heven hdef).lift R

end
end Cycle13
