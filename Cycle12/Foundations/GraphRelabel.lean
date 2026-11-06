import Cycle12.Foundations.SeedExtension

/-! Graph relabeling preserves degree deficiency and the budgeted clique
property; no model or minimum-order hypothesis is lost in canonical labels. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable

def graphRelabelIso {U V : Type} (G : SimpleGraph V) (e : U ≃ V) : G.comap e ≃g G where
  toEquiv := e
  map_rel_iff' := Iff.rfl

def neighborRelabelEquiv {U V : Type} (G : SimpleGraph V) (e : U ≃ V) (u : U) :
    (G.comap e).neighborSet u ≃ G.neighborSet (e u) where
  toFun v := ⟨e v.val,v.property⟩
  invFun v := ⟨e.symm v.val,by
    change G.Adj (e u) (e (e.symm v.val))
    rw [e.apply_symm_apply]
    exact v.property⟩
  left_inv v := Subtype.ext (e.symm_apply_apply v.val)
  right_inv v := Subtype.ext (e.apply_symm_apply v.val)

theorem neighbor_ncard_comap_equiv {U V : Type} (G : SimpleGraph V) (e : U ≃ V) (u : U) :
    ((G.comap e).neighborSet u).ncard=(G.neighborSet (e u)).ncard :=
  Nat.card_congr (neighborRelabelEquiv G e u)

theorem degree_comap_equiv {U V : Type}
    (G : SimpleGraph V) (e : U ≃ V) (u : U)
    [Fintype ((G.comap e).neighborSet u)] [Fintype (G.neighborSet (e u))] :
    (G.comap e).degree u=G.degree (e u) := by
  simpa only [ncard_neighborSet] using neighbor_ncard_comap_equiv G e u

theorem deficiency_comap_equiv {U V : Type} [Fintype U] [Fintype V]
    (G : SimpleGraph V) (e : U ≃ V) (d : ℕ) : degreeDeficiency (G.comap e) d=degreeDeficiency G d := by
  unfold degreeDeficiency
  simp_rw [← ncard_neighborSet,neighbor_ncard_comap_equiv G e]
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

theorem budgetedClique_comap_iff {U V : Type} [Fintype U] [Fintype V]
    (G : SimpleGraph V) (e : U ≃ V) (t : ℕ) : HasBudgetedClique t (G.comap e) ↔ HasBudgetedClique t G := by
  constructor
  · intro h
    exact h.lift (EdgeRouting.ofCopy (graphRelabelIso G e).toCopy)
  · intro h
    exact h.lift (EdgeRouting.ofCopy (graphRelabelIso G e).symm.toCopy)

def IsMinimumBad {V : Type} [Fintype V] (G : SimpleGraph V) (d t : ℕ) : Prop :=
  ∀ (U : Type) [Fintype U] [DecidableEq U] [Nonempty U] (H : SimpleGraph U),
    Fintype.card U<Fintype.card V → (∀ u, Even (H.degree u)) →
      degreeDeficiency H d<d → HasBudgetedClique t H

theorem isMinimumBad_of_fin_minimal {V : Type} [Fintype V]
    (G : SimpleGraph V) (d t : ℕ)
    (hmin : ∀ n, 0<n → n<Fintype.card V → ∀ H : SimpleGraph (Fin n),
      (∀ v, Even (H.degree v)) → degreeDeficiency H d<d → HasBudgetedClique t H) :
    IsMinimumBad G d t := by
  intro U _ _ _ H hcard heven hdef
  let e : Fin (Fintype.card U) ≃ U := (Fintype.equivFin U).symm
  have h := hmin (Fintype.card U) Fintype.card_pos hcard (H.comap e)
    (by intro u; simpa only [← ncard_neighborSet,neighbor_ncard_comap_equiv] using heven (e u))
    (by rwa [deficiency_comap_equiv])
  exact (budgetedClique_comap_iff H e t).mp h

theorem exists_minimum_bad {V : Type} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) {d t : ℕ} (heven : ∀ v, Even (G.degree v))
    (hdef : degreeDeficiency G d<d) (hbad : ¬HasBudgetedClique t G) :
    ∃ n : ℕ, ∃ H : SimpleGraph (Fin n), 0<n ∧
      (∀ v, Even (H.degree v)) ∧ degreeDeficiency H d<d ∧
      ¬HasBudgetedClique t H ∧ IsMinimumBad H d t := by
  let P := fun n => ∃ H : SimpleGraph (Fin n), 0<n ∧
    (∀ v, Even (H.degree v)) ∧ degreeDeficiency H d<d ∧ ¬HasBudgetedClique t H
  have hex : ∃ n, P n := by
    let e : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm
    refine ⟨Fintype.card V,G.comap e,Fintype.card_pos,?_,?_,?_⟩
    · intro u; simpa only [← ncard_neighborSet,neighbor_ncard_comap_equiv] using heven (e u)
    · rwa [deficiency_comap_equiv]
    · exact fun h => hbad ((budgetedClique_comap_iff G e t).mp h)
  obtain ⟨H,hn,hHe,hHd,hHb⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex,H,hn,hHe,hHd,hHb,?_⟩
  apply isMinimumBad_of_fin_minimal
  intro m hm hmn K hKe hKd
  by_contra hKb
  have hP : P m := ⟨K,hm,hKe,hKd,hKb⟩
  have hmin := Nat.find_min' hex hP
  simp only [Fintype.card_fin] at hmn
  exact not_lt_of_ge hmin hmn

end
end Cycle13
