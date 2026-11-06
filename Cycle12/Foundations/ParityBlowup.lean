import Cycle12.Foundations.ComponentObstruction

/-! A clique blowup for bounded-degree parity correction. Deleted complete
fibres are charged to the deletion set; partial fibres remain connected. -/
namespace Cycle13
open SimpleGraph GallaiEdmonds Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def parityBlowup (G : SimpleGraph V) (k : V → ℕ) : SimpleGraph (Σ v, Fin (k v)) where
  Adj x y := x≠y ∧ (x.1=y.1 ∨ G.Adj x.1 y.1)
  symm := ⟨by intro x y h; exact ⟨h.1.symm,h.2.imp Eq.symm Adj.symm⟩⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

def deletedFibers (k : V → ℕ) (S : Set (Σ v, Fin (k v))) : Set V :=
  {v | ∀ i : Fin (k v), (⟨v,i⟩ : Σ v, Fin (k v))∈S}

namespace ParityBlowup
variable (G : SimpleGraph V) (k : V → ℕ) (S : Set (Σ v, Fin (k v)))

def representative (v : ((deletedFibers k S)ᶜ : Set V)) : (Sᶜ : Set (Σ v, Fin (k v))) :=
  ⟨⟨v.val,Classical.choose (not_forall.mp v.property)⟩,
    Classical.choose_spec (not_forall.mp v.property)⟩

def representativeHom : (G.induce (deletedFibers k S)ᶜ) →g ((parityBlowup G k).induce Sᶜ) where
  toFun := representative k S
  map_rel' := by
    intro x y hxy
    refine ⟨?_,Or.inr hxy⟩
    intro he
    exact hxy.ne (Subtype.ext (congrArg Sigma.fst he))

theorem representative_components_surjective :
    Function.Surjective (ConnectedComponent.map (representativeHom G k S)) := by
  intro c
  induction c using ConnectedComponent.ind with
  | h x =>
    let v : ((deletedFibers k S)ᶜ : Set V) := ⟨x.val.1,fun h => x.property (h x.val.2)⟩
    refine ⟨(G.induce (deletedFibers k S)ᶜ).connectedComponentMk v,?_⟩
    rw [ConnectedComponent.map_mk,ConnectedComponent.eq]
    change ((parityBlowup G k).induce Sᶜ).Reachable (representative k S v) x
    by_cases he : representative k S v=x
    · rw [he]
    · apply Adj.reachable
      exact ⟨fun h => he (Subtype.ext h),Or.inl rfl⟩

theorem components_le :
    Nat.card ((parityBlowup G k).induce Sᶜ).ConnectedComponent ≤
      Nat.card (G.induce (deletedFibers k S)ᶜ).ConnectedComponent :=
  Nat.card_le_card_of_surjective _ (representative_components_surjective G k S)

theorem deleted_fibers_cost {q : ℕ} (hk : ∀ v, q ≤ k v) :
    q*(deletedFibers k S).ncard ≤ S.ncard := by
  let f : (Σ v : deletedFibers k S, Fin (k v.val)) → S :=
    fun x => ⟨⟨x.1.val,x.2⟩,x.1.property x.2⟩
  have hf : Function.Injective f := by
    rintro ⟨⟨v,hv⟩,i⟩ ⟨⟨w,hw⟩,j⟩ he
    have h := congrArg Subtype.val he
    have hvw : v=w := congrArg Sigma.fst h
    subst w
    have hij : i=j := by
      change (⟨v,i⟩ : Σ v, Fin (k v))=⟨v,j⟩ at h
      exact eq_of_heq (Sigma.mk.inj h).2
    subst j
    rfl
  have hc := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_sigma,Fintype.card_fin] at hc
  have hh : q*(deletedFibers k S).ncard ≤ ∑ v : deletedFibers k S, k v.val := by
    calc
      _ = ∑ _v : deletedFibers k S, q := by
        simp only [sum_const,card_univ,smul_eq_mul]
        rw [← Nat.card_eq_fintype_card,Nat.card_coe_set_eq,mul_comm]
      _ ≤ _ := sum_le_sum (fun v _ => hk v.val)
  exact hh.trans (by simpa only [← Nat.card_eq_fintype_card,Nat.card_coe_set_eq] using hc)

end ParityBlowup

theorem components_induce_univ_le_one (G : SimpleGraph V) (hG : G.Preconnected) :
    Nat.card (G.induce Set.univ).ConnectedComponent ≤ 1 := by
  have hp : (G.induce Set.univ).Preconnected := by
    intro x y
    let f : G →g G.induce Set.univ := {
      toFun := fun v => ⟨v,Set.mem_univ _⟩
      map_rel' := fun h => h }
    obtain ⟨p⟩ := hG x.val y.val
    exact ⟨p.map f⟩
  letI := hp.subsingleton_connectedComponent
  simpa using Nat.card_le_card_of_injective (fun _ : (G.induce Set.univ).ConnectedComponent => ()) (by intro x y _; exact Subsingleton.elim x y)

theorem perfect_matching_of_odd_component_bounds {I : Type} [Finite I] (H : SimpleGraph I)
    (h : ∀ S : Set I, oddC H Sᶜ ≤ S.ncard) : HasPerfectMatchingOn H Set.univ := by
  obtain ⟨M,S,hM,hmax,he⟩ := tb_eq H
  refine ⟨M,hM,?_⟩
  have hb := h S
  apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _) (by simpa using (show Nat.card I ≤ M.verts.ncard by omega))

theorem parity_blowup_perfect_matching (G : SimpleGraph V) (k : V → ℕ) {q : ℕ}
    (hG : G.Preconnected) (hk : ∀ v, q ≤ k v)
    (heven : Even (Nat.card (Σ v, Fin (k v))))
    (hcomp : ∀ U : Set V, U.Nonempty →
      Nat.card (G.induce Uᶜ).ConnectedComponent ≤ q*U.ncard) :
    HasPerfectMatchingOn (parityBlowup G k) Set.univ := by
  apply perfect_matching_of_odd_component_bounds
  intro S
  have ho : oddC (parityBlowup G k) Sᶜ ≤
      Nat.card ((parityBlowup G k).induce Sᶜ).ConnectedComponent := by
    rw [← oddComponents_ncard_eq]
    exact Set.ncard_le_card _
  have hc := ParityBlowup.components_le G k S
  by_cases hU : (deletedFibers k S).Nonempty
  · exact ho.trans (hc.trans ((hcomp _ hU).trans (ParityBlowup.deleted_fibers_cost k S hk)))
  · have hUe : deletedFibers k S=∅ := Set.not_nonempty_iff_eq_empty.mp hU
    rw [hUe,Set.compl_empty] at hc
    have hb : oddC (parityBlowup G k) Sᶜ ≤ 1 :=
      ho.trans (hc.trans (components_induce_univ_le_one G hG))
    by_cases hS : S.Nonempty
    · apply hb.trans
      have hh := Set.ncard_le_ncard (Set.singleton_subset_iff.mpr hS.choose_spec)
      simpa using hh
    · have hSe : S=∅ := Set.not_nonempty_iff_eq_empty.mp hS
      subst S
      simp only [Set.compl_empty,Set.ncard_empty] at hb ⊢
      have hn : ¬Odd (oddC (parityBlowup G k) Set.univ) := by
        intro hh
        rw [← oddComponents_ncard_eq] at hh
        have hp := (odd_ncard_oddComponents ((parityBlowup G k).induce Set.univ)).mp hh
        have hodd : Odd (Nat.card (Σ v, Fin (k v))) := by simpa using hp
        exact (Nat.not_even_iff_odd.mpr hodd) heven
      simp only [Nat.odd_iff] at hn
      omega

end
end Cycle13
