import Cycle12.Foundations.ComponentObstruction

/-! Deleting r vertices from a multipartite witness loses at most r in
each cross-part degree. This is the clone-removal step in GLW Lemma 3.3. -/
namespace Cycle13
open SimpleGraph GallaiEdmonds Finset
noncomputable section
attribute [local instance] Classical.propDecidable

lemma filter_subtype_finset_card {V : Type} [DecidableEq V] (S : Finset V)
    (P : V → Prop) [DecidablePred P] :
    (univ.filter (fun v : S => P v.val)).card=(S.filter P).card := by
  apply card_bij (fun v _ => v.val)
  · intro v hv
    exact mem_filter.mpr ⟨v.property,(mem_filter.mp hv).2⟩
  · intro v hv w hw heq
    exact Subtype.ext heq
  · intro v hv
    exact ⟨⟨v,(mem_filter.mp hv).1⟩,
      mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hv).2⟩,rfl⟩

lemma outside_part_delete_bound {V A : Type} [Fintype V] [DecidableEq V]
    (r : V → A) (S : Finset V) (v : S) :
    (univ.filter (fun w : V => r w ≠ r v.val)).card ≤
      (univ.filter (fun w : S => r w.val ≠ r v.val)).card+(univ \ S).card := by
  classical
  rw [filter_subtype_finset_card S (fun w => r w ≠ r v.val)]
  have hs : univ.filter (fun w : V => r w ≠ r v.val) ⊆
      S.filter (fun w => r w ≠ r v.val) ∪ (univ \ S) := by
    intro w hw
    by_cases hwS : w ∈ S
    · exact mem_union_left _ (mem_filter.mpr ⟨hwS,(mem_filter.mp hw).2⟩)
    · exact mem_union_right _ (mem_sdiff.mpr ⟨mem_univ _,hwS⟩)
  exact (card_le_card hs).trans (card_union_le _ _)

theorem strong_partite_after_deletion {V A : Type} [Fintype V] [DecidableEq V]
    [Nonempty V] (G : SimpleGraph V) (r : V → A) (S : Finset V) {t : ℕ} (ht : 0 < t)
    (hcross : ∀ x y, r x ≠ r y → G.Adj x y)
    (hdeg : ∀ v, t+(univ \ S).card ≤ (univ.filter (fun w => r w ≠ r v)).card) :
    Nonempty (StrongCliqueImmersion t (G.induce (S : Set V))) := by
  classical
  have hS : S.Nonempty := by
    by_contra! hS
    have hSE : S=∅ := hS
    have hd := hdeg (Classical.choice (inferInstance : Nonempty V))
    rw [hSE,sdiff_empty,card_univ] at hd
    have hc := card_filter_le (s := (univ : Finset V))
      (p := fun w => r w ≠ r (Classical.choice (inferInstance : Nonempty V)))
    rw [card_univ] at hc
    omega
  letI : Nonempty (S : Set V) := ⟨⟨hS.choose,hS.choose_spec⟩⟩
  apply strong_model_of_complete_multipartite (G.induce (S : Set V)) (fun v => r v.val) t
    (fun x y h => hcross x.val y.val h)
  intro v
  have h₁ := hdeg v.val
  have h₂ := outside_part_delete_bound r S v
  exact Nat.le_of_add_le_add_right (h₁.trans h₂)

theorem small_component_complement_after_deletion {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A : Finset V) {t : ℕ} (ht : 0 < t)
    (hno : ¬ Nonempty (StrongCliqueImmersion t (G.induce (A : Set V))))
    (S : Set V) (hS : S.Nonempty) :
    ∃ v : S, (S \ cc Gᶜ S v.val).ncard < t+(univ \ A).card := by
  classical
  letI : Nonempty S := ⟨⟨hS.choose,hS.choose_spec⟩⟩
  by_contra! hnone
  let H := Gᶜ.induce S
  let B : Finset S := univ.filter (fun v => v.val ∈ A)
  have hloss : (univ \ B).card ≤ (univ \ A).card := by
    let f : ↥(univ \ B) → ↥(univ \ A) := fun v => ⟨v.val.val,by
      have hv := (mem_sdiff.mp v.property).2
      have hvA : v.val.val ∉ A := by simpa [B] using hv
      exact mem_sdiff.mpr ⟨mem_univ _,hvA⟩⟩
    have hf : Function.Injective f := by
      intro x y h
      exact Subtype.ext (Subtype.ext (congrArg (fun z : ↥(univ \ A) => z.val) h))
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf
  obtain ⟨M⟩ := strong_partite_after_deletion (G.induce S) H.connectedComponentMk B ht (by
      intro x y hxy
      have hne : x.val ≠ y.val := fun he => hxy (congrArg H.connectedComponentMk (Subtype.ext he))
      by_contra hG
      apply hxy
      apply ConnectedComponent.eq.mpr
      apply Adj.reachable
      exact (compl_adj G x.val y.val).mpr ⟨hne,hG⟩) (by
      intro v
      have hv := hnone v
      rw [component_complement_card] at hv
      exact (Nat.add_le_add_left hloss t).trans hv)
  let F : ((G.induce S).induce (B : Set S)).Copy (G.induce (A : Set V)) := {
    toHom := {
      toFun := fun v => ⟨v.val.val,(mem_filter.mp v.property).2⟩
      map_rel' := fun h => h }
    injective' := fun _ _ h => Subtype.ext (Subtype.ext
      (congrArg (fun z : (A : Set V) => z.val) h)) }
  exact hno ⟨M.mapCopy F⟩

end
end Cycle13
