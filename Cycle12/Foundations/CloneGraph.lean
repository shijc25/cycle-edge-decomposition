import Cycle12.Foundations.MultipartiteDeletion
import Cycle12.Foundations.BipartiteImmersion

/-! GLW's actual auxiliary graph with one clone for each double neighbour. -/
namespace Cycle13
open SimpleGraph GallaiEdmonds Finset
noncomputable section
attribute [local instance] Classical.propDecidable

def cloneGraph {V : Type} (G : SimpleGraph V) (R : Finset V) : SimpleGraph (V ⊕ R) where
  Adj x y := match x,y with
    | .inl v,.inl w => G.Adj v w
    | .inl v,.inr w => v ∈ R ∨ G.Adj v w.val
    | .inr v,.inl w => w ∈ R ∨ G.Adj v.val w
    | .inr v,.inr w => v ≠ w
  symm := ⟨by
    rintro (v | v) (w | w) h
    · exact h.symm
    · exact h.imp id (fun h => h.symm)
    · exact h.imp id (fun h => h.symm)
    · exact h.symm⟩
  loopless := ⟨by rintro (v | v) h; exact G.irrefl h; exact h rfl⟩

namespace CloneGraph
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (R : Finset V)

def originals : Finset (V ⊕ R) := univ.image Sum.inl

def originalIso : G ≃g (cloneGraph G R).induce (originals R : Set (V ⊕ R)) := by
  let E : G ↪g (cloneGraph G R).induce (originals R : Set (V ⊕ R)) := {
    toFun := fun v => ⟨Sum.inl v,by simp [originals]⟩
    inj' := fun _ _ h => Sum.inl.inj (congrArg Subtype.val h)
    map_rel_iff' := by intro x y; rfl }
  apply RelIso.ofSurjective E
  rintro ⟨w,hw⟩
  obtain ⟨v,_,hv⟩ := mem_image.mp hw
  exact ⟨v,Subtype.ext hv⟩

lemma removed_card : (univ \ originals R).card=R.card := by
  rw [card_sdiff_of_subset (subset_univ _)]
  have hO : (originals R).card=Fintype.card V := by
    rw [originals,card_image_of_injective _ Sum.inl_injective,card_univ]
  rw [hO,card_univ,Fintype.card_sum,Fintype.card_coe]
  omega

lemma sum_set_card (S : Set (V ⊕ R)) :
    S.ncard=(Sum.inl ⁻¹' S).ncard+(Sum.inr ⁻¹' S).ncard := by
  have heq : S=Sum.inl '' (Sum.inl ⁻¹' S) ∪ Sum.inr '' (Sum.inr ⁻¹' S) := by
    ext v
    cases v <;> simp
  have hd : Disjoint (Sum.inl '' (Sum.inl ⁻¹' S)) (Sum.inr '' (Sum.inr ⁻¹' S)) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨v,_,rfl⟩ ⟨w,_,h⟩
    exact Sum.inr_ne_inl h
  conv_lhs => rw [heq]
  rw [Set.ncard_union_eq hd,Set.ncard_image_of_injective _ Sum.inl_injective,
    Set.ncard_image_of_injective _ Sum.inr_injective]

lemma old_part_bound (S : Set (V ⊕ R)) : S.ncard ≤ (Sum.inl ⁻¹' S).ncard+R.card := by
  have h := Set.ncard_le_card (Sum.inr ⁻¹' S)
  rw [Nat.card_eq_fintype_card,Fintype.card_coe] at h
  rw [sum_set_card]
  omega

lemma old_missing_le (v : V) : Gᶜ.degree v ≤ (cloneGraph G R)ᶜ.degree (Sum.inl v) := by
  let f : Gᶜ.neighborSet v → (cloneGraph G R)ᶜ.neighborSet (Sum.inl v) :=
    fun w => ⟨Sum.inl w.val,by
      have hw := (compl_adj G v w.val).mp w.property
      exact (compl_adj _ _ _).mpr ⟨fun h => hw.1 (Sum.inl.inj h),hw.2⟩⟩
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (Sum.inl.inj (congrArg Subtype.val h))
  simpa only [card_neighborSet_eq_degree] using Fintype.card_le_of_injective f hf

lemma clone_missing_le (v : R) :
    Gᶜ.degree v.val ≤ (cloneGraph G R)ᶜ.degree (Sum.inr v)+R.card := by
  classical
  let X := Gᶜ.neighborFinset v.val \ R
  let f : X → (cloneGraph G R)ᶜ.neighborSet (Sum.inr v) := fun w => ⟨Sum.inl w.val,by
    have hw := mem_sdiff.mp w.property
    have hG : Gᶜ.Adj v.val w.val := by simpa using hw.1
    exact (compl_adj _ _ _).mpr ⟨Sum.inr_ne_inl,fun h => h.elim hw.2 ((compl_adj _ _ _).mp hG).2⟩⟩
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (Sum.inl.inj (congrArg Subtype.val h))
  have hx : X.card ≤ (cloneGraph G R)ᶜ.degree (Sum.inr v) := by
    simpa only [Fintype.card_coe,card_neighborSet_eq_degree] using Fintype.card_le_of_injective f hf
  have h := card_le_card (show Gᶜ.neighborFinset v.val ⊆ X ∪ R from by
    intro w hw
    by_cases hwR : w ∈ R
    · exact mem_union_right _ hwR
    · exact mem_union_left _ (mem_sdiff.mpr ⟨hw,hwR⟩))
  have hu := card_union_le X R
  rw [card_neighborFinset_eq_degree] at h
  omega

theorem partition_bound {t : ℕ} (ht : 0 < t)
    (hno : ¬ Nonempty (StrongCliqueImmersion t G)) (S : Set (V ⊕ R)) (hS : S.Nonempty) :
    ∃ v : S, (S \ cc (cloneGraph G R)ᶜ S v.val).ncard < t+R.card := by
  have hn : ¬ Nonempty (StrongCliqueImmersion t
      ((cloneGraph G R).induce (originals R : Set (V ⊕ R)))) := by
    rintro ⟨M⟩
    exact hno ⟨M.mapCopy (originalIso G R).symm.toCopy⟩
  simpa only [removed_card] using
    small_component_complement_after_deletion (cloneGraph G R) (originals R) ht hn S hS

end CloneGraph
end
end Cycle13
