import Cycle12.Foundations.EquitableColoring

/-! A finite greedy list-coloring theorem, with the exact number of earlier
conflicting choices as its hypothesis. Used to realize ordered Link calls. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {I C : Type} [Fintype I] [LinearOrder I] [DecidableEq C] [Nonempty C]

theorem exists_ordered_list_coloring (H : SimpleGraph I) (L : I → Finset C)
    (hroom : ∀ i, (univ.filter (fun j => j < i ∧ H.Adj i j)).card < (L i).card) :
    ∃ f : H.Coloring C, ∀ i, f i ∈ L i := by
  have hpartial : ∀ S : Finset I, ∃ f : I → C,
      (∀ i ∈ S, f i ∈ L i) ∧ (∀ i ∈ S, ∀ j ∈ S, H.Adj i j → f i ≠ f j) := by
    intro S
    induction S using Finset.induction_on_max with
    | empty =>
      exact ⟨fun _ => Classical.choice inferInstance, by simp⟩
    | @insert a S hmax ih =>
      obtain ⟨f,hf,hproper⟩ := ih
      have ha : a ∉ S := by intro h; exact lt_irrefl a (hmax a h)
      let bad := (S.filter (fun j => H.Adj a j)).image f
      have hb : bad.card < (L a).card := by
        apply lt_of_le_of_lt (card_image_le) (?_ : _ < (L a).card)
        apply lt_of_le_of_lt (card_le_card ?_) (hroom a)
        intro j hj
        obtain ⟨hjS,haj⟩ := mem_filter.mp hj
        exact mem_filter.mpr ⟨mem_univ _,hmax j hjS,haj⟩
      obtain ⟨c,hc,hcbad⟩ := exists_mem_notMem_of_card_lt_card hb
      have hne : ∀ j ∈ S, H.Adj a j → c ≠ f j := by
        intro j hj hadj heq
        apply hcbad
        exact mem_image.mpr ⟨j,mem_filter.mpr ⟨hj,hadj⟩,heq.symm⟩
      refine ⟨Function.update f a c, ?_, ?_⟩
      · intro i hi
        rcases mem_insert.mp hi with rfl | hi
        · simpa using hc
        · have hia : i ≠ a := fun h => ha (h ▸ hi)
          simpa only [Function.update_of_ne hia] using hf i hi
      · intro i hi j hj hij
        rcases mem_insert.mp hi with hia | hi
        · subst i
          rcases mem_insert.mp hj with hja | hj
          · subst j
            exact False.elim (H.irrefl hij)
          · have hja : j ≠ a := fun h => ha (h ▸ hj)
            simpa only [Function.update_self, Function.update_of_ne hja] using hne j hj hij
        · have hia : i ≠ a := fun h => ha (h ▸ hi)
          rcases mem_insert.mp hj with hja | hj
          · subst j
            simpa only [Function.update_self, Function.update_of_ne hia]
              using (hne i hi hij.symm).symm
          · have hja : j ≠ a := fun h => ha (h ▸ hj)
            simpa only [Function.update_of_ne hia, Function.update_of_ne hja]
              using hproper i hi j hj hij
  obtain ⟨f,hf,hproper⟩ := hpartial univ
  exact ⟨Coloring.mk f (fun {i j} hij => hproper i (mem_univ _) j (mem_univ _) hij),
    fun i => hf i (mem_univ _)⟩

end
end Cycle13
