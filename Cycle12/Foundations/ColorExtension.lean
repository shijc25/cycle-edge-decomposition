import Cycle12.Foundations.OrderedListColoring

/-! Extending a proper partial coloring when every degree is smaller
than the palette, while retaining all preassigned colors. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {W C : Type} [Fintype W] [Fintype C] [DecidableEq W] [DecidableEq C]

theorem exists_coloring_extension (H : SimpleGraph W) (S : Finset W) (f₀ : W → C)
    (hf₀ : ∀ x∈S, ∀ y∈S, H.Adj x y → f₀ x≠f₀ y)
    (hd : ∀ x, H.degree x < Fintype.card C) :
    ∃ f : H.Coloring C, ∀ x∈S, f x=f₀ x := by
  have hpartial : ∀ A : Finset W, ∃ f : W → C,
      (∀ x∈S, f x=f₀ x) ∧
      (∀ x∈S∪A, ∀ y∈S∪A, H.Adj x y → f x≠f y) := by
    intro A
    induction A using Finset.induction_on with
    | empty => exact ⟨f₀,fun _ _ => rfl,by simpa using hf₀⟩
    | @insert a A ha ih =>
      obtain ⟨f,hfixed,hproper⟩ := ih
      by_cases haS : a∈S
      · refine ⟨f,hfixed,?_⟩
        have he : S∪insert a A=S∪A := by ext x; simp only [mem_union,mem_insert]; aesop
        simpa only [he] using hproper
      · let bad := ((S∪A).filter (fun x => H.Adj a x)).image f
        have hbad : bad.card < (univ : Finset C).card := by
          have hs : (S∪A).filter (fun x => H.Adj a x) ⊆ H.neighborFinset a := by
            intro x hx
            exact (H.mem_neighborFinset a x).mpr (mem_filter.mp hx).2
          have hh := (card_image_le (s:=(S∪A).filter (fun x => H.Adj a x)) (f:=f)).trans (card_le_card hs)
          rw [card_neighborFinset_eq_degree] at hh
          exact (hh.trans_lt (hd a)).trans_eq card_univ.symm
        obtain ⟨c,hc,hcbad⟩ := exists_mem_notMem_of_card_lt_card hbad
        have hne : ∀ x∈S∪A, H.Adj a x → c≠f x := by
          intro x hx hadj he
          exact hcbad (mem_image.mpr ⟨x,mem_filter.mpr ⟨hx,hadj⟩,he.symm⟩)
        refine ⟨Function.update f a c,?_,?_⟩
        · intro x hx
          have hxa : x≠a := by intro h; subst x; exact haS hx
          simpa only [Function.update_of_ne hxa] using hfixed x hx
        · intro x hx y hy hxy
          have hx' : x=a ∨ x∈S∪A := by simp only [mem_union,mem_insert] at hx ⊢; tauto
          have hy' : y=a ∨ y∈S∪A := by simp only [mem_union,mem_insert] at hy ⊢; tauto
          rcases hx' with hx' | hx'
          · subst x
            rcases hy' with hy' | hy'
            · subst y
              exact (H.irrefl hxy).elim
            · have hya : y≠a := by intro h; subst y; exact haS ((mem_union.mp hy').resolve_right ha)
              simpa only [Function.update_self,Function.update_of_ne hya] using hne y hy' hxy
          · have hxa : x≠a := by intro h; subst x; exact haS ((mem_union.mp hx').resolve_right ha)
            rcases hy' with hy' | hy'
            · subst y
              simpa only [Function.update_self,Function.update_of_ne hxa] using (hne x hx' hxy.symm).symm
            · have hya : y≠a := by intro h; subst y; exact haS ((mem_union.mp hy').resolve_right ha)
              simpa only [Function.update_of_ne hxa,Function.update_of_ne hya] using hproper x hx' y hy' hxy
  obtain ⟨f,hfixed,hproper⟩ := hpartial univ
  exact ⟨Coloring.mk f (fun {x y} hxy => hproper x (by simp) y (by simp) hxy),hfixed⟩

end
end Cycle13
