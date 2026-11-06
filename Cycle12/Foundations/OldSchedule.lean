import Cycle12.Foundations.CrossSchedule

/-! Exact earlier-load bounds for the descending old-branch clique phase. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev OldSlot (p : ℕ) := {z : (Fin p)ᵒᵈ ×ₗ (Fin p)ᵒᵈ //
  OrderDual.ofDual (ofLex z).2 < OrderDual.ofDual (ofLex z).1}

namespace OldSlot
variable {p : ℕ}
def big (i : OldSlot p) : Fin p := OrderDual.ofDual (ofLex i.val).1
def small (i : OldSlot p) : Fin p := OrderDual.ofDual (ofLex i.val).2
theorem small_lt_big (i : OldSlot p) : i.small < i.big := i.property

theorem ext {i j : OldSlot p} (hb : i.big=j.big) (hs : i.small=j.small) : i=j := by
  apply Subtype.ext
  apply ofLex.injective
  exact Prod.ext hb hs

def other (i : OldSlot p) (v : Fin p) : Fin p := if v=i.big then i.small else i.big

lemma other_ne (i : OldSlot p) (v : Fin p) (hv : v=i.big ∨ v=i.small) : i.other v ≠ v := by
  rcases hv with rfl | rfl <;> simp [other,ne_of_lt i.small_lt_big,(ne_of_lt i.small_lt_big).symm]

lemma eq_of_other_eq (i j : OldSlot p) (v : Fin p)
    (hi : v=i.big ∨ v=i.small) (hj : v=j.big ∨ v=j.small)
    (hother : i.other v=j.other v) : i=j := by
  have hiLt := i.small_lt_big
  have hjLt := j.small_lt_big
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · apply ext (hi.symm.trans hj)
    simpa only [other,if_pos hi,if_pos hj] using hother
  · have hvj : v ≠ j.big := by rw [hj]; exact ne_of_lt hjLt
    have h : i.small=j.big := by simpa only [other,if_pos hi,if_neg hvj] using hother
    omega
  · have hvi : v ≠ i.big := by rw [hi]; exact ne_of_lt hiLt
    have h : i.big=j.small := by simpa only [other,if_neg hvi,if_pos hj] using hother
    omega
  · apply ext _ (hi.symm.trans hj)
    have hvi : v ≠ i.big := by rw [hi]; exact ne_of_lt hiLt
    have hvj : v ≠ j.big := by rw [hj]; exact ne_of_lt hjLt
    simpa only [other,if_neg hvi,if_neg hvj] using hother

lemma earlier_big_ge {i j : OldSlot p} (hji : j < i) :
    i.big < j.big ∨ i.big=j.big ∧ i.small < j.small := by
  rcases (Prod.Lex.lt_iff (α := (Fin p)ᵒᵈ) (β := (Fin p)ᵒᵈ)
    (x := j.val) (y := i.val)).mp hji with h | ⟨h₁,h₂⟩
  · exact Or.inl h
  · exact Or.inr ⟨h₁.symm,h₂⟩

lemma earlier_other_gt_small {i j : OldSlot p} (hji : j < i)
    (hv : i.big=j.big ∨ i.big=j.small) : i.small < j.other i.big := by
  have hiLt := i.small_lt_big
  have hjLt := j.small_lt_big
  rcases earlier_big_ge hji with h | ⟨hb,hs⟩
  · rcases hv with hv | hv
    · omega
    · have hne : i.big ≠ j.big := ne_of_lt h
      simp only [other,if_neg hne]
      exact hiLt.trans h
  · simp [other,hb,hs]

lemma earlier_other_gt_big {i j : OldSlot p} (hji : j < i)
    (hv : i.small=j.big ∨ i.small=j.small) : i.big < j.other i.small := by
  have hiLt := i.small_lt_big
  have hjLt := j.small_lt_big
  rcases earlier_big_ge hji with h | ⟨hb,hs⟩
  · have hne : i.small ≠ j.big := ne_of_lt (hiLt.trans h)
    simp only [other,if_neg hne]
    exact h
  · rcases hv with hv | hv <;> omega

theorem big_load_lt (i : OldSlot p) :
    priorLinkLoad big small i i.big < p-1-i.small.val := by
  let S := univ.filter (fun j : OldSlot p => j < i ∧ (i.big=j.big ∨ i.big=j.small))
  have hS : ∀ j : S, j.val < i ∧ (i.big=j.val.big ∨ i.big=j.val.small) :=
    fun j => (mem_filter.mp j.property).2
  let f : S → {v : Fin p // i.small < v} := fun j =>
    ⟨j.val.other i.big,earlier_other_gt_small (hS j).1 (hS j).2⟩
  have hinj : Function.Injective f := by
    intro j k he
    apply Subtype.ext
    exact eq_of_other_eq j.val k.val i.big (hS j).2 (hS k).2 (congrArg Subtype.val he)
  have hmissing : (⟨i.big,i.small_lt_big⟩ : {v : Fin p // i.small < v}) ∉ Set.range f := by
    rintro ⟨j,hj⟩
    exact other_ne j.val i.big (hS j).2 (congrArg Subtype.val hj)
  have h := Fintype.card_lt_of_injective_of_notMem f hinj hmissing
  have hc : Fintype.card {v : Fin p // i.small < v} = p-1-i.small.val := by
    rw [Fintype.card_subtype]
    have he : univ.filter (fun v : Fin p => i.small < v) = Ioi i.small := by ext; simp
    rw [he,Fin.card_Ioi]
  simpa only [priorLinkLoad,S,Fintype.card_coe,hc] using h

theorem small_load_le (i : OldSlot p) :
    priorLinkLoad big small i i.small ≤ p-1-i.big.val := by
  let S := univ.filter (fun j : OldSlot p => j < i ∧ (i.small=j.big ∨ i.small=j.small))
  have hS : ∀ j : S, j.val < i ∧ (i.small=j.val.big ∨ i.small=j.val.small) :=
    fun j => (mem_filter.mp j.property).2
  let f : S → {v : Fin p // i.big < v} := fun j =>
    ⟨j.val.other i.small,earlier_other_gt_big (hS j).1 (hS j).2⟩
  have hinj : Function.Injective f := by
    intro j k he
    apply Subtype.ext
    exact eq_of_other_eq j.val k.val i.small (hS j).2 (hS k).2 (congrArg Subtype.val he)
  have h := Fintype.card_le_of_injective f hinj
  have hc : Fintype.card {v : Fin p // i.big < v} = p-1-i.big.val := by
    rw [Fintype.card_subtype]
    have he : univ.filter (fun v : Fin p => i.big < v) = Ioi i.big := by ext; simp
    rw [he,Fin.card_Ioi]
  simpa only [priorLinkLoad,S,Fintype.card_coe,hc] using h

end OldSlot
end
end Cycle13
