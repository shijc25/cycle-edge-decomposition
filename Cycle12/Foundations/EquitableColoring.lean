import Cycle12.Foundations.ColorSwitch

/-! Balancing proper colorings when every bichromatic graph has maximum
degree two. The decreasing potential is the sum of squared class sizes. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V C : Type} [Fintype V] [Fintype C] [DecidableEq V] [DecidableEq C]

def colorEnergy (f : V → C) : ℕ := ∑ a : C, (colorSize f a)^2

def IsEquitableColoring (f : V → C) : Prop :=
  ∀ a b : C, colorSize f a ≤ colorSize f b+1

lemma sum_split_two (f : C → ℕ) {a b : C} (hab : a ≠ b) :
    ∑ x : C, f x = f a+f b+∑ x ∈ (univ.erase a).erase b, f x := by
  rw [← add_sum_erase univ f (mem_univ a),
    ← add_sum_erase (univ.erase a) f (mem_erase.mpr ⟨hab.symm,mem_univ b⟩)]
  omega

lemma colorEnergy_decreases (f g : V → C) (a b : C) (hab : a ≠ b)
    (hgap : colorSize f b+1 < colorSize f a)
    (ha : colorSize g a+1 = colorSize f a)
    (hb : colorSize g b = colorSize f b+1)
    (hother : ∀ x, x ≠ a → x ≠ b → colorSize g x = colorSize f x) :
    colorEnergy g < colorEnergy f := by
  unfold colorEnergy
  rw [sum_split_two _ hab, sum_split_two _ hab]
  have he : ∑ x ∈ (univ.erase a).erase b, (colorSize g x)^2 =
      ∑ x ∈ (univ.erase a).erase b, (colorSize f x)^2 := by
    apply sum_congr rfl
    intro x hx
    rw [hother x (mem_erase.mp (mem_erase.mp hx).2).1 (mem_erase.mp hx).1]
  rw [he]
  nlinarith

theorem exists_equitable_coloring (H : SimpleGraph V) (f₀ : H.Coloring C)
    (hdeg : ∀ f : H.Coloring C, ∀ a b : C, a ≠ b →
      ∀ v, (twoColorGraph H f a b).degree v ≤ 2) :
    ∃ f : H.Coloring C, IsEquitableColoring f := by
  have hex : ∃ n : ℕ, ∃ f : H.Coloring C, colorEnergy f=n :=
    ⟨colorEnergy f₀, f₀, rfl⟩
  obtain ⟨f,hf⟩ := Nat.find_spec hex
  have hmin : ∀ g : H.Coloring C, colorEnergy f ≤ colorEnergy g :=
    fun g => hf ▸ Nat.find_min' hex ⟨g,rfl⟩
  refine ⟨f, ?_⟩
  intro a b
  by_contra! hgap
  have hab : a ≠ b := by intro he; subst b; omega
  obtain ⟨c,hc⟩ := exists_unbalanced_twoColor_component H f a b hab
    (hdeg f a b hab) (by omega)
  let g := switchComponent H f a b c
  have ha : colorSize g a+1 = colorSize f a := by
    have h := switchComponent_counts H f a b a c
    rw [Equiv.swap_apply_left, hc] at h
    dsimp [g]
    omega
  have hb : colorSize g b = colorSize f b+1 := by
    have h := switchComponent_counts H f a b b c
    rw [Equiv.swap_apply_right, hc] at h
    dsimp [g]
    omega
  have hother : ∀ x, x ≠ a → x ≠ b → colorSize g x = colorSize f x := by
    intro x hxa hxb
    have h := switchComponent_counts H f a b x c
    rw [Equiv.swap_apply_of_ne_of_ne hxa hxb] at h
    dsimp [g]
    omega
  exact (not_lt_of_ge (hmin g)) (colorEnergy_decreases f g a b hab hgap ha hb hother)

theorem sum_colorSize (f : V → C) : ∑ a : C, colorSize f a = Fintype.card V := by
  have h := card_eq_sum_card_fiberwise
    (f := f) (s := (univ : Finset V)) (t := (univ : Finset C))
    (fun _ _ => mem_univ _)
  simpa only [colorSize, card_univ] using h.symm

/-- The sharp ceiling, including the case where the number of vertices
is divisible by the number of colors. -/
theorem IsEquitableColoring.class_le_ceil {f : V → C} (hf : IsEquitableColoring f)
    (a : C) : colorSize f a ≤
      (Fintype.card V+Fintype.card C-1)/Fintype.card C := by
  have hp : 0 < Fintype.card C := Fintype.card_pos_iff.mpr ⟨a⟩
  have hs : ∑ _x : C, colorSize f a < ∑ x : C, (colorSize f x+1) := by
    apply sum_lt_sum (fun b _ => hf a b)
    exact ⟨a, mem_univ _, by omega⟩
  simp only [sum_const, card_univ, smul_eq_mul, sum_add_distrib, sum_colorSize,
    mul_one] at hs
  apply (Nat.le_div_iff_mul_le hp).mpr
  rw [Nat.mul_comm]
  omega

end
end Cycle13
