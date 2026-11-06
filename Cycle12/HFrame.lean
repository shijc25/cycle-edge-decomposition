import Cycle12.FiveCycleClassification

namespace Cycle12
open SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} {G : SimpleGraph V}

/-- A five-cycle core and two arbitrary sets of degree-two twins, sharing
hub 0. Core chords are unrestricted. -/
def HFrame (G : SimpleGraph V) (f : Fin 5 ↪ V) : Prop :=
  (∀ i, G.Adj (f i) (f (i+1))) ∧
  ∀ x, (∀ i, x≠f i) →
    (∀ v, G.Adj x v ↔ v=f 0 ∨ v=f 2) ∨
    (∀ v, G.Adj x v ↔ v=f 0 ∨ v=f 3)

theorem h_frame_of_five_cycle [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hconn : G.Connected)
    (hrobust : ∀ a, (G.induce ({a}ᶜ : Set V)).Preconnected)
    (hshort : Cycle13.NoCycleAtLeast G 6)
    {u : V} (c : G.Walk u u) (hc : c.IsCycle) (hlen : c.length=5) :
    ∃ f : Fin 5 ↪ V, HFrame G f := by
  obtain ⟨f,h,hcycle,_,hshape⟩ := five_cycle_common_hub_classification G hconn hrobust hshort c hc hlen
  let g : Fin 5 ↪ V := ⟨fun i => f (h+i),by
    intro i j he
    exact add_left_cancel (f.injective he)⟩
  refine ⟨g,?_,?_⟩
  · intro i
    change G.Adj (f (h+i)) (f (h+(i+1)))
    simpa only [add_assoc] using hcycle (h+i)
  · intro x hx
    have hxf : ∀ i, x≠f i := by
      intro i he
      apply hx (i-h)
      change x=f (h+(i-h))
      have hi : h+(i-h)=i := by fin_cases h <;> fin_cases i <;> decide
      rwa [hi]
    change (∀ v, G.Adj x v ↔ v=f (h+0) ∨ v=f (h+2)) ∨
      (∀ v, G.Adj x v ↔ v=f (h+0) ∨ v=f (h+3))
    simpa only [add_zero] using hshape x hxf

/-- Retaining the five core vertices preserves the entire H-frame shape. -/
theorem h_frame_induce (f : Fin 5 ↪ V) (hf : HFrame G f)
    (S : Set V) (hS : ∀ i, f i∈S) :
    HFrame (G.induce S) (⟨fun i => ⟨f i,hS i⟩,by
      intro i j he; exact f.injective (congrArg Subtype.val he)⟩ : Fin 5 ↪ S) := by
  constructor
  · intro i
    exact hf.1 i
  · intro x hx
    have hxo : ∀ i, x.val≠f i := fun i he => hx i (Subtype.ext he)
    rcases hf.2 x.val hxo with h | h
    · left
      intro v
      change G.Adj x.val v.val ↔ v=(⟨f 0,hS 0⟩:S) ∨ v=(⟨f 2,hS 2⟩:S)
      simpa only [Subtype.ext_iff] using h v.val
    · right
      intro v
      change G.Adj x.val v.val ↔ v=(⟨f 0,hS 0⟩:S) ∨ v=(⟨f 3,hS 3⟩:S)
      simpa only [Subtype.ext_iff] using h v.val

theorem h_frame_types_disjoint (f : Fin 5 ↪ V) (x : V)
    (hA : ∀ v, G.Adj x v ↔ v=f 0 ∨ v=f 2)
    (hB : ∀ v, G.Adj x v ↔ v=f 0 ∨ v=f 3) : False := by
  have hh := (hB (f 2)).mp ((hA (f 2)).mpr (Or.inr rfl))
  rcases hh with hh | hh
  · have := f.injective hh; contradiction
  · have := f.injective hh; contradiction

end
end Cycle12
