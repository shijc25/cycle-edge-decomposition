import Cycle12.Foundations.TwoColorComponents

/-! Swapping two colors on one connected bichromatic component preserves
properness and transfers exactly the component's color-class imbalance. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V C : Type} [Fintype V] [DecidableEq V] [DecidableEq C]

def regionColorSize (f : V → C) (S : Set V) (a : C) : ℕ :=
  (univ.filter (fun v => v ∈ S ∧ f v=a)).card

lemma colorSize_partition (f : V → C) (S : Set V) (a : C) :
    colorSize f a = regionColorSize f S a + regionColorSize f Sᶜ a := by
  have h := card_filter_add_card_filter_not (s := univ.filter (fun v => f v=a))
    (fun v : V => v ∈ S)
  simpa only [filter_filter, Set.mem_compl_iff, and_comm, colorSize, regionColorSize]
    using h.symm

lemma componentColorSize_eq_region (H : SimpleGraph V) (f : V → C) (a : C)
    (c : H.ConnectedComponent) :
    componentColorSize H f a c = regionColorSize f c.supp a := by
  classical
  unfold componentColorSize regionColorSize
  apply card_bij (fun v _ => v.val)
  · intro v hv
    simp only [mem_filter, mem_univ, true_and] at hv ⊢
    exact ⟨v.property, hv⟩
  · intro v hv w hw h
    exact Subtype.ext h
  · intro v hv
    simp only [mem_filter, mem_univ, true_and] at hv
    refine ⟨⟨v,hv.1⟩, ?_, rfl⟩
    simpa only [mem_filter, mem_univ, true_and] using hv.2

def switchColors (f : V → C) (a b : C) (S : Set V) : V → C :=
  fun v => if v ∈ S then Equiv.swap a b (f v) else f v

lemma switchColors_counts (f : V → C) (a b x : C) (S : Set V) :
    colorSize (switchColors f a b S) x + regionColorSize f S x =
      colorSize f x + regionColorSize f S (Equiv.swap a b x) := by
  have hin : regionColorSize (switchColors f a b S) S x =
      regionColorSize f S (Equiv.swap a b x) := by
    unfold regionColorSize
    congr 1
    ext v
    simp only [mem_filter, mem_univ, true_and]
    by_cases hv : v ∈ S
    · simp [switchColors, hv, Equiv.swap_apply_eq_iff]
    · simp [hv]
  have hout : regionColorSize (switchColors f a b S) Sᶜ x =
      regionColorSize f Sᶜ x := by
    unfold regionColorSize
    congr 1
    ext v
    simp only [mem_filter, mem_univ, true_and, Set.mem_compl_iff]
    by_cases hv : v ∈ S <;> simp [switchColors, hv]
  rw [colorSize_partition (switchColors f a b S) S,
    colorSize_partition f S, hin, hout]
  omega

lemma switchColors_component_valid (H : SimpleGraph V) (f : H.Coloring C) (a b : C)
    (c : (twoColorGraph H f a b).ConnectedComponent) :
    ∀ {v w}, H.Adj v w →
      switchColors f a b c.supp v ≠ switchColors f a b c.supp w := by
  have hcross : ∀ {v w}, H.Adj v w → v ∈ c.supp → w ∉ c.supp →
      Equiv.swap a b (f v) ≠ f w := by
    intro v w hvw hv hw heq
    have hne : Equiv.swap a b (f v) ≠ f v := by
      intro h
      exact f.valid hvw (h.symm.trans heq)
    have hmem := Equiv.eq_or_eq_of_swap_apply_ne_self hne
    have hadj : (twoColorGraph H f a b).Adj v w := by
      refine ⟨hvw, ?_⟩
      rcases hmem with ha | hb
      · exact Or.inl ⟨ha, by simpa [ha] using heq.symm⟩
      · exact Or.inr ⟨hb, by simpa [hb] using heq.symm⟩
    exact hw (c.mem_supp_of_adj_mem_supp hv hadj)
  intro v w hvw
  by_cases hv : v ∈ c.supp <;> by_cases hw : w ∈ c.supp
  · simpa only [switchColors, if_pos hv, if_pos hw, ne_eq, Equiv.apply_eq_iff_eq]
      using f.valid hvw
  · simpa only [switchColors, if_pos hv, if_neg hw] using hcross hvw hv hw
  · simpa only [switchColors, if_neg hv, if_pos hw] using (hcross hvw.symm hw hv).symm
  · simpa only [switchColors, if_neg hv, if_neg hw] using f.valid hvw

def switchComponent (H : SimpleGraph V) (f : H.Coloring C) (a b : C)
    (c : (twoColorGraph H f a b).ConnectedComponent) : H.Coloring C :=
  Coloring.mk (switchColors f a b c.supp) (switchColors_component_valid H f a b c)

theorem switchComponent_counts (H : SimpleGraph V) (f : H.Coloring C) (a b x : C)
    (c : (twoColorGraph H f a b).ConnectedComponent) :
    colorSize (switchComponent H f a b c) x + componentColorSize _ f x c =
      colorSize f x + componentColorSize _ f (Equiv.swap a b x) c := by
  simp only [componentColorSize_eq_region]
  exact switchColors_counts f a b x c.supp

end
end Cycle13
