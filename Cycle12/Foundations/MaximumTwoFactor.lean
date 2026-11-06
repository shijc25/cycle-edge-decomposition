import Cycle12.Foundations.IndependentExtension

/-! Extending a prescribed partial two-factor to an edge-maximal one.
Every unused allowed edge then has a saturated endpoint. -/
namespace Cycle13
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

theorem indexedDegreeOn_insert (a b : I → V) (F : Finset I) {i : I} (hi : i∉F) (v : V) :
    indexedDegreeOn a b (insert i F) v=
      (if a i=v then 1 else 0)+(if b i=v then 1 else 0)+indexedDegreeOn a b F v := by
  exact sum_insert hi

theorem exists_maximal_two_factor (a b : I → V) (hne : ∀ i, a i≠b i)
    (T F₀ : Finset I) (hsub : F₀⊆T) (hcap : ∀ v, indexedDegreeOn a b F₀ v ≤ 2) :
    ∃ F : Finset I, F₀⊆F ∧ F⊆T ∧ (∀ v, indexedDegreeOn a b F v ≤ 2) ∧
      ∀ i∈T, i∉F → indexedDegreeOn a b F (a i)=2 ∨ indexedDegreeOn a b F (b i)=2 := by
  let A := (univ : Finset (Finset I)).filter
    (fun F => F₀⊆F ∧ F⊆T ∧ ∀ v, indexedDegreeOn a b F v ≤ 2)
  have hA : A.Nonempty := ⟨F₀,mem_filter.mpr ⟨mem_univ _,Subset.rfl,hsub,hcap⟩⟩
  obtain ⟨F,hFA,hmax⟩ := exists_max_image A Finset.card hA
  have hF := (mem_filter.mp hFA).2
  refine ⟨F,hF.1,hF.2.1,hF.2.2,?_⟩
  intro i hi hiF
  by_contra hns
  push Not at hns
  have ha : indexedDegreeOn a b F (a i) ≤ 1 := by have hh := hF.2.2 (a i); omega
  have hb : indexedDegreeOn a b F (b i) ≤ 1 := by have hh := hF.2.2 (b i); omega
  have hnew : insert i F∈A := by
    refine mem_filter.mpr ⟨mem_univ _,hF.1.trans (subset_insert _ _),insert_subset hi hF.2.1,?_⟩
    intro v
    rw [indexedDegreeOn_insert a b F hiF v]
    by_cases hav : a i=v <;> by_cases hbv : b i=v
    · exact (hne i (hav.trans hbv.symm)).elim
    · have hh := hav ▸ ha
      simp only [if_pos hav,if_neg hbv]
      omega
    · have hh := hbv ▸ hb
      simp only [if_neg hav,if_pos hbv]
      omega
    · simpa only [if_neg hav,if_neg hbv,zero_add] using hF.2.2 v
  have hh := hmax (insert i F) hnew
  rw [card_insert_of_notMem hiF] at hh
  omega

theorem maximal_two_factor_low_edge (a b : I → V) (T F : Finset I)
    (hsat : ∀ i∈T, i∉F → indexedDegreeOn a b F (a i)=2 ∨ indexedDegreeOn a b F (b i)=2)
    {i : I} (hi : i∈T) (ha : indexedDegreeOn a b F (a i) ≤ 1)
    (hb : indexedDegreeOn a b F (b i) ≤ 1) : i∈F := by
  by_contra hiF
  rcases hsat i hi hiF with h | h <;> omega

end
end Cycle13
