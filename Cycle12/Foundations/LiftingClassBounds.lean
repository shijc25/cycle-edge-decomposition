import Cycle12.Foundations.PrescribedLiftingColoring

namespace Cycle13
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem balanced_three_class_lower (f : V → Fin 3)
    (hf : ∀ r s, colorSize f r ≤ colorSize f s+2) (r : Fin 3) :
    Fintype.card V/3 ≤ colorSize f r+1 := by
  have hp : ∀ s : Fin 3, colorSize f s ≤ colorSize f r+(if s=r then 0 else 2) := by
    intro s
    by_cases hs : s=r
    · subst s; simp
    · simpa only [if_neg hs] using hf s r
  have hsum := sum_le_sum (fun s (_ : s∈(univ : Finset (Fin 3))) => hp s)
  have hfour : (∑ s : Fin 3, if s=r then (0:ℕ) else 2)=4 := by fin_cases r <;> decide
  rw [sum_colorSize,sum_add_distrib,hfour] at hsum
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at hsum
  omega

theorem balanced_three_available_lower (f : V → Fin 3)
    (hf : ∀ r s, colorSize f r ≤ colorSize f s+2)
    (w : Fin 3 ↪ V) (hw : ∀ r, f (w r)=r) (B : Finset V) (hB : B.card ≤ 3)
    (r : Fin 3) :
    Fintype.card V/3 ≤ ((univ.filter (fun v => f v=r))\((univ.image w)∪B)).card+5 := by
  let A := univ.filter (fun v => f v=r)
  have hwcard : (A∩(univ.image w)).card=1 := by
    have he : A∩(univ.image w)={w r} := by
      ext v
      simp only [mem_inter,mem_image,mem_univ,true_and,mem_singleton]
      constructor
      · rintro ⟨hv,⟨s,rfl⟩⟩
        have hs : s=r := (hw s).symm.trans (mem_filter.mp hv).2
        exact congrArg w hs
      · rintro rfl
        exact ⟨mem_filter.mpr ⟨mem_univ _,hw r⟩,r,rfl⟩
    simp only [he,card_singleton]
  have hloss : (A∩((univ.image w)∪B)).card ≤ 4 := by
    rw [inter_union_distrib_left]
    have hh := card_union_le (A∩(univ.image w)) (A∩B)
    have hAB := card_le_card (inter_subset_right (s₁:=A) (s₂:=B))
    omega
  have he := card_sdiff_add_card_inter A ((univ.image w)∪B)
  have hlo := balanced_three_class_lower f hf r
  change Fintype.card V/3 ≤ A.card+1 at hlo
  change Fintype.card V/3 ≤ (A\((univ.image w)∪B)).card+5
  omega

end
end Cycle13
