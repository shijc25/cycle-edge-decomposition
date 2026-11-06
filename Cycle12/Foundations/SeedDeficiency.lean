import Cycle12.Foundations.SeedEdgePartition

/-! Exact degree deficiency when three independent vertices are removed
from an indexed two-factor. -/
namespace Cycle13
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

theorem indexedDegreeOn_mono (a b : I → V) {F T : Finset I} (h : F⊆T) (v : V) :
    indexedDegreeOn a b F v ≤ indexedDegreeOn a b T v :=
  sum_le_sum_of_subset_of_nonneg h (fun _ _ _ => Nat.zero_le _)

namespace SeedEdgeData
variable {a b : I → V} {w : Fin 3 ↪ V} (D : SeedEdgeData a b w)

theorem keep_degree_add_star (v : SeedInterior w) :
    Suppression.incidenceDegree (seedKeepLeft a b w) (seedKeepRight a b w) v+
      (univ.filter (fun i => D.otherVertex i=v)).card=Suppression.incidenceDegree a b v.val := by
  rw [← D.split_degree]
  unfold Suppression.incidenceDegree
  rw [Fintype.sum_sum_type]
  change (∑ i : SeedKeep a b w, ((if seedKeepLeft a b w i=v then (1:ℕ) else 0)+
        (if seedKeepRight a b w i=v then 1 else 0)))+
      (univ.filter (fun i => D.otherVertex i=v)).card=
    (∑ i : SeedKeep a b w, ((if (seedKeepLeft a b w i).val=v.val then 1 else 0)+
        (if (seedKeepRight a b w i).val=v.val then 1 else 0)))+
    (∑ i : SeedStar a b w, ((if w (D.group i)=v.val then 1 else 0)+
        (if (D.otherVertex i).val=v.val then 1 else 0)))
  simp only [Subtype.val_injective.eq_iff,if_neg (v.property _).symm,zero_add,sum_boole,Nat.cast_id]

include D in
theorem star_card (hne : ∀ i, a i≠b i) :
    Fintype.card (SeedStar a b w)=∑ r, Suppression.incidenceDegree a b (w r) := by
  have hcount := sum_card_fiberwise_eq_card_filter (s:=univ) (t:=univ) (g:=D.group)
  simp only [mem_univ,filter_true,card_univ] at hcount
  rw [← hcount]
  exact sum_congr rfl (fun r _ => D.fiber_degree hne r)

include D in
theorem two_factor_deficiency (hne : ∀ i, a i≠b i)
    (hdeg : ∀ v, Suppression.incidenceDegree a b v=2) :
    (∀ v, Suppression.incidenceDegree (seedKeepLeft a b w) (seedKeepRight a b w) v ≤ 2) ∧
    (∑ v, (2-Suppression.incidenceDegree (seedKeepLeft a b w) (seedKeepRight a b w) v))=6 := by
  have hpoint : ∀ v : SeedInterior w,
      Suppression.incidenceDegree (seedKeepLeft a b w) (seedKeepRight a b w) v+
        (univ.filter (fun i => D.otherVertex i=v)).card=2 :=
    fun v => (D.keep_degree_add_star v).trans (hdeg v.val)
  refine ⟨fun v => by have hh := hpoint v; omega,?_⟩
  have he : ∀ v : SeedInterior w,
      2-Suppression.incidenceDegree (seedKeepLeft a b w) (seedKeepRight a b w) v=
        (univ.filter (fun i => D.otherVertex i=v)).card := by
    intro v; have hh := hpoint v; omega
  rw [sum_congr rfl (fun v _ => he v)]
  have hcount := sum_card_fiberwise_eq_card_filter (s:=univ) (t:=univ) (g:=D.otherVertex)
  simp only [mem_univ,filter_true,card_univ] at hcount
  rw [hcount,D.star_card hne]
  simp [hdeg]

end SeedEdgeData
end
end Cycle13
