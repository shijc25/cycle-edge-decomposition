import Cycle12.FixedSampleMGF

namespace Cycle12
open Finset Cycle13
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem fixed_size_membership_probability (D : Finset V) {v : V} (hv : v∈D)
    {k : ℕ} (hk : k ≤ D.card) :
    (fixedSizeLaw D k).prob (fun A => v∈A)=(k:ℝ)/D.card := by
  by_cases hzero : k=0
  · subst k
    have hh : (fixedSizeLaw D 0).prob (fun A => v∈A) ≤
        (fixedSizeLaw D 0).prob (fun _ => False) := by
      apply FiniteLaw.prob_mono_support
      intro A hA hvA
      have hz := card_eq_zero.mp (fixed_size_support D A (Nat.zero_le _) hA).2
      simpa only [hz,notMem_empty] using hvA
    have hz : (fixedSizeLaw D 0).prob (fun _ => False)=0 := by
      simp [FiniteLaw.prob]
    rw [hz] at hh
    simpa using le_antisymm hh (FiniteLaw.prob_nonneg _ _)
  · have hh := fixed_size_contains_symmetric D {v} (singleton_subset_iff.mpr hv) hk
      (by simp; omega)
    simpa only [singleton_subset_iff,card_singleton,Nat.choose_one_right] using hh

theorem intersection_card_indicator_sum (T B : Finset V) :
    ((T∩B).card:ℝ)=∑ v∈B, if v∈T then (1:ℝ) else 0 := by
  rw [sum_boole,filter_mem_eq_inter,inter_comm B T]

/-- The exact mean of the actual fixed-size intersection count. -/
theorem fixed_sample_count_mean (D B : Finset V) (hB : B⊆D)
    {k : ℕ} (hk : k ≤ D.card) :
    (fixedSizeLaw D k).expect (fun T => ((T∩B).card:ℝ))=
      (k:ℝ)*B.card/D.card := by
  simp_rw [intersection_card_indicator_sum,FiniteLaw.expect_finset_sum]
  calc
    _ = ∑ v∈B, (fixedSizeLaw D k).prob (fun T => v∈T) := by
      apply sum_congr rfl
      intro v _
      unfold FiniteLaw.prob
      congr 1
      funext T
      by_cases hv : v∈T <;> simp [hv]
    _ = ∑ _v∈B, (k:ℝ)/D.card := sum_congr rfl (fun v hv => fixed_size_membership_probability D (hB hv) hk)
    _ = _ := by rw [sum_const,nsmul_eq_mul]; ring

end
end Cycle12
