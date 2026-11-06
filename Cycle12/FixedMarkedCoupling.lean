import Cycle12.FixedSizeLaw
import Cycle12.Foundations.MarkedSamplingCoupling

namespace Cycle12
open Finset Cycle13
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Exact atom identity for first choosing N sample vertices and then t
marked vertices. No labels or successful-event conditioning enter it. -/
theorem fixed_marked_atom_identity (D U T : Finset V) {N t : ℕ}
    (hN : N ≤ D.card) (ht : t ≤ N) :
    (fixedSizeLaw D N).mass U*(fixedSizeLaw U t).mass T=
      (fixedSizeLaw D t).mass T*
        (if T⊆U then (fixedSizeLaw (D\T) (N-t)).mass (U\T) else 0) := by
  have htD : t ≤ D.card := ht.trans hN
  by_cases hg : U⊆D ∧ U.card=N ∧ T⊆U ∧ T.card=t
  · obtain ⟨hUD,hUN,hTU,hTt⟩ := hg
    have hTD : T⊆D := hTU.trans hUD
    have hrest : N-t ≤ (D\T).card := by
      rw [card_sdiff_of_subset hTD,hTt]
      omega
    have hr : U\T⊆D\T ∧ (U\T).card=N-t :=
      ⟨sdiff_subset_sdiff_left T hUD,by rw [card_sdiff_of_subset hTU,hUN,hTt]⟩
    rw [fixed_size_mass D U hN,fixed_size_mass U T (by omega : t ≤ U.card),
      fixed_size_mass D T htD,if_pos hTU,fixed_size_mass (D\T) (U\T) hrest]
    rw [if_pos (show U⊆D ∧ U.card=N from ⟨hUD,hUN⟩),
      if_pos (show T⊆U ∧ T.card=t from ⟨hTU,hTt⟩),
      if_pos (show T⊆D ∧ T.card=t from ⟨hTD,hTt⟩),if_pos hr,
      hUN,card_sdiff_of_subset hTD,hTt]
    have hc : (D.card.choose N:ℝ)*(N.choose t:ℝ)=
        (D.card.choose t:ℝ)*((D.card-t).choose (N-t):ℝ) := by
      exact_mod_cast (Nat.choose_mul (n:=D.card) ht)
    rw [one_div_mul_one_div,one_div_mul_one_div,hc]
  · have hl : (fixedSizeLaw D N).mass U*(fixedSizeLaw U t).mass T=0 := by
      by_cases hU : U⊆D ∧ U.card=N
      · have hT : ¬(T⊆U ∧ T.card=t) := fun h => hg ⟨hU.1,hU.2,h.1,h.2⟩
        rw [fixed_size_mass U T (by omega : t ≤ U.card),if_neg hT,mul_zero]
      · rw [fixed_size_mass D U hN,if_neg hU,zero_mul]
    rw [hl]
    by_cases hT : T⊆D ∧ T.card=t
    · by_cases hTU : T⊆U
      · have hrest : N-t ≤ (D\T).card := by
          rw [card_sdiff_of_subset hT.1,hT.2]
          omega
        have hr : ¬(U\T⊆D\T ∧ (U\T).card=N-t) := by
          intro hr
          apply hg
          have hUD : U⊆D := by
            intro v hv
            by_cases hvT : v∈T
            · exact hT.1 hvT
            · exact (mem_sdiff.mp (hr.1 (mem_sdiff.mpr ⟨hv,hvT⟩))).1
          have hUN : U.card=N := by
            have hh := card_sdiff_add_card_eq_card hTU
            rw [hr.2,hT.2] at hh
            omega
          exact ⟨hUD,hUN,hTU,hT.2⟩
        rw [if_pos hTU,fixed_size_mass (D\T) (U\T) hrest,if_neg hr,mul_zero]
      · rw [if_neg hTU,mul_zero]
    · rw [fixed_size_mass D T htD,if_neg hT,zero_mul]

theorem disjoint_remaining_union_expect (mu : FiniteLaw (Finset V)) (T : Finset V)
    (hdisj : ∀ R, 0 < mu.mass R → Disjoint R T) (f : Finset V → ℝ) :
    (∑ U : Finset V, (if T⊆U then mu.mass (U\T) else 0)*f U)=
      mu.expect (fun R => f (T∪R)) := by
  have hr : mu.expect (fun R => f (T∪R))=
      ∑ R∈(univ\T).powerset, mu.mass R*f (T∪R) := by
    apply (sum_subset (subset_univ _) ?_).symm
    intro R hR hn
    have hz : mu.mass R=0 := by
      by_contra hz
      have hp := lt_of_le_of_ne (mu.nonneg R) (Ne.symm hz)
      apply hn
      apply mem_powerset.mpr
      intro v hv
      exact mem_sdiff.mpr ⟨mem_univ _,fun ht => disjoint_left.mp (hdisj R hp) hv ht⟩
    rw [hz,zero_mul]
  rw [hr]
  have hp : ∀ U : Finset V, (if T⊆U then mu.mass (U\T) else 0)*f U=
      if T⊆U then mu.mass (U\T)*f (T∪(U\T)) else 0 := by
    intro U
    by_cases h : T⊆U
    · simp only [if_pos h,union_sdiff_of_subset h]
    · simp only [if_neg h,zero_mul]
  simp_rw [hp]
  rw [← sum_filter]
  exact sum_supersets_sdiff T (fun R => mu.mass R*f (T∪R))

/-- Reversal of the complete fixed-size sample/mark experiment for any
statistic. This is the fixed-size counterpart of the inherited Bernoulli coupling. -/
theorem fixed_marked_sampling_order_reversal (D : Finset V) {N t : ℕ}
    (hN : N ≤ D.card) (ht : t ≤ N) (f : Finset V → Finset V → ℝ) :
    (fixedSizeLaw D N).expect (fun U => (fixedSizeLaw U t).expect (f U))=
      (fixedSizeLaw D t).expect (fun T => (fixedSizeLaw (D\T) (N-t)).expect
        (fun R => f (T∪R) T)) := by
  unfold FiniteLaw.expect
  simp_rw [mul_sum,← mul_assoc,fixed_marked_atom_identity D _ _ hN ht,mul_assoc]
  rw [sum_comm]
  apply sum_congr rfl
  intro T hT
  rw [← mul_sum,← mul_sum]
  by_cases hz : (fixedSizeLaw D t).mass T=0
  · simp only [hz,zero_mul]
  · have hp := lt_of_le_of_ne ((fixedSizeLaw D t).nonneg T) (Ne.symm hz)
    obtain ⟨hTD,hTt⟩ := fixed_size_support D T (ht.trans hN) hp
    have hrest : N-t ≤ (D\T).card := by
      rw [card_sdiff_of_subset hTD,hTt]
      omega
    congr 1
    apply disjoint_remaining_union_expect
    intro R hR
    have hRD := (fixed_size_support (D\T) R hrest hR).1
    exact disjoint_of_subset_left hRD disjoint_sdiff_self_left

end
end Cycle12
