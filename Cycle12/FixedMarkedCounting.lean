import Cycle12.FixedSampleTails
import Cycle12.FixedMarkedCoupling

namespace Cycle12
open Finset Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem fixed_marked_side_card (D T S R : Finset V) (hR : R⊆D\T) :
    ((T∪R)∩S).card=(S∩T).card+(R∩(S\T)).card := by
  have he : (T∪R)∩S=(S∩T)∪(R∩(S\T)) := by
    ext v
    simp only [mem_inter,mem_union,mem_sdiff]
    constructor
    · rintro ⟨hvT | hvR,hvS⟩
      · exact Or.inl ⟨hvS,hvT⟩
      · exact Or.inr ⟨hvR,hvS,(mem_sdiff.mp (hR hvR)).2⟩
    · rintro (h | h)
      · exact ⟨Or.inl h.2,h.1⟩
      · exact ⟨Or.inr h.1,h.2.1⟩
  rw [he,card_union_of_disjoint]
  apply disjoint_left.mpr
  intro v hv hw
  exact (mem_sdiff.mp (mem_inter.mp hw).2).2 (mem_inter.mp hv).2

theorem fixed_marked_side_mgf (D T S : Finset V) (hT : T⊆D) (hS : S⊆D)
    {N : ℕ} (hN : N ≤ D.card) (hTN : T.card ≤ N) (hTD : T.card<D.card)
    {theta lam : ℝ} (htheta : 0 ≤ theta)
    (hbase : 1-((N-T.card:ℕ):ℝ)/(D.card-T.card)+
      ((N-T.card:ℕ):ℝ)/(D.card-T.card)*exp theta ≤ exp lam) :
    (fixedSizeLaw (D\T) (N-T.card)).expect
        (fun R => exp (theta*((T∪R)∩S).card)) ≤
      exp (lam*S.card+(theta-lam)*(S∩T).card) := by
  have hrest : (D\T).Nonempty := card_pos.mp (by rw [card_sdiff_of_subset hT]; omega)
  have hk : N-T.card ≤ (D\T).card := by rw [card_sdiff_of_subset hT]; omega
  have hB : S\T⊆D\T := sdiff_subset_sdiff_left T hS
  have hh := fixed_sample_count_mgf (D\T) (S\T) hrest hB hk htheta
  have hsplit : (fixedSizeLaw (D\T) (N-T.card)).expect
      (fun R => exp (theta*((T∪R)∩S).card)) ≤
      exp (theta*(S∩T).card)*(fixedSizeLaw (D\T) (N-T.card)).expect
        (fun R => exp (theta*(R∩(S\T)).card)) := by
    rw [← FiniteLaw.expect_const_mul]
    apply FiniteLaw.expect_mono_support
    intro R hR
    rw [fixed_marked_side_card D T S R (fixed_size_support (D\T) R hk hR).1,Nat.cast_add,
      mul_add,exp_add]
  have hnn : 0 ≤ 1-((N-T.card:ℕ):ℝ)/(D.card-T.card)+
      ((N-T.card:ℕ):ℝ)/(D.card-T.card)*exp theta := by
    have hden : (0:ℝ)<(D.card:ℝ)-T.card := sub_pos.mpr (by exact_mod_cast hTD)
    have hnum : ((N-T.card:ℕ):ℝ) ≤ (D.card:ℝ)-T.card := by
      rw [Nat.cast_sub hTN]
      exact sub_le_sub_right (by exact_mod_cast hN) _
    exact add_nonneg (sub_nonneg.mpr ((div_le_one hden).mpr hnum))
      (mul_nonneg (div_nonneg (Nat.cast_nonneg _) hden.le) (exp_pos _).le)
  have hpow := pow_le_pow_left₀ hnn hbase (S\T).card
  rw [card_sdiff_of_subset hT,Nat.cast_sub (card_le_card hT)] at hh
  have hsum : ((S\T).card:ℝ)+(S∩T).card=S.card := by
    exact_mod_cast card_sdiff_add_card_inter S T
  apply hsplit.trans
  apply (mul_le_mul_of_nonneg_left (hh.trans hpow) (exp_pos _).le).trans_eq
  rw [← exp_nat_mul,← exp_add]
  congr 1
  rw [← hsum]
  ring

theorem fixed_marked_side_tail (D T S : Finset V) (hT : T⊆D) (hS : S⊆D)
    {N : ℕ} (hN : N ≤ D.card) (hTN : T.card ≤ N) (hTD : T.card<D.card)
    {theta lam err : ℝ} (htheta : 0<theta)
    (hbase : 1-((N-T.card:ℕ):ℝ)/(D.card-T.card)+
      ((N-T.card:ℕ):ℝ)/(D.card-T.card)*exp theta ≤ exp lam) :
    (fixedSizeLaw (D\T) (N-T.card)).prob
        (fun R => (lam/theta)*S.card+err < (((T∪R)∩S).card:ℝ)) ≤
      exp (-theta*err+(theta-lam)*(S∩T).card) := by
  have hm := (fixedSizeLaw (D\T) (N-T.card)).exp_markov
    (fun R => (((T∪R)∩S).card:ℝ)) theta ((lam/theta)*S.card+err) htheta
  have hb := mul_le_mul_of_nonneg_left (fixed_marked_side_mgf D T S hT hS hN hTN hTD htheta.le hbase)
    (exp_pos (-theta*((lam/theta)*S.card+err))).le
  apply hm.trans
  apply hb.trans_eq
  rw [← exp_add]
  congr 1
  field_simp
  <;> ring

theorem prob_exists_finset_le_sum {Ω I : Type} [Fintype Ω] [DecidableEq I]
    (mu : FiniteLaw Ω) (S : Finset I) (E : I → Ω → Prop) :
    mu.prob (fun w => ∃ i∈S, E i w) ≤ ∑ i∈S, mu.prob (E i) := by
  induction S using Finset.induction_on with
  | empty => simp [FiniteLaw.prob]
  | @insert i S hi ih =>
    have he : (fun w => ∃ j∈insert i S, E j w)=(fun w => E i w ∨ ∃ j∈S,E j w) := by
      funext w
      apply propext
      simp
    rw [he,sum_insert hi]
    apply (mu.prob_union_le _ _).trans
    linarith only [ih]

/-- Sum all label-dependent classified sides exactly. Their mark intersection
is the label itself, so the label budget is a binomial generating function. -/
theorem fixed_marked_all_labels_tail (D T : Finset V) (S : Finset V → Finset V)
    (hT : T⊆D) {N : ℕ} (hN : N ≤ D.card) (hTN : T.card ≤ N) (hTD : T.card<D.card)
    (hS : ∀ A⊆T, S A⊆D) (hlabel : ∀ A⊆T, S A∩T=A)
    {theta lam err : ℝ} (htheta : 0<theta)
    (hbase : 1-((N-T.card:ℕ):ℝ)/(D.card-T.card)+
      ((N-T.card:ℕ):ℝ)/(D.card-T.card)*exp theta ≤ exp lam) :
    (fixedSizeLaw (D\T) (N-T.card)).prob (fun R => ∃ A⊆T,
        (lam/theta)*(S A).card+err < (((T∪R)∩S A).card:ℝ)) ≤
      exp (-theta*err)*(1+exp (theta-lam))^T.card := by
  have hu := prob_exists_finset_le_sum (fixedSizeLaw (D\T) (N-T.card)) T.powerset
    (fun A R => (lam/theta)*(S A).card+err < (((T∪R)∩S A).card:ℝ))
  simp only [mem_powerset] at hu
  apply hu.trans
  calc
    _ ≤ ∑ A∈T.powerset, exp (-theta*err+(theta-lam)*A.card) := by
      apply sum_le_sum
      intro A hA
      have ha := mem_powerset.mp hA
      have hh := fixed_marked_side_tail D T (S A) hT (hS A ha) hN hTN hTD htheta hbase (err:=err)
      simpa only [hlabel A ha] using hh
    _ = _ := by
      simp_rw [exp_add]
      rw [← mul_sum,label_exponential_sum]

end
end Cycle12
