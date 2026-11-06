import Cycle12.FixedSampleMiss

namespace Cycle12
open Finset Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem fixed_size_contains_symmetric (D S : Finset V) (hS : S⊆D)
    {k : ℕ} (hk : k ≤ D.card) (hSk : S.card ≤ k) :
    (fixedSizeLaw D k).prob (fun A => S⊆A)=(k.choose S.card:ℝ)/(D.card.choose S.card:ℝ) := by
  rw [fixed_size_contains_probability D S hk hS hSk]
  have h₁ : (0:ℝ)<(D.card.choose k:ℝ) := by exact_mod_cast Nat.choose_pos hk
  have h₂ : (0:ℝ)<(D.card.choose S.card:ℝ) := by exact_mod_cast Nat.choose_pos (hSk.trans hk)
  have hh : (D.card.choose k:ℝ)*(k.choose S.card:ℝ)=
      (D.card.choose S.card:ℝ)*((D.card-S.card).choose (k-S.card):ℝ) := by
    exact_mod_cast (Nat.choose_mul (n:=D.card) hSk)
  apply (div_eq_div_iff h₁.ne' h₂.ne').mpr
  nlinarith only [hh]

/-- Every fixed set has the usual negative-correlation containment bound. -/
theorem fixed_size_contains_le (D S : Finset V) (hD : D.Nonempty) (hS : S⊆D)
    {k : ℕ} (hk : k ≤ D.card) :
    (fixedSizeLaw D k).prob (fun A => S⊆A) ≤ ((k:ℝ)/D.card)^S.card := by
  by_cases hs : S.card ≤ k
  · rw [fixed_size_contains_symmetric D S hS hk hs]
    exact choose_ratio_le_power hk (card_pos.mpr hD) (card_le_card hS)
  · have hp : (fixedSizeLaw D k).prob (fun A => S⊆A) ≤
        (fixedSizeLaw D k).prob (fun _ => False) := by
      apply FiniteLaw.prob_mono_support
      intro A hA hSA
      have hc := (fixed_size_support D A hk hA).2
      have hh := card_le_card hSA
      omega
    have hz : (fixedSizeLaw D k).prob (fun _ => False)=0 := by
      simp only [FiniteLaw.prob,ite_false,FiniteLaw.expect_const]
    rw [hz] at hp
    exact hp.trans (pow_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _)

theorem intersection_power_expansion (B T : Finset V) (u : ℝ) :
    (1+u)^(T∩B).card=∑ S∈B.powerset, if S⊆T then u^S.card else 0 := by
  have hprod : ∀ S : Finset V, (∏ v∈S, if v∈T then u else 0)=
      if S⊆T then u^S.card else 0 := by
    intro S
    by_cases hS : S⊆T
    · rw [if_pos hS]
      calc
        _ = ∏ _v∈S, u := prod_congr rfl (fun v hv => if_pos (hS hv))
        _ = _ := by rw [prod_const]
    · rw [if_neg hS]
      obtain ⟨v,hvS,hvT⟩ := not_subset.mp hS
      exact prod_eq_zero hvS (if_neg hvT)
  have hh := prod_one_add (s:=B) (f:=fun v => if v∈T then u else 0)
  simp_rw [hprod] at hh
  rw [← hh]
  have he (v : V) : 1+(if v∈T then u else 0)=if v∈T then 1+u else 1 := by
    split_ifs <;> simp
  simp_rw [he]
  rw [prod_ite]
  simp only [prod_const,one_pow,mul_one,filter_mem_eq_inter,inter_comm B T]

/-- The full positive counting MGF is controlled by the Bernoulli power,
proved directly from the uniform fixed-size law and the subset expansion. -/
theorem fixed_sample_count_power (D B : Finset V) (hD : D.Nonempty) (hB : B⊆D)
    {k : ℕ} (hk : k ≤ D.card) {u : ℝ} (hu : 0 ≤ u) :
    (fixedSizeLaw D k).expect (fun T => (1+u)^(T∩B).card) ≤
      (1+((k:ℝ)/D.card)*u)^B.card := by
  simp_rw [intersection_power_expansion,FiniteLaw.expect_finset_sum]
  have hterm (S : Finset V) : (fixedSizeLaw D k).expect
      (fun T => if S⊆T then u^S.card else 0)=
      u^S.card*(fixedSizeLaw D k).prob (fun T => S⊆T) := by
    rw [FiniteLaw.prob,← FiniteLaw.expect_const_mul]
    congr 1
    funext T
    by_cases h : S⊆T <;> simp [h]
  simp_rw [hterm]
  calc
    _ ≤ ∑ S∈B.powerset, (((k:ℝ)/D.card)*u)^S.card := by
      apply sum_le_sum
      intro S hS
      have hh := mul_le_mul_of_nonneg_left
        (fixed_size_contains_le D S hD ((mem_powerset.mp hS).trans hB) hk) (pow_nonneg hu S.card)
      simpa only [mul_pow,mul_comm] using hh
    _ = _ := by
      have hh := prod_one_add (s:=B) (f:=fun _ => ((k:ℝ)/D.card)*u)
      simpa only [prod_const] using hh.symm

theorem fixed_sample_count_mgf (D B : Finset V) (hD : D.Nonempty) (hB : B⊆D)
    {k : ℕ} (hk : k ≤ D.card) {theta : ℝ} (htheta : 0 ≤ theta) :
    (fixedSizeLaw D k).expect (fun T => exp (theta*(T∩B).card)) ≤
      (1-((k:ℝ)/D.card)+((k:ℝ)/D.card)*exp theta)^B.card := by
  have hu : 0 ≤ exp theta-1 := sub_nonneg.mpr (one_le_exp_iff.mpr htheta)
  have hh := fixed_sample_count_power D B hD hB hk hu
  have he (T : Finset V) : (1+(exp theta-1))^(T∩B).card=exp (theta*(T∩B).card) := by
    rw [add_sub_cancel,← exp_nat_mul,mul_comm]
  simp_rw [he] at hh
  convert hh using 1 <;> ring

end
end Cycle12
