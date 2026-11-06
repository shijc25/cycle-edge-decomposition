import Cycle12.FixedSampleMGF

namespace Cycle12
open Finset Cycle13 Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem fixed_size_complement_expect (D : Finset V) {k : ℕ} (hk : k ≤ D.card)
    (f : Finset V → ℝ) :
    (fixedSizeLaw D k).expect (fun A => f (D\A))=(fixedSizeLaw D (D.card-k)).expect f := by
  rw [fixed_size_expect D hk,fixed_size_expect D (Nat.sub_le _ _),Nat.choose_symm hk]
  congr 1
  apply sum_bij (fun A _ => D\A)
  · intro A hA
    obtain ⟨hAD,hAk⟩ := mem_powersetCard.mp hA
    exact mem_powersetCard.mpr ⟨sdiff_subset,by rw [card_sdiff_of_subset hAD,hAk]⟩
  · intro A hA B hB he
    have hh := congrArg (fun T => D\T) he
    simpa only [Finset.sdiff_sdiff_eq_self (mem_powersetCard.mp hA).1,
      Finset.sdiff_sdiff_eq_self (mem_powersetCard.mp hB).1] using hh
  · intro B hB
    obtain ⟨hBD,hBk⟩ := mem_powersetCard.mp hB
    refine ⟨D\B,mem_powersetCard.mpr ⟨sdiff_subset,?_⟩,Finset.sdiff_sdiff_eq_self hBD⟩
    rw [card_sdiff_of_subset hBD,hBk]
    omega
  · intro A hA
    rfl

/-- The negative counting MGF follows from exact complementation of a
fixed-size sample, so both Chernoff directions use the correct probability law. -/
theorem fixed_sample_count_mgf_negative (D B : Finset V) (hD : D.Nonempty) (hB : B⊆D)
    {k : ℕ} (hk : k ≤ D.card) {theta : ℝ} (htheta : theta ≤ 0) :
    (fixedSizeLaw D k).expect (fun T => exp (theta*(T∩B).card)) ≤
      (1-((k:ℝ)/D.card)+((k:ℝ)/D.card)*exp theta)^B.card := by
  have hh := fixed_sample_count_mgf D B hD hB (Nat.sub_le D.card k)
    (neg_nonneg.mpr htheta)
  rw [← fixed_size_complement_expect D hk] at hh
  have hid (T : Finset V) (hT : T⊆D) : ((D\T)∩B).card+(T∩B).card=B.card := by
    have he : (D\T)∩B=B\T := by
      ext v
      simp only [mem_inter,mem_sdiff]
      exact ⟨fun h => ⟨h.2,h.1.2⟩,fun h => ⟨⟨hB h.1,h.2⟩,h.1⟩⟩
    rw [he,inter_comm T B]
    exact card_sdiff_add_card_inter B T
  have hscale : (fixedSizeLaw D k).expect (fun T => exp (theta*(T∩B).card))=
      exp (theta*B.card)*(fixedSizeLaw D k).expect
        (fun T => exp ((-theta)*((D\T)∩B).card)) := by
    rw [← FiniteLaw.expect_const_mul]
    apply le_antisymm
    all_goals
      apply FiniteLaw.expect_mono_support
      intro T hT
      have hc : (((D\T)∩B).card:ℝ)+(T∩B).card=B.card := by
        exact_mod_cast hid T (fixed_size_support D T hk hT).1
      have he : exp (theta*B.card)*exp (-theta*((D\T)∩B).card)=exp (theta*(T∩B).card) := by
        rw [← exp_add]
        congr 1
        rw [← hc]
        ring
      rw [he]
  rw [hscale]
  apply (mul_le_mul_of_nonneg_left hh (exp_pos _).le).trans_eq
  have hn : (D.card:ℝ)≠0 := ne_of_gt (by exact_mod_cast card_pos.mpr hD)
  have hp : ((D.card-k:ℕ):ℝ)/(D.card:ℝ)=1-(k:ℝ)/D.card := by
    rw [Nat.cast_sub hk]
    field_simp
  rw [hp,show theta*(B.card:ℝ)=(B.card:ℝ)*theta by ring,exp_nat_mul,← mul_pow]
  congr 1
  have he : exp theta*exp (-theta)=1 := by rw [← exp_add]; simp
  have hm := congrArg (fun x : ℝ => (1-(k:ℝ)/D.card)*x) he
  nlinarith only [hm]

theorem fixed_sample_count_mgf_all (D B : Finset V) (hD : D.Nonempty) (hB : B⊆D)
    {k : ℕ} (hk : k ≤ D.card) (theta : ℝ) :
    (fixedSizeLaw D k).expect (fun T => exp (theta*(T∩B).card)) ≤
      (1-((k:ℝ)/D.card)+((k:ℝ)/D.card)*exp theta)^B.card := by
  rcases le_total 0 theta with h | h
  · exact fixed_sample_count_mgf D B hD hB hk h
  · exact fixed_sample_count_mgf_negative D B hD hB hk h

theorem fixed_sample_count_mgf_exponential (D B : Finset V) (hD : D.Nonempty) (hB : B⊆D)
    {k : ℕ} (hk : k ≤ D.card) (theta : ℝ) :
    (fixedSizeLaw D k).expect (fun T => exp (theta*(T∩B).card)) ≤
      exp (((k:ℝ)/D.card)*(exp theta-1)*B.card) := by
  apply (fixed_sample_count_mgf_all D B hD hB hk theta).trans
  have hn : (0:ℝ)<D.card := by exact_mod_cast card_pos.mpr hD
  have hp : (k:ℝ)/D.card ≤ 1 := (div_le_one hn).mpr (by exact_mod_cast hk)
  have hpn : 0 ≤ (k:ℝ)/D.card := div_nonneg (Nat.cast_nonneg _) hn.le
  have hbase : 0 ≤ 1-((k:ℝ)/D.card)+((k:ℝ)/D.card)*exp theta := by positivity
  have he : 1-((k:ℝ)/D.card)+((k:ℝ)/D.card)*exp theta ≤
      exp (((k:ℝ)/D.card)*(exp theta-1)) := by
    have hh := add_one_le_exp (((k:ℝ)/D.card)*(exp theta-1))
    nlinarith only [hh]
  have hh := pow_le_pow_left₀ hbase he B.card
  rw [← exp_nat_mul] at hh
  convert hh using 1 <;> ring

end
end Cycle12
