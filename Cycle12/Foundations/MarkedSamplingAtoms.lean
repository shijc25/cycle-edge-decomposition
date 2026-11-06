import Cycle12.Foundations.FiniteBernoulli

/-! Exact atom identity for the two orders of the same marked sample.
First sample U then mark T inside U, or first sample T then add an
independent residual sample outside T. -/
namespace Cycle13
open Finset Real
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

def subsetBernoulli (A : Finset V) (p : unitInterval) : FiniteLaw (Finset V) where
  mass S := if S⊆A then (p:ℝ)^S.card*(1-(p:ℝ))^(A.card-S.card) else 0
  nonneg S := by split_ifs; exact mul_nonneg (pow_nonneg p.2.1 _)
                  (pow_nonneg (by linarith [p.2.2]) _); exact le_rfl
  total := by
    rw [← sum_filter]
    have he : univ.filter (fun S : Finset V => S⊆A)=A.powerset := by ext S; simp
    rw [he,sum_pow_mul_eq_add_pow]
    simp

theorem subsetBernoulli_mass (A S : Finset V) (p : unitInterval) (h : S⊆A) :
    (subsetBernoulli A p).mass S=(p:ℝ)^S.card*(1-(p:ℝ))^(A.card-S.card) := if_pos h

theorem subsetBernoulli_mass_not_subset (A S : Finset V) (p : unitInterval) (h : ¬S⊆A) :
    (subsetBernoulli A p).mass S=0 := if_neg h

theorem marked_sampling_atom_identity (p q markP ρ : unitInterval)
    (hmarkP : (markP:ℝ)=(p:ℝ)*(q:ℝ))
    (hρ : (1-(markP:ℝ))*(ρ:ℝ)=(p:ℝ)*(1-(q:ℝ))) (U T : Finset V) :
    (bernoulliSubset p).mass U*(subsetBernoulli U q).mass T=
      (bernoulliSubset markP).mass T*
        (if T⊆U then (subsetBernoulli (univ\T) ρ).mass (U\T) else 0) := by
  by_cases hTU : T⊆U
  · have hsub : U\T⊆univ\T := sdiff_subset_sdiff_left T (subset_univ U)
    rw [if_pos hTU,subsetBernoulli_mass _ _ _ hTU,subsetBernoulli_mass _ _ _ hsub]
    have hcount : U.card=T.card+(U\T).card := by
      have hh := card_sdiff_add_card_eq_card hTU; omega
    have hout : Fintype.card V=U.card+(univ\U).card := by
      have hh := card_sdiff_add_card_eq_card (subset_univ U); rw [card_univ] at hh; omega
    have htc : (univ\T).card=Fintype.card V-T.card := by rw [card_sdiff_of_subset (subset_univ _),card_univ]
    have hnot : (1-(markP:ℝ))*(1-(ρ:ℝ))=1-(p:ℝ) := by nlinarith
    change (p:ℝ)^U.card*(1-(p:ℝ))^(Fintype.card V-U.card)*
        ((q:ℝ)^T.card*(1-(q:ℝ))^(U.card-T.card))=
      (markP:ℝ)^T.card*(1-(markP:ℝ))^(Fintype.card V-T.card)*
        ((ρ:ℝ)^(U\T).card*(1-(ρ:ℝ))^((univ\T).card-(U\T).card))
    have h₁ : Fintype.card V-U.card=(univ\U).card := by omega
    have h₂ : U.card-T.card=(U\T).card := by omega
    have h₃ : Fintype.card V-T.card=(U\T).card+(univ\U).card := by omega
    have h₄ : (univ\T).card-(U\T).card=(univ\U).card := by omega
    rw [h₁,h₂,h₃,h₄,hcount]
    calc
      _ = ((p:ℝ)*(q:ℝ))^T.card*((p:ℝ)*(1-(q:ℝ)))^(U\T).card*
          (1-(p:ℝ))^(univ\U).card := by rw [pow_add,mul_pow,mul_pow]; ring
      _ = (markP:ℝ)^T.card*((1-(markP:ℝ))*(ρ:ℝ))^(U\T).card*
          ((1-(markP:ℝ))*(1-(ρ:ℝ)))^(univ\U).card := by rw [hρ,hnot,hmarkP]
      _ = _ := by rw [pow_add,mul_pow,mul_pow]; ring
  · rw [if_neg hTU,subsetBernoulli_mass_not_subset _ _ _ hTU,mul_zero,mul_zero]

theorem residual_probability_bounds (p q : unitInterval) (h : (p:ℝ)*(q:ℝ) < 1) :
    0 ≤ (p:ℝ)*(1-(q:ℝ))/(1-(p:ℝ)*(q:ℝ)) ∧
      (p:ℝ)*(1-(q:ℝ))/(1-(p:ℝ)*(q:ℝ)) ≤ (p:ℝ) := by
  have hden : 0 < 1-(p:ℝ)*(q:ℝ) := by linarith
  constructor
  · exact div_nonneg (mul_nonneg p.2.1 (by linarith [q.2.2])) hden.le
  · apply (div_le_iff₀ hden).mpr
    have hh : 0 ≤ (p:ℝ)*(q:ℝ)*(1-(p:ℝ)) := mul_nonneg
      (mul_nonneg p.2.1 q.2.1) (by linarith [p.2.2])
    nlinarith

def markProbability (p q : unitInterval) : unitInterval :=
  ⟨(p:ℝ)*(q:ℝ),mul_nonneg p.2.1 q.2.1,by
    have hh := mul_le_mul p.2.2 q.2.2 q.2.1 (by norm_num : (0:ℝ) ≤ 1)
    simpa only [one_mul] using hh⟩

def residualProbability (p q : unitInterval) (h : (p:ℝ)*(q:ℝ) < 1) : unitInterval :=
  ⟨(p:ℝ)*(1-(q:ℝ))/(1-(p:ℝ)*(q:ℝ)),(residual_probability_bounds p q h).1,
    (residual_probability_bounds p q h).2.trans p.2.2⟩

theorem residualProbability_identity (p q : unitInterval) (h : (p:ℝ)*(q:ℝ) < 1) :
    (1-(markProbability p q:ℝ))*(residualProbability p q h:ℝ)=(p:ℝ)*(1-(q:ℝ)) := by
  change (1-(p:ℝ)*(q:ℝ))*((p:ℝ)*(1-(q:ℝ))/(1-(p:ℝ)*(q:ℝ)))=_
  field_simp [ne_of_gt (show 0 < 1-(p:ℝ)*(q:ℝ) by linarith)]

end
end Cycle13
