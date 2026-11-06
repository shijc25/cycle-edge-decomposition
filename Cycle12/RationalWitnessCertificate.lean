import Cycle12.CoverWitnessMonotonicity
import Cycle12.RationalMajorityInputs

namespace Cycle12
open Real Cycle13

inductive CoverWitnessKind where
  | globalCut | anchor | localCut
  deriving DecidableEq

def ratMissSix : ℚ := (49787068367863943/1000000000000000000)^2

theorem exp_neg_six_le_ratMissSix : exp (-6) ≤ (ratMissSix:ℝ) := by
  have hh := rational_negative_exp_upper (q:=6) (x:=3)
    (r:=49787068367863943/1000000000000000000) 30
    (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
  norm_num [ratMissSix] at hh ⊢
  exact hh

structure RatWitnessCertificate where
  kind : CoverWitnessKind
  majority : RatMajorityEnvelope
  dm : ℚ
  beta : ℚ
  zlo : ℚ
  qmark : ℚ
  L : ℚ
  factor : ℚ
  error : ℚ
  fullCorrection : ℚ
  omega : ℚ

def RatWitnessCertificate.BranchValid (c : RatWitnessCertificate) : Prop :=
  match c.kind with
  | .globalCut =>
    c.beta < c.factor ∧ c.factor < c.dm ∧ c.majority.c=1+c.factor/c.dm ∧
    c.omega ≤ 1-(2*c.majority.bound*c.beta+(c.dm+c.factor)*c.majority.inputs.reciprocal^2)/
      (c.factor-c.beta)-ratMissSix
  | .anchor =>
    0 < c.factor ∧ c.majority.c=1 ∧ 1 ≤ c.fullCorrection ∧
    (9/8)*c.majority.inputs.lower^2/((c.majority.inputs.lower-1)*(c.majority.inputs.lower-2)) ≤ c.fullCorrection ∧
    c.omega ≤ 1-(2*c.majority.bound+(c.dm/c.beta)*c.majority.inputs.reciprocal^2)/c.factor-
      8*(c.fullCorrection*c.L/(c.dm*c.zlo)+c.majority.inputs.reciprocal^2)
  | .localCut =>
    0 < c.error ∧ c.majority.c=1 ∧
    c.omega ≤ 1-(2*c.majority.bound*c.beta+c.dm*c.majority.inputs.reciprocal^2)/c.error-ratMissSix

def RatWitnessCertificate.Valid (c : RatWitnessCertificate) : Prop :=
  c.majority.inputs.Valid ∧ 0 < c.dm ∧ 0 < c.beta ∧ 0 < c.zlo ∧
  0 < c.qmark ∧ 0 < c.L ∧ 0 < c.omega ∧ 0 ≤ c.majority.bound ∧
  c.majority.inputs.lower=c.dm*c.zlo ∧ c.majority.inputs.mean=c.dm*c.qmark ∧
  3 ≤ c.majority.inputs.mean ∧ c.BranchValid

instance instDecidableRatWitnessBranchValid (c : RatWitnessCertificate) : Decidable c.BranchValid := by
  unfold RatWitnessCertificate.BranchValid
  cases c.kind <;> infer_instance

instance instDecidableRatWitnessValid (c : RatWitnessCertificate) : Decidable c.Valid := by
  unfold RatWitnessCertificate.Valid
  infer_instance

noncomputable section

def RatWitnessCertificate.LowerBound (c : RatWitnessCertificate) (z : ℝ) : Prop :=
  match c.kind with
  | .globalCut =>
    (c.omega:ℝ) ≤ 1-(2*(c.majority.bound:ℝ)*(c.beta:ℝ)+((c.dm:ℝ)+(c.factor:ℝ))*
      exp (-(c.majority.inputs.mean:ℝ)))/((c.factor:ℝ)-(c.beta:ℝ))-exp (-6)
  | .anchor =>
    majorityCorrection ((c.dm:ℝ)*z)*(9/8) ≤ (c.fullCorrection:ℝ) ∧
    (c.omega:ℝ) ≤ 1-(2*(c.majority.bound:ℝ)+((c.dm:ℝ)/(c.beta:ℝ))*exp (-(c.majority.inputs.mean:ℝ)))/
      (c.factor:ℝ)-((c.fullCorrection:ℝ)*(c.L:ℝ)/((c.dm:ℝ)*z)+exp (-(c.majority.inputs.mean:ℝ)))/(1/8)
  | .localCut =>
    (c.omega:ℝ) ≤ 1-(2*(c.majority.bound:ℝ)*(c.beta:ℝ)+(c.dm:ℝ)*exp (-(c.majority.inputs.mean:ℝ)))/
      (c.error:ℝ)-exp (-6)

def RatWitnessCertificate.Sound (c : RatWitnessCertificate) : Prop :=
  0 < (c.omega:ℝ) ∧ ∀ z : ℝ, (c.zlo:ℝ) ≤ z →
    2 < (c.dm:ℝ)*z ∧ c.LowerBound z ∧
    ∀ rho : ℝ, 0 ≤ rho → rho ≤ 1 →
      majorityCorrection ((c.dm:ℝ)*z)*((c.majority.c:ℝ)-rho)*(3*rho-2*rho^2) ≤ (c.majority.bound:ℝ) ∧
      ((c.majority.c:ℝ)-rho)*(min 1 (poissonTailTwo (c.majority.inputs.mean:ℝ))+
        (1-min 1 (poissonTailTwo (c.majority.inputs.mean:ℝ)))*majorityCorrection ((c.dm:ℝ)*z)*
          (3*rho-2*rho^2)) ≤ (c.majority.bound:ℝ)

theorem rat_witness_certificate_sound (c : RatWitnessCertificate) (hc : c.Valid)
    (hmajority : c.majority.Sound) : c.Sound := by
  obtain ⟨hi,hdm,hb,hzlo,hq,hL,ho,hK,hdelta,hmean,hmean3,hbranch⟩ := hc
  have hd0 : 2 < (c.majority.inputs.lower:ℝ) := by exact_mod_cast hi.1
  have hdeltaR : (c.majority.inputs.lower:ℝ)=(c.dm:ℝ)*(c.zlo:ℝ) := by exact_mod_cast hdelta
  have he := rational_negative_exp_upper c.majority.inputs.terms hi.2.2.2.1 hi.2.2.2.2.1
    hi.2.2.2.2.2.1 hi.2.2.2.2.2.2.1
  have hdmR : (0:ℝ) < (c.dm:ℝ) := by exact_mod_cast hdm
  have hbR : (0:ℝ) < (c.beta:ℝ) := by exact_mod_cast hb
  have hL0 : (0:ℝ) ≤ (c.L:ℝ) := by exact_mod_cast hL.le
  refine ⟨by exact_mod_cast ho,?_⟩
  intro z hz
  have hd : (c.majority.inputs.lower:ℝ) ≤ (c.dm:ℝ)*z := by
    rw [hdeltaR]
    exact mul_le_mul_of_nonneg_left hz hdmR.le
  refine ⟨hd0.trans_le hd,?_,fun rho hr0 hr1 => hmajority _ hd rho hr0 hr1⟩
  cases hk : c.kind with
  | globalCut =>
    rw [RatWitnessCertificate.BranchValid,hk] at hbranch
    obtain ⟨hgap,ht,_,hw⟩ := hbranch
    have hwR := (Rat.cast_le (K:=ℝ)).mpr hw
    norm_num only [Rat.cast_sub,Rat.cast_div,Rat.cast_mul,Rat.cast_add,Rat.cast_pow,
      Rat.cast_one,Rat.cast_ofNat] at hwR
    rw [RatWitnessCertificate.LowerBound,hk]
    exact global_witness_lower_transfer hdmR.le
      (by exact_mod_cast (hb.trans hgap).le) (by exact_mod_cast hgap) he exp_neg_six_le_ratMissSix hwR
  | anchor =>
    rw [RatWitnessCertificate.BranchValid,hk] at hbranch
    obtain ⟨hew,_,hf1,hf,hw⟩ := hbranch
    have hwR := (Rat.cast_le (K:=ℝ)).mpr hw
    norm_num only [Rat.cast_sub,Rat.cast_div,Rat.cast_mul,Rat.cast_add,Rat.cast_pow,
      Rat.cast_one,Rat.cast_ofNat] at hwR
    have hfR : (9/8)*majorityCorrection (c.majority.inputs.lower:ℝ) ≤ (c.fullCorrection:ℝ) := by
      have hh := (Rat.cast_le (K:=ℝ)).mpr hf
      norm_num only [Rat.cast_div,Rat.cast_mul,Rat.cast_pow,Rat.cast_sub,Rat.cast_ofNat,Rat.cast_one] at hh
      simpa only [majorityCorrection,mul_div_assoc] using hh
    rw [RatWitnessCertificate.LowerBound,hk]
    exact ⟨full_majority_correction_transfer hd0 hd hfR,
      anchor_witness_lower_transfer hdmR hbR hL0 (by exact_mod_cast hew)
        (by exact_mod_cast hzlo) hz (by exact_mod_cast (le_trans (by norm_num : (0:ℚ) ≤ 1) hf1)) he hwR⟩
  | localCut =>
    rw [RatWitnessCertificate.BranchValid,hk] at hbranch
    obtain ⟨herr,_,hw⟩ := hbranch
    have hwR := (Rat.cast_le (K:=ℝ)).mpr hw
    norm_num only [Rat.cast_sub,Rat.cast_div,Rat.cast_mul,Rat.cast_add,Rat.cast_pow,
      Rat.cast_one,Rat.cast_ofNat] at hwR
    rw [RatWitnessCertificate.LowerBound,hk]
    exact local_witness_lower_transfer hdmR.le (by exact_mod_cast herr) he exp_neg_six_le_ratMissSix hwR

end
end Cycle12
