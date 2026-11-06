import Cycle12.RationalMarkedGeometry
import Cycle12.RationalWitnessCertificate
import Cycle12.RationalCountingCertificate

namespace Cycle12
open Real Cycle13

structure RatMarkedWitnessBundle where
  geometry : RatMarkedGeometry
  witness : RatWitnessCertificate
  counting : RatCountingCertificate

def RatMarkedWitnessBundle.Matches (b : RatMarkedWitnessBundle) : Prop :=
  b.geometry.qmark=b.witness.qmark ∧ b.geometry.dm=b.witness.dm ∧
  b.geometry.zlo=b.witness.zlo ∧ b.counting.M=b.geometry.M ∧
  b.counting.D=b.geometry.Dlo ∧ b.counting.pl=b.geometry.inputs.pl

instance instDecidableRatMarkedWitnessMatches (b : RatMarkedWitnessBundle) : Decidable b.Matches := by
  unfold RatMarkedWitnessBundle.Matches
  infer_instance

noncomputable section

theorem fixed_residual_probability_le_sample (n N t : ℕ) (hN : N ≤ n) (ht : t < N) :
    ((N-t:ℕ):ℝ)/(n-t:ℕ) ≤ (N:ℝ)/n := by
  have htD : t < n := ht.trans_le hN
  have hden : (0:ℝ) < (n-t:ℕ) := by exact_mod_cast Nat.sub_pos_of_lt htD
  have hn : (0:ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt htD
  apply (div_le_div_iff₀ hden hn).mpr
  rw [Nat.cast_sub ht.le,Nat.cast_sub htD.le]
  have hNreal : (N:ℝ) ≤ n := by exact_mod_cast hN
  have hh := mul_le_mul_of_nonneg_right hNreal (Nat.cast_nonneg t : (0:ℝ) ≤ t)
  nlinarith only [hh]

def RatMarkedWitnessBundle.Sound (b : RatMarkedWitnessBundle) : Prop :=
  ∀ {x s : ℝ} {n N : ℕ}, 0 < x → (b.geometry.inputs.xl:ℝ) ≤ x → x ≤ (b.geometry.inputs.xh:ℝ) →
    (b.geometry.inputs.s0:ℝ) ≤ s → (n:ℝ)=4*(43/10)^3*s^2/(coverScaleW x)^3 →
    N=⌊coverSampleP x*(n:ℝ)⌋₊ →
    let p := (N:ℝ)/n
    let P := p/coverScaleW x
    let R := coverScaleR x s
    let z := coverScaleZ x s P
    let t := ⌈(b.witness.qmark:ℝ)*R⌉₊
    t < N ∧ 0 < (b.witness.omega:ℝ) ∧ 2 < (b.witness.dm:ℝ)*z ∧
    b.witness.LowerBound z ∧
    (b.witness.dm:ℝ)*(b.witness.qmark:ℝ) ≤ ((t:ℝ)/N)*((b.witness.dm:ℝ)*z) ∧
    1-((N-t:ℕ):ℝ)/(n-t:ℕ)+((N-t:ℕ):ℝ)/(n-t:ℕ)*exp (b.counting.theta:ℝ) ≤
      exp ((b.counting.theta:ℝ)*(b.counting.slope:ℝ)*p) ∧
    2*exp (-(b.counting.theta:ℝ)*((b.counting.intercept:ℝ)*z))*
      (1+exp ((b.counting.theta:ℝ)-(b.counting.theta:ℝ)*(b.counting.slope:ℝ)*p))^t ≤
        2*exp (-(b.counting.aa:ℝ)*R)

/-- Joins the independent numeric certificates at the actual floor sample
and ceil marks. No scale, vote-mean, MGF or counting-tail hypothesis remains. -/
theorem rat_marked_witness_bundle_sound (b : RatMarkedWitnessBundle)
    (hg : b.geometry.Valid) (hi : b.geometry.inputs.Valid)
    (hgeo : b.geometry.Sound) (hw : b.witness.Sound) (hc : b.counting.Sound)
    (hm : b.Matches) : b.Sound := by
  obtain ⟨hqm,hdm,hzm,hMM,hDD,hpp⟩ := hm
  intro x s n N hx hxl hxh hs hn hN
  let p : ℝ := (N:ℝ)/n
  let P : ℝ := p/coverScaleW x
  let R := coverScaleR x s
  let z := coverScaleZ x s P
  let t := ⌈(b.witness.qmark:ℝ)*R⌉₊
  obtain ⟨hRlo,hzlo,hDlo,hWlo,hNn,hNhalf,hpl,hpu,hp0,hphalf,ht,hq,hM,hvote,hps,hres0,hresHalf⟩ :=
    hgeo hx hxl hxh hs hn hN
  rw [hqm] at ht hq hM hvote hps hres0 hresHalf
  rw [hdm] at hvote
  rw [hzm] at hzlo
  have hwz := hw.2 z hzlo
  have hres := fixed_residual_probability_le_sample n N t hNn ht
  have hmgf := hc.1 p (((N-t:ℕ):ℝ)/(n-t:ℕ)) hp0.le (by rwa [hpp]) hres
  have hRp : 0 < R := (show (0:ℝ) < (b.geometry.Rlo:ℝ) by exact_mod_cast hg.1).trans_le hRlo
  have hsmin := (rat_moment_certificate_valid b.geometry.inputs hi).sampling.density_lower
  have hs0 : (0:ℝ) < (b.geometry.inputs.s0:ℝ) := by
    change (1:ℝ) ≤ (b.geometry.inputs.s0:ℝ) at hsmin
    linarith only [hsmin]
  have hmax := (rat_moment_certificate_valid b.geometry.inputs hi).sampling.xmax
  have hDidentity := (cover_scale_relations (P:=P) hx (hxh.trans hmax) (hs0.trans_le hs) hn).1
  change z/R=coverScaleD x P at hDidentity
  have hDz : (b.counting.D:ℝ)*R ≤ z := by
    rw [hDD]
    exact (le_div_iff₀ hRp).mp (by rwa [hDidentity])
  have hmarks : (t:ℝ) ≤ (b.counting.M:ℝ)*R := by
    rw [hMM]
    exact (div_le_iff₀ hRp).mp hM
  exact ⟨ht,hw.1,hwz.1,hwz.2.1,hvote,hmgf,hc.2 hRp hDz (by rwa [hpp]) hmarks⟩

end
end Cycle12
