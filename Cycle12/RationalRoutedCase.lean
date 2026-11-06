import Cycle12.CoverRoutedSample
import Cycle12.RationalCapacityParameters

namespace Cycle12
open Real Finset SimpleGraph Cycle13 Cycle13.MixedSample
attribute [local instance] Classical.propDecidable

structure RatCoverRectangle where
  xl : ℚ
  xh : ℚ
  sl : ℚ
  sh : Option ℚ

noncomputable def RatCoverRectangle.Sound (r : RatCoverRectangle) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    (0:ℝ) < Fintype.card G.edgeSet →
    (r.xl:ℝ) ≤ coverGraphX (Fintype.card V) (Fintype.card G.edgeSet) →
    coverGraphX (Fintype.card V) (Fintype.card G.edgeSet) ≤ (r.xh:ℝ) →
    (r.sl:ℝ) ≤ sOf (Fintype.card V) (Fintype.card G.edgeSet) →
    (∀ sh, r.sh=some sh → sOf (Fintype.card V) (Fintype.card G.edgeSet) ≤ (sh:ℝ)) →
    (∀ v, coverDeleteThreshold (Fintype.card V) (Fintype.card G.edgeSet) ≤ (G.degree v:ℝ)) →
    CoverSparseCutIrreducible G → FineCover G 2 ∧ CoarseCover G 1

structure RatRoutedCase where
  capacity : RatCapacityParameters
  sampler : RatSamplerCase

def RatRoutedCase.rectangle (c : RatRoutedCase) : RatCoverRectangle :=
  ⟨c.capacity.bank.sample.xl,c.capacity.bank.sample.xh,c.capacity.bank.sample.s0,c.capacity.bank.maximumScale⟩

def RatRoutedCase.Matches (c : RatRoutedCase) : Prop :=
  c.sampler.moment.inputs.xl ≤ c.capacity.bank.sample.xl ∧
  c.capacity.bank.sample.xh ≤ c.sampler.moment.inputs.xh ∧
  c.sampler.moment.inputs.s0 ≤ c.capacity.bank.sample.s0 ∧
  c.capacity.bank.dm=c.sampler.degree.dm ∧ c.capacity.bank.beta=c.sampler.beta ∧
  c.capacity.bank.L=c.sampler.L ∧
  (c.capacity.localCuts=true → c.sampler.localBeta=some c.capacity.routeBeta)

instance instDecidableRatRoutedMatches (c : RatRoutedCase) : Decidable c.Matches := by
  unfold RatRoutedCase.Matches
  infer_instance

noncomputable section
attribute [local instance] Classical.propDecidable

theorem rat_routed_case_sound (c : RatRoutedCase) (hc : c.Matches)
    (hcap : c.capacity.realParameters.Valid) (hsample : c.sampler.Sound) : c.rectangle.Sound := by
  intro V _ _ G hm hxl hxh hs hbounded hdegree hI
  obtain ⟨hlo,hhi,hs0,hdm,hbeta,hL,hloc⟩ := hc
  refine cover_from_capacity_and_sampler c.capacity.realParameters hcap c.sampler hsample
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ G hm hxl hxh hs ?_ hdegree hI
  · exact (Rat.cast_le (K:=ℝ)).mpr hlo
  · exact (Rat.cast_le (K:=ℝ)).mpr hhi
  · exact (Rat.cast_le (K:=ℝ)).mpr hs0
  · change (c.capacity.bank.dm:ℝ)=(c.sampler.degree.dm:ℝ)
    exact congrArg (fun q : ℚ => (q:ℝ)) hdm
  · change (c.capacity.bank.beta:ℝ)=(c.sampler.beta:ℝ)
    exact congrArg (fun q : ℚ => (q:ℝ)) hbeta
  · change (c.capacity.bank.L:ℝ)=(c.sampler.L:ℝ)
    exact congrArg (fun q : ℚ => (q:ℝ)) hL
  · intro he
    exact ⟨c.capacity.routeBeta,hloc he,rfl⟩
  · intro sh hsh
    change c.capacity.bank.maximumScale.map (fun q => (q:ℝ))=some sh at hsh
    cases he : c.capacity.bank.maximumScale with
    | none => simp [he] at hsh
    | some u =>
      simp [he] at hsh
      rw [← hsh]
      exact hbounded u he

end
end Cycle12
