import Cycle12.DirectRoutedSample
import Cycle12.RationalDirectParameters
import Cycle12.RationalRoutedCase

namespace Cycle12
open Real Finset SimpleGraph Cycle13 Cycle13.MixedSample
attribute [local instance] Classical.propDecidable

structure RatDirectCase where
  bank : RatDirectParameters
  sampler : RatSamplerCase

def RatDirectCase.rectangle (c : RatDirectCase) : RatCoverRectangle :=
  ⟨c.bank.sample.xl,c.bank.sample.xh,c.bank.sample.s0,none⟩

def RatDirectCase.Matches (c : RatDirectCase) : Prop :=
  c.sampler.moment.inputs.xl ≤ c.bank.sample.xl ∧
  c.bank.sample.xh ≤ c.sampler.moment.inputs.xh ∧
  c.sampler.moment.inputs.s0 ≤ c.bank.sample.s0 ∧
  c.bank.dm=c.sampler.degree.dm ∧ c.bank.beta=c.sampler.beta ∧ c.bank.L=c.sampler.L

instance instDecidableRatDirectMatches (c : RatDirectCase) : Decidable c.Matches := by
  unfold RatDirectCase.Matches
  infer_instance

noncomputable section

theorem rat_direct_case_sound (c : RatDirectCase) (hc : c.Matches)
    (hbank : c.bank.realParameters.Valid) (hsample : c.sampler.Sound) : c.rectangle.Sound := by
  intro V _ _ G hm hxl hxh hs _ hdegree hI
  obtain ⟨hlo,hhi,hs0,hdm,hbeta,hL⟩ := hc
  refine cover_from_direct_and_sampler c.bank.realParameters hbank c.sampler hsample
    ?_ ?_ ?_ ?_ ?_ ?_ G hm hxl hxh hs hdegree hI
  · exact (Rat.cast_le (K:=ℝ)).mpr hlo
  · exact (Rat.cast_le (K:=ℝ)).mpr hhi
  · exact (Rat.cast_le (K:=ℝ)).mpr hs0
  · change (c.bank.dm:ℝ)=(c.sampler.degree.dm:ℝ)
    exact congrArg (fun q : ℚ => (q:ℝ)) hdm
  · change (c.bank.beta:ℝ)=(c.sampler.beta:ℝ)
    exact congrArg (fun q : ℚ => (q:ℝ)) hbeta
  · change (c.bank.L:ℝ)=(c.sampler.L:ℝ)
    exact congrArg (fun q : ℚ => (q:ℝ)) hL

end
end Cycle12
