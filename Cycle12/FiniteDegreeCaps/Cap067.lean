import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap067
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(6333/40),158,(13/40),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,457692782018839814581682734468571644584438050645⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((6333/40):ℚ):ℝ)≤(457692782018839814581682734468571644584438050645:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap067
