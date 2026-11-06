import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap036
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(155921/1000),155,(921/1000),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,86476470133496381824622539010960141854697347951⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((155921/1000):ℚ):ℝ)≤(86476470133496381824622539010960141854697347951:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap036
