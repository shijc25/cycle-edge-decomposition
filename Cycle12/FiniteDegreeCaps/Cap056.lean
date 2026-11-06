import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap056
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(30691/200),153,(91/200),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,15651572764866283557533390975155428889086270833⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((30691/200):ℚ):ℝ)≤(15651572764866283557533390975155428889086270833:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap056
