import Cycle12.PrecisePowerCertificate

namespace Cycle12.FiniteDegreeCaps.Cap026
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : RatPrecisePowerUpper := ⟨(145367/1000),145,(367/1000),80,(1386294361119890618834464242916353136151000268720510508241360019/2000000000000000000000000000000000000000000000000000000000000000),64,57521126097023267414344203098046682104218576⟩
theorem valid : certificate.Valid := by decide +kernel

theorem degree_cap : (2:ℝ)^(((145367/1000):ℚ):ℝ)≤(57521126097023267414344203098046682104218576:ℝ) :=
  precise_power_upper_sound certificate valid

end Cycle12.FiniteDegreeCaps.Cap026
