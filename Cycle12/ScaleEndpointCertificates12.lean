import Cycle12.GlobalParameters12
import Cycle12.Foundations.RationalPowers

namespace Cycle12.Global12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem entropyPoint0 :
    (((58680361761946101470726977/1000000000000000000000000):ℚ):ℝ)≤(2:ℝ)^(((29374029300399668672799/5000000000000000000000):ℚ):ℝ) ∧
    (2:ℝ)^(((29374029300399668672799/5000000000000000000000):ℚ):ℝ)≤(((5868036176194610148958501/100000000000000000000000):ℚ):ℝ) := by
  exact Cycle13.certified_power_two (y:=(4374029300399668672799/5000000000000000000000)) (5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem entropyPoint1 :
    (((10941611796109088420236209/250000000000000000000000):ℚ):ℝ)≤(2:ℝ)^(((21937435430753467253871/4023922936400000000000):ℚ):ℝ) ∧
    (2:ℝ)^(((21937435430753467253871/4023922936400000000000):ℚ):ℝ)≤(((21883223592218176840472551/500000000000000000000000):ℚ):ℝ) := by
  exact Cycle13.certified_power_two (y:=(1817820748753467253871/4023922936400000000000)) (5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem entropyPoint2 :
    (((10917185729129118228174991/200000000000000000000000):ℚ):ℝ)≤(2:ℝ)^(((3369360930445557049803/583898436288774103240):ℚ):ℝ) ∧
    (2:ℝ)^(((3369360930445557049803/583898436288774103240):ℚ):ℝ)≤(((54585928645645591143042299/1000000000000000000000000):ℚ):ℝ) := by
  exact Cycle13.certified_power_two (y:=(449868749001686533603/583898436288774103240)) (5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem dfsDeltaPoint :
    (((3832127170074339487071/500000000000000000000000):ℚ):ℝ)≤(2:ℝ)^(((-35138194233034754854443/5000000000000000000000):ℚ):ℝ) ∧
    (2:ℝ)^(((-35138194233034754854443/5000000000000000000000):ℚ):ℝ)≤(((3832127170074339494043/500000000000000000000000):ℚ):ℝ) := by
  exact Cycle13.certified_power_two (y:=(4861805766965245145557/5000000000000000000000)) (-8)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem dfsOrderPoint :
    (((0/1):ℚ):ℝ)≤(2:ℝ)^(((-1118837691750425709098157/10000000000000000000000):ℚ):ℝ) ∧
    (2:ℝ)^(((-1118837691750425709098157/10000000000000000000000):ℚ):ℝ)≤(((1/1000000000000000000000000):ℚ):ℝ) := by
  exact Cycle13.certified_power_two (y:=(1162308249574290901843/10000000000000000000000)) (-112)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

end Cycle12.Global12
