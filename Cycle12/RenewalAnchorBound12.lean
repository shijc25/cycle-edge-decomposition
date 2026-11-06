import Cycle12.GlobalRenewalAnalytic12
import Cycle12.RenewalAnchor.Point00
import Cycle12.RenewalAnchor.Point01
import Cycle12.RenewalAnchor.Point02
import Cycle12.RenewalAnchor.Point03
import Cycle12.RenewalAnchor.Point04
import Cycle12.RenewalAnchor.Point05
import Cycle12.RenewalAnchor.Point06
import Cycle12.RenewalAnchor.Point07
import Cycle12.RenewalAnchor.Point08

namespace Cycle12.Global12
open Real Finset
noncomputable section

def renewalAnchorUpper : ℕ → ℝ
  | 0 => (((61603201153957846430609/1000000000000000000000000):ℚ):ℝ)
  | 1 => (((11478843553540825574007/1000000000000000000000000):ℚ):ℝ)
  | 2 => (((410088630312876226203/200000000000000000000000):ℚ):ℝ)
  | 3 => (((386003689695073836303/1000000000000000000000000):ℚ):ℝ)
  | 4 => (((29949110287231089411/500000000000000000000000):ℚ):ℝ)
  | 5 => (((5749052549862618171/1000000000000000000000000):ℚ):ℝ)
  | 6 => (((33849473908196339/125000000000000000000000):ℚ):ℝ)
  | 7 => (((2418546555876387/500000000000000000000000):ℚ):ℝ)
  | 8 => (((2923179640071/125000000000000000000000):ℚ):ℝ)
  | _ => 0

theorem renewal_anchor_point (i : ℕ) (hi : i≤8) :
    lossH (wA/b^i)≤renewalAnchorUpper i := by
  interval_cases i
  · have he : wA/b^0=(((2311587725257500000000/14597460907219352581):ℚ):ℝ) := by norm_num [wA,b]
    rw [he]
    exact RenewalAnchor00.actual_loss_bound
  · have he : wA/b^1=(((9246350901030000000000000000000/43852819435852806358162260401):ℚ):ℝ) := by norm_num [wA,b]
    rw [he]
    exact RenewalAnchor01.actual_loss_bound
  · have he : wA/b^2=(((36985403604120000000000000000000000000000/131740018671495945016279778114919688621):ℚ):ℝ) := by norm_num [wA,b]
    rw [he]
    exact RenewalAnchor02.actual_loss_bound
  · have he : wA/b^3=(((147941614416480000000000000000000000000000000000000/395765488806331954661810581223985796771142125241):ℚ):ℝ) := by norm_num [wA,b]
    rw [he]
    exact RenewalAnchor03.actual_loss_bound
  · have he : wA/b^4=(((591766457665920000000000000000000000000000000000000000000000/1188935023006827104477093619738363142012919990543907418261):ℚ):ℝ) := by norm_num [wA,b]
    rw [he]
    exact RenewalAnchor04.actual_loss_bound
  · have he : wA/b^5=(((2367065830663680000000000000000000000000000000000000000000000000000000/3571727522770369662152606116238496211624947845247891941698139975681):ℚ):ℝ) := by norm_num [wA,b]
    rw [he]
    exact RenewalAnchor05.actual_loss_bound
  · have he : wA/b^6=(((9468263322654720000000000000000000000000000000000000000000000000000000000000000/10729970309607160849110825473762667697898633588936475897517169341831253965501):ℚ):ℝ) := by norm_num [wA,b]
    rw [he]
    exact RenewalAnchor06.actual_loss_bound
  · have he : wA/b^7=(((37873053290618880000000000000000000000000000000000000000000000000000000000000000000000000/32234335377226694616430342892241810239514762345465647857728402457863367832627300515721):ℚ):ℝ) := by norm_num [wA,b]
    rw [he]
    exact RenewalAnchor07.actual_loss_bound
  · have he : wA/b^8=(((151492213162475520000000000000000000000000000000000000000000000000000000000000000000000000000000000/96836463403929920732102560527405090998375941085269649703224379517742601028513269581931498914341):ℚ):ℝ) := by norm_num [wA,b]
    rw [he]
    exact RenewalAnchor08.actual_loss_bound

theorem globalLoss_anchor_bound : globalLoss (b*wA)≤(((75584414501537703333549/1000000000000000000000000):ℚ):ℝ) := by
  have hh := globalLoss_half_tail (w:=wA) le_rfl 8
    (by norm_num [lossRate,eps,theta2,wA,b])
  have hs : (∑ j∈range 8,lossH (wA/b^j))≤∑ j∈range 8,renewalAnchorUpper j := by
    apply sum_le_sum
    intro j hj
    exact renewal_anchor_point j (by have := mem_range.mp hj; omega)
  have ht := renewal_anchor_point 8 le_rfl
  calc
    _ ≤ (∑ j∈range 8,lossH (wA/b^j))+2*lossH (wA/b^8) := hh
    _ ≤ (∑ j∈range 8,renewalAnchorUpper j)+2*renewalAnchorUpper 8 := by linarith only [hs,ht]
    _ ≤ _ := by norm_num [renewalAnchorUpper,sum_range_succ]

theorem globalLoss_floor_margin : phi0+globalLoss (b*wA)+(1/1000000:ℝ)≤1 := by
  have hh := globalLoss_anchor_bound
  norm_num [phi0] at *
  linarith only [hh]

theorem globalLoss_floor : phi0≤1-globalLoss (b*wA) := by
  have hh := globalLoss_floor_margin
  linarith only [hh]

end
end Cycle12.Global12
