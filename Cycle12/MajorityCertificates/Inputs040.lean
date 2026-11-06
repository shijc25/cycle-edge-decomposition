import Cycle12.RationalMajorityInputs
import Cycle12.MajorityCertificates.Batch040

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Inputs040

def inputs800 : RatMajorityInputs := ⟨(899653928672830782139874159/100000000000000000000000),(29808961874737/6250000000000),(500166774032030507/500000000000000000),(145463038790670933/1000000000000000000),(29808961874737/12500000000000),(46057524528098791/500000000000000000),26⟩
theorem inputs_valid800 : inputs800.Valid := by decide +kernel
def envelope800 : RatMajorityEnvelope := ⟨400,0,inputs800,(1370829413/1154105000),(707401170754404581/1000000000000000000)⟩
theorem envelope_sound800 : envelope800.Sound := by
  apply rat_majority_inputs_envelopes inputs800 inputs_valid800
  · norm_num [envelope800]
  · intro rho hr0 hr1
    have hh := Batch040.bound1600 rho hr0 hr1
    norm_num [Batch040.certificate1600,envelope800,inputs800,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch040.bound1601 rho hr0 hr1
    norm_num [Batch040.certificate1601,envelope800,inputs800,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs801 : RatMajorityInputs := ⟨(899653928672830782139874159/100000000000000000000000),(220686666194863/50000000000000),(500166774032030507/500000000000000000),(45879064190402609/250000000000000000),(220686666194863/100000000000000),(110044916804566743/1000000000000000000),25⟩
theorem inputs_valid801 : inputs801.Valid := by decide +kernel
def envelope801 : RatMajorityEnvelope := ⟨400,1,inputs801,1,(546660680353036237/1000000000000000000)⟩
theorem envelope_sound801 : envelope801.Sound := by
  apply rat_majority_inputs_envelopes inputs801 inputs_valid801
  · norm_num [envelope801]
  · intro rho hr0 hr1
    have hh := Batch040.bound1602 rho hr0 hr1
    norm_num [Batch040.certificate1602,envelope801,inputs801,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch040.bound1603 rho hr0 hr1
    norm_num [Batch040.certificate1603,envelope801,inputs801,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs802 : RatMajorityInputs := ⟨(3477528715494296869244007/390625000000000000000),(3738206296599/781250000000),(500168536670381579/500000000000000000),(71988365138957591/500000000000000000),(3738206296599/1562500000000),(11425660049297907/125000000000000000),26⟩
theorem inputs_valid802 : inputs802.Valid := by decide +kernel
def envelope802 : RatMajorityEnvelope := ⟨401,0,inputs802,(912400611/769280000),(352849080541217031/500000000000000000)⟩
theorem envelope_sound802 : envelope802.Sound := by
  apply rat_majority_inputs_envelopes inputs802 inputs_valid802
  · norm_num [envelope802]
  · intro rho hr0 hr1
    have hh := Batch040.bound1604 rho hr0 hr1
    norm_num [Batch040.certificate1604,envelope802,inputs802,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch040.bound1605 rho hr0 hr1
    norm_num [Batch040.certificate1605,envelope802,inputs802,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs803 : RatMajorityInputs := ⟨(3477528715494296869244007/390625000000000000000),(1726367110833/390625000000),(500168536670381579/500000000000000000),(91418567152261983/500000000000000000),(1726367110833/781250000000),(21945617574820111/200000000000000000),25⟩
theorem inputs_valid803 : inputs803.Valid := by decide +kernel
def envelope803 : RatMajorityEnvelope := ⟨401,1,inputs803,1,(546577789594147311/1000000000000000000)⟩
theorem envelope_sound803 : envelope803.Sound := by
  apply rat_majority_inputs_envelopes inputs803 inputs_valid803
  · norm_num [envelope803]
  · intro rho hr0 hr1
    have hh := Batch040.bound1606 rho hr0 hr1
    norm_num [Batch040.certificate1606,envelope803,inputs803,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch040.bound1607 rho hr0 hr1
    norm_num [Batch040.certificate1607,envelope803,inputs803,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs804 : RatMajorityInputs := ⟨(220272643433101969901329971/25000000000000000000000),(119983842182421/25000000000000),(500170288660025089/500000000000000000),(17825063150799149/125000000000000000),(119983842182421/50000000000000),(11343409263696223/125000000000000000),27⟩
theorem inputs_valid804 : inputs804.Valid := by decide +kernel
def envelope804 : RatMajorityEnvelope := ⟨402,0,inputs804,(455467053/384580000),(88002791959582963/125000000000000000)⟩
theorem envelope_sound804 : envelope804.Sound := by
  apply rat_majority_inputs_envelopes inputs804 inputs_valid804
  · norm_num [envelope804]
  · intro rho hr0 hr1
    have hh := Batch040.bound1608 rho hr0 hr1
    norm_num [Batch040.certificate1608,envelope804,inputs804,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch040.bound1609 rho hr0 hr1
    norm_num [Batch040.certificate1609,envelope804,inputs804,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs805 : RatMajorityInputs := ⟨(220272643433101969901329971/25000000000000000000000),(27677895918519/6250000000000),(500170288660025089/500000000000000000),(181785739461320789/1000000000000000000),(27677895918519/12500000000000),(109237412014358363/1000000000000000000),25⟩
theorem inputs_valid805 : inputs805.Valid := by decide +kernel
def envelope805 : RatMajorityEnvelope := ⟨402,1,inputs805,1,(5464489174036439/10000000000000000)⟩
theorem envelope_sound805 : envelope805.Sound := by
  apply rat_majority_inputs_envelopes inputs805 inputs_valid805
  · norm_num [envelope805]
  · intro rho hr0 hr1
    have hh := Batch040.bound1610 rho hr0 hr1
    norm_num [Batch040.certificate1610,envelope805,inputs805,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch040.bound1611 rho hr0 hr1
    norm_num [Batch040.certificate1611,envelope805,inputs805,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs806 : RatMajorityInputs := ⟨(872176237084701365631140459/100000000000000000000000),(30096284059121/6250000000000),(62521503701457681/62500000000000000),(70542613608456263/500000000000000000),(30096284059121/12500000000000),(45010931103939601/500000000000000000),26⟩
theorem inputs_valid806 : inputs806.Valid := by decide +kernel
def envelope806 : RatMajorityEnvelope := ⟨403,0,inputs806,(389769277/329590000),(351161645065036967/500000000000000000)⟩
theorem envelope_sound806 : envelope806.Sound := by
  apply rat_majority_inputs_envelopes inputs806 inputs_valid806
  · norm_num [envelope806]
  · intro rho hr0 hr1
    have hh := Batch040.bound1612 rho hr0 hr1
    norm_num [Batch040.certificate1612,envelope806,inputs806,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch040.bound1613 rho hr0 hr1
    norm_num [Batch040.certificate1613,envelope806,inputs806,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs807 : RatMajorityInputs := ⟨(872176237084701365631140459/100000000000000000000000),(221711858505011/50000000000000),(62521503701457681/62500000000000000),(90555609760202817/500000000000000000),(221711858505011/100000000000000),(108922508034569967/1000000000000000000),25⟩
theorem inputs_valid807 : inputs807.Valid := by decide +kernel
def envelope807 : RatMajorityEnvelope := ⟨403,1,inputs807,1,(546366955306748703/1000000000000000000)⟩
theorem envelope_sound807 : envelope807.Sound := by
  apply rat_majority_inputs_envelopes inputs807 inputs_valid807
  · norm_num [envelope807]
  · intro rho hr0 hr1
    have hh := Batch040.bound1614 rho hr0 hr1
    norm_num [Batch040.certificate1614,envelope807,inputs807,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch040.bound1615 rho hr0 hr1
    norm_num [Batch040.certificate1615,envelope807,inputs807,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs808 : RatMajorityInputs := ⟨(84949902333551001470473151/10000000000000000000000),(96591563832089/20000000000000),(1000353246341731947/1000000000000000000),(139759096803253241/1000000000000000000),(96591563832089/40000000000000),(89386188856371067/1000000000000000000),26⟩
theorem inputs_valid808 : inputs808.Valid := by decide +kernel
def envelope808 : RatMajorityEnvelope := ⟨404,0,inputs808,(1360667577/1152925000),(140007963710336297/200000000000000000)⟩
theorem envelope_sound808 : envelope808.Sound := by
  apply rat_majority_inputs_envelopes inputs808 inputs_valid808
  · norm_num [envelope808]
  · intro rho hr0 hr1
    have hh := Batch040.bound1616 rho hr0 hr1
    norm_num [Batch040.certificate1616,envelope808,inputs808,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch040.bound1617 rho hr0 hr1
    norm_num [Batch040.certificate1617,envelope808,inputs808,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs809 : RatMajorityInputs := ⟨(84949902333551001470473151/10000000000000000000000),(11096711693333/2500000000000),(1000353246341731947/1000000000000000000),(90296550234430491/500000000000000000),(11096711693333/5000000000000),(27170140082289403/250000000000000000),25⟩
theorem inputs_valid809 : inputs809.Valid := by decide +kernel
def envelope809 : RatMajorityEnvelope := ⟨404,1,inputs809,1,(546306892425773309/1000000000000000000)⟩
theorem envelope_sound809 : envelope809.Sound := by
  apply rat_majority_inputs_envelopes inputs809 inputs_valid809
  · norm_num [envelope809]
  · intro rho hr0 hr1
    have hh := Batch040.bound1618 rho hr0 hr1
    norm_num [Batch040.certificate1618,envelope809,inputs809,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch040.bound1619 rho hr0 hr1
    norm_num [Batch040.certificate1619,envelope809,inputs809,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs810 : RatMajorityInputs := ⟨(21170373893906028940699431/2500000000000000000000),(486392984178369/100000000000000),(1000354366301126869/1000000000000000000),(136590210988062031/1000000000000000000),(486392984178369/200000000000000),(8786401701084523/100000000000000000),26⟩
theorem inputs_valid810 : inputs810.Valid := by decide +kernel
def envelope810 : RatMajorityEnvelope := ⟨405,0,inputs810,(1356745859/1153065000),(174140614104088339/250000000000000000)⟩
theorem envelope_sound810 : envelope810.Sound := by
  apply rat_majority_inputs_envelopes inputs810 inputs_valid810
  · norm_num [envelope810]
  · intro rho hr0 hr1
    have hh := Batch040.bound1620 rho hr0 hr1
    norm_num [Batch040.certificate1620,envelope810,inputs810,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch040.bound1621 rho hr0 hr1
    norm_num [Batch040.certificate1621,envelope810,inputs810,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs811 : RatMajorityInputs := ⟨(21170373893906028940699431/2500000000000000000000),(445658413857267/100000000000000),(1000354366301126869/1000000000000000000),(178520640192083563/1000000000000000000),(445658413857267/200000000000000),(26928059541306103/250000000000000000),26⟩
theorem inputs_valid811 : inputs811.Valid := by decide +kernel
def envelope811 : RatMajorityEnvelope := ⟨405,1,inputs811,1,(68256525790631719/125000000000000000)⟩
theorem envelope_sound811 : envelope811.Sound := by
  apply rat_majority_inputs_envelopes inputs811 inputs_valid811
  · norm_num [envelope811]
  · intro rho hr0 hr1
    have hh := Batch040.bound1622 rho hr0 hr1
    norm_num [Batch040.certificate1622,envelope811,inputs811,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch040.bound1623 rho hr0 hr1
    norm_num [Batch040.certificate1623,envelope811,inputs811,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs812 : RatMajorityInputs := ⟨(838798891566359875799261653/100000000000000000000000),(487907268429113/100000000000000),(125044719222480411/125000000000000000),(135213515073201723/1000000000000000000),(487907268429113/200000000000000),(17440254729133641/200000000000000000),26⟩
theorem inputs_valid812 : inputs812.Valid := by decide +kernel
def envelope812 : RatMajorityEnvelope := ⟨406,0,inputs812,(2709205341/2305810000),(694912996304539663/1000000000000000000)⟩
theorem envelope_sound812 : envelope812.Sound := by
  apply rat_majority_inputs_envelopes inputs812 inputs_valid812
  · norm_num [envelope812]
  · intro rho hr0 hr1
    have hh := Batch040.bound1624 rho hr0 hr1
    norm_num [Batch040.certificate1624,envelope812,inputs812,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch040.bound1625 rho hr0 hr1
    norm_num [Batch040.certificate1625,envelope812,inputs812,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs813 : RatMajorityInputs := ⟨(838798891566359875799261653/100000000000000000000000),(44623994366757/10000000000000),(125044719222480411/125000000000000000),(177851710963278037/1000000000000000000),(44623994366757/20000000000000),(21479900731902729/200000000000000000),26⟩
theorem inputs_valid813 : inputs813.Valid := by decide +kernel
def envelope813 : RatMajorityEnvelope := ⟨406,1,inputs813,1,(545971592585996513/1000000000000000000)⟩
theorem envelope_sound813 : envelope813.Sound := by
  apply rat_majority_inputs_envelopes inputs813 inputs_valid813
  · norm_num [envelope813]
  · intro rho hr0 hr1
    have hh := Batch040.bound1626 rho hr0 hr1
    norm_num [Batch040.certificate1626,envelope813,inputs813,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch040.bound1627 rho hr0 hr1
    norm_num [Batch040.certificate1627,envelope813,inputs813,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs814 : RatMajorityInputs := ⟨(16619854086198645542776809/2000000000000000000000),(9795841177113/2000000000000),(500180557697300367/500000000000000000),(133517075849614873/1000000000000000000),(9795841177113/4000000000000),(86383353092338017/1000000000000000000),26⟩
theorem inputs_valid814 : inputs814.Valid := by decide +kernel
def envelope814 : RatMajorityEnvelope := ⟨407,0,inputs814,(450512157/384250000),(692506993331668381/1000000000000000000)⟩
theorem envelope_sound814 : envelope814.Sound := by
  apply rat_majority_inputs_envelopes inputs814 inputs_valid814
  · norm_num [envelope814]
  · intro rho hr0 hr1
    have hh := Batch040.bound1628 rho hr0 hr1
    norm_num [Batch040.certificate1628,envelope814,inputs814,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch040.bound1629 rho hr0 hr1
    norm_num [Batch040.certificate1629,envelope814,inputs814,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs815 : RatMajorityInputs := ⟨(16619854086198645542776809/2000000000000000000000),(8940305696367/2000000000000),(500180557697300367/500000000000000000),(176963174774439639/1000000000000000000),(8940305696367/4000000000000),(106983953389209439/1000000000000000000),26⟩
theorem inputs_valid815 : inputs815.Valid := by decide +kernel
def envelope815 : RatMajorityEnvelope := ⟨407,1,inputs815,1,(272932121426157131/500000000000000000)⟩
theorem envelope_sound815 : envelope815.Sound := by
  apply rat_majority_inputs_envelopes inputs815 inputs_valid815
  · norm_num [envelope815]
  · intro rho hr0 hr1
    have hh := Batch040.bound1630 rho hr0 hr1
    norm_num [Batch040.certificate1630,envelope815,inputs815,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch040.bound1631 rho hr0 hr1
    norm_num [Batch040.certificate1631,envelope815,inputs815,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs816 : RatMajorityInputs := ⟨(20584765315733389387878477/2500000000000000000000),(3070615905153/625000000000),(7815347268734153/7812500000000000),(26434934356706383/200000000000000000),(3070615905153/1250000000000),(21433780247949259/250000000000000000),26⟩
theorem inputs_valid816 : inputs816.Valid := by decide +kernel
def envelope816 : RatMajorityEnvelope := ⟨408,0,inputs816,(39688943/33900000),(690875683994856141/1000000000000000000)⟩
theorem envelope_sound816 : envelope816.Sound := by
  apply rat_majority_inputs_envelopes inputs816 inputs_valid816
  · norm_num [envelope816]
  · intro rho hr0 hr1
    have hh := Batch040.bound1632 rho hr0 hr1
    norm_num [Batch040.certificate1632,envelope816,inputs816,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch040.bound1633 rho hr0 hr1
    norm_num [Batch040.certificate1633,envelope816,inputs816,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs817 : RatMajorityInputs := ⟨(20584765315733389387878477/2500000000000000000000),(5598900194403/1250000000000),(7815347268734153/7812500000000000),(87970131780373707/500000000000000000),(5598900194403/2500000000000),(6656584259118157/62500000000000000),25⟩
theorem inputs_valid817 : inputs817.Valid := by decide +kernel
def envelope817 : RatMajorityEnvelope := ⟨408,1,inputs817,1,(68217591992466883/125000000000000000)⟩
theorem envelope_sound817 : envelope817.Sound := by
  apply rat_majority_inputs_envelopes inputs817 inputs_valid817
  · norm_num [envelope817]
  · intro rho hr0 hr1
    have hh := Batch040.bound1634 rho hr0 hr1
    norm_num [Batch040.certificate1634,envelope817,inputs817,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch040.bound1635 rho hr0 hr1
    norm_num [Batch040.certificate1635,envelope817,inputs817,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs818 : RatMajorityInputs := ⟨(815987058589449738414996227/100000000000000000000000),(493275388938031/100000000000000),(1000367758048426413/1000000000000000000),(32607809074353027/250000000000000000),(493275388938031/200000000000000),(5305741902999723/62500000000000000),27⟩
theorem inputs_valid818 : inputs818.Valid := by decide +kernel
def envelope818 : RatMajorityEnvelope := ⟨409,0,inputs818,(168298026/144056875),(172119512286371603/250000000000000000)⟩
theorem envelope_sound818 : envelope818.Sound := by
  apply rat_majority_inputs_envelopes inputs818 inputs_valid818
  · norm_num [envelope818]
  · intro rho hr0 hr1
    have hh := Batch040.bound1636 rho hr0 hr1
    norm_num [Batch040.certificate1636,envelope818,inputs818,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch040.bound1637 rho hr0 hr1
    norm_num [Batch040.certificate1637,envelope818,inputs818,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs819 : RatMajorityInputs := ⟨(815987058589449738414996227/100000000000000000000000),(448698306455837/100000000000000),(1000367758048426413/1000000000000000000),(175047500138016851/1000000000000000000),(448698306455837/200000000000000),(13260931153411737/125000000000000000),25⟩
theorem inputs_valid819 : inputs819.Valid := by decide +kernel
def envelope819 : RatMajorityEnvelope := ⟨409,1,inputs819,1,(272816691711521101/500000000000000000)⟩
theorem envelope_sound819 : envelope819.Sound := by
  apply rat_majority_inputs_envelopes inputs819 inputs_valid819
  · norm_num [envelope819]
  · intro rho hr0 hr1
    have hh := Batch040.bound1638 rho hr0 hr1
    norm_num [Batch040.certificate1638,envelope819,inputs819,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch040.bound1639 rho hr0 hr1
    norm_num [Batch040.certificate1639,envelope819,inputs819,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def configurations : List RatMajorityEnvelope := [envelope800,envelope801,envelope802,envelope803,envelope804,envelope805,envelope806,envelope807,envelope808,envelope809,envelope810,envelope811,envelope812,envelope813,envelope814,envelope815,envelope816,envelope817,envelope818,envelope819]
theorem configurations_sound : ∀ s∈configurations, s.Sound := by
  intro s hs
  simp only [configurations,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact envelope_sound800
  · exact envelope_sound801
  · exact envelope_sound802
  · exact envelope_sound803
  · exact envelope_sound804
  · exact envelope_sound805
  · exact envelope_sound806
  · exact envelope_sound807
  · exact envelope_sound808
  · exact envelope_sound809
  · exact envelope_sound810
  · exact envelope_sound811
  · exact envelope_sound812
  · exact envelope_sound813
  · exact envelope_sound814
  · exact envelope_sound815
  · exact envelope_sound816
  · exact envelope_sound817
  · exact envelope_sound818
  · exact envelope_sound819

end Cycle12.MajorityCertificates.Inputs040
