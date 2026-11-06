import Cycle12.RationalMajorityInputs
import Cycle12.MajorityCertificates.Batch037

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Inputs037

def inputs740 : RatMajorityInputs := ⟨(491382013563568355147326499/25000000000000000000000),(216627903643069/50000000000000),(100015264886047943/100000000000000000),(6040812382444063/31250000000000000),(216627903643069/100000000000000),(2292065181443511/20000000000000000),26⟩
theorem inputs_valid740 : inputs740.Valid := by decide +kernel
def envelope740 : RatMajorityEnvelope := ⟨370,0,inputs740,(56534509/46726600),(365800162111979433/500000000000000000)⟩
theorem envelope_sound740 : envelope740.Sound := by
  apply rat_majority_inputs_envelopes inputs740 inputs_valid740
  · norm_num [envelope740]
  · intro rho hr0 hr1
    have hh := Batch037.bound1480 rho hr0 hr1
    norm_num [Batch037.certificate1480,envelope740,inputs740,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch037.bound1481 rho hr0 hr1
    norm_num [Batch037.certificate1481,envelope740,inputs740,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs741 : RatMajorityInputs := ⟨(491382013563568355147326499/25000000000000000000000),(84952658845821/20000000000000),(100015264886047943/100000000000000000),(1275101344633821/6250000000000000),(84952658845821/40000000000000),(119574404311149101/1000000000000000000),25⟩
theorem inputs_valid741 : inputs741.Valid := by decide +kernel
def envelope741 : RatMajorityEnvelope := ⟨370,1,inputs741,1,(549203598035334569/1000000000000000000)⟩
theorem envelope_sound741 : envelope741.Sound := by
  apply rat_majority_inputs_envelopes inputs741 inputs_valid741
  · norm_num [envelope741]
  · intro rho hr0 hr1
    have hh := Batch037.bound1482 rho hr0 hr1
    norm_num [Batch037.certificate1482,envelope741,inputs741,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch037.bound1483 rho hr0 hr1
    norm_num [Batch037.certificate1483,envelope741,inputs741,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs742 : RatMajorityInputs := ⟨(187731377692376880711949361/10000000000000000000000),(217014805718767/50000000000000),(500079911332688487/500000000000000000),(192354123257377021/1000000000000000000),(217014805718767/100000000000000),(114160713345359867/1000000000000000000),25⟩
theorem inputs_valid742 : inputs742.Valid := by decide +kernel
def envelope742 : RatMajorityEnvelope := ⟨371,0,inputs742,(2826685369/2334740000),(732246157711804631/1000000000000000000)⟩
theorem envelope_sound742 : envelope742.Sound := by
  apply rat_majority_inputs_envelopes inputs742 inputs_valid742
  · norm_num [envelope742]
  · intro rho hr0 hr1
    have hh := Batch037.bound1484 rho hr0 hr1
    norm_num [Batch037.certificate1484,envelope742,inputs742,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch037.bound1485 rho hr0 hr1
    norm_num [Batch037.certificate1485,envelope742,inputs742,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs743 : RatMajorityInputs := ⟨(187731377692376880711949361/10000000000000000000000),(26569496576947/6250000000000),(500079911332688487/500000000000000000),(50891730267725907/250000000000000000),(26569496576947/12500000000000),(59683068607904549/500000000000000000),25⟩
theorem inputs_valid743 : inputs743.Valid := by decide +kernel
def envelope743 : RatMajorityEnvelope := ⟨371,1,inputs743,1,(137286915059496267/250000000000000000)⟩
theorem envelope_sound743 : envelope743.Sound := by
  apply rat_majority_inputs_envelopes inputs743 inputs_valid743
  · norm_num [envelope743]
  · intro rho hr0 hr1
    have hh := Batch037.bound1486 rho hr0 hr1
    norm_num [Batch037.certificate1486,envelope743,inputs743,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch037.bound1487 rho hr0 hr1
    norm_num [Batch037.certificate1487,envelope743,inputs743,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs744 : RatMajorityInputs := ⟨(1795865805792949688803375119/100000000000000000000000),(86964153021471/20000000000000),(1000167072050760799/1000000000000000000),(191385005756465297/1000000000000000000),(86964153021471/40000000000000),(113710012031511391/1000000000000000000),26⟩
theorem inputs_valid744 : inputs744.Valid := by decide +kernel
def envelope744 : RatMajorityEnvelope := ⟨372,0,inputs744,(942227273/777730000),(183221880895145799/250000000000000000)⟩
theorem envelope_sound744 : envelope744.Sound := by
  apply rat_majority_inputs_envelopes inputs744 inputs_valid744
  · norm_num [envelope744]
  · intro rho hr0 hr1
    have hh := Batch037.bound1488 rho hr0 hr1
    norm_num [Batch037.certificate1488,envelope744,inputs744,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch037.bound1489 rho hr0 hr1
    norm_num [Batch037.certificate1489,envelope744,inputs744,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs745 : RatMajorityInputs := ⟨(1795865805792949688803375119/100000000000000000000000),(106313570208063/25000000000000),(1000167072050760799/1000000000000000000),(25422967069057633/125000000000000000),(106313570208063/50000000000000),(119281217182795203/1000000000000000000),26⟩
theorem inputs_valid745 : inputs745.Valid := by decide +kernel
def envelope745 : RatMajorityEnvelope := ⟨372,1,inputs745,1,(274563336913167701/500000000000000000)⟩
theorem envelope_sound745 : envelope745.Sound := by
  apply rat_majority_inputs_envelopes inputs745 inputs_valid745
  · norm_num [envelope745]
  · intro rho hr0 hr1
    have hh := Batch037.bound1490 rho hr0 hr1
    norm_num [Batch037.certificate1490,envelope745,inputs745,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch037.bound1491 rho hr0 hr1
    norm_num [Batch037.certificate1491,envelope745,inputs745,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs746 : RatMajorityInputs := ⟨(1720505813833282319967454793/100000000000000000000000),(217819124280989/50000000000000),(1000174390977563221/1000000000000000000),(23798496996597833/125000000000000000),(217819124280989/100000000000000),(113246180346796347/1000000000000000000),26⟩
theorem inputs_valid746 : inputs746.Valid := by decide +kernel
def envelope746 : RatMajorityEnvelope := ⟨373,0,inputs746,(353337617/291458750),(366761362169672749/500000000000000000)⟩
theorem envelope_sound746 : envelope746.Sound := by
  apply rat_majority_inputs_envelopes inputs746 inputs_valid746
  · norm_num [envelope746]
  · intro rho hr0 hr1
    have hh := Batch037.bound1492 rho hr0 hr1
    norm_num [Batch037.certificate1492,envelope746,inputs746,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch037.bound1493 rho hr0 hr1
    norm_num [Batch037.certificate1493,envelope746,inputs746,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs747 : RatMajorityInputs := ⟨(1720505813833282319967454793/100000000000000000000000),(106462597471087/25000000000000),(1000174390977563221/1000000000000000000),(202618049193793403/1000000000000000000),(106462597471087/50000000000000),(594631117082769/5000000000000000),25⟩
theorem inputs_valid747 : inputs747.Valid := by decide +kernel
def envelope747 : RatMajorityEnvelope := ⟨373,1,inputs747,1,(274514759268336531/500000000000000000)⟩
theorem envelope_sound747 : envelope747.Sound := by
  apply rat_majority_inputs_envelopes inputs747 inputs_valid747
  · norm_num [envelope747]
  · intro rho hr0 hr1
    have hh := Batch037.bound1494 rho hr0 hr1
    norm_num [Batch037.certificate1494,envelope747,inputs747,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch037.bound1495 rho hr0 hr1
    norm_num [Batch037.certificate1495,envelope747,inputs747,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs748 : RatMajorityInputs := ⟨(41266499071085935546353039/2500000000000000000000),(5455552076889/1250000000000),(500090885591078837/500000000000000000),(189409358368304249/1000000000000000000),(5455552076889/2500000000000),(14098845386469137/125000000000000000),26⟩
theorem inputs_valid748 : inputs748.Valid := by decide +kernel
def envelope748 : RatMajorityEnvelope := ⟨374,0,inputs748,(1413390123/1165100000),(367080596447226497/500000000000000000)⟩
theorem envelope_sound748 : envelope748.Sound := by
  apply rat_majority_inputs_envelopes inputs748 inputs_valid748
  · norm_num [envelope748]
  · intro rho hr0 hr1
    have hh := Batch037.bound1496 rho hr0 hr1
    norm_num [Batch037.certificate1496,envelope748,inputs748,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch037.bound1497 rho hr0 hr1
    norm_num [Batch037.certificate1497,envelope748,inputs748,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs749 : RatMajorityInputs := ⟨(41266499071085935546353039/2500000000000000000000),(5326000063999/1250000000000),(500090885591078837/500000000000000000),(101161879561518211/500000000000000000),(5326000063999/2500000000000),(118789765399614197/1000000000000000000),26⟩
theorem inputs_valid749 : inputs749.Valid := by decide +kernel
def envelope749 : RatMajorityEnvelope := ⟨374,1,inputs749,1,(54899413499007261/100000000000000000)⟩
theorem envelope_sound749 : envelope749.Sound := by
  apply rat_majority_inputs_envelopes inputs749 inputs_valid749
  · norm_num [envelope749]
  · intro rho hr0 hr1
    have hh := Batch037.bound1498 rho hr0 hr1
    norm_num [Batch037.certificate1498,envelope749,inputs749,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch037.bound1499 rho hr0 hr1
    norm_num [Batch037.certificate1499,envelope749,inputs749,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs750 : RatMajorityInputs := ⟨(2537261324856124804806309/160000000000000000000),(1749016557243/400000000000),(50009460409776771/50000000000000000),(7537204469358613/40000000000000000),(1749016557243/800000000000),(112334899354506893/1000000000000000000),25⟩
theorem inputs_valid750 : inputs750.Valid := by decide +kernel
def envelope750 : RatMajorityEnvelope := ⟨375,0,inputs750,(40969319/33750000),(367400490991315919/500000000000000000)⟩
theorem envelope_sound750 : envelope750.Sound := by
  apply rat_majority_inputs_envelopes inputs750 inputs_valid750
  · norm_num [envelope750]
  · intro rho hr0 hr1
    have hh := Batch037.bound1500 rho hr0 hr1
    norm_num [Batch037.certificate1500,envelope750,inputs750,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch037.bound1501 rho hr0 hr1
    norm_num [Batch037.certificate1501,envelope750,inputs750,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs751 : RatMajorityInputs := ⟨(2537261324856124804806309/160000000000000000000),(3410345626101/800000000000),(50009460409776771/50000000000000000),(25256353888183481/125000000000000000),(3410345626101/1600000000000),(14832900510177003/125000000000000000),26⟩
theorem inputs_valid751 : inputs751.Valid := by decide +kernel
def envelope751 : RatMajorityEnvelope := ⟨375,1,inputs751,1,(21958463810895989/40000000000000000)⟩
theorem envelope_sound751 : envelope751.Sound := by
  apply rat_majority_inputs_envelopes inputs751 inputs_valid751
  · norm_num [envelope751]
  · intro rho hr0 hr1
    have hh := Batch037.bound1502 rho hr0 hr1
    norm_num [Batch037.certificate1502,envelope751,inputs751,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch037.bound1503 rho hr0 hr1
    norm_num [Batch037.certificate1503,envelope751,inputs751,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs752 : RatMajorityInputs := ⟨(305090785590641659129120899/20000000000000000000000),(43807951885699/10000000000000),(250049173214760727/250000000000000000),(93718328230984769/500000000000000000),(43807951885699/20000000000000),(13984032500310501/125000000000000000),26⟩
theorem inputs_valid752 : inputs752.Valid := by decide +kernel
def envelope752 : RatMajorityEnvelope := ⟨376,0,inputs752,(565406641/465470000),(22982373824386657/31250000000000000)⟩
theorem envelope_sound752 : envelope752.Sound := by
  apply rat_majority_inputs_envelopes inputs752 inputs_valid752
  · norm_num [envelope752]
  · intro rho hr0 hr1
    have hh := Batch037.bound1504 rho hr0 hr1
    norm_num [Batch037.certificate1504,envelope752,inputs752,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch037.bound1505 rho hr0 hr1
    norm_num [Batch037.certificate1505,envelope752,inputs752,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs753 : RatMajorityInputs := ⟨(305090785590641659129120899/20000000000000000000000),(85367580476699/20000000000000),(250049173214760727/250000000000000000),(100677464880200341/500000000000000000),(85367580476699/40000000000000),(59170232527676363/500000000000000000),26⟩
theorem inputs_valid753 : inputs753.Valid := by decide +kernel
def envelope753 : RatMajorityEnvelope := ⟨376,1,inputs753,1,(548873960960232817/1000000000000000000)⟩
theorem envelope_sound753 : envelope753.Sound := by
  apply rat_majority_inputs_envelopes inputs753 inputs_valid753
  · norm_num [envelope753]
  · intro rho hr0 hr1
    have hh := Batch037.bound1506 rho hr0 hr1
    norm_num [Batch037.certificate1506,envelope753,inputs753,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch037.bound1507 rho hr0 hr1
    norm_num [Batch037.certificate1507,envelope753,inputs753,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs754 : RatMajorityInputs := ⟨(367309324498353435841041203/25000000000000000000000),(54923587056997/12500000000000),(1000204220006616269/1000000000000000000),(37173999878565311/200000000000000000),(54923587056997/25000000000000),(111142348285250751/1000000000000000000),25⟩
theorem inputs_valid754 : inputs754.Valid := by decide +kernel
def envelope754 : RatMajorityEnvelope := ⟨377,0,inputs754,(148689137/122420000),(367594952568330507/500000000000000000)⟩
theorem envelope_sound754 : envelope754.Sound := by
  apply rat_majority_inputs_envelopes inputs754 inputs_valid754
  · norm_num [envelope754]
  · intro rho hr0 hr1
    have hh := Batch037.bound1508 rho hr0 hr1
    norm_num [Batch037.certificate1508,envelope754,inputs754,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch037.bound1509 rho hr0 hr1
    norm_num [Batch037.certificate1509,envelope754,inputs754,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs755 : RatMajorityInputs := ⟨(367309324498353435841041203/25000000000000000000000),(3337540909967/781250000000),(1000204220006616269/1000000000000000000),(12555422740047709/62500000000000000),(3337540909967/1562500000000),(118123312099051411/1000000000000000000),25⟩
theorem inputs_valid755 : inputs755.Valid := by decide +kernel
def envelope755 : RatMajorityEnvelope := ⟨377,1,inputs755,1,(34301008801446371/62500000000000000)⟩
theorem envelope_sound755 : envelope755.Sound := by
  apply rat_majority_inputs_envelopes inputs755 inputs_valid755
  · norm_num [envelope755]
  · intro rho hr0 hr1
    have hh := Batch037.bound1510 rho hr0 hr1
    norm_num [Batch037.certificate1510,envelope755,inputs755,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch037.bound1511 rho hr0 hr1
    norm_num [Batch037.certificate1511,envelope755,inputs755,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs756 : RatMajorityInputs := ⟨(3541945576603933384531227/250000000000000000000),(6876862458873/1562500000000),(125026472863647463/125000000000000000),(185000672088050089/1000000000000000000),(6876862458873/3125000000000),(22147428162587967/200000000000000000),25⟩
theorem inputs_valid756 : inputs756.Valid := by decide +kernel
def envelope756 : RatMajorityEnvelope := ⟨378,0,inputs756,(2823457469/2324640000),(367556006135646799/500000000000000000)⟩
theorem envelope_sound756 : envelope756.Sound := by
  apply rat_majority_inputs_envelopes inputs756 inputs_valid756
  · norm_num [envelope756]
  · intro rho hr0 hr1
    have hh := Batch037.bound1512 rho hr0 hr1
    norm_num [Batch037.certificate1512,envelope756,inputs756,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch037.bound1513 rho hr0 hr1
    norm_num [Batch037.certificate1513,envelope756,inputs756,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs757 : RatMajorityInputs := ⟨(3541945576603933384531227/250000000000000000000),(26721043810287/6250000000000),(125026472863647463/125000000000000000),(50116274469370009/250000000000000000),(26721043810287/12500000000000),(29481926454713177/250000000000000000),25⟩
theorem inputs_valid757 : inputs757.Valid := by decide +kernel
def envelope757 : RatMajorityEnvelope := ⟨378,1,inputs757,1,(68595557175532567/125000000000000000)⟩
theorem envelope_sound757 : envelope757.Sound := by
  apply rat_majority_inputs_envelopes inputs757 inputs_valid757
  · norm_num [envelope757]
  · intro rho hr0 hr1
    have hh := Batch037.bound1514 rho hr0 hr1
    norm_num [Batch037.certificate1514,envelope757,inputs757,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch037.bound1515 rho hr0 hr1
    norm_num [Batch037.certificate1515,envelope757,inputs757,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs758 : RatMajorityInputs := ⟨(136776159894542677110024801/10000000000000000000000),(110394188621809/25000000000000),(1000219373892906593/1000000000000000000),(91638220227432381/500000000000000000),(110394188621809/50000000000000),(21986609173555823/200000000000000000),25⟩
theorem inputs_valid758 : inputs758.Valid := by decide +kernel
def envelope758 : RatMajorityEnvelope := ⟨379,0,inputs758,(176464483/145208750),(735568258327585539/1000000000000000000)⟩
theorem envelope_sound758 : envelope758.Sound := by
  apply rat_majority_inputs_envelopes inputs758 inputs_valid758
  · norm_num [envelope758]
  · intro rho hr0 hr1
    have hh := Batch037.bound1516 rho hr0 hr1
    norm_num [Batch037.certificate1516,envelope758,inputs758,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch037.bound1517 rho hr0 hr1
    norm_num [Batch037.certificate1517,envelope758,inputs758,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs759 : RatMajorityInputs := ⟨(136776159894542677110024801/10000000000000000000000),(214041723035051/50000000000000),(1000219373892906593/1000000000000000000),(9988559527518507/50000000000000000),(214041723035051/100000000000000),(29401441022427003/250000000000000000),25⟩
theorem inputs_valid759 : inputs759.Valid := by decide +kernel
def envelope759 : RatMajorityEnvelope := ⟨379,1,inputs759,1,(274338756413075707/500000000000000000)⟩
theorem envelope_sound759 : envelope759.Sound := by
  apply rat_majority_inputs_envelopes inputs759 inputs_valid759
  · norm_num [envelope759]
  · intro rho hr0 hr1
    have hh := Batch037.bound1518 rho hr0 hr1
    norm_num [Batch037.certificate1518,envelope759,inputs759,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch037.bound1519 rho hr0 hr1
    norm_num [Batch037.certificate1519,envelope759,inputs759,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def configurations : List RatMajorityEnvelope := [envelope740,envelope741,envelope742,envelope743,envelope744,envelope745,envelope746,envelope747,envelope748,envelope749,envelope750,envelope751,envelope752,envelope753,envelope754,envelope755,envelope756,envelope757,envelope758,envelope759]
theorem configurations_sound : ∀ s∈configurations, s.Sound := by
  intro s hs
  simp only [configurations,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact envelope_sound740
  · exact envelope_sound741
  · exact envelope_sound742
  · exact envelope_sound743
  · exact envelope_sound744
  · exact envelope_sound745
  · exact envelope_sound746
  · exact envelope_sound747
  · exact envelope_sound748
  · exact envelope_sound749
  · exact envelope_sound750
  · exact envelope_sound751
  · exact envelope_sound752
  · exact envelope_sound753
  · exact envelope_sound754
  · exact envelope_sound755
  · exact envelope_sound756
  · exact envelope_sound757
  · exact envelope_sound758
  · exact envelope_sound759

end Cycle12.MajorityCertificates.Inputs037
