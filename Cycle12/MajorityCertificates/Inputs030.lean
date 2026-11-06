import Cycle12.RationalMajorityInputs
import Cycle12.MajorityCertificates.Batch030

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Inputs030

def inputs600 : RatMajorityInputs := ⟨(58900479335314573087798787/25000000000000000000000),(234351011852953/50000000000000),(100127459651088709/100000000000000000),(76804598760858471/500000000000000000),(234351011852953/100000000000000),(11998763691507403/125000000000000000),26⟩
theorem inputs_valid600 : inputs600.Valid := by decide +kernel
def envelope600 : RatMajorityEnvelope := ⟨300,0,inputs600,(2570699131/2198260000),(692025253624891523/1000000000000000000)⟩
theorem envelope_sound600 : envelope600.Sound := by
  apply rat_majority_inputs_envelopes inputs600 inputs_valid600
  · norm_num [envelope600]
  · intro rho hr0 hr1
    have hh := Batch030.bound1200 rho hr0 hr1
    norm_num [Batch030.certificate1200,envelope600,inputs600,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch030.bound1201 rho hr0 hr1
    norm_num [Batch030.certificate1201,envelope600,inputs600,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs601 : RatMajorityInputs := ⟨(58900479335314573087798787/25000000000000000000000),(244384326192251/50000000000000),(100127459651088709/100000000000000000),(134435866655231199/1000000000000000000),(244384326192251/100000000000000),(43413256184155957/500000000000000000),26⟩
theorem inputs_valid601 : inputs601.Valid := by decide +kernel
def envelope601 : RatMajorityEnvelope := ⟨300,1,inputs601,1,(541348396687249177/1000000000000000000)⟩
theorem envelope_sound601 : envelope601.Sound := by
  apply rat_majority_inputs_envelopes inputs601 inputs_valid601
  · norm_num [envelope601]
  · intro rho hr0 hr1
    have hh := Batch030.bound1202 rho hr0 hr1
    norm_num [Batch030.certificate1202,envelope601,inputs601,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch030.bound1203 rho hr0 hr1
    norm_num [Batch030.certificate1203,envelope601,inputs601,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs602 : RatMajorityInputs := ⟨(58538953130656946443758951/25000000000000000000000),(471134272556693/100000000000000),(1001282476043732383/1000000000000000000),(151164661607566119/1000000000000000000),(471134272556693/200000000000000),(47414909973368919/500000000000000000),26⟩
theorem inputs_valid602 : inputs602.Valid := by decide +kernel
def envelope602 : RatMajorityEnvelope := ⟨301,0,inputs602,(2566446543/2198270000),(5520510224332153/8000000000000000)⟩
theorem envelope_sound602 : envelope602.Sound := by
  apply rat_majority_inputs_envelopes inputs602 inputs_valid602
  · norm_num [envelope602]
  · intro rho hr0 hr1
    have hh := Batch030.bound1204 rho hr0 hr1
    norm_num [Batch030.certificate1204,envelope602,inputs602,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch030.bound1205 rho hr0 hr1
    norm_num [Batch030.certificate1205,envelope602,inputs602,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs603 : RatMajorityInputs := ⟨(58538953130656946443758951/25000000000000000000000),(490160154760527/100000000000000),(1001282476043732383/1000000000000000000),(33296991351033941/250000000000000000),(490160154760527/200000000000000),(86224512515975647/1000000000000000000),26⟩
theorem inputs_valid603 : inputs603.Valid := by decide +kernel
def envelope603 : RatMajorityEnvelope := ⟨301,1,inputs603,1,(270607852280851683/500000000000000000)⟩
theorem envelope_sound603 : envelope603.Sound := by
  apply rat_majority_inputs_envelopes inputs603 inputs_valid603
  · norm_num [envelope603]
  · intro rho hr0 hr1
    have hh := Batch030.bound1206 rho hr0 hr1
    norm_num [Batch030.certificate1206,envelope603,inputs603,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch030.bound1207 rho hr0 hr1
    norm_num [Batch030.certificate1207,envelope603,inputs603,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs604 : RatMajorityInputs := ⟨(231328180889967928671155239/100000000000000000000000),(235409292178329/50000000000000),(1001298168168712383/1000000000000000000),(151480018335493871/1000000000000000000),(235409292178329/100000000000000),(47489810708935357/500000000000000000),26⟩
theorem inputs_valid604 : inputs604.Valid := by decide +kernel
def envelope604 : RatMajorityEnvelope := ⟨302,0,inputs604,(2562194357/2197430000),(5510058380429187/8000000000000000)⟩
theorem envelope_sound604 : envelope604.Sound := by
  apply rat_majority_inputs_envelopes inputs604 inputs_valid604
  · norm_num [envelope604]
  · intro rho hr0 hr1
    have hh := Batch030.bound1208 rho hr0 hr1
    norm_num [Batch030.certificate1208,envelope604,inputs604,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch030.bound1209 rho hr0 hr1
    norm_num [Batch030.certificate1209,envelope604,inputs604,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs605 : RatMajorityInputs := ⟨(231328180889967928671155239/100000000000000000000000),(245612069100343/50000000000000),(1001298168168712383/1000000000000000000),(66120346679803301/500000000000000000),(245612069100343/100000000000000),(85767023230241557/1000000000000000000),27⟩
theorem inputs_valid605 : inputs605.Valid := by decide +kernel
def envelope605 : RatMajorityEnvelope := ⟨302,1,inputs605,1,(10822394050735463/20000000000000000)⟩
theorem envelope_sound605 : envelope605.Sound := by
  apply rat_majority_inputs_envelopes inputs605 inputs_valid605
  · norm_num [envelope605]
  · intro rho hr0 hr1
    have hh := Batch030.bound1210 rho hr0 hr1
    norm_num [Batch030.certificate1210,envelope605,inputs605,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch030.bound1211 rho hr0 hr1
    norm_num [Batch030.certificate1211,envelope605,inputs605,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs606 : RatMajorityInputs := ⟨(2857224686752553588138367/1250000000000000000000),(11835589411317/2500000000000),(1001313803434737897/1000000000000000000),(930592754888207/6250000000000000),(11835589411317/5000000000000),(4687526868209269/50000000000000000),26⟩
theorem inputs_valid606 : inputs606.Valid := by decide +kernel
def envelope606 : RatMajorityEnvelope := ⟨303,0,inputs606,(121851213/104600000),(687573471917092191/1000000000000000000)⟩
theorem envelope_sound606 : envelope606.Sound := by
  apply rat_majority_inputs_envelopes inputs606 inputs_valid606
  · norm_num [envelope606]
  · intro rho hr0 hr1
    have hh := Batch030.bound1212 rho hr0 hr1
    norm_num [Batch030.certificate1212,envelope606,inputs606,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch030.bound1213 rho hr0 hr1
    norm_num [Batch030.certificate1213,envelope606,inputs606,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs607 : RatMajorityInputs := ⟨(2857224686752553588138367/1250000000000000000000),(24570924842751/5000000000000),(1001313803434737897/1000000000000000000),(33017074680646979/250000000000000000),(24570924842751/10000000000000),(42841857949721591/500000000000000000),27⟩
theorem inputs_valid607 : inputs607.Valid := by decide +kernel
def envelope607 : RatMajorityEnvelope := ⟨303,1,inputs607,1,(270554046986062407/500000000000000000)⟩
theorem envelope_sound607 : envelope607.Sound := by
  apply rat_majority_inputs_envelopes inputs607 inputs_valid607
  · norm_num [envelope607]
  · intro rho hr0 hr1
    have hh := Batch030.bound1214 rho hr0 hr1
    norm_num [Batch030.certificate1214,envelope607,inputs607,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch030.bound1215 rho hr0 hr1
    norm_num [Batch030.certificate1215,envelope607,inputs607,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs608 : RatMajorityInputs := ⟨(225903726492844627369805997/100000000000000000000000),(118695035548701/25000000000000),(1001329372318796259/1000000000000000000),(29512781202989583/200000000000000000),(118695035548701/50000000000000),(23279198809888701/250000000000000000),26⟩
theorem inputs_valid608 : inputs608.Valid := by decide +kernel
def envelope608 : RatMajorityEnvelope := ⟨304,0,inputs608,(2554192211/2195790000),(685929594937430631/1000000000000000000)⟩
theorem envelope_sound608 : envelope608.Sound := by
  apply rat_majority_inputs_envelopes inputs608 inputs_valid608
  · norm_num [envelope608]
  · intro rho hr0 hr1
    have hh := Batch030.bound1216 rho hr0 hr1
    norm_num [Batch030.certificate1216,envelope608,inputs608,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch030.bound1217 rho hr0 hr1
    norm_num [Batch030.certificate1217,envelope608,inputs608,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs609 : RatMajorityInputs := ⟨(225903726492844627369805997/100000000000000000000000),(492500653862289/100000000000000),(1001329372318796259/1000000000000000000),(131112059841110263/1000000000000000000),(492500653862289/200000000000000),(85221351736180801/1000000000000000000),26⟩
theorem inputs_valid609 : inputs609.Valid := by decide +kernel
def envelope609 : RatMajorityEnvelope := ⟨304,1,inputs609,1,(135252844390707223/250000000000000000)⟩
theorem envelope_sound609 : envelope609.Sound := by
  apply rat_majority_inputs_envelopes inputs609 inputs_valid609
  · norm_num [envelope609]
  · intro rho hr0 hr1
    have hh := Batch030.bound1218 rho hr0 hr1
    norm_num [Batch030.certificate1218,envelope609,inputs609,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch030.bound1219 rho hr0 hr1
    norm_num [Batch030.certificate1219,envelope609,inputs609,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs610 : RatMajorityInputs := ⟨(446606020656178492626327/200000000000000000000),(952208656141/200000000000),(1001344871150872827/1000000000000000000),(146274778536148131/1000000000000000000),(952208656141/400000000000),(46251155992092099/500000000000000000),26⟩
theorem inputs_valid610 : inputs610.Valid := by decide +kernel
def envelope610 : RatMajorityEnvelope := ⟨305,0,inputs610,(1274776353/1097500000),(684297183287436997/1000000000000000000)⟩
theorem envelope_sound610 : envelope610.Sound := by
  apply rat_majority_inputs_envelopes inputs610 inputs_valid610
  · norm_num [envelope610]
  · intro rho hr0 hr1
    have hh := Batch030.bound1220 rho hr0 hr1
    norm_num [Batch030.certificate1220,envelope610,inputs610,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch030.bound1221 rho hr0 hr1
    norm_num [Batch030.certificate1221,envelope610,inputs610,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs611 : RatMajorityInputs := ⟨(446606020656178492626327/200000000000000000000),(197448134879/40000000000),(1001344871150872827/1000000000000000000),(65064554583616709/500000000000000000),(197448134879/80000000000),(10593197515746187/125000000000000000),26⟩
theorem inputs_valid611 : inputs611.Valid := by decide +kernel
def envelope611 : RatMajorityEnvelope := ⟨305,1,inputs611,1,(54091200367750547/100000000000000000)⟩
theorem envelope_sound611 : envelope611.Sound := by
  apply rat_majority_inputs_envelopes inputs611 inputs_valid611
  · norm_num [envelope611]
  · intro rho hr0 hr1
    have hh := Batch030.bound1222 rho hr0 hr1
    norm_num [Batch030.certificate1222,envelope611,inputs611,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch030.bound1223 rho hr0 hr1
    norm_num [Batch030.certificate1223,envelope611,inputs611,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs612 : RatMajorityInputs := ⟨(110386248906672153083413689/50000000000000000000000),(238505232383831/50000000000000),(500680151240516327/500000000000000000),(14539831864617363/100000000000000000),(238505232383831/100000000000000),(92084161256461203/1000000000000000000),26⟩
theorem inputs_valid612 : inputs612.Valid := by decide +kernel
def envelope612 : RatMajorityEnvelope := ⟨306,0,inputs612,(2546799299/2194220000),(136694066337953067/200000000000000000)⟩
theorem envelope_sound612 : envelope612.Sound := by
  apply rat_majority_inputs_envelopes inputs612 inputs_valid612
  · norm_num [envelope612]
  · intro rho hr0 hr1
    have hh := Batch030.bound1224 rho hr0 hr1
    norm_num [Batch030.certificate1224,envelope612,inputs612,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch030.bound1225 rho hr0 hr1
    norm_num [Batch030.certificate1225,envelope612,inputs612,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs613 : RatMajorityInputs := ⟨(110386248906672153083413689/50000000000000000000000),(987636085471/200000000000),(500680151240516327/500000000000000000),(64978112807844491/500000000000000000),(987636085471/400000000000),(10582731020738609/125000000000000000),26⟩
theorem inputs_valid613 : inputs613.Valid := by decide +kernel
def envelope613 : RatMajorityEnvelope := ⟨306,1,inputs613,1,(540900370328915759/1000000000000000000)⟩
theorem envelope_sound613 : envelope613.Sound := by
  apply rat_majority_inputs_envelopes inputs613 inputs_valid613
  · norm_num [envelope613]
  · intro rho hr0 hr1
    have hh := Batch030.bound1226 rho hr0 hr1
    norm_num [Batch030.certificate1226,envelope613,inputs613,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch030.bound1227 rho hr0 hr1
    norm_num [Batch030.certificate1227,envelope613,inputs613,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs614 : RatMajorityInputs := ⟨(109155496014272711643010527/50000000000000000000000),(14928303478751/3125000000000),(500687828303413407/500000000000000000),(72364480828701227/500000000000000000),(14928303478751/6250000000000),(91764611015554463/1000000000000000000),26⟩
theorem inputs_valid614 : inputs614.Valid := by decide +kernel
def envelope614 : RatMajorityEnvelope := ⟨307,0,inputs614,(508476429/438692000),(681967941236421713/1000000000000000000)⟩
theorem envelope_sound614 : envelope614.Sound := by
  apply rat_majority_inputs_envelopes inputs614 inputs_valid614
  · norm_num [envelope614]
  · intro rho hr0 hr1
    have hh := Batch030.bound1228 rho hr0 hr1
    norm_num [Batch030.certificate1228,envelope614,inputs614,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch030.bound1229 rho hr0 hr1
    norm_num [Batch030.certificate1229,envelope614,inputs614,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs615 : RatMajorityInputs := ⟨(109155496014272711643010527/50000000000000000000000),(49487873584931/10000000000000),(500687828303413407/500000000000000000),(64516084288257383/500000000000000000),(49487873584931/20000000000000),(16842807099661297/200000000000000000),27⟩
theorem inputs_valid615 : inputs615.Valid := by decide +kernel
def envelope615 : RatMajorityEnvelope := ⟨307,1,inputs615,1,(33800475964468037/62500000000000000)⟩
theorem envelope_sound615 : envelope615.Sound := by
  apply rat_majority_inputs_envelopes inputs615 inputs_valid615
  · norm_num [envelope615]
  · intro rho hr0 hr1
    have hh := Batch030.bound1230 rho hr0 hr1
    norm_num [Batch030.certificate1230,envelope615,inputs615,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch030.bound1231 rho hr0 hr1
    norm_num [Batch030.certificate1231,envelope615,inputs615,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs616 : RatMajorityInputs := ⟨(2698954501888743653746041/1250000000000000000000),(59955756722791/12500000000000),(500695464951012553/500000000000000000),(71437565081867349/500000000000000000),(59955756722791/25000000000000),(90878641817423941/1000000000000000000),26⟩
theorem inputs_valid616 : inputs616.Valid := by decide +kernel
def envelope616 : RatMajorityEnvelope := ⟨308,0,inputs616,(1268832261/1096360000),(170057146159946381/250000000000000000)⟩
theorem envelope_sound616 : envelope616.Sound := by
  apply rat_majority_inputs_envelopes inputs616 inputs_valid616
  · norm_num [envelope616]
  · intro rho hr0 hr1
    have hh := Batch030.bound1232 rho hr0 hr1
    norm_num [Batch030.certificate1232,envelope616,inputs616,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch030.bound1233 rho hr0 hr1
    norm_num [Batch030.certificate1233,envelope616,inputs616,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs617 : RatMajorityInputs := ⟨(2698954501888743653746041/1250000000000000000000),(30957549847537/6250000000000),(500695464951012553/500000000000000000),(128648772664085439/1000000000000000000),(30957549847537/12500000000000),(3361124082236467/40000000000000000),26⟩
theorem inputs_valid617 : inputs617.Valid := by decide +kernel
def envelope617 : RatMajorityEnvelope := ⟨308,1,inputs617,1,(2112395644097261/3906250000000000)⟩
theorem envelope_sound617 : envelope617.Sound := by
  apply rat_majority_inputs_envelopes inputs617 inputs_valid617
  · norm_num [envelope617]
  · intro rho hr0 hr1
    have hh := Batch030.bound1234 rho hr0 hr1
    norm_num [Batch030.certificate1234,envelope617,inputs617,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch030.bound1235 rho hr0 hr1
    norm_num [Batch030.certificate1235,envelope617,inputs617,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs618 : RatMajorityInputs := ⟨(4271711666998873969455607/2000000000000000000000),(120254345377507/25000000000000),(125175765647367107/125000000000000000),(141577531135107187/1000000000000000000),(120254345377507/50000000000000),(90257651197572927/1000000000000000000),26⟩
theorem inputs_valid618 : inputs618.Valid := by decide +kernel
def envelope618 : RatMajorityEnvelope := ⟨309,0,inputs618,(2533125569/2191990000),(339302969839736151/500000000000000000)⟩
theorem envelope_sound618 : envelope618.Sound := by
  apply rat_majority_inputs_envelopes inputs618 inputs_valid618
  · norm_num [envelope618]
  · intro rho hr0 hr1
    have hh := Batch030.bound1236 rho hr0 hr1
    norm_num [Batch030.certificate1236,envelope618,inputs618,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch030.bound1237 rho hr0 hr1
    norm_num [Batch030.certificate1237,envelope618,inputs618,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs619 : RatMajorityInputs := ⟨(4271711666998873969455607/2000000000000000000000),(248204084840129/50000000000000),(125175765647367107/125000000000000000),(63854997550494669/500000000000000000),(248204084840129/100000000000000),(41786246321709739/500000000000000000),26⟩
theorem inputs_valid619 : inputs619.Valid := by decide +kernel
def envelope619 : RatMajorityEnvelope := ⟨309,1,inputs619,1,(54067922660640677/100000000000000000)⟩
theorem envelope_sound619 : envelope619.Sound := by
  apply rat_majority_inputs_envelopes inputs619 inputs_valid619
  · norm_num [envelope619]
  · intro rho hr0 hr1
    have hh := Batch030.bound1238 rho hr0 hr1
    norm_num [Batch030.certificate1238,envelope619,inputs619,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch030.bound1239 rho hr0 hr1
    norm_num [Batch030.certificate1239,envelope619,inputs619,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def configurations : List RatMajorityEnvelope := [envelope600,envelope601,envelope602,envelope603,envelope604,envelope605,envelope606,envelope607,envelope608,envelope609,envelope610,envelope611,envelope612,envelope613,envelope614,envelope615,envelope616,envelope617,envelope618,envelope619]
theorem configurations_sound : ∀ s∈configurations, s.Sound := by
  intro s hs
  simp only [configurations,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact envelope_sound600
  · exact envelope_sound601
  · exact envelope_sound602
  · exact envelope_sound603
  · exact envelope_sound604
  · exact envelope_sound605
  · exact envelope_sound606
  · exact envelope_sound607
  · exact envelope_sound608
  · exact envelope_sound609
  · exact envelope_sound610
  · exact envelope_sound611
  · exact envelope_sound612
  · exact envelope_sound613
  · exact envelope_sound614
  · exact envelope_sound615
  · exact envelope_sound616
  · exact envelope_sound617
  · exact envelope_sound618
  · exact envelope_sound619

end Cycle12.MajorityCertificates.Inputs030
