import Cycle12.RationalMajorityInputs
import Cycle12.MajorityCertificates.Batch028

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Inputs028

def inputs560 : RatMajorityInputs := ⟨(3166080184848138790552649/800000000000000000000),(8846430925101/2000000000000),(250189620573805721/250000000000000000),(91200336397223381/500000000000000000),(8846430925101/4000000000000),(21904884210627721/200000000000000000),26⟩
theorem inputs_valid560 : inputs560.Valid := by decide +kernel
def envelope560 : RatMajorityEnvelope := ⟨280,0,inputs560,(1331165781/1117375000),(89265922304246939/125000000000000000)⟩
theorem envelope_sound560 : envelope560.Sound := by
  apply rat_majority_inputs_envelopes inputs560 inputs_valid560
  · norm_num [envelope560]
  · intro rho hr0 hr1
    have hh := Batch028.bound1120 rho hr0 hr1
    norm_num [Batch028.certificate1120,envelope560,inputs560,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch028.bound1121 rho hr0 hr1
    norm_num [Batch028.certificate1121,envelope560,inputs560,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs561 : RatMajorityInputs := ⟨(3166080184848138790552649/800000000000000000000),(18948735043441/4000000000000),(250189620573805721/250000000000000000),(18575590360708237/125000000000000000),(18948735043441/8000000000000),(93612451038477899/1000000000000000000),26⟩
theorem inputs_valid561 : inputs561.Valid := by decide +kernel
def envelope561 : RatMajorityEnvelope := ⟨280,1,inputs561,1,(542695171675267371/1000000000000000000)⟩
theorem envelope_sound561 : envelope561.Sound := by
  apply rat_majority_inputs_envelopes inputs561 inputs_valid561
  · norm_num [envelope561]
  · intro rho hr0 hr1
    have hh := Batch028.bound1122 rho hr0 hr1
    norm_num [Batch028.certificate1122,envelope561,inputs561,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch028.bound1123 rho hr0 hr1
    norm_num [Batch028.certificate1123,envelope561,inputs561,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs562 : RatMajorityInputs := ⟨(75993285256336384940247517/20000000000000000000000),(44377015628477/10000000000000),(250197507141416213/250000000000000000),(180707520935090677/1000000000000000000),(44377015628477/20000000000000),(108733996178046841/1000000000000000000),25⟩
theorem inputs_valid562 : inputs562.Valid := by decide +kernel
def envelope562 : RatMajorityEnvelope := ⟨281,0,inputs562,(166074073/139496875),(142650925546224317/200000000000000000)⟩
theorem envelope_sound562 : envelope562.Sound := by
  apply rat_majority_inputs_envelopes inputs562 inputs_valid562
  · norm_num [envelope562]
  · intro rho hr0 hr1
    have hh := Batch028.bound1124 rho hr0 hr1
    norm_num [Batch028.certificate1124,envelope562,inputs562,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch028.bound1125 rho hr0 hr1
    norm_num [Batch028.certificate1125,envelope562,inputs562,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs563 : RatMajorityInputs := ⟨(75993285256336384940247517/20000000000000000000000),(47488963697217/10000000000000),(250197507141416213/250000000000000000),(5898277391930989/40000000000000000),(47488963697217/20000000000000),(11633228772253623/125000000000000000),26⟩
theorem inputs_valid563 : inputs563.Valid := by decide +kernel
def envelope563 : RatMajorityEnvelope := ⟨281,1,inputs563,1,(542579069794660991/1000000000000000000)⟩
theorem envelope_sound563 : envelope563.Sound := by
  apply rat_majority_inputs_envelopes inputs563 inputs_valid563
  · norm_num [envelope563]
  · intro rho hr0 hr1
    have hh := Batch028.bound1126 rho hr0 hr1
    norm_num [Batch028.certificate1126,envelope563,inputs563,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch028.bound1127 rho hr0 hr1
    norm_num [Batch028.certificate1127,envelope563,inputs563,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs564 : RatMajorityInputs := ⟨(365283903502575693220781789/100000000000000000000000),(222604448160229/50000000000000),(1000821803921194051/1000000000000000000),(1432313505770239/8000000000000000),(222604448160229/100000000000000),(6747162695710837/62500000000000000),25⟩
theorem inputs_valid564 : inputs564.Valid := by decide +kernel
def envelope564 : RatMajorityEnvelope := ⟨282,0,inputs564,(1326066993/1114615000),(712383108462862189/1000000000000000000)⟩
theorem envelope_sound564 : envelope564.Sound := by
  apply rat_majority_inputs_envelopes inputs564 inputs_valid564
  · norm_num [envelope564]
  · intro rho hr0 hr1
    have hh := Batch028.bound1128 rho hr0 hr1
    norm_num [Batch028.certificate1128,envelope564,inputs564,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch028.bound1129 rho hr0 hr1
    norm_num [Batch028.certificate1129,envelope564,inputs564,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs565 : RatMajorityInputs := ⟨(365283903502575693220781789/100000000000000000000000),(476009564223743/100000000000000),(1000821803921194051/1000000000000000000),(146366705190625249/1000000000000000000),(476009564223743/200000000000000),(18509230348802481/200000000000000000),26⟩
theorem inputs_valid565 : inputs565.Valid := by decide +kernel
def envelope565 : RatMajorityEnvelope := ⟨282,1,inputs565,1,(135617496786760383/250000000000000000)⟩
theorem envelope_sound565 : envelope565.Sound := by
  apply rat_majority_inputs_envelopes inputs565 inputs_valid565
  · norm_num [envelope565]
  · intro rho hr0 hr1
    have hh := Batch028.bound1130 rho hr0 hr1
    norm_num [Batch028.certificate1130,envelope565,inputs565,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch028.bound1131 rho hr0 hr1
    norm_num [Batch028.certificate1131,envelope565,inputs565,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs566 : RatMajorityInputs := ⟨(343368508631825043727599/97656250000000000000),(446150779072521/100000000000000),(1000853786179341187/1000000000000000000),(88977068541218831/500000000000000000),(446150779072521/200000000000000),(107447395500623271/1000000000000000000),26⟩
theorem inputs_valid566 : inputs566.Valid := by decide +kernel
def envelope566 : RatMajorityEnvelope := ⟨283,0,inputs566,(331147133/278321250),(356192691062841067/500000000000000000)⟩
theorem envelope_sound566 : envelope566.Sound := by
  apply rat_majority_inputs_envelopes inputs566 inputs_valid566
  · norm_num [envelope566]
  · intro rho hr0 hr1
    have hh := Batch028.bound1132 rho hr0 hr1
    norm_num [Batch028.certificate1132,envelope566,inputs566,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch028.bound1133 rho hr0 hr1
    norm_num [Batch028.certificate1133,envelope566,inputs566,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs567 : RatMajorityInputs := ⟨(343368508631825043727599/97656250000000000000),(476296867835649/100000000000000),(1000853786179341187/1000000000000000000),(14608815886842183/100000000000000000),(476296867835649/200000000000000),(9241330296837021/100000000000000000),26⟩
theorem inputs_valid567 : inputs567.Valid := by decide +kernel
def envelope567 : RatMajorityEnvelope := ⟨283,1,inputs567,1,(135613221592827663/250000000000000000)⟩
theorem envelope_sound567 : envelope567.Sound := by
  apply rat_majority_inputs_envelopes inputs567 inputs_valid567
  · norm_num [envelope567]
  · intro rho hr0 hr1
    have hh := Batch028.bound1134 rho hr0 hr1
    norm_num [Batch028.certificate1134,envelope567,inputs567,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch028.bound1135 rho hr0 hr1
    norm_num [Batch028.certificate1135,envelope567,inputs567,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs568 : RatMajorityInputs := ⟨(169427917605722762016073901/50000000000000000000000),(223004081364779/50000000000000),(500442971135576883/500000000000000000),(44529517413784621/250000000000000000),(223004081364779/100000000000000),(107524041597876707/1000000000000000000),26⟩
theorem inputs_valid568 : inputs568.Valid := by decide +kernel
def envelope568 : RatMajorityEnvelope := ⟨284,0,inputs568,(2644890537/2223980000),(142385851332866939/200000000000000000)⟩
theorem envelope_sound568 : envelope568.Sound := by
  apply rat_majority_inputs_envelopes inputs568 inputs_valid568
  · norm_num [envelope568]
  · intro rho hr0 hr1
    have hh := Batch028.bound1136 rho hr0 hr1
    norm_num [Batch028.certificate1136,envelope568,inputs568,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch028.bound1137 rho hr0 hr1
    norm_num [Batch028.certificate1137,envelope568,inputs568,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs569 : RatMajorityInputs := ⟨(169427917605722762016073901/50000000000000000000000),(238647856477283/50000000000000),(500442971135576883/500000000000000000),(145123365383360139/1000000000000000000),(238647856477283/100000000000000),(2298823016721313/25000000000000000),27⟩
theorem inputs_valid569 : inputs569.Valid := by decide +kernel
def envelope569 : RatMajorityEnvelope := ⟨284,1,inputs569,1,(542358579001953007/1000000000000000000)⟩
theorem envelope_sound569 : envelope569.Sound := by
  apply rat_majority_inputs_envelopes inputs569 inputs_valid569
  · norm_num [envelope569]
  · intro rho hr0 hr1
    have hh := Batch028.bound1138 rho hr0 hr1
    norm_num [Batch028.certificate1138,envelope569,inputs569,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch028.bound1139 rho hr0 hr1
    norm_num [Batch028.certificate1139,envelope569,inputs569,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs570 : RatMajorityInputs := ⟨(163472188273582714970586703/50000000000000000000000),(3507735211777/781250000000),(125114780321076651/125000000000000000),(174717174775983307/1000000000000000000),(3507735211777/1562500000000),(105932780152007553/1000000000000000000),25⟩
theorem inputs_valid570 : inputs570.Valid := by decide +kernel
def envelope570 : RatMajorityEnvelope := ⟨285,0,inputs570,(2639465099/2221460000),(710647051426388659/1000000000000000000)⟩
theorem envelope_sound570 : envelope570.Sound := by
  apply rat_majority_inputs_envelopes inputs570 inputs_valid570
  · norm_num [envelope570]
  · intro rho hr0 hr1
    have hh := Batch028.bound1140 rho hr0 hr1
    norm_num [Batch028.certificate1140,envelope570,inputs570,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch028.bound1141 rho hr0 hr1
    norm_num [Batch028.certificate1141,envelope570,inputs570,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs571 : RatMajorityInputs := ⟨(163472188273582714970586703/50000000000000000000000),(239110404879263/50000000000000),(125114780321076651/125000000000000000),(144234786030146567/1000000000000000000),(239110404879263/100000000000000),(45764288029951513/500000000000000000),26⟩
theorem inputs_valid571 : inputs571.Valid := by decide +kernel
def envelope571 : RatMajorityEnvelope := ⟨285,1,inputs571,1,(542273192185609531/1000000000000000000)⟩
theorem envelope_sound571 : envelope571.Sound := by
  apply rat_majority_inputs_envelopes inputs571 inputs_valid571
  · norm_num [envelope571]
  · intro rho hr0 hr1
    have hh := Batch028.bound1142 rho hr0 hr1
    norm_num [Batch028.certificate1142,envelope571,inputs571,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch028.bound1143 rho hr0 hr1
    norm_num [Batch028.certificate1143,envelope571,inputs571,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs572 : RatMajorityInputs := ⟨(39475731854803128789842123/12500000000000000000000),(112570260944429/25000000000000),(250237663267691597/250000000000000000),(34652440705482333/200000000000000000),(112570260944429/50000000000000),(26312804898677689/250000000000000000),25⟩
theorem inputs_valid572 : inputs572.Valid := by decide +kernel
def envelope572 : RatMajorityEnvelope := ⟨286,0,inputs572,(2634786251/2219020000),(141961543097391603/200000000000000000)⟩
theorem envelope_sound572 : envelope572.Sound := by
  apply rat_majority_inputs_envelopes inputs572 inputs_valid572
  · norm_num [envelope572]
  · intro rho hr0 hr1
    have hh := Batch028.bound1144 rho hr0 hr1
    norm_num [Batch028.certificate1144,envelope572,inputs572,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch028.bound1145 rho hr0 hr1
    norm_num [Batch028.certificate1145,envelope572,inputs572,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs573 : RatMajorityInputs := ⟨(39475731854803128789842123/12500000000000000000000),(239206725794231/50000000000000),(250237663267691597/250000000000000000),(36012587307162941/250000000000000000),(239206725794231/100000000000000),(91440457343174889/1000000000000000000),27⟩
theorem inputs_valid573 : inputs573.Valid := by decide +kernel
def envelope573 : RatMajorityEnvelope := ⟨286,1,inputs573,1,(542267065774470489/1000000000000000000)⟩
theorem envelope_sound573 : envelope573.Sound := by
  apply rat_majority_inputs_envelopes inputs573 inputs_valid573
  · norm_num [envelope573]
  · intro rho hr0 hr1
    have hh := Batch028.bound1146 rho hr0 hr1
    norm_num [Batch028.certificate1146,envelope573,inputs573,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch028.bound1147 rho hr0 hr1
    norm_num [Batch028.certificate1147,envelope573,inputs573,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs574 : RatMajorityInputs := ⟨(9542943907532814178649349/3125000000000000000000),(14125357806183/3125000000000),(1000983152417468819/1000000000000000000),(171328229618787477/1000000000000000000),(14125357806183/6250000000000),(20868902193196049/200000000000000000),27⟩
theorem inputs_valid574 : inputs574.Valid := by decide +kernel
def envelope574 : RatMajorityEnvelope := ⟨287,0,inputs574,(525638231/443328000),(5532134810859069/7812500000000000)⟩
theorem envelope_sound574 : envelope574.Sound := by
  apply rat_majority_inputs_envelopes inputs574 inputs_valid574
  · norm_num [envelope574]
  · intro rho hr0 hr1
    have hh := Batch028.bound1148 rho hr0 hr1
    norm_num [Batch028.certificate1148,envelope574,inputs574,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch028.bound1149 rho hr0 hr1
    norm_num [Batch028.certificate1149,envelope574,inputs574,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs575 : RatMajorityInputs := ⟨(9542943907532814178649349/3125000000000000000000),(3746275497159/781250000000),(1000983152417468819/1000000000000000000),(71495912868570377/500000000000000000),(3746275497159/1562500000000),(11366806744637133/125000000000000000),26⟩
theorem inputs_valid575 : inputs575.Valid := by decide +kernel
def envelope575 : RatMajorityEnvelope := ⟨287,1,inputs575,1,(135540766362372857/250000000000000000)⟩
theorem envelope_sound575 : envelope575.Sound := by
  apply rat_majority_inputs_envelopes inputs575 inputs_valid575
  · norm_num [envelope575]
  · intro rho hr0 hr1
    have hh := Batch028.bound1150 rho hr0 hr1
    norm_num [Batch028.certificate1150,envelope575,inputs575,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch028.bound1151 rho hr0 hr1
    norm_num [Batch028.certificate1151,envelope575,inputs575,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs576 : RatMajorityInputs := ⟨(147797096241412598299245243/50000000000000000000000),(453396091090467/100000000000000),(1001015706636243659/1000000000000000000),(16979407633283771/100000000000000000),(453396091090467/200000000000000),(25906151817424501/250000000000000000),26⟩
theorem inputs_valid576 : inputs576.Valid := by decide +kernel
def envelope576 : RatMajorityEnvelope := ⟨288,0,inputs576,(163976869/138395625),(707248880558204027/1000000000000000000)⟩
theorem envelope_sound576 : envelope576.Sound := by
  apply rat_majority_inputs_envelopes inputs576 inputs_valid576
  · norm_num [envelope576]
  · intro rho hr0 hr1
    have hh := Batch028.bound1152 rho hr0 hr1
    norm_num [Batch028.certificate1152,envelope576,inputs576,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch028.bound1153 rho hr0 hr1
    norm_num [Batch028.certificate1153,envelope576,inputs576,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs577 : RatMajorityInputs := ⟨(147797096241412598299245243/50000000000000000000000),(7506549692277/1562500000000),(1001015706636243659/1000000000000000000),(28428458703219351/200000000000000000),(7506549692277/3125000000000),(9052801650636467/100000000000000000),27⟩
theorem inputs_valid577 : inputs577.Valid := by decide +kernel
def envelope577 : RatMajorityEnvelope := ⟨288,1,inputs577,1,(33880173265323237/62500000000000000)⟩
theorem envelope_sound577 : envelope577.Sound := by
  apply rat_majority_inputs_envelopes inputs577 inputs_valid577
  · norm_num [envelope577]
  · intro rho hr0 hr1
    have hh := Batch028.bound1154 rho hr0 hr1
    norm_num [Batch028.certificate1154,envelope577,inputs577,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch028.bound1155 rho hr0 hr1
    norm_num [Batch028.certificate1155,envelope577,inputs577,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs578 : RatMajorityInputs := ⟨(35801688159357911307251241/12500000000000000000000),(56895859301463/12500000000000),(500524145299260239/500000000000000000),(167849310515754373/1000000000000000000),(56895859301463/25000000000000),(51355586669821881/500000000000000000),26⟩
theorem inputs_valid578 : inputs578.Valid := by decide +kernel
def envelope578 : RatMajorityEnvelope := ⟨289,0,inputs578,(218098947/184340000),(705548641582900779/1000000000000000000)⟩
theorem envelope_sound578 : envelope578.Sound := by
  apply rat_majority_inputs_envelopes inputs578 inputs_valid578
  · norm_num [envelope578]
  · intro rho hr0 hr1
    have hh := Batch028.bound1156 rho hr0 hr1
    norm_num [Batch028.certificate1156,envelope578,inputs578,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch028.bound1157 rho hr0 hr1
    norm_num [Batch028.certificate1157,envelope578,inputs578,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs579 : RatMajorityInputs := ⟨(35801688159357911307251241/12500000000000000000000),(60188064120639/12500000000000),(500524145299260239/500000000000000000),(141119085551529303/1000000000000000000),(60188064120639/25000000000000),(90038081998977411/1000000000000000000),26⟩
theorem inputs_valid579 : inputs579.Valid := by decide +kernel
def envelope579 : RatMajorityEnvelope := ⟨289,1,inputs579,1,(541983381706013357/1000000000000000000)⟩
theorem envelope_sound579 : envelope579.Sound := by
  apply rat_majority_inputs_envelopes inputs579 inputs_valid579
  · norm_num [envelope579]
  · intro rho hr0 hr1
    have hh := Batch028.bound1158 rho hr0 hr1
    norm_num [Batch028.certificate1158,envelope579,inputs579,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch028.bound1159 rho hr0 hr1
    norm_num [Batch028.certificate1159,envelope579,inputs579,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def configurations : List RatMajorityEnvelope := [envelope560,envelope561,envelope562,envelope563,envelope564,envelope565,envelope566,envelope567,envelope568,envelope569,envelope570,envelope571,envelope572,envelope573,envelope574,envelope575,envelope576,envelope577,envelope578,envelope579]
theorem configurations_sound : ∀ s∈configurations, s.Sound := by
  intro s hs
  simp only [configurations,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact envelope_sound560
  · exact envelope_sound561
  · exact envelope_sound562
  · exact envelope_sound563
  · exact envelope_sound564
  · exact envelope_sound565
  · exact envelope_sound566
  · exact envelope_sound567
  · exact envelope_sound568
  · exact envelope_sound569
  · exact envelope_sound570
  · exact envelope_sound571
  · exact envelope_sound572
  · exact envelope_sound573
  · exact envelope_sound574
  · exact envelope_sound575
  · exact envelope_sound576
  · exact envelope_sound577
  · exact envelope_sound578
  · exact envelope_sound579

end Cycle12.MajorityCertificates.Inputs028
