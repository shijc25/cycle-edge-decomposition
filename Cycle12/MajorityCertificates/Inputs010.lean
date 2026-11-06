import Cycle12.RationalMajorityInputs
import Cycle12.MajorityCertificates.Batch010

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Inputs010

def inputs200 : RatMajorityInputs := ⟨(21079804626618634735410933/50000000000000000000000),(213057876461013/50000000000000),(1007155399278960521/1000000000000000000),(202277974618520173/1000000000000000000),(213057876461013/100000000000000),(59384267465949249/500000000000000000),25⟩
theorem inputs_valid200 : inputs200.Valid := by decide +kernel
def envelope200 : RatMajorityEnvelope := ⟨100,0,inputs200,(2333934031/1956060000),(180316827439910943/250000000000000000)⟩
theorem envelope_sound200 : envelope200.Sound := by
  apply rat_majority_inputs_envelopes inputs200 inputs_valid200
  · norm_num [envelope200]
  · intro rho hr0 hr1
    have hh := Batch010.bound400 rho hr0 hr1
    norm_num [Batch010.certificate400,envelope200,inputs200,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch010.bound401 rho hr0 hr1
    norm_num [Batch010.certificate401,envelope200,inputs200,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs201 : RatMajorityInputs := ⟨(21079804626618634735410933/50000000000000000000000),(123794225590203/25000000000000),(1007155399278960521/1000000000000000000),(64386730358823341/500000000000000000),(123794225590203/50000000000000),(84088580012184177/1000000000000000000),26⟩
theorem inputs_valid201 : inputs201.Valid := by decide +kernel
def envelope201 : RatMajorityEnvelope := ⟨100,1,inputs201,1,(543429314248083431/1000000000000000000)⟩
theorem envelope_sound201 : envelope201.Sound := by
  apply rat_majority_inputs_envelopes inputs201 inputs_valid201
  · norm_num [envelope201]
  · intro rho hr0 hr1
    have hh := Batch010.bound402 rho hr0 hr1
    norm_num [Batch010.certificate402,envelope201,inputs201,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch010.bound403 rho hr0 hr1
    norm_num [Batch010.certificate403,envelope201,inputs201,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs202 : RatMajorityInputs := ⟨(10552670605582632086656371/25000000000000000000000),(430353553918959/100000000000000),(251786673365702731/250000000000000000),(3938232145823043/20000000000000000),(430353553918959/200000000000000),(116278422520948729/1000000000000000000),25⟩
theorem inputs_valid202 : inputs202.Valid := by decide +kernel
def envelope202 : RatMajorityEnvelope := ⟨101,0,inputs202,(31063427/26193200),(357099820529344571/500000000000000000)⟩
theorem envelope_sound202 : envelope202.Sound := by
  apply rat_majority_inputs_envelopes inputs202 inputs_valid202
  · norm_num [envelope202]
  · intro rho hr0 hr1
    have hh := Batch010.bound404 rho hr0 hr1
    norm_num [Batch010.certificate404,envelope202,inputs202,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch010.bound405 rho hr0 hr1
    norm_num [Batch010.certificate405,envelope202,inputs202,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs203 : RatMajorityInputs := ⟨(10552670605582632086656371/25000000000000000000000),(124381975290969/25000000000000),(251786673365702731/250000000000000000),(15843703664807663/125000000000000000),(124381975290969/50000000000000),(41552953117510991/500000000000000000),26⟩
theorem inputs_valid203 : inputs203.Valid := by decide +kernel
def envelope203 : RatMajorityEnvelope := ⟨101,1,inputs203,1,(543214216519857657/1000000000000000000)⟩
theorem envelope_sound203 : envelope203.Sound := by
  apply rat_majority_inputs_envelopes inputs203 inputs_valid203
  · norm_num [envelope203]
  · intro rho hr0 hr1
    have hh := Batch010.bound406 rho hr0 hr1
    norm_num [Batch010.certificate406,envelope203,inputs203,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch010.bound407 rho hr0 hr1
    norm_num [Batch010.certificate407,envelope203,inputs203,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs204 : RatMajorityInputs := ⟨(20971998535697738418141369/50000000000000000000000),(43034408711353/10000000000000),(1007192387024942709/1000000000000000000),(12307716277109277/62500000000000000),(43034408711353/20000000000000),(5814196328861013/50000000000000000),25⟩
theorem inputs_valid204 : inputs204.Valid := by decide +kernel
def envelope204 : RatMajorityEnvelope := ⟨102,0,inputs204,(2328158023/1963730000),(713904834251680939/1000000000000000000)⟩
theorem envelope_sound204 : envelope204.Sound := by
  apply rat_majority_inputs_envelopes inputs204 inputs_valid204
  · norm_num [envelope204]
  · intro rho hr0 hr1
    have hh := Batch010.bound408 rho hr0 hr1
    norm_num [Batch010.certificate408,envelope204,inputs204,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch010.bound409 rho hr0 hr1
    norm_num [Batch010.certificate409,envelope204,inputs204,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs205 : RatMajorityInputs := ⟨(20971998535697738418141369/50000000000000000000000),(62201139698707/12500000000000),(1007192387024942709/1000000000000000000),(126680221711093457/1000000000000000000),(62201139698707/25000000000000),(1298002582233757/15625000000000000),26⟩
theorem inputs_valid205 : inputs205.Valid := by decide +kernel
def envelope205 : RatMajorityEnvelope := ⟨102,1,inputs205,1,(108645599344552757/200000000000000000)⟩
theorem envelope_sound205 : envelope205.Sound := by
  apply rat_majority_inputs_envelopes inputs205 inputs_valid205
  · norm_num [envelope205]
  · intro rho hr0 hr1
    have hh := Batch010.bound410 rho hr0 hr1
    norm_num [Batch010.certificate410,envelope205,inputs205,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch010.bound411 rho hr0 hr1
    norm_num [Batch010.certificate411,envelope205,inputs205,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs206 : RatMajorityInputs := ⟨(10420288669020719648175117/25000000000000000000000),(215557379686911/50000000000000),(503618998746617691/500000000000000000),(39192097142790547/200000000000000000),(215557379686911/100000000000000),(115836704801484611/1000000000000000000),25⟩
theorem inputs_valid206 : inputs206.Valid := by decide +kernel
def envelope206 : RatMajorityEnvelope := ⟨103,0,inputs206,(2326215387/1962980000),(713354287576641449/1000000000000000000)⟩
theorem envelope_sound206 : envelope206.Sound := by
  apply rat_majority_inputs_envelopes inputs206 inputs_valid206
  · norm_num [envelope206]
  · intro rho hr0 hr1
    have hh := Batch010.bound412 rho hr0 hr1
    norm_num [Batch010.certificate412,envelope206,inputs206,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch010.bound413 rho hr0 hr1
    norm_num [Batch010.certificate413,envelope206,inputs206,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs207 : RatMajorityInputs := ⟨(10420288669020719648175117/25000000000000000000000),(248923220767309/50000000000000),(503618998746617691/500000000000000000),(126477597624040507/1000000000000000000),(248923220767309/100000000000000),(4148682432775569/50000000000000000),26⟩
theorem inputs_valid207 : inputs207.Valid := by decide +kernel
def envelope207 : RatMajorityEnvelope := ⟨103,1,inputs207,1,(543227897614675109/1000000000000000000)⟩
theorem envelope_sound207 : envelope207.Sound := by
  apply rat_majority_inputs_envelopes inputs207 inputs_valid207
  · norm_num [envelope207]
  · intro rho hr0 hr1
    have hh := Batch010.bound414 rho hr0 hr1
    norm_num [Batch010.certificate414,envelope207,inputs207,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch010.bound415 rho hr0 hr1
    norm_num [Batch010.certificate415,envelope207,inputs207,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs208 : RatMajorityInputs := ⟨(323610088708253975035023/781250000000000000000),(3372856895541/781250000000),(503641760903407947/500000000000000000),(195199943081267833/1000000000000000000),(3372856895541/1562500000000),(5774170399265991/50000000000000000),25⟩
theorem inputs_valid208 : inputs208.Valid := by decide +kernel
def envelope208 : RatMajorityEnvelope := ⟨104,0,inputs208,(774707947/654080000),(356374217416025491/500000000000000000)⟩
theorem envelope_sound208 : envelope208.Sound := by
  apply rat_majority_inputs_envelopes inputs208 inputs_valid208
  · norm_num [envelope208]
  · intro rho hr0 hr1
    have hh := Batch010.bound416 rho hr0 hr1
    norm_num [Batch010.certificate416,envelope208,inputs208,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch010.bound417 rho hr0 hr1
    norm_num [Batch010.certificate417,envelope208,inputs208,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs209 : RatMajorityInputs := ⟨(323610088708253975035023/781250000000000000000),(1945920848613/390625000000),(503641760903407947/500000000000000000),(31553489105418193/250000000000000000),(1945920848613/781250000000),(10355678857014237/125000000000000000),26⟩
theorem inputs_valid209 : inputs209.Valid := by decide +kernel
def envelope209 : RatMajorityEnvelope := ⟨104,1,inputs209,1,(67902680577441123/125000000000000000)⟩
theorem envelope_sound209 : envelope209.Sound := by
  apply rat_majority_inputs_envelopes inputs209 inputs_valid209
  · norm_num [envelope209]
  · intro rho hr0 hr1
    have hh := Batch010.bound418 rho hr0 hr1
    norm_num [Batch010.certificate418,envelope209,inputs209,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch010.bound419 rho hr0 hr1
    norm_num [Batch010.certificate419,envelope209,inputs209,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs210 : RatMajorityInputs := ⟨(10291686157725971752283513/25000000000000000000000),(216006042299203/50000000000000),(50366447845363727/50000000000000000),(12177766049312987/62500000000000000),(216006042299203/100000000000000),(922545223677691/8000000000000000),25⟩
theorem inputs_valid210 : inputs210.Valid := by decide +kernel
def envelope210 : RatMajorityEnvelope := ⟨105,0,inputs210,(2322423181/1961510000),(712354896962078953/1000000000000000000)⟩
theorem envelope_sound210 : envelope210.Sound := by
  apply rat_majority_inputs_envelopes inputs210 inputs_valid210
  · norm_num [envelope210]
  · intro rho hr0 hr1
    have hh := Batch010.bound420 rho hr0 hr1
    norm_num [Batch010.certificate420,envelope210,inputs210,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch010.bound421 rho hr0 hr1
    norm_num [Batch010.certificate421,envelope210,inputs210,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs211 : RatMajorityInputs := ⟨(10291686157725971752283513/25000000000000000000000),(49819225587701/10000000000000),(50366447845363727/50000000000000000),(246450899273557/1953125000000000),(49819225587701/20000000000000),(20707576307007123/250000000000000000),27⟩
theorem inputs_valid211 : inputs211.Valid := by decide +kernel
def envelope211 : RatMajorityEnvelope := ⟨105,1,inputs211,1,(543239110852466509/1000000000000000000)⟩
theorem envelope_sound211 : envelope211.Sound := by
  apply rat_majority_inputs_envelopes inputs211 inputs_valid211
  · norm_num [envelope211]
  · intro rho hr0 hr1
    have hh := Batch010.bound422 rho hr0 hr1
    norm_num [Batch010.certificate422,envelope211,inputs211,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch010.bound423 rho hr0 hr1
    norm_num [Batch010.certificate423,envelope211,inputs211,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs212 : RatMajorityInputs := ⟨(8221831773067060228431237/20000000000000000000000),(211461368579/48828125000),(62958705116858597/62500000000000000),(193531595822817787/1000000000000000000),(211461368579/97656250000),(11470812570438511/100000000000000000),26⟩
theorem inputs_valid212 : inputs212.Valid := by decide +kernel
def envelope212 : RatMajorityEnvelope := ⟨106,0,inputs212,(2321112909/1961530000),(711622883322017541/1000000000000000000)⟩
theorem envelope_sound212 : envelope212.Sound := by
  apply rat_majority_inputs_envelopes inputs212 inputs_valid212
  · norm_num [envelope212]
  · intro rho hr0 hr1
    have hh := Batch010.bound424 rho hr0 hr1
    norm_num [Batch010.certificate424,envelope212,inputs212,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch010.bound425 rho hr0 hr1
    norm_num [Batch010.certificate425,envelope212,inputs212,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs213 : RatMajorityInputs := ⟨(8221831773067060228431237/20000000000000000000000),(124663402645521/25000000000000),(62958705116858597/62500000000000000),(31447649253634677/250000000000000000),(124663402645521/50000000000000),(41319727340976603/500000000000000000),26⟩
theorem inputs_valid213 : inputs213.Valid := by decide +kernel
def envelope213 : RatMajorityEnvelope := ⟨106,1,inputs213,1,(10864063381217783/20000000000000000)⟩
theorem envelope_sound213 : envelope213.Sound := by
  apply rat_majority_inputs_envelopes inputs213 inputs_valid213
  · norm_num [envelope213]
  · intro rho hr0 hr1
    have hh := Batch010.bound426 rho hr0 hr1
    norm_num [Batch010.certificate426,envelope213,inputs213,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch010.bound427 rho hr0 hr1
    norm_num [Batch010.certificate427,envelope213,inputs213,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs214 : RatMajorityInputs := ⟨(20491806252090428297414483/50000000000000000000000),(86592158543603/20000000000000),(20147237862634103/20000000000000000),(24208743210364729/125000000000000000),(86592158543603/40000000000000),(114772431967576141/1000000000000000000),26⟩
theorem inputs_valid214 : inputs214.Valid := by decide +kernel
def envelope214 : RatMajorityEnvelope := ⟨107,0,inputs214,(2320351889/1961170000),(711493885803406667/1000000000000000000)⟩
theorem envelope_sound214 : envelope214.Sound := by
  apply rat_majority_inputs_envelopes inputs214 inputs_valid214
  · norm_num [envelope214]
  · intro rho hr0 hr1
    have hh := Batch010.bound428 rho hr0 hr1
    norm_num [Batch010.certificate428,envelope214,inputs214,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch010.bound429 rho hr0 hr1
    norm_num [Batch010.certificate429,envelope214,inputs214,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs215 : RatMajorityInputs := ⟨(20491806252090428297414483/50000000000000000000000),(49879744122039/10000000000000),(20147237862634103/20000000000000000),(125668527511175287/1000000000000000000),(49879744122039/20000000000000),(41290022809520709/500000000000000000),26⟩
theorem inputs_valid215 : inputs215.Valid := by decide +kernel
def envelope215 : RatMajorityEnvelope := ⟨107,1,inputs215,1,(543200919817270311/1000000000000000000)⟩
theorem envelope_sound215 : envelope215.Sound := by
  apply rat_majority_inputs_envelopes inputs215 inputs_valid215
  · norm_num [envelope215]
  · intro rho hr0 hr1
    have hh := Batch010.bound430 rho hr0 hr1
    norm_num [Batch010.certificate430,envelope215,inputs215,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch010.bound431 rho hr0 hr1
    norm_num [Batch010.certificate431,envelope215,inputs215,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs216 : RatMajorityInputs := ⟨(8133350081374068377473297/20000000000000000000000),(431977388384899/100000000000000),(1007419585320748907/1000000000000000000),(48721829337767579/250000000000000000),(431977388384899/200000000000000),(57669080105691251/500000000000000000),25⟩
theorem inputs_valid216 : inputs216.Valid := by decide +kernel
def envelope216 : RatMajorityEnvelope := ⟨108,0,inputs216,(2319092819/1960070000),(177914851456653599/250000000000000000)⟩
theorem envelope_sound216 : envelope216.Sound := by
  apply rat_majority_inputs_envelopes inputs216 inputs_valid216
  · norm_num [envelope216]
  · intro rho hr0 hr1
    have hh := Batch010.bound432 rho hr0 hr1
    norm_num [Batch010.certificate432,envelope216,inputs216,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch010.bound433 rho hr0 hr1
    norm_num [Batch010.certificate433,envelope216,inputs216,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs217 : RatMajorityInputs := ⟨(8133350081374068377473297/20000000000000000000000),(124684743735531/25000000000000),(1007419585320748907/1000000000000000000),(125718135335098743/1000000000000000000),(124684743735531/50000000000000),(82604189887565189/1000000000000000000),27⟩
theorem inputs_valid217 : inputs217.Valid := by decide +kernel
def envelope217 : RatMajorityEnvelope := ⟨108,1,inputs217,1,(543232607452270633/1000000000000000000)⟩
theorem envelope_sound217 : envelope217.Sound := by
  apply rat_majority_inputs_envelopes inputs217 inputs_valid217
  · norm_num [envelope217]
  · intro rho hr0 hr1
    have hh := Batch010.bound434 rho hr0 hr1
    norm_num [Batch010.certificate434,envelope217,inputs217,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch010.bound435 rho hr0 hr1
    norm_num [Batch010.certificate435,envelope217,inputs217,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs218 : RatMajorityInputs := ⟨(315796773509008097091201/781250000000000000000),(13540969746993/3125000000000),(7870818539260401/7812500000000000),(193237931703321211/1000000000000000000),(13540969746993/6250000000000),(114571618834864953/1000000000000000000),25⟩
theorem inputs_valid218 : inputs218.Valid := by decide +kernel
def envelope218 : RatMajorityEnvelope := ⟨109,0,inputs218,(193059071/163280000),(710817685054558479/1000000000000000000)⟩
theorem envelope_sound218 : envelope218.Sound := by
  apply rat_majority_inputs_envelopes inputs218 inputs_valid218
  · norm_num [envelope218]
  · intro rho hr0 hr1
    have hh := Batch010.bound436 rho hr0 hr1
    norm_num [Batch010.certificate436,envelope218,inputs218,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch010.bound437 rho hr0 hr1
    norm_num [Batch010.certificate437,envelope218,inputs218,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs219 : RatMajorityInputs := ⟨(315796773509008097091201/781250000000000000000),(7797884581149/1562500000000),(7870818539260401/7812500000000000),(62721028400140759/500000000000000000),(7797884581149/3125000000000),(41234901950263247/500000000000000000),27⟩
theorem inputs_valid219 : inputs219.Valid := by decide +kernel
def envelope219 : RatMajorityEnvelope := ⟨109,1,inputs219,1,(543224810924872243/1000000000000000000)⟩
theorem envelope_sound219 : envelope219.Sound := by
  apply rat_majority_inputs_envelopes inputs219 inputs_valid219
  · norm_num [envelope219]
  · intro rho hr0 hr1
    have hh := Batch010.bound438 rho hr0 hr1
    norm_num [Batch010.certificate438,envelope219,inputs219,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch010.bound439 rho hr0 hr1
    norm_num [Batch010.certificate439,envelope219,inputs219,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def configurations : List RatMajorityEnvelope := [envelope200,envelope201,envelope202,envelope203,envelope204,envelope205,envelope206,envelope207,envelope208,envelope209,envelope210,envelope211,envelope212,envelope213,envelope214,envelope215,envelope216,envelope217,envelope218,envelope219]
theorem configurations_sound : ∀ s∈configurations, s.Sound := by
  intro s hs
  simp only [configurations,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact envelope_sound200
  · exact envelope_sound201
  · exact envelope_sound202
  · exact envelope_sound203
  · exact envelope_sound204
  · exact envelope_sound205
  · exact envelope_sound206
  · exact envelope_sound207
  · exact envelope_sound208
  · exact envelope_sound209
  · exact envelope_sound210
  · exact envelope_sound211
  · exact envelope_sound212
  · exact envelope_sound213
  · exact envelope_sound214
  · exact envelope_sound215
  · exact envelope_sound216
  · exact envelope_sound217
  · exact envelope_sound218
  · exact envelope_sound219

end Cycle12.MajorityCertificates.Inputs010
