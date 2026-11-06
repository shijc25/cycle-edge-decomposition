import Cycle12.RationalMajorityInputs
import Cycle12.MajorityCertificates.Batch006

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Inputs006

def inputs120 : RatMajorityInputs := ⟨(737596202908485080430109/1250000000000000000000),(3240811429611/781250000000),(251276064938497917/250000000000000000),(217177293802218173/1000000000000000000),(3240811429611/1562500000000),(12566705186715733/100000000000000000),25⟩
theorem inputs_valid120 : inputs120.Valid := by decide +kernel
def envelope120 : RatMajorityEnvelope := ⟨60,0,inputs120,(1204440619/1003160000),(72833062498620823/100000000000000000)⟩
theorem envelope_sound120 : envelope120.Sound := by
  apply rat_majority_inputs_envelopes inputs120 inputs_valid120
  · norm_num [envelope120]
  · intro rho hr0 hr1
    have hh := Batch006.bound240 rho hr0 hr1
    norm_num [Batch006.certificate240,envelope120,inputs120,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch006.bound241 rho hr0 hr1
    norm_num [Batch006.certificate241,envelope120,inputs120,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs121 : RatMajorityInputs := ⟨(737596202908485080430109/1250000000000000000000),(12296882167703/2500000000000),(251276064938497917/250000000000000000),(65831955562072261/500000000000000000),(12296882167703/5000000000000),(17097648390142613/200000000000000000),26⟩
theorem inputs_valid121 : inputs121.Valid := by decide +kernel
def envelope121 : RatMajorityEnvelope := ⟨60,1,inputs121,1,(16962365378947727/31250000000000000)⟩
theorem envelope_sound121 : envelope121.Sound := by
  apply rat_majority_inputs_envelopes inputs121 inputs_valid121
  · norm_num [envelope121]
  · intro rho hr0 hr1
    have hh := Batch006.bound242 rho hr0 hr1
    norm_num [Batch006.certificate242,envelope121,inputs121,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch006.bound243 rho hr0 hr1
    norm_num [Batch006.certificate243,envelope121,inputs121,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs122 : RatMajorityInputs := ⟨(14620100890162058472066851/25000000000000000000000),(52033302209819/12500000000000),(502575233457690119/500000000000000000),(4304490604225097/20000000000000000),(52033302209819/25000000000000),(3119097622640177/25000000000000000),26⟩
theorem inputs_valid122 : inputs122.Valid := by decide +kernel
def envelope122 : RatMajorityEnvelope := ⟨61,0,inputs122,(1203203687/1002590000),(363831982379372727/500000000000000000)⟩
theorem envelope_sound122 : envelope122.Sound := by
  apply rat_majority_inputs_envelopes inputs122 inputs_valid122
  · norm_num [envelope122]
  · intro rho hr0 hr1
    have hh := Batch006.bound244 rho hr0 hr1
    norm_num [Batch006.certificate244,envelope122,inputs122,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch006.bound245 rho hr0 hr1
    norm_num [Batch006.certificate245,envelope122,inputs122,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs123 : RatMajorityInputs := ⟨(14620100890162058472066851/25000000000000000000000),(30750253112663/6250000000000),(502575233457690119/500000000000000000),(131550117410178467/1000000000000000000),(30750253112663/12500000000000),(21358305252850007/250000000000000000),26⟩
theorem inputs_valid123 : inputs123.Valid := by decide +kernel
def envelope123 : RatMajorityEnvelope := ⟨61,1,inputs123,1,(271402343458869577/500000000000000000)⟩
theorem envelope_sound123 : envelope123.Sound := by
  apply rat_majority_inputs_envelopes inputs123 inputs_valid123
  · norm_num [envelope123]
  · intro rho hr0 hr1
    have hh := Batch006.bound246 rho hr0 hr1
    norm_num [Batch006.certificate246,envelope123,inputs123,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch006.bound247 rho hr0 hr1
    norm_num [Batch006.certificate247,envelope123,inputs123,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs124 : RatMajorityInputs := ⟨(895044152369152124553403/1562500000000000000000),(103881667600179/25000000000000),(1005258584762215319/1000000000000000000),(54056022291521539/250000000000000000),(103881667600179/50000000000000),(125226228179622737/1000000000000000000),25⟩
theorem inputs_valid124 : inputs124.Valid := by decide +kernel
def envelope124 : RatMajorityEnvelope := ⟨62,0,inputs124,(1201675283/1001140000),(145602774753124663/200000000000000000)⟩
theorem envelope_sound124 : envelope124.Sound := by
  apply rat_majority_inputs_envelopes inputs124 inputs_valid124
  · norm_num [envelope124]
  · intro rho hr0 hr1
    have hh := Batch006.bound248 rho hr0 hr1
    norm_num [Batch006.certificate248,envelope124,inputs124,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch006.bound249 rho hr0 hr1
    norm_num [Batch006.certificate249,envelope124,inputs124,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs125 : RatMajorityInputs := ⟨(895044152369152124553403/1562500000000000000000),(122953730293821/25000000000000),(1005258584762215319/1000000000000000000),(131717288793084209/1000000000000000000),(122953730293821/50000000000000),(85514048561474511/1000000000000000000),27⟩
theorem inputs_valid125 : inputs125.Valid := by decide +kernel
def envelope125 : RatMajorityEnvelope := ⟨62,1,inputs125,1,(54287187143138583/100000000000000000)⟩
theorem envelope_sound125 : envelope125.Sound := by
  apply rat_majority_inputs_envelopes inputs125 inputs_valid125
  · norm_num [envelope125]
  · intro rho hr0 hr1
    have hh := Batch006.bound250 rho hr0 hr1
    norm_num [Batch006.certificate250,envelope125,inputs125,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch006.bound251 rho hr0 hr1
    norm_num [Batch006.certificate251,envelope125,inputs125,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs126 : RatMajorityInputs := ⟨(56950586532228609639887847/100000000000000000000000),(416987213614167/100000000000000),(1005289388498388519/1000000000000000000),(26781783351944799/125000000000000000),(416987213614167/200000000000000),(124315067613825661/1000000000000000000),25⟩
theorem inputs_valid126 : inputs126.Valid := by decide +kernel
def envelope126 : RatMajorityEnvelope := ⟨63,0,inputs126,(1200605009/1000905000),(727124142161518381/1000000000000000000)⟩
theorem envelope_sound126 : envelope126.Sound := by
  apply rat_majority_inputs_envelopes inputs126 inputs_valid126
  · norm_num [envelope126]
  · intro rho hr0 hr1
    have hh := Batch006.bound252 rho hr0 hr1
    norm_num [Batch006.certificate252,envelope126,inputs126,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch006.bound253 rho hr0 hr1
    norm_num [Batch006.certificate253,envelope126,inputs126,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs127 : RatMajorityInputs := ⟨(56950586532228609639887847/100000000000000000000000),(492300609809943/100000000000000),(1005289388498388519/1000000000000000000),(32822091156345273/250000000000000000),(492300609809943/200000000000000),(85306634502584787/1000000000000000000),26⟩
theorem inputs_valid127 : inputs127.Valid := by decide +kernel
def envelope127 : RatMajorityEnvelope := ⟨63,1,inputs127,1,(542840327415411983/1000000000000000000)⟩
theorem envelope_sound127 : envelope127.Sound := by
  apply rat_majority_inputs_envelopes inputs127 inputs_valid127
  · norm_num [envelope127]
  · intro rho hr0 hr1
    have hh := Batch006.bound254 rho hr0 hr1
    norm_num [Batch006.certificate254,envelope127,inputs127,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch006.bound255 rho hr0 hr1
    norm_num [Batch006.certificate255,envelope127,inputs127,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs128 : RatMajorityInputs := ⟨(705716269162260361920603/1250000000000000000000),(20853535523769/5000000000000),(1005335795196675851/1000000000000000000),(4282842132076897/20000000000000000),(20853535523769/10000000000000),(31065794714053529/250000000000000000),25⟩
theorem inputs_valid128 : inputs128.Valid := by decide +kernel
def envelope128 : RatMajorityEnvelope := ⟨64,0,inputs128,(799900441/666900000),(727058628596223211/1000000000000000000)⟩
theorem envelope_sound128 : envelope128.Sound := by
  apply rat_majority_inputs_envelopes inputs128 inputs_valid128
  · norm_num [envelope128]
  · intro rho hr0 hr1
    have hh := Batch006.bound256 rho hr0 hr1
    norm_num [Batch006.certificate256,envelope128,inputs128,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch006.bound257 rho hr0 hr1
    norm_num [Batch006.certificate257,envelope128,inputs128,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs129 : RatMajorityInputs := ⟨(705716269162260361920603/1250000000000000000000),(24622120787121/5000000000000),(1005335795196675851/1000000000000000000),(26232673044430883/200000000000000000),(24622120787121/10000000000000),(42623085503031757/500000000000000000),26⟩
theorem inputs_valid129 : inputs129.Valid := by decide +kernel
def envelope129 : RatMajorityEnvelope := ⟨64,1,inputs129,1,(33928015998581197/62500000000000000)⟩
theorem envelope_sound129 : envelope129.Sound := by
  apply rat_majority_inputs_envelopes inputs129 inputs_valid129
  · norm_num [envelope129]
  · intro rho hr0 hr1
    have hh := Batch006.bound258 rho hr0 hr1
    norm_num [Batch006.certificate258,envelope129,inputs129,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch006.bound259 rho hr0 hr1
    norm_num [Batch006.certificate259,envelope129,inputs129,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs130 : RatMajorityInputs := ⟨(55972427927708466209291231/100000000000000000000000),(13041624187279/3125000000000),(251345552768229817/250000000000000000),(106895734786719793/500000000000000000),(13041624187279/6250000000000),(124100957659435731/1000000000000000000),25⟩
theorem inputs_valid130 : inputs130.Valid := by decide +kernel
def envelope130 : RatMajorityEnvelope := ⟨65,0,inputs130,(2397842313/1999610000),(726800361416719837/1000000000000000000)⟩
theorem envelope_sound130 : envelope130.Sound := by
  apply rat_majority_inputs_envelopes inputs130 inputs_valid130
  · norm_num [envelope130]
  · intro rho hr0 hr1
    have hh := Batch006.bound260 rho hr0 hr1
    norm_num [Batch006.certificate260,envelope130,inputs130,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch006.bound261 rho hr0 hr1
    norm_num [Batch006.certificate261,envelope130,inputs130,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs131 : RatMajorityInputs := ⟨(55972427927708466209291231/100000000000000000000000),(492444705953477/100000000000000),(251345552768229817/250000000000000000),(16395168413186617/125000000000000000),(492444705953477/200000000000000),(85245194853035491/1000000000000000000),26⟩
theorem inputs_valid131 : inputs131.Valid := by decide +kernel
def envelope131 : RatMajorityEnvelope := ⟨65,1,inputs131,1,(108573851687884247/200000000000000000)⟩
theorem envelope_sound131 : envelope131.Sound := by
  apply rat_majority_inputs_envelopes inputs131 inputs_valid131
  · norm_num [envelope131]
  · intro rho hr0 hr1
    have hh := Batch006.bound262 rho hr0 hr1
    norm_num [Batch006.certificate262,envelope131,inputs131,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch006.bound263 rho hr0 hr1
    norm_num [Batch006.certificate263,envelope131,inputs131,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs132 : RatMajorityInputs := ⟨(13873808744839566226486493/25000000000000000000000),(104358693827427/25000000000000),(502714343478728713/500000000000000000),(53413408127455957/250000000000000000),(104358693827427/50000000000000),(124037185341230269/1000000000000000000),25⟩
theorem inputs_valid132 : inputs132.Valid := by decide +kernel
def envelope132 : RatMajorityEnvelope := ⟨66,0,inputs132,(149770231/124907500),(72671677135094981/100000000000000000)⟩
theorem envelope_sound132 : envelope132.Sound := by
  apply rat_majority_inputs_envelopes inputs132 inputs_valid132
  · norm_num [envelope132]
  · intro rho hr0 hr1
    have hh := Batch006.bound264 rho hr0 hr1
    norm_num [Batch006.certificate264,envelope132,inputs132,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch006.bound265 rho hr0 hr1
    norm_num [Batch006.certificate265,envelope132,inputs132,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs133 : RatMajorityInputs := ⟨(13873808744839566226486493/25000000000000000000000),(61552462396737/12500000000000),(502714343478728713/500000000000000000),(131183382393000921/1000000000000000000),(61552462396737/25000000000000),(21313963514598187/250000000000000000),26⟩
theorem inputs_valid133 : inputs133.Valid := by decide +kernel
def envelope133 : RatMajorityEnvelope := ⟨66,1,inputs133,1,(542892842400020917/1000000000000000000)⟩
theorem envelope_sound133 : envelope133.Sound := by
  apply rat_majority_inputs_envelopes inputs133 inputs_valid133
  · norm_num [envelope133]
  · intro rho hr0 hr1
    have hh := Batch006.bound266 rho hr0 hr1
    norm_num [Batch006.certificate266,envelope133,inputs133,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch006.bound267 rho hr0 hr1
    norm_num [Batch006.certificate267,envelope133,inputs133,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs134 : RatMajorityInputs := ⟨(429889380100639789478017/781250000000000000000),(6525875882547/1562500000000),(502737596542916913/500000000000000000),(53339296690852831/250000000000000000),(6525875882547/3125000000000),(24780005152555503/200000000000000000),25⟩
theorem inputs_valid134 : inputs134.Valid := by decide +kernel
def envelope134 : RatMajorityEnvelope := ⟨67,0,inputs134,(2394505591/1997440000),(18161914096003373/25000000000000000)⟩
theorem envelope_sound134 : envelope134.Sound := by
  apply rat_majority_inputs_envelopes inputs134 inputs_valid134
  · norm_num [envelope134]
  · intro rho hr0 hr1
    have hh := Batch006.bound268 rho hr0 hr1
    norm_num [Batch006.certificate268,envelope134,inputs134,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch006.bound269 rho hr0 hr1
    norm_num [Batch006.certificate269,envelope134,inputs134,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs135 : RatMajorityInputs := ⟨(429889380100639789478017/781250000000000000000),(3848851353103/781250000000),(502737596542916913/500000000000000000),(32744489166544933/250000000000000000),(3848851353103/1562500000000),(42578236073639921/500000000000000000),26⟩
theorem inputs_valid135 : inputs135.Valid := by decide +kernel
def envelope135 : RatMajorityEnvelope := ⟨67,1,inputs135,1,(67861537262191429/125000000000000000)⟩
theorem envelope_sound135 : envelope135.Sound := by
  apply rat_majority_inputs_envelopes inputs135 inputs_valid135
  · norm_num [envelope135]
  · intro rho hr0 hr1
    have hh := Batch006.bound270 rho hr0 hr1
    norm_num [Batch006.certificate270,envelope135,inputs135,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch006.bound271 rho hr0 hr1
    norm_num [Batch006.certificate271,envelope135,inputs135,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs136 : RatMajorityInputs := ⟨(54564085032590520792275401/100000000000000000000000),(208831168840821/50000000000000),(502760863234007793/500000000000000000),(213348776961151609/1000000000000000000),(208831168840821/100000000000000),(3097403365512939/25000000000000000),25⟩
theorem inputs_valid136 : inputs136.Valid := by decide +kernel
def envelope136 : RatMajorityEnvelope := ⟨68,0,inputs136,(1196536993/998185000),(145286804276568761/200000000000000000)⟩
theorem envelope_sound136 : envelope136.Sound := by
  apply rat_majority_inputs_envelopes inputs136 inputs_valid136
  · norm_num [envelope136]
  · intro rho hr0 hr1
    have hh := Batch006.bound272 rho hr0 hr1
    norm_num [Batch006.certificate272,envelope136,inputs136,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch006.bound273 rho hr0 hr1
    norm_num [Batch006.certificate273,envelope136,inputs136,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs137 : RatMajorityInputs := ⟨(54564085032590520792275401/100000000000000000000000),(492627017588059/100000000000000),(502760863234007793/500000000000000000),(65500399809673207/500000000000000000),(492627017588059/200000000000000),(17033504860991127/200000000000000000),26⟩
theorem inputs_valid137 : inputs137.Valid := by decide +kernel
def envelope137 : RatMajorityEnvelope := ⟨68,1,inputs137,1,(135728999143799809/250000000000000000)⟩
theorem envelope_sound137 : envelope137.Sound := by
  apply rat_majority_inputs_envelopes inputs137 inputs_valid137
  · norm_num [envelope137]
  · intro rho hr0 hr1
    have hh := Batch006.bound274 rho hr0 hr1
    norm_num [Batch006.certificate274,envelope137,inputs137,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch006.bound275 rho hr0 hr1
    norm_num [Batch006.certificate275,envelope137,inputs137,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs138 : RatMajorityInputs := ⟨(6763726546947693292244681/12500000000000000000000),(41799994812661/10000000000000),(502784142054231537/500000000000000000),(212897160329287011/1000000000000000000),(41799994812661/20000000000000),(30921791974453537/250000000000000000),25⟩
theorem inputs_valid138 : inputs138.Valid := by decide +kernel
def envelope138 : RatMajorityEnvelope := ⟨69,0,inputs138,(149449153/124706875),(145227175272897181/200000000000000000)⟩
theorem envelope_sound138 : envelope138.Sound := by
  apply rat_majority_inputs_envelopes inputs138 inputs_valid138
  · norm_num [envelope138]
  · intro rho hr0 hr1
    have hh := Batch006.bound276 rho hr0 hr1
    norm_num [Batch006.certificate276,envelope138,inputs138,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch006.bound277 rho hr0 hr1
    norm_num [Batch006.certificate277,envelope138,inputs138,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs139 : RatMajorityInputs := ⟨(6763726546947693292244681/12500000000000000000000),(492663255330761/100000000000000),(502784142054231537/500000000000000000),(130968908563479147/1000000000000000000),(492663255330761/200000000000000),(85152094308706787/1000000000000000000),26⟩
theorem inputs_valid139 : inputs139.Valid := by decide +kernel
def envelope139 : RatMajorityEnvelope := ⟨69,1,inputs139,1,(54293390027115631/100000000000000000)⟩
theorem envelope_sound139 : envelope139.Sound := by
  apply rat_majority_inputs_envelopes inputs139 inputs_valid139
  · norm_num [envelope139]
  · intro rho hr0 hr1
    have hh := Batch006.bound278 rho hr0 hr1
    norm_num [Batch006.certificate278,envelope139,inputs139,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch006.bound279 rho hr0 hr1
    norm_num [Batch006.certificate279,envelope139,inputs139,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def configurations : List RatMajorityEnvelope := [envelope120,envelope121,envelope122,envelope123,envelope124,envelope125,envelope126,envelope127,envelope128,envelope129,envelope130,envelope131,envelope132,envelope133,envelope134,envelope135,envelope136,envelope137,envelope138,envelope139]
theorem configurations_sound : ∀ s∈configurations, s.Sound := by
  intro s hs
  simp only [configurations,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact envelope_sound120
  · exact envelope_sound121
  · exact envelope_sound122
  · exact envelope_sound123
  · exact envelope_sound124
  · exact envelope_sound125
  · exact envelope_sound126
  · exact envelope_sound127
  · exact envelope_sound128
  · exact envelope_sound129
  · exact envelope_sound130
  · exact envelope_sound131
  · exact envelope_sound132
  · exact envelope_sound133
  · exact envelope_sound134
  · exact envelope_sound135
  · exact envelope_sound136
  · exact envelope_sound137
  · exact envelope_sound138
  · exact envelope_sound139

end Cycle12.MajorityCertificates.Inputs006
