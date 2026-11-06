import Cycle12.RationalMajorityInputs
import Cycle12.MajorityCertificates.Batch027

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Inputs027

def inputs540 : RatMajorityInputs := ⟨(324699391156291301692622157/50000000000000000000000),(27080793748743/6250000000000),(500231065899539629/500000000000000000),(38652104723968483/200000000000000000),(27080793748743/12500000000000),(114582120907146603/1000000000000000000),25⟩
theorem inputs_valid540 : inputs540.Valid := by decide +kernel
def envelope540 : RatMajorityEnvelope := ⟨270,0,inputs540,(1346942437/1133430000),(356165411479192317/500000000000000000)⟩
theorem envelope_sound540 : envelope540.Sound := by
  apply rat_majority_inputs_envelopes inputs540 inputs_valid540
  · norm_num [envelope540]
  · intro rho hr0 hr1
    have hh := Batch027.bound1080 rho hr0 hr1
    norm_num [Batch027.certificate1080,envelope540,inputs540,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch027.bound1081 rho hr0 hr1
    norm_num [Batch027.certificate1081,envelope540,inputs540,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs541 : RatMajorityInputs := ⟨(324699391156291301692622157/50000000000000000000000),(233695720390257/50000000000000),(500231065899539629/500000000000000000),(154940609775269569/1000000000000000000),(233695720390257/100000000000000),(96621189974736291/1000000000000000000),26⟩
theorem inputs_valid541 : inputs541.Valid := by decide +kernel
def envelope541 : RatMajorityEnvelope := ⟨270,1,inputs541,1,(543289364098608161/1000000000000000000)⟩
theorem envelope_sound541 : envelope541.Sound := by
  apply rat_majority_inputs_envelopes inputs541 inputs_valid541
  · norm_num [envelope541]
  · intro rho hr0 hr1
    have hh := Batch027.bound1082 rho hr0 hr1
    norm_num [Batch027.certificate1082,envelope541,inputs541,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch027.bound1083 rho hr0 hr1
    norm_num [Batch027.certificate1083,envelope541,inputs541,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs542 : RatMajorityInputs := ⟨(61275730748343319230247381/10000000000000000000000),(4337792549077/1000000000000),(31265305523187043/31250000000000000),(192661657948553167/1000000000000000000),(4337792549077/2000000000000),(14287963403187421/125000000000000000),25⟩
theorem inputs_valid542 : inputs542.Valid := by decide +kernel
def envelope542 : RatMajorityEnvelope := ⟨271,0,inputs542,(673002823/565825000),(356613024201688691/500000000000000000)⟩
theorem envelope_sound542 : envelope542.Sound := by
  apply rat_majority_inputs_envelopes inputs542 inputs_valid542
  · norm_num [envelope542]
  · intro rho hr0 hr1
    have hh := Batch027.bound1084 rho hr0 hr1
    norm_num [Batch027.certificate1084,envelope542,inputs542,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch027.bound1085 rho hr0 hr1
    norm_num [Batch027.certificate1085,envelope542,inputs542,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs543 : RatMajorityInputs := ⟨(61275730748343319230247381/10000000000000000000000),(46818643196481/10000000000000),(31265305523187043/31250000000000000),(7706589576263253/50000000000000000),(46818643196481/20000000000000),(24059471828446793/250000000000000000),27⟩
theorem inputs_valid543 : inputs543.Valid := by decide +kernel
def envelope543 : RatMajorityEnvelope := ⟨271,1,inputs543,1,(67901027898955943/125000000000000000)⟩
theorem envelope_sound543 : envelope543.Sound := by
  apply rat_majority_inputs_envelopes inputs543 inputs_valid543
  · norm_num [envelope543]
  · intro rho hr0 hr1
    have hh := Batch027.bound1086 rho hr0 hr1
    norm_num [Batch027.certificate1086,envelope543,inputs543,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch027.bound1087 rho hr0 hr1
    norm_num [Batch027.certificate1087,envelope543,inputs543,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs544 : RatMajorityInputs := ⟨(289726216539259030026225213/50000000000000000000000),(108700648229651/25000000000000),(500258969357328593/500000000000000000),(191407219232125113/1000000000000000000),(108700648229651/50000000000000),(14215043037488961/125000000000000000),25⟩
theorem inputs_valid544 : inputs544.Valid := by decide +kernel
def envelope544 : RatMajorityEnvelope := ⟨272,0,inputs544,(1344075391/1129910000),(89153922177171361/125000000000000000)⟩
theorem envelope_sound544 : envelope544.Sound := by
  apply rat_majority_inputs_envelopes inputs544 inputs_valid544
  · norm_num [envelope544]
  · intro rho hr0 hr1
    have hh := Batch027.bound1088 rho hr0 hr1
    norm_num [Batch027.certificate1088,envelope544,inputs544,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch027.bound1089 rho hr0 hr1
    norm_num [Batch027.certificate1089,envelope544,inputs544,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs545 : RatMajorityInputs := ⟨(289726216539259030026225213/50000000000000000000000),(7318360292319/1562500000000),(500258969357328593/500000000000000000),(30788084781383861/200000000000000000),(7318360292319/3125000000000),(1502299451651803/15625000000000000),27⟩
theorem inputs_valid545 : inputs545.Valid := by decide +kernel
def envelope545 : RatMajorityEnvelope := ⟨272,1,inputs545,1,(135799665890183447/250000000000000000)⟩
theorem envelope_sound545 : envelope545.Sound := by
  apply rat_majority_inputs_envelopes inputs545 inputs_valid545
  · norm_num [envelope545]
  · intro rho hr0 hr1
    have hh := Batch027.bound1090 rho hr0 hr1
    norm_num [Batch027.certificate1090,envelope545,inputs545,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch027.bound1091 rho hr0 hr1
    norm_num [Batch027.certificate1091,envelope545,inputs545,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs546 : RatMajorityInputs := ⟨(274545512444391023148977757/50000000000000000000000),(43530413171427/10000000000000),(1000546589763049639/1000000000000000000),(1490585497320541/7812500000000000),(43530413171427/20000000000000),(11343552574544163/100000000000000000),25⟩
theorem inputs_valid546 : inputs546.Valid := by decide +kernel
def envelope546 : RatMajorityEnvelope := ⟨273,0,inputs546,(268643897/225642000),(714120238045222989/1000000000000000000)⟩
theorem envelope_sound546 : envelope546.Sound := by
  apply rat_majority_inputs_envelopes inputs546 inputs_valid546
  · norm_num [envelope546]
  · intro rho hr0 hr1
    have hh := Batch027.bound1092 rho hr0 hr1
    norm_num [Batch027.certificate1092,envelope546,inputs546,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch027.bound1093 rho hr0 hr1
    norm_num [Batch027.certificate1093,envelope546,inputs546,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs547 : RatMajorityInputs := ⟨(274545512444391023148977757/50000000000000000000000),(234586794225081/50000000000000),(1000546589763049639/1000000000000000000),(153132579008469983/1000000000000000000),(234586794225081/100000000000000),(23941012096423009/250000000000000000),26⟩
theorem inputs_valid547 : inputs547.Valid := by decide +kernel
def envelope547 : RatMajorityEnvelope := ⟨273,1,inputs547,1,(271559178935745003/500000000000000000)⟩
theorem envelope_sound547 : envelope547.Sound := by
  apply rat_majority_inputs_envelopes inputs547 inputs_valid547
  · norm_num [envelope547]
  · intro rho hr0 hr1
    have hh := Batch027.bound1094 rho hr0 hr1
    norm_num [Batch027.certificate1094,envelope547,inputs547,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch027.bound1095 rho hr0 hr1
    norm_num [Batch027.certificate1095,envelope547,inputs547,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs548 : RatMajorityInputs := ⟨(26066826770526143517741243/5000000000000000000000),(8725144597929/2000000000000),(500287850845951069/500000000000000000),(189635972975471061/1000000000000000000),(8725144597929/4000000000000),(112896235789821013/1000000000000000000),26⟩
theorem inputs_valid548 : inputs548.Valid := by decide +kernel
def envelope548 : RatMajorityEnvelope := ⟨274,0,inputs548,(335347169/281637500),(714141746397430143/1000000000000000000)⟩
theorem envelope_sound548 : envelope548.Sound := by
  apply rat_majority_inputs_envelopes inputs548 inputs_valid548
  · norm_num [envelope548]
  · intro rho hr0 hr1
    have hh := Batch027.bound1096 rho hr0 hr1
    norm_num [Batch027.certificate1096,envelope548,inputs548,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch027.bound1097 rho hr0 hr1
    norm_num [Batch027.certificate1097,envelope548,inputs548,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs549 : RatMajorityInputs := ⟨(26066826770526143517741243/5000000000000000000000),(23468263216199/5000000000000),(500287850845951069/500000000000000000),(4779350536539371/31250000000000000),(23468263216199/10000000000000),(19134462812516287/200000000000000000),26⟩
theorem inputs_valid549 : inputs549.Valid := by decide +kernel
def envelope549 : RatMajorityEnvelope := ⟨274,1,inputs549,1,(271554534474063121/500000000000000000)⟩
theorem envelope_sound549 : envelope549.Sound := by
  apply rat_majority_inputs_envelopes inputs549 inputs_valid549
  · norm_num [envelope549]
  · intro rho hr0 hr1
    have hh := Batch027.bound1098 rho hr0 hr1
    norm_num [Batch027.certificate1098,envelope549,inputs549,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch027.bound1099 rho hr0 hr1
    norm_num [Batch027.certificate1099,envelope549,inputs549,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs550 : RatMajorityInputs := ⟨(19835891375866974309074349/4000000000000000000000),(87459804372639/20000000000000),(1000605248765683253/1000000000000000000),(188375975015340831/1000000000000000000),(87459804372639/40000000000000),(28077423199472691/250000000000000000),26⟩
theorem inputs_valid550 : inputs550.Valid := by decide +kernel
def envelope550 : RatMajorityEnvelope := ⟨275,0,inputs550,(2679152971/2249850000),(714136237924556893/1000000000000000000)⟩
theorem envelope_sound550 : envelope550.Sound := by
  apply rat_majority_inputs_envelopes inputs550 inputs_valid550
  · norm_num [envelope550]
  · intro rho hr0 hr1
    have hh := Batch027.bound1100 rho hr0 hr1
    norm_num [Batch027.certificate1100,envelope550,inputs550,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch027.bound1101 rho hr0 hr1
    norm_num [Batch027.certificate1101,envelope550,inputs550,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs551 : RatMajorityInputs := ⟨(19835891375866974309074349/4000000000000000000000),(18814200941313/4000000000000),(1000605248765683253/1000000000000000000),(151944131397098933/1000000000000000000),(18814200941313/8000000000000),(95200020898372213/1000000000000000000),26⟩
theorem inputs_valid551 : inputs551.Valid := by decide +kernel
def envelope551 : RatMajorityEnvelope := ⟨275,1,inputs551,1,(27150398110855889/50000000000000000)⟩
theorem envelope_sound551 : envelope551.Sound := by
  apply rat_majority_inputs_envelopes inputs551 inputs_valid551
  · norm_num [envelope551]
  · intro rho hr0 hr1
    have hh := Batch027.bound1102 rho hr0 hr1
    norm_num [Batch027.certificate1102,envelope551,inputs551,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch027.bound1103 rho hr0 hr1
    norm_num [Batch027.certificate1103,envelope551,inputs551,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs552 : RatMajorityInputs := ⟨(472527678946547037490574871/100000000000000000000000),(438266512309417/100000000000000),(1000635197090143403/1000000000000000000),(23401525366137269/125000000000000000),(438266512309417/200000000000000),(111767711983943967/1000000000000000000),25⟩
theorem inputs_valid552 : inputs552.Valid := by decide +kernel
def envelope552 : RatMajorityEnvelope := ⟨276,0,inputs552,(668913687/561672500),(714148615317772683/1000000000000000000)⟩
theorem envelope_sound552 : envelope552.Sound := by
  apply rat_majority_inputs_envelopes inputs552 inputs_valid552
  · norm_num [envelope552]
  · intro rho hr0 hr1
    have hh := Batch027.bound1104 rho hr0 hr1
    norm_num [Batch027.certificate1104,envelope552,inputs552,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch027.bound1105 rho hr0 hr1
    norm_num [Batch027.certificate1105,envelope552,inputs552,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs553 : RatMajorityInputs := ⟨(472527678946547037490574871/100000000000000000000000),(471339998953701/100000000000000),(1000635197090143403/1000000000000000000),(75479729664014737/500000000000000000),(471339998953701/200000000000000),(94732325112553923/1000000000000000000),26⟩
theorem inputs_valid553 : inputs553.Valid := by decide +kernel
def envelope553 : RatMajorityEnvelope := ⟨276,1,inputs553,1,(67863568005820287/125000000000000000)⟩
theorem envelope_sound553 : envelope553.Sound := by
  apply rat_majority_inputs_envelopes inputs553 inputs_valid553
  · norm_num [envelope553]
  · intro rho hr0 hr1
    have hh := Batch027.bound1106 rho hr0 hr1
    norm_num [Batch027.certificate1106,envelope553,inputs553,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch027.bound1107 rho hr0 hr1
    norm_num [Batch027.certificate1107,envelope553,inputs553,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs554 : RatMajorityInputs := ⟨(451004391600610438388429181/100000000000000000000000),(439227785037199/100000000000000),(12508319078719077/12500000000000000),(186061956470394847/1000000000000000000),(439227785037199/200000000000000),(111231804631538171/1000000000000000000),26⟩
theorem inputs_valid554 : inputs554.Valid := by decide +kernel
def envelope554 : RatMajorityEnvelope := ⟨277,0,inputs554,(2672223999/2243590000),(142832342628043919/200000000000000000)⟩
theorem envelope_sound554 : envelope554.Sound := by
  apply rat_majority_inputs_envelopes inputs554 inputs_valid554
  · norm_num [envelope554]
  · intro rho hr0 hr1
    have hh := Batch027.bound1108 rho hr0 hr1
    norm_num [Batch027.certificate1108,envelope554,inputs554,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch027.bound1109 rho hr0 hr1
    norm_num [Batch027.certificate1109,envelope554,inputs554,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs555 : RatMajorityInputs := ⟨(451004391600610438388429181/100000000000000000000000),(58944176896733/12500000000000),(12508319078719077/12500000000000000),(37686710870677039/250000000000000000),(58944176896733/25000000000000),(94631291953664143/1000000000000000000),26⟩
theorem inputs_valid555 : inputs555.Valid := by decide +kernel
def envelope555 : RatMajorityEnvelope := ⟨277,1,inputs555,1,(542897763879778503/1000000000000000000)⟩
theorem envelope_sound555 : envelope555.Sound := by
  apply rat_majority_inputs_envelopes inputs555 inputs_valid555
  · norm_num [envelope555]
  · intro rho hr0 hr1
    have hh := Batch027.bound1110 rho hr0 hr1
    norm_num [Batch027.certificate1110,envelope555,inputs555,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch027.bound1111 rho hr0 hr1
    norm_num [Batch027.certificate1111,envelope555,inputs555,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs556 : RatMajorityInputs := ⟨(431142769841046264989997839/100000000000000000000000),(220157692785999/50000000000000),(62543512622288661/62500000000000000),(184767789135185571/1000000000000000000),(220157692785999/100000000000000),(11062856746973837/100000000000000000),26⟩
theorem inputs_valid556 : inputs556.Valid := by decide +kernel
def envelope556 : RatMajorityEnvelope := ⟨278,0,inputs556,(1334412831/1120285000),(357068456338098407/500000000000000000)⟩
theorem envelope_sound556 : envelope556.Sound := by
  apply rat_majority_inputs_envelopes inputs556 inputs_valid556
  · norm_num [envelope556]
  · intro rho hr0 hr1
    have hh := Batch027.bound1112 rho hr0 hr1
    norm_num [Batch027.certificate1112,envelope556,inputs556,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch027.bound1113 rho hr0 hr1
    norm_num [Batch027.certificate1113,envelope556,inputs556,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs557 : RatMajorityInputs := ⟨(431142769841046264989997839/100000000000000000000000),(472523212988803/100000000000000),(62543512622288661/62500000000000000),(1497839687978449/10000000000000000),(472523212988803/200000000000000),(11771692071899079/125000000000000000),26⟩
theorem inputs_valid557 : inputs557.Valid := by decide +kernel
def envelope557 : RatMajorityEnvelope := ⟨278,1,inputs557,1,(135700386939407563/250000000000000000)⟩
theorem envelope_sound557 : envelope557.Sound := by
  apply rat_majority_inputs_envelopes inputs557 inputs_valid557
  · norm_num [envelope557]
  · intro rho hr0 hr1
    have hh := Batch027.bound1114 rho hr0 hr1
    norm_num [Batch027.certificate1114,envelope557,inputs557,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch027.bound1115 rho hr0 hr1
    norm_num [Batch027.certificate1115,envelope557,inputs557,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs558 : RatMajorityInputs := ⟨(412777509705593085565235163/100000000000000000000000),(440239252109223/100000000000000),(500363597414956843/500000000000000000),(184858132885527197/1000000000000000000),(440239252109223/200000000000000),(110670688165832401/1000000000000000000),26⟩
theorem inputs_valid558 : inputs558.Valid := by decide +kernel
def envelope558 : RatMajorityEnvelope := ⟨279,0,inputs558,(2665998839/2237630000),(714435441265451647/1000000000000000000)⟩
theorem envelope_sound558 : envelope558.Sound := by
  apply rat_majority_inputs_envelopes inputs558 inputs_valid558
  · norm_num [envelope558]
  · intro rho hr0 hr1
    have hh := Batch027.bound1116 rho hr0 hr1
    norm_num [Batch027.certificate1116,envelope558,inputs558,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch027.bound1117 rho hr0 hr1
    norm_num [Batch027.certificate1117,envelope558,inputs558,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs559 : RatMajorityInputs := ⟨(412777509705593085565235163/100000000000000000000000),(118376381960597/25000000000000),(500363597414956843/500000000000000000),(37203535320485789/250000000000000000),(118376381960597/50000000000000),(5857008143711829/62500000000000000),26⟩
theorem inputs_valid559 : inputs559.Valid := by decide +kernel
def envelope559 : RatMajorityEnvelope := ⟨279,1,inputs559,1,(271352490828728283/500000000000000000)⟩
theorem envelope_sound559 : envelope559.Sound := by
  apply rat_majority_inputs_envelopes inputs559 inputs_valid559
  · norm_num [envelope559]
  · intro rho hr0 hr1
    have hh := Batch027.bound1118 rho hr0 hr1
    norm_num [Batch027.certificate1118,envelope559,inputs559,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch027.bound1119 rho hr0 hr1
    norm_num [Batch027.certificate1119,envelope559,inputs559,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def configurations : List RatMajorityEnvelope := [envelope540,envelope541,envelope542,envelope543,envelope544,envelope545,envelope546,envelope547,envelope548,envelope549,envelope550,envelope551,envelope552,envelope553,envelope554,envelope555,envelope556,envelope557,envelope558,envelope559]
theorem configurations_sound : ∀ s∈configurations, s.Sound := by
  intro s hs
  simp only [configurations,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact envelope_sound540
  · exact envelope_sound541
  · exact envelope_sound542
  · exact envelope_sound543
  · exact envelope_sound544
  · exact envelope_sound545
  · exact envelope_sound546
  · exact envelope_sound547
  · exact envelope_sound548
  · exact envelope_sound549
  · exact envelope_sound550
  · exact envelope_sound551
  · exact envelope_sound552
  · exact envelope_sound553
  · exact envelope_sound554
  · exact envelope_sound555
  · exact envelope_sound556
  · exact envelope_sound557
  · exact envelope_sound558
  · exact envelope_sound559

end Cycle12.MajorityCertificates.Inputs027
