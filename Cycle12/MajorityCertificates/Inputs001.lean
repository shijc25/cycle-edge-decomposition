import Cycle12.RationalMajorityInputs
import Cycle12.MajorityCertificates.Batch001

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Inputs001

def inputs20 : RatMajorityInputs := ⟨(69410346837136866762506241/10000000000000000000000),(419946681779113/100000000000000),(1000432357558111133/1000000000000000000),(210308516076638651/1000000000000000000),(419946681779113/200000000000000),(122489078399360957/1000000000000000000),25⟩
theorem inputs_valid20 : inputs20.Valid := by decide +kernel
def envelope20 : RatMajorityEnvelope := ⟨10,0,inputs20,(105605419/90210800),(87269456259513071/125000000000000000)⟩
theorem envelope_sound20 : envelope20.Sound := by
  apply rat_majority_inputs_envelopes inputs20 inputs_valid20
  · norm_num [envelope20]
  · intro rho hr0 hr1
    have hh := Batch001.bound40 rho hr0 hr1
    norm_num [Batch001.certificate40,envelope20,inputs20,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch001.bound41 rho hr0 hr1
    norm_num [Batch001.certificate41,envelope20,inputs20,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs21 : RatMajorityInputs := ⟨(69410346837136866762506241/10000000000000000000000),(500108164195931/100000000000000),(1000432357558111133/1000000000000000000),(15570118557768357/125000000000000000),(500108164195931/200000000000000),(82040617336775377/1000000000000000000),26⟩
theorem inputs_valid21 : inputs21.Valid := by decide +kernel
def envelope21 : RatMajorityEnvelope := ⟨10,1,inputs21,1,(539893397233443771/1000000000000000000)⟩
theorem envelope_sound21 : envelope21.Sound := by
  apply rat_majority_inputs_envelopes inputs21 inputs_valid21
  · norm_num [envelope21]
  · intro rho hr0 hr1
    have hh := Batch001.bound42 rho hr0 hr1
    norm_num [Batch001.certificate42,envelope21,inputs21,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch001.bound43 rho hr0 hr1
    norm_num [Batch001.certificate43,envelope21,inputs21,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs22 : RatMajorityInputs := ⟨(148289482309319982127670103/25000000000000000000000),(419619230850561/100000000000000),(1000505966523029923/1000000000000000000),(105371049240832781/500000000000000000),(419619230850561/200000000000000),(122689788473572801/1000000000000000000),25⟩
theorem inputs_valid22 : inputs22.Valid := by decide +kernel
def envelope22 : RatMajorityEnvelope := ⟨11,0,inputs22,(2631083451/2244130000),(87478547183972471/125000000000000000)⟩
theorem envelope_sound22 : envelope22.Sound := by
  apply rat_majority_inputs_envelopes inputs22 inputs_valid22
  · norm_num [envelope22]
  · intro rho hr0 hr1
    have hh := Batch001.bound44 rho hr0 hr1
    norm_num [Batch001.certificate44,envelope22,inputs22,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch001.bound45 rho hr0 hr1
    norm_num [Batch001.certificate45,envelope22,inputs22,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs23 : RatMajorityInputs := ⟨(148289482309319982127670103/25000000000000000000000),(62577868680789/12500000000000),(1000505966523029923/1000000000000000000),(62064162013579821/500000000000000000),(62577868680789/25000000000000),(20457430592142641/250000000000000000),26⟩
theorem inputs_valid23 : inputs23.Valid := by decide +kernel
def envelope23 : RatMajorityEnvelope := ⟨11,1,inputs23,1,(134970245846570637/250000000000000000)⟩
theorem envelope_sound23 : envelope23.Sound := by
  apply rat_majority_inputs_envelopes inputs23 inputs_valid23
  · norm_num [envelope23]
  · intro rho hr0 hr1
    have hh := Batch001.bound46 rho hr0 hr1
    norm_num [Batch001.certificate46,envelope23,inputs23,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch001.bound47 rho hr0 hr1
    norm_num [Batch001.certificate47,envelope23,inputs23,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs24 : RatMajorityInputs := ⟨(513031658733157844601345261/100000000000000000000000),(209591266968201/50000000000000),(100058502530151069/100000000000000000),(211321492454374833/1000000000000000000),(209591266968201/100000000000000),(122957972414898379/1000000000000000000),25⟩
theorem inputs_valid24 : inputs24.Valid := by decide +kernel
def envelope24 : RatMajorityEnvelope := ⟨12,0,inputs24,(874133637/744430000),(70154299302723541/100000000000000000)⟩
theorem envelope_sound24 : envelope24.Sound := by
  apply rat_majority_inputs_envelopes inputs24 inputs_valid24
  · norm_num [envelope24]
  · intro rho hr0 hr1
    have hh := Batch001.bound48 rho hr0 hr1
    norm_num [Batch001.certificate48,envelope24,inputs24,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch001.bound49 rho hr0 hr1
    norm_num [Batch001.certificate49,envelope24,inputs24,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs25 : RatMajorityInputs := ⟨(513031658733157844601345261/100000000000000000000000),(500066092540137/100000000000000),(100058502530151069/100000000000000000),(31149091128802371/250000000000000000),(500066092540137/200000000000000),(2051446926878619/25000000000000000),27⟩
theorem inputs_valid25 : inputs25.Valid := by decide +kernel
def envelope25 : RatMajorityEnvelope := ⟨12,1,inputs25,1,(539967533218585479/1000000000000000000)⟩
theorem envelope_sound25 : envelope25.Sound := by
  apply rat_majority_inputs_envelopes inputs25 inputs_valid25
  · norm_num [envelope25]
  · intro rho hr0 hr1
    have hh := Batch001.bound50 rho hr0 hr1
    norm_num [Batch001.certificate50,envelope25,inputs25,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch001.bound51 rho hr0 hr1
    norm_num [Batch001.certificate51,envelope25,inputs25,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs26 : RatMajorityInputs := ⟨(28022890460336282923038003/6250000000000000000000),(104719727012589/25000000000000),(50033472211476713/50000000000000000),(211725112991211811/1000000000000000000),(104719727012589/50000000000000),(123144780294894783/1000000000000000000),25⟩
theorem inputs_valid26 : inputs26.Valid := by decide +kernel
def envelope26 : RatMajorityEnvelope := ⟨13,0,inputs26,(65348939/55568500),(703217464914007971/1000000000000000000)⟩
theorem envelope_sound26 : envelope26.Sound := by
  apply rat_majority_inputs_envelopes inputs26 inputs_valid26
  · norm_num [envelope26]
  · intro rho hr0 hr1
    have hh := Batch001.bound52 rho hr0 hr1
    norm_num [Batch001.certificate52,envelope26,inputs26,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch001.bound53 rho hr0 hr1
    norm_num [Batch001.certificate53,envelope26,inputs26,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs27 : RatMajorityInputs := ⟨(28022890460336282923038003/6250000000000000000000),(24976143752547/5000000000000),(50033472211476713/50000000000000000),(25010890088602851/200000000000000000),(24976143752547/10000000000000),(41140528197492623/500000000000000000),26⟩
theorem inputs_valid27 : inputs27.Valid := by decide +kernel
def envelope27 : RatMajorityEnvelope := ⟨13,1,inputs27,1,(540055501411442719/1000000000000000000)⟩
theorem envelope_sound27 : envelope27.Sound := by
  apply rat_majority_inputs_envelopes inputs27 inputs_valid27
  · norm_num [envelope27]
  · intro rho hr0 hr1
    have hh := Batch001.bound54 rho hr0 hr1
    norm_num [Batch001.certificate54,envelope27,inputs27,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch001.bound55 rho hr0 hr1
    norm_num [Batch001.certificate55,envelope27,inputs27,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs28 : RatMajorityInputs := ⟨(98855267711151849335784701/25000000000000000000000),(3269206451509/781250000000),(100075913284494947/100000000000000000),(212285133241444099/1000000000000000000),(3269206451509/1562500000000),(61701976809898917/500000000000000000),25⟩
theorem inputs_valid28 : inputs28.Valid := by decide +kernel
def envelope28 : RatMajorityEnvelope := ⟨14,0,inputs28,(1302928639/1106230000),(704937359199490487/1000000000000000000)⟩
theorem envelope_sound28 : envelope28.Sound := by
  apply rat_majority_inputs_envelopes inputs28 inputs_valid28
  · norm_num [envelope28]
  · intro rho hr0 hr1
    have hh := Batch001.bound56 rho hr0 hr1
    norm_num [Batch001.certificate56,envelope28,inputs28,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch001.bound57 rho hr0 hr1
    norm_num [Batch001.certificate57,envelope28,inputs28,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs29 : RatMajorityInputs := ⟨(98855267711151849335784701/25000000000000000000000),(249496352275559/50000000000000),(100075913284494947/100000000000000000),(62751487575939947/500000000000000000),(249496352275559/100000000000000),(10312432586231311/125000000000000000),26⟩
theorem inputs_valid29 : inputs29.Valid := by decide +kernel
def envelope29 : RatMajorityEnvelope := ⟨14,1,inputs29,1,(135036220564240059/250000000000000000)⟩
theorem envelope_sound29 : envelope29.Sound := by
  apply rat_majority_inputs_envelopes inputs29 inputs_valid29
  · norm_num [envelope29]
  · intro rho hr0 hr1
    have hh := Batch001.bound58 rho hr0 hr1
    norm_num [Batch001.certificate58,envelope29,inputs29,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch001.bound59 rho hr0 hr1
    norm_num [Batch001.certificate59,envelope29,inputs29,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs30 : RatMajorityInputs := ⟨(8788129717590807976756191/2500000000000000000000),(41729742667809/10000000000000),(1000853990733387327/1000000000000000000),(213837807538064457/1000000000000000000),(41729742667809/20000000000000),(24824479257055921/200000000000000000),25⟩
theorem inputs_valid30 : inputs30.Valid := by decide +kernel
def envelope30 : RatMajorityEnvelope := ⟨15,0,inputs30,(866139389/734150000),(706919710432712773/1000000000000000000)⟩
theorem envelope_sound30 : envelope30.Sound := by
  apply rat_majority_inputs_envelopes inputs30 inputs_valid30
  · norm_num [envelope30]
  · intro rho hr0 hr1
    have hh := Batch001.bound60 rho hr0 hr1
    norm_num [Batch001.certificate60,envelope30,inputs30,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch001.bound61 rho hr0 hr1
    norm_num [Batch001.certificate61,envelope30,inputs30,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs31 : RatMajorityInputs := ⟨(8788129717590807976756191/2500000000000000000000),(12461898052953/2500000000000),(1000853990733387327/1000000000000000000),(125941547026419479/1000000000000000000),(12461898052953/5000000000000),(82712907695330747/1000000000000000000),27⟩
theorem inputs_valid31 : inputs31.Valid := by decide +kernel
def envelope31 : RatMajorityEnvelope := ⟨15,1,inputs31,1,(135058895415743427/250000000000000000)⟩
theorem envelope_sound31 : envelope31.Sound := by
  apply rat_majority_inputs_envelopes inputs31 inputs_valid31
  · norm_num [envelope31]
  · intro rho hr0 hr1
    have hh := Batch001.bound62 rho hr0 hr1
    norm_num [Batch001.certificate62,envelope31,inputs31,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch001.bound63 rho hr0 hr1
    norm_num [Batch001.certificate63,envelope31,inputs31,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs32 : RatMajorityInputs := ⟨(3934078680993608733233589/1250000000000000000000),(41772486751863/10000000000000),(1000953916378391959/1000000000000000000),(53316267928555369/250000000000000000),(41772486751863/20000000000000),(61928702324886809/500000000000000000),25⟩
theorem inputs_valid32 : inputs32.Valid := by decide +kernel
def envelope32 : RatMajorityEnvelope := ⟨16,0,inputs32,(1295224883/1096350000),(70835647780368939/100000000000000000)⟩
theorem envelope_sound32 : envelope32.Sound := by
  apply rat_majority_inputs_envelopes inputs32 inputs_valid32
  · norm_num [envelope32]
  · intro rho hr0 hr1
    have hh := Batch001.bound64 rho hr0 hr1
    norm_num [Batch001.certificate64,envelope32,inputs32,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch001.bound65 rho hr0 hr1
    norm_num [Batch001.certificate65,envelope32,inputs32,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs33 : RatMajorityInputs := ⟨(3934078680993608733233589/1250000000000000000000),(49797222857271/10000000000000),(1000953916378391959/1000000000000000000),(126370318881676237/1000000000000000000),(49797222857271/20000000000000),(10365185001882203/125000000000000000),27⟩
theorem inputs_valid33 : inputs33.Valid := by decide +kernel
def envelope33 : RatMajorityEnvelope := ⟨16,1,inputs33,1,(135081890931862863/250000000000000000)⟩
theorem envelope_sound33 : envelope33.Sound := by
  apply rat_majority_inputs_envelopes inputs33 inputs_valid33
  · norm_num [envelope33]
  · intro rho hr0 hr1
    have hh := Batch001.bound66 rho hr0 hr1
    norm_num [Batch001.certificate66,envelope33,inputs33,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch001.bound67 rho hr0 hr1
    norm_num [Batch001.certificate67,envelope33,inputs33,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs34 : RatMajorityInputs := ⟨(1772322888674759392069141/625000000000000000000),(5216377906803/1250000000000),(250264701200693601/250000000000000000),(3340947346667793/15625000000000000),(5216377906803/2500000000000),(62057224532872331/500000000000000000),25⟩
theorem inputs_valid34 : inputs34.Valid := by decide +kernel
def envelope34 : RatMajorityEnvelope := ⟨17,0,inputs34,(2583171993/2183200000),(355045165899116331/500000000000000000)⟩
theorem envelope_sound34 : envelope34.Sound := by
  apply rat_majority_inputs_envelopes inputs34 inputs_valid34
  · norm_num [envelope34]
  · intro rho hr0 hr1
    have hh := Batch001.bound68 rho hr0 hr1
    norm_num [Batch001.certificate68,envelope34,inputs34,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch001.bound69 rho hr0 hr1
    norm_num [Batch001.certificate69,envelope34,inputs34,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs35 : RatMajorityInputs := ⟨(1772322888674759392069141/625000000000000000000),(3111565664597/625000000000),(250264701200693601/250000000000000000),(126474129655153707/1000000000000000000),(3111565664597/1250000000000),(82971962315838539/1000000000000000000),28⟩
theorem inputs_valid35 : inputs35.Valid := by decide +kernel
def envelope35 : RatMajorityEnvelope := ⟨17,1,inputs35,1,(540386929123939477/1000000000000000000)⟩
theorem envelope_sound35 : envelope35.Sound := by
  apply rat_majority_inputs_envelopes inputs35 inputs_valid35
  · norm_num [envelope35]
  · intro rho hr0 hr1
    have hh := Batch001.bound70 rho hr0 hr1
    norm_num [Batch001.certificate70,envelope35,inputs35,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch001.bound71 rho hr0 hr1
    norm_num [Batch001.certificate71,envelope35,inputs35,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs36 : RatMajorityInputs := ⟨(256961033902881805319547241/100000000000000000000000),(417012177234829/100000000000000),(100116855321462273/100000000000000000),(13388795525741923/62500000000000000),(417012177234829/200000000000000),(124299551811219919/1000000000000000000),25⟩
theorem inputs_valid36 : inputs36.Valid := by decide +kernel
def envelope36 : RatMajorityEnvelope := ⟨18,0,inputs36,(644020801/543482500),(355895548683991427/500000000000000000)⟩
theorem envelope_sound36 : envelope36.Sound := by
  apply rat_majority_inputs_envelopes inputs36 inputs_valid36
  · norm_num [envelope36]
  · intro rho hr0 hr1
    have hh := Batch001.bound72 rho hr0 hr1
    norm_num [Batch001.certificate72,envelope36,inputs36,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch001.bound73 rho hr0 hr1
    norm_num [Batch001.certificate73,envelope36,inputs36,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs37 : RatMajorityInputs := ⟨(256961033902881805319547241/100000000000000000000000),(248695580897357/50000000000000),(100116855321462273/100000000000000000),(63433281524305277/500000000000000000),(248695580897357/100000000000000),(41581372454490019/500000000000000000),26⟩
theorem inputs_valid37 : inputs37.Valid := by decide +kernel
def envelope37 : RatMajorityEnvelope := ⟨18,1,inputs37,1,(270239752158407211/500000000000000000)⟩
theorem envelope_sound37 : envelope37.Sound := by
  apply rat_majority_inputs_envelopes inputs37 inputs_valid37
  · norm_num [envelope37]
  · intro rho hr0 hr1
    have hh := Batch001.bound74 rho hr0 hr1
    norm_num [Batch001.certificate74,envelope37,inputs37,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch001.bound75 rho hr0 hr1
    norm_num [Batch001.certificate75,envelope37,inputs37,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs38 : RatMajorityInputs := ⟨(1168561909540120136013207/500000000000000000000),(666584752379/160000000000),(500642455880708803/500000000000000000),(214754216469374157/1000000000000000000),(666584752379/320000000000),(31136587251492247/250000000000000000),25⟩
theorem inputs_valid38 : inputs38.Valid := by decide +kernel
def envelope38 : RatMajorityEnvelope := ⟨19,0,inputs38,(512869787/432350000),(17825734327130617/25000000000000000)⟩
theorem envelope_sound38 : envelope38.Sound := by
  apply rat_majority_inputs_envelopes inputs38 inputs_valid38
  · norm_num [envelope38]
  · intro rho hr0 hr1
    have hh := Batch001.bound76 rho hr0 hr1
    norm_num [Batch001.certificate76,envelope38,inputs38,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch001.bound77 rho hr0 hr1
    norm_num [Batch001.certificate77,envelope38,inputs38,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs39 : RatMajorityInputs := ⟨(1168561909540120136013207/500000000000000000000),(621106305523/125000000000),(500642455880708803/500000000000000000),(127300205841610377/1000000000000000000),(621106305523/250000000000),(83373461966742729/1000000000000000000),27⟩
theorem inputs_valid39 : inputs39.Valid := by decide +kernel
def envelope39 : RatMajorityEnvelope := ⟨19,1,inputs39,1,(540579536149986187/1000000000000000000)⟩
theorem envelope_sound39 : envelope39.Sound := by
  apply rat_majority_inputs_envelopes inputs39 inputs_valid39
  · norm_num [envelope39]
  · intro rho hr0 hr1
    have hh := Batch001.bound78 rho hr0 hr1
    norm_num [Batch001.certificate78,envelope39,inputs39,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch001.bound79 rho hr0 hr1
    norm_num [Batch001.certificate79,envelope39,inputs39,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def configurations : List RatMajorityEnvelope := [envelope20,envelope21,envelope22,envelope23,envelope24,envelope25,envelope26,envelope27,envelope28,envelope29,envelope30,envelope31,envelope32,envelope33,envelope34,envelope35,envelope36,envelope37,envelope38,envelope39]
theorem configurations_sound : ∀ s∈configurations, s.Sound := by
  intro s hs
  simp only [configurations,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact envelope_sound20
  · exact envelope_sound21
  · exact envelope_sound22
  · exact envelope_sound23
  · exact envelope_sound24
  · exact envelope_sound25
  · exact envelope_sound26
  · exact envelope_sound27
  · exact envelope_sound28
  · exact envelope_sound29
  · exact envelope_sound30
  · exact envelope_sound31
  · exact envelope_sound32
  · exact envelope_sound33
  · exact envelope_sound34
  · exact envelope_sound35
  · exact envelope_sound36
  · exact envelope_sound37
  · exact envelope_sound38
  · exact envelope_sound39

end Cycle12.MajorityCertificates.Inputs001
