import Cycle12.RationalMajorityInputs
import Cycle12.MajorityCertificates.Batch015

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Inputs015

def inputs300 : RatMajorityInputs := ⟨(13550996628371923407309/39062500000000000000),(5566162735659/1250000000000),(504353208116021683/500000000000000000),(35788409929210627/200000000000000000),(5566162735659/2500000000000),(107909205606505807/1000000000000000000),26⟩
theorem inputs_valid300 : inputs300.Valid := by decide +kernel
def envelope300 : RatMajorityEnvelope := ⟨150,0,inputs300,(1131026219/971400000),(693875006136212573/1000000000000000000)⟩
theorem envelope_sound300 : envelope300.Sound := by
  apply rat_majority_inputs_envelopes inputs300 inputs_valid300
  · norm_num [envelope300]
  · intro rho hr0 hr1
    have hh := Batch015.bound600 rho hr0 hr1
    norm_num [Batch015.certificate600,envelope300,inputs300,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch015.bound601 rho hr0 hr1
    norm_num [Batch015.certificate601,envelope300,inputs300,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs301 : RatMajorityInputs := ⟨(13550996628371923407309/39062500000000000000),(12659204324367/2500000000000),(504353208116021683/500000000000000000),(119389923397859551/1000000000000000000),(12659204324367/5000000000000),(79512513684405723/1000000000000000000),27⟩
theorem inputs_valid301 : inputs301.Valid := by decide +kernel
def envelope301 : RatMajorityEnvelope := ⟨150,1,inputs301,1,(21727152529529763/40000000000000000)⟩
theorem envelope_sound301 : envelope301.Sound := by
  apply rat_majority_inputs_envelopes inputs301 inputs_valid301
  · norm_num [envelope301]
  · intro rho hr0 hr1
    have hh := Batch015.bound602 rho hr0 hr1
    norm_num [Batch015.certificate602,envelope301,inputs301,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch015.bound603 rho hr0 hr1
    norm_num [Batch015.certificate603,envelope301,inputs301,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs302 : RatMajorityInputs := ⟨(34609565485030170552023211/100000000000000000000000),(44510282989613/10000000000000),(504363463625543843/500000000000000000),(44790432542544553/250000000000000000),(44510282989613/20000000000000),(108011870109009527/1000000000000000000),25⟩
theorem inputs_valid302 : inputs302.Valid := by decide +kernel
def envelope302 : RatMajorityEnvelope := ⟨151,0,inputs302,(565316349/485642500),(693665104602796187/1000000000000000000)⟩
theorem envelope_sound302 : envelope302.Sound := by
  apply rat_majority_inputs_envelopes inputs302 inputs_valid302
  · norm_num [envelope302]
  · intro rho hr0 hr1
    have hh := Batch015.bound604 rho hr0 hr1
    norm_num [Batch015.certificate604,envelope302,inputs302,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch015.bound605 rho hr0 hr1
    norm_num [Batch015.certificate605,envelope302,inputs302,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs303 : RatMajorityInputs := ⟨(34609565485030170552023211/100000000000000000000000),(506550234634479/100000000000000),(504363463625543843/500000000000000000),(119242436622629549/1000000000000000000),(506550234634479/200000000000000),(3972008285889903/50000000000000000),27⟩
theorem inputs_valid303 : inputs303.Valid := by decide +kernel
def envelope303 : RatMajorityEnvelope := ⟨151,1,inputs303,1,(54317339580174863/100000000000000000)⟩
theorem envelope_sound303 : envelope303.Sound := by
  apply rat_majority_inputs_envelopes inputs303 inputs_valid303
  · norm_num [envelope303]
  · intro rho hr0 hr1
    have hh := Batch015.bound606 rho hr0 hr1
    norm_num [Batch015.certificate606,envelope303,inputs303,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch015.bound607 rho hr0 hr1
    norm_num [Batch015.certificate607,envelope303,inputs303,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs304 : RatMajorityInputs := ⟨(6905783931225688235258961/20000000000000000000000),(55781309693499/12500000000000),(1008747448405069081/1000000000000000000),(2222995171226833/12500000000000000),(55781309693499/25000000000000),(419507215393879/3906250000000000),25⟩
theorem inputs_valid304 : inputs304.Valid := by decide +kernel
def envelope304 : RatMajorityEnvelope := ⟨152,0,inputs304,(564984709/485582500),(138613867834410973/200000000000000000)⟩
theorem envelope_sound304 : envelope304.Sound := by
  apply rat_majority_inputs_envelopes inputs304 inputs_valid304
  · norm_num [envelope304]
  · intro rho hr0 hr1
    have hh := Batch015.bound608 rho hr0 hr1
    norm_num [Batch015.certificate608,envelope304,inputs304,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch015.bound609 rho hr0 hr1
    norm_num [Batch015.certificate609,envelope304,inputs304,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs305 : RatMajorityInputs := ⟨(6905783931225688235258961/20000000000000000000000),(506731913514827/100000000000000),(1008747448405069081/1000000000000000000),(119095421831920221/1000000000000000000),(506731913514827/200000000000000),(15873607096459563/200000000000000000),26⟩
theorem inputs_valid305 : inputs305.Valid := by decide +kernel
def envelope305 : RatMajorityEnvelope := ⟨152,1,inputs305,1,(108633607960502669/200000000000000000)⟩
theorem envelope_sound305 : envelope305.Sound := by
  apply rat_majority_inputs_envelopes inputs305 inputs_valid305
  · norm_num [envelope305]
  · intro rho hr0 hr1
    have hh := Batch015.bound610 rho hr0 hr1
    norm_num [Batch015.certificate610,envelope305,inputs305,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch015.bound611 rho hr0 hr1
    norm_num [Batch015.certificate611,envelope305,inputs305,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs306 : RatMajorityInputs := ⟨(8612285912124423716830599/25000000000000000000000),(111630321037359/25000000000000),(100876784339938333/100000000000000000),(177528856692024241/1000000000000000000),(111630321037359/50000000000000),(26812132682710449/250000000000000000),26⟩
theorem inputs_valid306 : inputs306.Valid := by decide +kernel
def envelope306 : RatMajorityEnvelope := ⟨153,0,inputs306,(1129491679/971055000),(10823863103524857/15625000000000000)⟩
theorem envelope_sound306 : envelope306.Sound := by
  apply rat_majority_inputs_envelopes inputs306 inputs_valid306
  · norm_num [envelope306]
  · intro rho hr0 hr1
    have hh := Batch015.bound612 rho hr0 hr1
    norm_num [Batch015.certificate612,envelope306,inputs306,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch015.bound613 rho hr0 hr1
    norm_num [Batch015.certificate613,envelope306,inputs306,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs307 : RatMajorityInputs := ⟨(8612285912124423716830599/25000000000000000000000),(506865798360819/100000000000000),(100876784339938333/100000000000000000),(118987185460817917/1000000000000000000),(506865798360819/200000000000000),(79314922375845293/1000000000000000000),26⟩
theorem inputs_valid307 : inputs307.Valid := by decide +kernel
def envelope307 : RatMajorityEnvelope := ⟨153,1,inputs307,1,(543166554658378463/1000000000000000000)⟩
theorem envelope_sound307 : envelope307.Sound := by
  apply rat_majority_inputs_envelopes inputs307 inputs_valid307
  · norm_num [envelope307]
  · intro rho hr0 hr1
    have hh := Batch015.bound614 rho hr0 hr1
    norm_num [Batch015.certificate614,envelope307,inputs307,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch015.bound615 rho hr0 hr1
    norm_num [Batch015.certificate615,envelope307,inputs307,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs308 : RatMajorityInputs := ⟨(1718485031954377652995593/5000000000000000000000),(55787901611347/12500000000000),(1008788247989916963/1000000000000000000),(177779062216485843/1000000000000000000),(55787901611347/25000000000000),(53682766808548097/500000000000000000),25⟩
theorem inputs_valid308 : inputs308.Valid := by decide +kernel
def envelope308 : RatMajorityEnvelope := ⟨154,0,inputs308,(28227587/24273500),(43282796655331063/62500000000000000)⟩
theorem envelope_sound308 : envelope308.Sound := by
  apply rat_majority_inputs_envelopes inputs308 inputs_valid308
  · norm_num [envelope308]
  · intro rho hr0 hr1
    have hh := Batch015.bound616 rho hr0 hr1
    norm_num [Batch015.certificate616,envelope308,inputs308,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch015.bound617 rho hr0 hr1
    norm_num [Batch015.certificate617,envelope308,inputs308,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs309 : RatMajorityInputs := ⟨(1718485031954377652995593/5000000000000000000000),(63380837375417/12500000000000),(1008788247989916963/1000000000000000000),(14855134931465801/125000000000000000),(63380837375417/25000000000000),(39621607104386507/500000000000000000),26⟩
theorem inputs_valid309 : inputs309.Valid := by decide +kernel
def envelope309 : RatMajorityEnvelope := ⟨154,1,inputs309,1,(271580626192399747/500000000000000000)⟩
theorem envelope_sound309 : envelope309.Sound := by
  apply rat_majority_inputs_envelopes inputs309 inputs_valid309
  · norm_num [envelope309]
  · intro rho hr0 hr1
    have hh := Batch015.bound618 rho hr0 hr1
    norm_num [Batch015.certificate618,envelope309,inputs309,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch015.bound619 rho hr0 hr1
    norm_num [Batch015.certificate619,envelope309,inputs309,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs310 : RatMajorityInputs := ⟨(6858152984197509984919019/20000000000000000000000),(22335379610191/5000000000000),(1008808616566238077/1000000000000000000),(35463066675238897/200000000000000000),(22335379610191/10000000000000),(53574335462149347/500000000000000000),25⟩
theorem inputs_valid310 : inputs310.Valid := by decide +kernel
def envelope310 : RatMajorityEnvelope := ⟨155,0,inputs310,(2257187933/1941650000),(346072232936335609/500000000000000000)⟩
theorem envelope_sound310 : envelope310.Sound := by
  apply rat_majority_inputs_envelopes inputs310 inputs_valid310
  · norm_num [envelope310]
  · intro rho hr0 hr1
    have hh := Batch015.bound620 rho hr0 hr1
    norm_num [Batch015.certificate620,envelope310,inputs310,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch015.bound621 rho hr0 hr1
    norm_num [Batch015.certificate621,envelope310,inputs310,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs311 : RatMajorityInputs := ⟨(6858152984197509984919019/20000000000000000000000),(811563449897/160000000000),(1008808616566238077/1000000000000000000),(14836936373159531/125000000000000000),(811563449897/320000000000),(39585873210026437/500000000000000000),26⟩
theorem inputs_valid311 : inputs311.Valid := by decide +kernel
def envelope311 : RatMajorityEnvelope := ⟨155,1,inputs311,1,(271577997255698149/500000000000000000)⟩
theorem envelope_sound311 : envelope311.Sound := by
  apply rat_majority_inputs_envelopes inputs311 inputs_valid311
  · norm_num [envelope311]
  · intro rho hr0 hr1
    have hh := Batch015.bound622 rho hr0 hr1
    norm_num [Batch015.certificate622,envelope311,inputs311,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch015.bound623 rho hr0 hr1
    norm_num [Batch015.certificate623,envelope311,inputs311,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs312 : RatMajorityInputs := ⟨(34212509273228235065660329/100000000000000000000000),(111798154556811/25000000000000),(1008828903071547729/1000000000000000000),(176760485949369323/1000000000000000000),(111798154556811/50000000000000),(106889136285264703/1000000000000000000),25⟩
theorem inputs_valid312 : inputs312.Valid := by decide +kernel
def envelope312 : RatMajorityEnvelope := ⟨156,0,inputs312,(90245891/77657200),(172935092445179733/250000000000000000)⟩
theorem envelope_sound312 : envelope312.Sound := by
  apply rat_majority_inputs_envelopes inputs312 inputs_valid312
  · norm_num [envelope312]
  · intro rho hr0 hr1
    have hh := Batch015.bound624 rho hr0 hr1
    norm_num [Batch015.certificate624,envelope312,inputs312,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch015.bound625 rho hr0 hr1
    norm_num [Batch015.certificate625,envelope312,inputs312,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs313 : RatMajorityInputs := ⟨(34212509273228235065660329/100000000000000000000000),(50740820952139/10000000000000),(1008828903071547729/1000000000000000000),(29637395347716421/250000000000000000),(50740820952139/20000000000000),(3164004292290307/40000000000000000),27⟩
theorem inputs_valid313 : inputs313.Valid := by decide +kernel
def envelope313 : RatMajorityEnvelope := ⟨156,1,inputs313,1,(543150674906234341/1000000000000000000)⟩
theorem envelope_sound313 : envelope313.Sound := by
  apply rat_majority_inputs_envelopes inputs313 inputs_valid313
  · norm_num [envelope313]
  · intro rho hr0 hr1
    have hh := Batch015.bound626 rho hr0 hr1
    norm_num [Batch015.certificate626,envelope313,inputs313,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch015.bound627 rho hr0 hr1
    norm_num [Batch015.certificate627,envelope313,inputs313,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs314 : RatMajorityInputs := ⟨(34134753300129447082903431/100000000000000000000000),(447723013363929/100000000000000),(252212288201007861/250000000000000000),(88077719388036843/500000000000000000),(447723013363929/200000000000000),(26651511109319301/250000000000000000),27⟩
theorem inputs_valid314 : inputs314.Valid := by decide +kernel
def envelope314 : RatMajorityEnvelope := ⟨157,0,inputs314,(751623467/647070000),(43201366783117419/62500000000000000)⟩
theorem envelope_sound314 : envelope314.Sound := by
  apply rat_majority_inputs_envelopes inputs314 inputs_valid314
  · norm_num [envelope314]
  · intro rho hr0 hr1
    have hh := Batch015.bound628 rho hr0 hr1
    norm_num [Batch015.certificate628,envelope314,inputs314,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch015.bound629 rho hr0 hr1
    norm_num [Batch015.certificate629,envelope314,inputs314,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs315 : RatMajorityInputs := ⟨(34134753300129447082903431/100000000000000000000000),(507623976257877/100000000000000),(252212288201007861/250000000000000000),(4735036216226301/40000000000000000),(507623976257877/200000000000000),(15802963492452287/200000000000000000),27⟩
theorem inputs_valid315 : inputs315.Valid := by decide +kernel
def envelope315 : RatMajorityEnvelope := ⟨157,1,inputs315,1,(265206320948599/488281250000000)⟩
theorem envelope_sound315 : envelope315.Sound := by
  apply rat_majority_inputs_envelopes inputs315 inputs_valid315
  · norm_num [envelope315]
  · intro rho hr0 hr1
    have hh := Batch015.bound630 rho hr0 hr1
    norm_num [Batch015.certificate630,envelope315,inputs315,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch015.bound631 rho hr0 hr1
    norm_num [Batch015.certificate631,envelope315,inputs315,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs316 : RatMajorityInputs := ⟨(4257186703801394283241427/12500000000000000000000),(112029230658577/25000000000000),(1008869365496675817/1000000000000000000),(878536175538911/5000000000000000),(112029230658577/50000000000000),(21279257104824687/200000000000000000),26⟩
theorem inputs_valid316 : inputs316.Valid := by decide +kernel
def envelope316 : RatMajorityEnvelope := ⟨158,0,inputs316,(2253912731/1940990000),(43179121045838453/62500000000000000)⟩
theorem envelope_sound316 : envelope316.Sound := by
  apply rat_majority_inputs_envelopes inputs316 inputs_valid316
  · norm_num [envelope316]
  · intro rho hr0 hr1
    have hh := Batch015.bound632 rho hr0 hr1
    norm_num [Batch015.certificate632,envelope316,inputs316,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch015.bound633 rho hr0 hr1
    norm_num [Batch015.certificate633,envelope316,inputs316,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs317 : RatMajorityInputs := ⟨(4257186703801394283241427/12500000000000000000000),(507755177920517/100000000000000),(1008869365496675817/1000000000000000000),(59135204455651777/500000000000000000),(507755177920517/200000000000000),(39481500041657089/500000000000000000),26⟩
theorem inputs_valid317 : inputs317.Valid := by decide +kernel
def envelope317 : RatMajorityEnvelope := ⟨158,1,inputs317,1,(543141286275224849/1000000000000000000)⟩
theorem envelope_sound317 : envelope317.Sound := by
  apply rat_majority_inputs_envelopes inputs317 inputs_valid317
  · norm_num [envelope317]
  · intro rho hr0 hr1
    have hh := Batch015.bound634 rho hr0 hr1
    norm_num [Batch015.certificate634,envelope317,inputs317,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch015.bound635 rho hr0 hr1
    norm_num [Batch015.certificate635,envelope317,inputs317,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs318 : RatMajorityInputs := ⟨(33980726924948013979761863/100000000000000000000000),(447831654908287/100000000000000),(504444770441448463/500000000000000000),(35206345009352487/200000000000000000),(447831654908287/200000000000000),(106548150936271357/1000000000000000000),25⟩
theorem inputs_valid318 : inputs318.Valid := by decide +kernel
def envelope318 : RatMajorityEnvelope := ⟨159,0,inputs318,(450626349/388154000),(690662151290239921/1000000000000000000)⟩
theorem envelope_sound318 : envelope318.Sound := by
  apply rat_majority_inputs_envelopes inputs318 inputs_valid318
  · norm_num [envelope318]
  · intro rho hr0 hr1
    have hh := Batch015.bound636 rho hr0 hr1
    norm_num [Batch015.certificate636,envelope318,inputs318,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch015.bound637 rho hr0 hr1
    norm_num [Batch015.certificate637,envelope318,inputs318,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs319 : RatMajorityInputs := ⟨(33980726924948013979761863/100000000000000000000000),(507934716314493/100000000000000),(504444770441448463/500000000000000000),(118126181753002423/1000000000000000000),(507934716314493/200000000000000),(39446073719452387/500000000000000000),26⟩
theorem inputs_valid319 : inputs319.Valid := by decide +kernel
def envelope319 : RatMajorityEnvelope := ⟨159,1,inputs319,1,(543136110427771117/1000000000000000000)⟩
theorem envelope_sound319 : envelope319.Sound := by
  apply rat_majority_inputs_envelopes inputs319 inputs_valid319
  · norm_num [envelope319]
  · intro rho hr0 hr1
    have hh := Batch015.bound638 rho hr0 hr1
    norm_num [Batch015.certificate638,envelope319,inputs319,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch015.bound639 rho hr0 hr1
    norm_num [Batch015.certificate639,envelope319,inputs319,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def configurations : List RatMajorityEnvelope := [envelope300,envelope301,envelope302,envelope303,envelope304,envelope305,envelope306,envelope307,envelope308,envelope309,envelope310,envelope311,envelope312,envelope313,envelope314,envelope315,envelope316,envelope317,envelope318,envelope319]
theorem configurations_sound : ∀ s∈configurations, s.Sound := by
  intro s hs
  simp only [configurations,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact envelope_sound300
  · exact envelope_sound301
  · exact envelope_sound302
  · exact envelope_sound303
  · exact envelope_sound304
  · exact envelope_sound305
  · exact envelope_sound306
  · exact envelope_sound307
  · exact envelope_sound308
  · exact envelope_sound309
  · exact envelope_sound310
  · exact envelope_sound311
  · exact envelope_sound312
  · exact envelope_sound313
  · exact envelope_sound314
  · exact envelope_sound315
  · exact envelope_sound316
  · exact envelope_sound317
  · exact envelope_sound318
  · exact envelope_sound319

end Cycle12.MajorityCertificates.Inputs015
