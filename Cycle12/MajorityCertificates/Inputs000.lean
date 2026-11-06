import Cycle12.RationalMajorityInputs
import Cycle12.MajorityCertificates.Batch000

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Inputs000

def inputs0 : RatMajorityInputs := ⟨(1065019996535959517/10000000000000),(8376898031/2000000000),(62501760568896327/62500000000000000),(21177035892260179/100000000000000000),(8376898031/4000000000),(61582860345096461/500000000000000000),25⟩
theorem inputs_valid0 : inputs0.Valid := by decide +kernel
def envelope0 : RatMajorityEnvelope := ⟨0,0,inputs0,(136781647/117500000),(173063789282714933/250000000000000000)⟩
theorem envelope_sound0 : envelope0.Sound := by
  apply rat_majority_inputs_envelopes inputs0 inputs_valid0
  · norm_num [envelope0]
  · intro rho hr0 hr1
    have hh := Batch000.bound0 rho hr0 hr1
    norm_num [Batch000.certificate0,envelope0,inputs0,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch000.bound1 rho hr0 hr1
    norm_num [Batch000.certificate1,envelope0,inputs0,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs1 : RatMajorityInputs := ⟨(1065019996535959517/10000000000000),(49366274643/10000000000),(62501760568896327/62500000000000000),(13009200729360669/100000000000000000),(49366274643/20000000000),(42363806028006207/500000000000000000),27⟩
theorem inputs_valid1 : inputs1.Valid := by decide +kernel
def envelope1 : RatMajorityEnvelope := ⟨0,1,inputs1,1,(33769084988993921/62500000000000000)⟩
theorem envelope_sound1 : envelope1.Sound := by
  apply rat_majority_inputs_envelopes inputs1 inputs_valid1
  · norm_num [envelope1]
  · intro rho hr0 hr1
    have hh := Batch000.bound2 rho hr0 hr1
    norm_num [Batch000.certificate2,envelope1,inputs1,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch000.bound3 rho hr0 hr1
    norm_num [Batch000.certificate3,envelope1,inputs1,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs2 : RatMajorityInputs := ⟨(1065019999133989878174217/5000000000000000000),(16468417279/4000000000),(1000014084396847021/1000000000000000000),(221441883142654059/1000000000000000000),(16468417279/8000000000),(31909659129534923/250000000000000000),25⟩
theorem inputs_valid2 : inputs2.Valid := by decide +kernel
def envelope2 : RatMajorityEnvelope := ⟨1,0,inputs2,(54999269/47000000),(174683476400834809/250000000000000000)⟩
theorem envelope_sound2 : envelope2.Sound := by
  apply rat_majority_inputs_envelopes inputs2 inputs_valid2
  · norm_num [envelope2]
  · intro rho hr0 hr1
    have hh := Batch000.bound4 rho hr0 hr1
    norm_num [Batch000.certificate4,envelope2,inputs2,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch000.bound5 rho hr0 hr1
    norm_num [Batch000.certificate5,envelope2,inputs2,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs3 : RatMajorityInputs := ⟨(1065019999133989878174217/5000000000000000000),(23151704949/5000000000),(1000014084396847021/1000000000000000000),(39859885601182651/250000000000000000),(23151704949/10000000000),(98749346306878077/1000000000000000000),26⟩
theorem inputs_valid3 : inputs3.Valid := by decide +kernel
def envelope3 : RatMajorityEnvelope := ⟨1,1,inputs3,1,(135903700603807237/250000000000000000)⟩
theorem envelope_sound3 : envelope3.Sound := by
  apply rat_majority_inputs_envelopes inputs3 inputs_valid3
  · norm_num [envelope3]
  · intro rho hr0 hr1
    have hh := Batch000.bound6 rho hr0 hr1
    norm_num [Batch000.certificate6,envelope3,inputs3,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch000.bound7 rho hr0 hr1
    norm_num [Batch000.certificate7,envelope3,inputs3,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs4 : RatMajorityInputs := ⟨(1535954595111243401281412359/25000000000000000000000),(423291478688719/100000000000000),(1000048831422966257/1000000000000000000),(205922045846601323/1000000000000000000),(423291478688719/200000000000000),(60228803718980657/500000000000000000),25⟩
theorem inputs_valid4 : inputs4.Valid := by decide +kernel
def envelope4 : RatMajorityEnvelope := ⟨2,0,inputs4,(2724208969/2357590000),(68398978337488429/100000000000000000)⟩
theorem envelope_sound4 : envelope4.Sound := by
  apply rat_majority_inputs_envelopes inputs4 inputs_valid4
  · norm_num [envelope4]
  · intro rho hr0 hr1
    have hh := Batch000.bound8 rho hr0 hr1
    norm_num [Batch000.certificate8,envelope4,inputs4,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch000.bound9 rho hr0 hr1
    norm_num [Batch000.certificate9,envelope4,inputs4,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs5 : RatMajorityInputs := ⟨(1535954595111243401281412359/25000000000000000000000),(499611720718643/100000000000000),(1000048831422966257/1000000000000000000),(31244856574344031/250000000000000000),(499611720718643/200000000000000),(20561128233858189/250000000000000000),27⟩
theorem inputs_valid5 : inputs5.Valid := by decide +kernel
def envelope5 : RatMajorityEnvelope := ⟨2,1,inputs5,1,(26988082684439061/50000000000000000)⟩
theorem envelope_sound5 : envelope5.Sound := by
  apply rat_majority_inputs_envelopes inputs5 inputs_valid5
  · norm_num [envelope5]
  · intro rho hr0 hr1
    have hh := Batch000.bound10 rho hr0 hr1
    norm_num [Batch000.certificate10,envelope5,inputs5,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch000.bound11 rho hr0 hr1
    norm_num [Batch000.certificate11,envelope5,inputs5,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs6 : RatMajorityInputs := ⟨(123058694545256666278006263/3125000000000000000000),(211751193230601/50000000000000),(1000076187672614857/1000000000000000000),(20564803452803487/100000000000000000),(211751193230601/100000000000000),(120330647163681597/1000000000000000000),25⟩
theorem inputs_valid6 : inputs6.Valid := by decide +kernel
def envelope6 : RatMajorityEnvelope := ⟨3,0,inputs6,(677976413/585897500),(685444797203885443/1000000000000000000)⟩
theorem envelope_sound6 : envelope6.Sound := by
  apply rat_majority_inputs_envelopes inputs6 inputs_valid6
  · norm_num [envelope6]
  · intro rho hr0 hr1
    have hh := Batch000.bound12 rho hr0 hr1
    norm_num [Batch000.certificate12,envelope6,inputs6,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch000.bound13 rho hr0 hr1
    norm_num [Batch000.certificate13,envelope6,inputs6,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs7 : RatMajorityInputs := ⟨(123058694545256666278006263/3125000000000000000000),(500160569233439/100000000000000),(1000076187672614857/1000000000000000000),(31129211559775413/250000000000000000),(500160569233439/200000000000000),(41009561722362667/500000000000000000),27⟩
theorem inputs_valid7 : inputs7.Valid := by decide +kernel
def envelope7 : RatMajorityEnvelope := ⟨3,1,inputs7,1,(539724554264025111/1000000000000000000)⟩
theorem envelope_sound7 : envelope7.Sound := by
  apply rat_majority_inputs_envelopes inputs7 inputs_valid7
  · norm_num [envelope7]
  · intro rho hr0 hr1
    have hh := Batch000.bound14 rho hr0 hr1
    norm_num [Batch000.certificate14,envelope7,inputs7,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch000.bound15 rho hr0 hr1
    norm_num [Batch000.certificate15,envelope7,inputs7,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs8 : RatMajorityInputs := ⟨(547762358835901492645242339/20000000000000000000000),(42300148866363/10000000000000),(1000109545884520517/1000000000000000000),(206299298873256143/1000000000000000000),(42300148866363/20000000000000),(120632391644546381/1000000000000000000),25⟩
theorem inputs_valid8 : inputs8.Valid := by decide +kernel
def envelope8 : RatMajorityEnvelope := ⟨4,0,inputs8,(2700025271/2329650000),(343577777257066661/500000000000000000)⟩
theorem envelope_sound8 : envelope8.Sound := by
  apply rat_majority_inputs_envelopes inputs8 inputs_valid8
  · norm_num [envelope8]
  · intro rho hr0 hr1
    have hh := Batch000.bound16 rho hr0 hr1
    norm_num [Batch000.certificate16,envelope8,inputs8,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch000.bound17 rho hr0 hr1
    norm_num [Batch000.certificate17,envelope8,inputs8,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs9 : RatMajorityInputs := ⟨(547762358835901492645242339/20000000000000000000000),(99941008736871/20000000000000),(1000109545884520517/1000000000000000000),(124900664410254657/1000000000000000000),(99941008736871/40000000000000),(8220614537826109/100000000000000000),26⟩
theorem inputs_valid9 : inputs9.Valid := by decide +kernel
def envelope9 : RatMajorityEnvelope := ⟨4,1,inputs9,1,(134945287418778513/250000000000000000)⟩
theorem envelope_sound9 : envelope9.Sound := by
  apply rat_majority_inputs_envelopes inputs9 inputs_valid9
  · norm_num [envelope9]
  · intro rho hr0 hr1
    have hh := Batch000.bound18 rho hr0 hr1
    norm_num [Batch000.certificate18,envelope9,inputs9,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch000.bound19 rho hr0 hr1
    norm_num [Batch000.certificate19,envelope9,inputs9,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs10 : RatMajorityInputs := ⟨(1007869128306195215987130357/50000000000000000000000),(13205057547091/3125000000000),(100014884607633889/100000000000000000),(206872344468827847/1000000000000000000),(13205057547091/6250000000000),(120897861760572447/1000000000000000000),25⟩
theorem inputs_valid10 : inputs10.Valid := by decide +kernel
def envelope10 : RatMajorityEnvelope := ⟨5,0,inputs10,(2688640631/2316220000),(344422186976356671/500000000000000000)⟩
theorem envelope_sound10 : envelope10.Sound := by
  apply rat_majority_inputs_envelopes inputs10 inputs_valid10
  · norm_num [envelope10]
  · intro rho hr0 hr1
    have hh := Batch000.bound20 rho hr0 hr1
    norm_num [Batch000.certificate20,envelope10,inputs10,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch000.bound21 rho hr0 hr1
    norm_num [Batch000.certificate21,envelope10,inputs10,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs11 : RatMajorityInputs := ⟨(1007869128306195215987130357/50000000000000000000000),(250236313726911/50000000000000),(100014884607633889/100000000000000000),(124254516139088079/1000000000000000000),(250236313726911/100000000000000),(20472812380610431/250000000000000000),26⟩
theorem inputs_valid11 : inputs11.Valid := by decide +kernel
def envelope11 : RatMajorityEnvelope := ⟨5,1,inputs11,1,(269864943018699869/500000000000000000)⟩
theorem envelope_sound11 : envelope11.Sound := by
  apply rat_majority_inputs_envelopes inputs11 inputs_valid11
  · norm_num [envelope11]
  · intro rho hr0 hr1
    have hh := Batch000.bound22 rho hr0 hr1
    norm_num [Batch000.certificate22,envelope11,inputs11,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch000.bound23 rho hr0 hr1
    norm_num [Batch000.certificate23,envelope11,inputs11,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs12 : RatMajorityInputs := ⟨(96648059999165217989302397/6250000000000000000000),(105520381395823/25000000000000),(1000194032136813037/1000000000000000000),(41499983436050141/200000000000000000),(105520381395823/50000000000000),(6059427826242089/50000000000000000),25⟩
theorem inputs_valid12 : inputs12.Valid := by decide +kernel
def envelope12 : RatMajorityEnvelope := ⟨6,0,inputs12,(2677761569/2303260000),(345272913233724549/500000000000000000)⟩
theorem envelope_sound12 : envelope12.Sound := by
  apply rat_majority_inputs_envelopes inputs12 inputs_valid12
  · norm_num [envelope12]
  · intro rho hr0 hr1
    have hh := Batch000.bound24 rho hr0 hr1
    norm_num [Batch000.certificate24,envelope12,inputs12,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch000.bound25 rho hr0 hr1
    norm_num [Batch000.certificate25,envelope12,inputs12,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs13 : RatMajorityInputs := ⟨(96648059999165217989302397/6250000000000000000000),(250150938818999/50000000000000),(1000194032136813037/1000000000000000000),(12439799519552507/100000000000000000),(250150938818999/100000000000000),(81961193954558281/1000000000000000000),26⟩
theorem inputs_valid13 : inputs13.Valid := by decide +kernel
def envelope13 : RatMajorityEnvelope := ⟨6,1,inputs13,1,(2698830513645927/5000000000000000)⟩
theorem envelope_sound13 : envelope13.Sound := by
  apply rat_majority_inputs_envelopes inputs13 inputs_valid13
  · norm_num [envelope13]
  · intro rho hr0 hr1
    have hh := Batch000.bound26 rho hr0 hr1
    norm_num [Batch000.certificate26,envelope13,inputs13,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch000.bound27 rho hr0 hr1
    norm_num [Batch000.certificate27,envelope13,inputs13,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs14 : RatMajorityInputs := ⟨(612249671555258265247888719/50000000000000000000000),(210812623121439/50000000000000),(1000245044783335231/1000000000000000000),(41619510972545701/200000000000000000),(210812623121439/100000000000000),(121465351317335103/1000000000000000000),25⟩
theorem inputs_valid14 : inputs14.Valid := by decide +kernel
def envelope14 : RatMajorityEnvelope := ⟨7,0,inputs14,(889098753/763570000),(692241387556439571/1000000000000000000)⟩
theorem envelope_sound14 : envelope14.Sound := by
  apply rat_majority_inputs_envelopes inputs14 inputs_valid14
  · norm_num [envelope14]
  · intro rho hr0 hr1
    have hh := Batch000.bound28 rho hr0 hr1
    norm_num [Batch000.certificate28,envelope14,inputs14,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch000.bound29 rho hr0 hr1
    norm_num [Batch000.certificate29,envelope14,inputs14,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs15 : RatMajorityInputs := ⟨(612249671555258265247888719/50000000000000000000000),(250128928704849/50000000000000),(1000245044783335231/1000000000000000000),(124435008724123123/1000000000000000000),(250128928704849/100000000000000),(81979235692337087/1000000000000000000),26⟩
theorem inputs_valid15 : inputs15.Valid := by decide +kernel
def envelope15 : RatMajorityEnvelope := ⟨7,1,inputs15,1,(539793581540657223/1000000000000000000)⟩
theorem envelope_sound15 : envelope15.Sound := by
  apply rat_majority_inputs_envelopes inputs15 inputs_valid15
  · norm_num [envelope15]
  · intro rho hr0 hr1
    have hh := Batch000.bound30 rho hr0 hr1
    norm_num [Batch000.certificate30,envelope15,inputs15,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch000.bound31 rho hr0 hr1
    norm_num [Batch000.certificate31,envelope15,inputs15,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs16 : RatMajorityInputs := ⟨(62138015483507093270846431/6250000000000000000000),(105313848679083/25000000000000),(1000301818480832519/1000000000000000000),(52145760456150941/250000000000000000),(105313848679083/50000000000000),(60845089932126309/500000000000000000),25⟩
theorem inputs_valid16 : inputs16.Valid := by decide +kernel
def envelope16 : RatMajorityEnvelope := ⟨8,0,inputs16,(2657183821/2278540000),(346955590092396669/500000000000000000)⟩
theorem envelope_sound16 : envelope16.Sound := by
  apply rat_majority_inputs_envelopes inputs16 inputs_valid16
  · norm_num [envelope16]
  · intro rho hr0 hr1
    have hh := Batch000.bound32 rho hr0 hr1
    norm_num [Batch000.certificate32,envelope16,inputs16,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch000.bound33 rho hr0 hr1
    norm_num [Batch000.certificate33,envelope16,inputs16,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs17 : RatMajorityInputs := ⟨(62138015483507093270846431/6250000000000000000000),(31264153689703/6250000000000),(1000301818480832519/1000000000000000000),(124461415395373259/1000000000000000000),(31264153689703/12500000000000),(81992106776335403/1000000000000000000),26⟩
theorem inputs_valid17 : inputs17.Valid := by decide +kernel
def envelope17 : RatMajorityEnvelope := ⟨8,1,inputs17,1,(269911287958720621/500000000000000000)⟩
theorem envelope_sound17 : envelope17.Sound := by
  apply rat_majority_inputs_envelopes inputs17 inputs_valid17
  · norm_num [envelope17]
  · intro rho hr0 hr1
    have hh := Batch000.bound34 rho hr0 hr1
    norm_num [Batch000.certificate34,envelope17,inputs17,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch000.bound35 rho hr0 hr1
    norm_num [Batch000.certificate35,envelope17,inputs17,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs18 : RatMajorityInputs := ⟨(51485925034209234278004939/6250000000000000000000),(21040109280729/5000000000000),(1000364280379285999/1000000000000000000),(104589617824653929/500000000000000000),(21040109280729/10000000000000),(60983124011583363/500000000000000000),25⟩
theorem inputs_valid18 : inputs18.Valid := by decide +kernel
def envelope18 : RatMajorityEnvelope := ⟨9,0,inputs18,(882499253/755580000),(695611327831907727/1000000000000000000)⟩
theorem envelope_sound18 : envelope18.Sound := by
  apply rat_majority_inputs_envelopes inputs18 inputs_valid18
  · norm_num [envelope18]
  · intro rho hr0 hr1
    have hh := Batch000.bound36 rho hr0 hr1
    norm_num [Batch000.certificate36,envelope18,inputs18,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch000.bound37 rho hr0 hr1
    norm_num [Batch000.certificate37,envelope18,inputs18,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs19 : RatMajorityInputs := ⟨(51485925034209234278004939/6250000000000000000000),(250097176564137/50000000000000),(1000364280379285999/1000000000000000000),(124488422262078077/1000000000000000000),(250097176564137/100000000000000),(82005269987613043/1000000000000000000),27⟩
theorem inputs_valid19 : inputs19.Valid := by decide +kernel
def envelope19 : RatMajorityEnvelope := ⟨9,1,inputs19,1,(53985425427305963/100000000000000000)⟩
theorem envelope_sound19 : envelope19.Sound := by
  apply rat_majority_inputs_envelopes inputs19 inputs_valid19
  · norm_num [envelope19]
  · intro rho hr0 hr1
    have hh := Batch000.bound38 rho hr0 hr1
    norm_num [Batch000.certificate38,envelope19,inputs19,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch000.bound39 rho hr0 hr1
    norm_num [Batch000.certificate39,envelope19,inputs19,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def configurations : List RatMajorityEnvelope := [envelope0,envelope1,envelope2,envelope3,envelope4,envelope5,envelope6,envelope7,envelope8,envelope9,envelope10,envelope11,envelope12,envelope13,envelope14,envelope15,envelope16,envelope17,envelope18,envelope19]
theorem configurations_sound : ∀ s∈configurations, s.Sound := by
  intro s hs
  simp only [configurations,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact envelope_sound0
  · exact envelope_sound1
  · exact envelope_sound2
  · exact envelope_sound3
  · exact envelope_sound4
  · exact envelope_sound5
  · exact envelope_sound6
  · exact envelope_sound7
  · exact envelope_sound8
  · exact envelope_sound9
  · exact envelope_sound10
  · exact envelope_sound11
  · exact envelope_sound12
  · exact envelope_sound13
  · exact envelope_sound14
  · exact envelope_sound15
  · exact envelope_sound16
  · exact envelope_sound17
  · exact envelope_sound18
  · exact envelope_sound19

end Cycle12.MajorityCertificates.Inputs000
