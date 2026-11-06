import Cycle12.RationalMajorityInputs
import Cycle12.MajorityCertificates.Batch023

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Inputs023

def inputs460 : RatMajorityInputs := ⟨(19356895752885231543172359/25000000000000000000000),(116717067356121/25000000000000),(125485787118178843/125000000000000000),(38868722821207557/250000000000000000),(116717067356121/50000000000000),(96874268033304011/1000000000000000000),26⟩
theorem inputs_valid460 : inputs460.Valid := by decide +kernel
def envelope460 : RatMajorityEnvelope := ⟨230,0,inputs460,(2377450717/2068680000),(337753373735367069/500000000000000000)⟩
theorem envelope_sound460 : envelope460.Sound := by
  apply rat_majority_inputs_envelopes inputs460 inputs_valid460
  · norm_num [envelope460]
  · intro rho hr0 hr1
    have hh := Batch023.bound920 rho hr0 hr1
    norm_num [Batch023.certificate920,envelope460,inputs460,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch023.bound921 rho hr0 hr1
    norm_num [Batch023.certificate921,envelope460,inputs460,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs461 : RatMajorityInputs := ⟨(19356895752885231543172359/25000000000000000000000),(8097470274183/1562500000000),(125485787118178843/125000000000000000),(22021578321497489/200000000000000000),(8097470274183/3125000000000),(37465391393929973/500000000000000000),27⟩
theorem inputs_valid461 : inputs461.Valid := by decide +kernel
def envelope461 : RatMajorityEnvelope := ⟨230,1,inputs461,1,(53999064742750823/100000000000000000)⟩
theorem envelope_sound461 : envelope461.Sound := by
  apply rat_majority_inputs_envelopes inputs461 inputs_valid461
  · norm_num [envelope461]
  · intro rho hr0 hr1
    have hh := Batch023.bound922 rho hr0 hr1
    norm_num [Batch023.certificate922,envelope461,inputs461,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch023.bound923 rho hr0 hr1
    norm_num [Batch023.certificate923,envelope461,inputs461,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs462 : RatMajorityInputs := ⟨(15329367744744473329584179/20000000000000000000000),(58538353031589/12500000000000),(1003926004580156381/1000000000000000000),(154009625982725163/1000000000000000000),(58538353031589/25000000000000),(24044993312342489/250000000000000000),26⟩
theorem inputs_valid462 : inputs462.Valid := by decide +kernel
def envelope462 : RatMajorityEnvelope := ⟨231,0,inputs462,(2372703849/2067770000),(673788532970444511/1000000000000000000)⟩
theorem envelope_sound462 : envelope462.Sound := by
  apply rat_majority_inputs_envelopes inputs462 inputs_valid462
  · norm_num [envelope462]
  · intro rho hr0 hr1
    have hh := Batch023.bound924 rho hr0 hr1
    norm_num [Batch023.certificate924,envelope462,inputs462,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch023.bound925 rho hr0 hr1
    norm_num [Batch023.certificate925,envelope462,inputs462,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs463 : RatMajorityInputs := ⟨(15329367744744473329584179/20000000000000000000000),(51945207180597/10000000000000),(1003926004580156381/1000000000000000000),(54598003240301801/500000000000000000),(51945207180597/20000000000000),(74477340142025309/1000000000000000000),26⟩
theorem inputs_valid463 : inputs463.Valid := by decide +kernel
def envelope463 : RatMajorityEnvelope := ⟨231,1,inputs463,1,(539916811243660673/1000000000000000000)⟩
theorem envelope_sound463 : envelope463.Sound := by
  apply rat_majority_inputs_envelopes inputs463 inputs_valid463
  · norm_num [envelope463]
  · intro rho hr0 hr1
    have hh := Batch023.bound926 rho hr0 hr1
    norm_num [Batch023.certificate926,envelope463,inputs463,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch023.bound927 rho hr0 hr1
    norm_num [Batch023.certificate927,envelope463,inputs463,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs464 : RatMajorityInputs := ⟨(37943606064743221009239429/50000000000000000000000),(464220744829611/100000000000000),(250991356201191259/250000000000000000),(79101624381284187/500000000000000000),(464220744829611/200000000000000),(49082589255791149/500000000000000000),26⟩
theorem inputs_valid464 : inputs464.Valid := by decide +kernel
def envelope464 : RatMajorityEnvelope := ⟨232,0,inputs464,(94864393/82675600),(337077095229768533/500000000000000000)⟩
theorem envelope_sound464 : envelope464.Sound := by
  apply rat_majority_inputs_envelopes inputs464 inputs_valid464
  · norm_num [envelope464]
  · intro rho hr0 hr1
    have hh := Batch023.bound928 rho hr0 hr1
    norm_num [Batch023.certificate928,envelope464,inputs464,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch023.bound929 rho hr0 hr1
    norm_num [Batch023.certificate929,envelope464,inputs464,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs465 : RatMajorityInputs := ⟨(37943606064743221009239429/50000000000000000000000),(519894693944563/100000000000000),(250991356201191259/250000000000000000),(108865217247462893/1000000000000000000),(519894693944563/200000000000000),(9289086974931417/125000000000000000),27⟩
theorem inputs_valid465 : inputs465.Valid := by decide +kernel
def envelope465 : RatMajorityEnvelope := ⟨232,1,inputs465,1,(269950916366418811/500000000000000000)⟩
theorem envelope_sound465 : envelope465.Sound := by
  apply rat_majority_inputs_envelopes inputs465 inputs_valid465
  · norm_num [envelope465]
  · intro rho hr0 hr1
    have hh := Batch023.bound930 rho hr0 hr1
    norm_num [Batch023.certificate930,envelope465,inputs465,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch023.bound931 rho hr0 hr1
    norm_num [Batch023.certificate931,envelope465,inputs465,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs466 : RatMajorityInputs := ⟨(37573869972940349182966081/50000000000000000000000),(469811470709329/100000000000000),(100400456703208171/100000000000000000),(152489909156318807/1000000000000000000),(469811470709329/200000000000000),(95459104003064993/1000000000000000000),26⟩
theorem inputs_valid466 : inputs466.Valid := by decide +kernel
def envelope466 : RatMajorityEnvelope := ⟨233,0,inputs466,(1182789507/1033015000),(83933242094376899/125000000000000000)⟩
theorem envelope_sound466 : envelope466.Sound := by
  apply rat_majority_inputs_envelopes inputs466 inputs_valid466
  · norm_num [envelope466]
  · intro rho hr0 hr1
    have hh := Batch023.bound932 rho hr0 hr1
    norm_num [Batch023.certificate932,envelope466,inputs466,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch023.bound933 rho hr0 hr1
    norm_num [Batch023.certificate933,envelope466,inputs466,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs467 : RatMajorityInputs := ⟨(37573869972940349182966081/50000000000000000000000),(65058407257059/12500000000000),(100400456703208171/100000000000000000),(108438651515042169/1000000000000000000),(65058407257059/25000000000000),(18525064029878713/250000000000000000),27⟩
theorem inputs_valid467 : inputs467.Valid := by decide +kernel
def envelope467 : RatMajorityEnvelope := ⟨233,1,inputs467,1,(134969272012137467/250000000000000000)⟩
theorem envelope_sound467 : envelope467.Sound := by
  apply rat_majority_inputs_envelopes inputs467 inputs_valid467
  · norm_num [envelope467]
  · intro rho hr0 hr1
    have hh := Batch023.bound934 rho hr0 hr1
    norm_num [Batch023.certificate934,envelope467,inputs467,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch023.bound935 rho hr0 hr1
    norm_num [Batch023.certificate935,envelope467,inputs467,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs468 : RatMajorityInputs := ⟨(2325870509969351209800663/3125000000000000000000),(471226256284081/100000000000000),(1004043421889635797/1000000000000000000),(37768220546981923/250000000000000000),(471226256284081/200000000000000),(94786215973115337/1000000000000000000),26⟩
theorem inputs_valid468 : inputs468.Valid := by decide +kernel
def envelope468 : RatMajorityEnvelope := ⟨234,0,inputs468,(590225883/516297500),(669745515767289457/1000000000000000000)⟩
theorem envelope_sound468 : envelope468.Sound := by
  apply rat_majority_inputs_envelopes inputs468 inputs_valid468
  · norm_num [envelope468]
  · intro rho hr0 hr1
    have hh := Batch023.bound936 rho hr0 hr1
    norm_num [Batch023.certificate936,envelope468,inputs468,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch023.bound937 rho hr0 hr1
    norm_num [Batch023.certificate937,envelope468,inputs468,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs469 : RatMajorityInputs := ⟨(2325870509969351209800663/3125000000000000000000),(521794312343943/100000000000000),(1004043421889635797/1000000000000000000),(13431968501093877/125000000000000000),(521794312343943/200000000000000),(36805104202161983/500000000000000000),27⟩
theorem inputs_valid469 : inputs469.Valid := by decide +kernel
def envelope469 : RatMajorityEnvelope := ⟨234,1,inputs469,1,(269898087741099833/500000000000000000)⟩
theorem envelope_sound469 : envelope469.Sound := by
  apply rat_majority_inputs_envelopes inputs469 inputs_valid469
  · norm_num [envelope469]
  · intro rho hr0 hr1
    have hh := Batch023.bound938 rho hr0 hr1
    norm_num [Batch023.certificate938,envelope469,inputs469,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch023.bound939 rho hr0 hr1
    norm_num [Batch023.certificate939,envelope469,inputs469,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs470 : RatMajorityInputs := ⟨(73727017496449756091279319/100000000000000000000000),(233210188800281/50000000000000),(502040990032828799/500000000000000000),(9745847865201533/62500000000000000),(233210188800281/100000000000000),(48545728549276517/500000000000000000),26⟩
theorem inputs_valid470 : inputs470.Valid := by decide +kernel
def envelope470 : RatMajorityEnvelope := ⟨235,0,inputs470,(235999473/206437000),(670219642856864893/1000000000000000000)⟩
theorem envelope_sound470 : envelope470.Sound := by
  apply rat_majority_inputs_envelopes inputs470 inputs_valid470
  · norm_num [envelope470]
  · intro rho hr0 hr1
    have hh := Batch023.bound940 rho hr0 hr1
    norm_num [Batch023.certificate940,envelope470,inputs470,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch023.bound941 rho hr0 hr1
    norm_num [Batch023.certificate941,envelope470,inputs470,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs471 : RatMajorityInputs := ⟨(73727017496449756091279319/100000000000000000000000),(522101662453217/100000000000000),(502040990032828799/500000000000000000),(53614624429613409/500000000000000000),(522101662453217/200000000000000),(73497174750849623/1000000000000000000),27⟩
theorem inputs_valid471 : inputs471.Valid := by decide +kernel
def envelope471 : RatMajorityEnvelope := ⟨235,1,inputs471,1,(539791495123494283/1000000000000000000)⟩
theorem envelope_sound471 : envelope471.Sound := by
  apply rat_majority_inputs_envelopes inputs471 inputs_valid471
  · norm_num [envelope471]
  · intro rho hr0 hr1
    have hh := Batch023.bound942 rho hr0 hr1
    norm_num [Batch023.certificate942,envelope471,inputs471,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch023.bound943 rho hr0 hr1
    norm_num [Batch023.certificate943,envelope471,inputs471,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs472 : RatMajorityInputs := ⟨(9130631851548706014333333/12500000000000000000000),(236666204643933/50000000000000),(125515026535188333/125000000000000000),(18623082521047951/125000000000000000),(236666204643933/100000000000000),(93793281959160481/1000000000000000000),26⟩
theorem inputs_valid472 : inputs472.Valid := by decide +kernel
def envelope472 : RatMajorityEnvelope := ⟨236,0,inputs472,(9415003/8254320),(667290096979147881/1000000000000000000)⟩
theorem envelope_sound472 : envelope472.Sound := by
  apply rat_majority_inputs_envelopes inputs472 inputs_valid472
  · norm_num [envelope472]
  · intro rho hr0 hr1
    have hh := Batch023.bound944 rho hr0 hr1
    norm_num [Batch023.certificate944,envelope472,inputs472,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch023.bound945 rho hr0 hr1
    norm_num [Batch023.certificate945,envelope472,inputs472,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs473 : RatMajorityInputs := ⟨(9130631851548706014333333/12500000000000000000000),(65429763600483/12500000000000),(125515026535188333/125000000000000000),(106249346311501031/1000000000000000000),(65429763600483/25000000000000),(14601537370627007/200000000000000000),27⟩
theorem inputs_valid473 : inputs473.Valid := by decide +kernel
def envelope473 : RatMajorityEnvelope := ⟨236,1,inputs473,1,(134927739516464753/250000000000000000)⟩
theorem envelope_sound473 : envelope473.Sound := by
  apply rat_majority_inputs_envelopes inputs473 inputs_valid473
  · norm_num [envelope473]
  · intro rho hr0 hr1
    have hh := Batch023.bound946 rho hr0 hr1
    norm_num [Batch023.certificate946,envelope473,inputs473,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch023.bound947 rho hr0 hr1
    norm_num [Batch023.certificate947,envelope473,inputs473,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs474 : RatMajorityInputs := ⟨(18095364136995468409368217/25000000000000000000000),(237527825294479/50000000000000),(251039527194461451/250000000000000000),(73647438312467309/500000000000000000),(237527825294479/100000000000000),(5811788203475503/62500000000000000),26⟩
theorem inputs_valid474 : inputs474.Valid := by decide +kernel
def envelope474 : RatMajorityEnvelope := ⟨237,0,inputs474,(2349139771/2062820000),(665531169852599333/1000000000000000000)⟩
theorem envelope_sound474 : envelope474.Sound := by
  apply rat_majority_inputs_envelopes inputs474 inputs_valid474
  · norm_num [envelope474]
  · intro rho hr0 hr1
    have hh := Batch023.bound948 rho hr0 hr1
    norm_num [Batch023.certificate948,envelope474,inputs474,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch023.bound949 rho hr0 hr1
    norm_num [Batch023.certificate949,envelope474,inputs474,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs475 : RatMajorityInputs := ⟨(18095364136995468409368217/25000000000000000000000),(52404501117089/10000000000000),(251039527194461451/250000000000000000),(5290351017911081/50000000000000000),(52404501117089/20000000000000),(72786479960534763/1000000000000000000),27⟩
theorem inputs_valid475 : inputs475.Valid := by decide +kernel
def envelope475 : RatMajorityEnvelope := ⟨237,1,inputs475,1,(539684419916150699/1000000000000000000)⟩
theorem envelope_sound475 : envelope475.Sound := by
  apply rat_majority_inputs_envelopes inputs475 inputs_valid475
  · norm_num [envelope475]
  · intro rho hr0 hr1
    have hh := Batch023.bound950 rho hr0 hr1
    norm_num [Batch023.certificate950,envelope475,inputs475,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch023.bound951 rho hr0 hr1
    norm_num [Batch023.certificate951,envelope475,inputs475,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs476 : RatMajorityInputs := ⟨(71735034995709416547190531/100000000000000000000000),(47640444286773/10000000000000),(502097850350640981/500000000000000000),(912399888820987/6250000000000000),(47640444286773/20000000000000),(4618180475692401/50000000000000000),26⟩
theorem inputs_valid476 : inputs476.Valid := by decide +kernel
def envelope476 : RatMajorityEnvelope := ⟨238,0,inputs476,(586173133/515517500),(663871736754526731/1000000000000000000)⟩
theorem envelope_sound476 : envelope476.Sound := by
  apply rat_majority_inputs_envelopes inputs476 inputs_valid476
  · norm_num [envelope476]
  · intro rho hr0 hr1
    have hh := Batch023.bound952 rho hr0 hr1
    norm_num [Batch023.certificate952,envelope476,inputs476,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch023.bound953 rho hr0 hr1
    norm_num [Batch023.certificate953,envelope476,inputs476,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs477 : RatMajorityInputs := ⟨(71735034995709416547190531/100000000000000000000000),(524846559758059/100000000000000),(502097850350640981/500000000000000000),(52612684792171983/500000000000000000),(524846559758059/200000000000000),(14499070845573789/200000000000000000),27⟩
theorem inputs_valid477 : inputs477.Valid := by decide +kernel
def envelope477 : RatMajorityEnvelope := ⟨238,1,inputs477,1,(26982192714536241/50000000000000000)⟩
theorem envelope_sound477 : envelope477.Sound := by
  apply rat_majority_inputs_envelopes inputs477 inputs_valid477
  · norm_num [envelope477]
  · intro rho hr0 hr1
    have hh := Batch023.bound954 rho hr0 hr1
    norm_num [Batch023.certificate954,envelope477,inputs477,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch023.bound955 rho hr0 hr1
    norm_num [Batch023.certificate955,envelope477,inputs477,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs478 : RatMajorityInputs := ⟨(3555301229541073874435849/5000000000000000000000),(1490609142553/312500000000),(200846587676723613/200000000000000000),(1163306480472391/8000000000000000),(1490609142553/625000000000),(92091316082702569/1000000000000000000),26⟩
theorem inputs_valid478 : inputs478.Valid := by decide +kernel
def envelope478 : RatMajorityEnvelope := ⟨239,0,inputs478,(292775623/257668750),(66311529739928901/100000000000000000)⟩
theorem envelope_sound478 : envelope478.Sound := by
  apply rat_majority_inputs_envelopes inputs478 inputs_valid478
  · norm_num [envelope478]
  · intro rho hr0 hr1
    have hh := Batch023.bound956 rho hr0 hr1
    norm_num [Batch023.certificate956,envelope478,inputs478,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch023.bound957 rho hr0 hr1
    norm_num [Batch023.certificate957,envelope478,inputs478,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs479 : RatMajorityInputs := ⟨(3555301229541073874435849/5000000000000000000000),(1051551981757/200000000000),(200846587676723613/200000000000000000),(52277261460313193/500000000000000000),(1051551981757/400000000000),(36079619315984833/500000000000000000),28⟩
theorem inputs_valid479 : inputs479.Valid := by decide +kernel
def envelope479 : RatMajorityEnvelope := ⟨239,1,inputs479,1,(539594315969969431/1000000000000000000)⟩
theorem envelope_sound479 : envelope479.Sound := by
  apply rat_majority_inputs_envelopes inputs479 inputs_valid479
  · norm_num [envelope479]
  · intro rho hr0 hr1
    have hh := Batch023.bound958 rho hr0 hr1
    norm_num [Batch023.certificate958,envelope479,inputs479,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch023.bound959 rho hr0 hr1
    norm_num [Batch023.certificate959,envelope479,inputs479,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def configurations : List RatMajorityEnvelope := [envelope460,envelope461,envelope462,envelope463,envelope464,envelope465,envelope466,envelope467,envelope468,envelope469,envelope470,envelope471,envelope472,envelope473,envelope474,envelope475,envelope476,envelope477,envelope478,envelope479]
theorem configurations_sound : ∀ s∈configurations, s.Sound := by
  intro s hs
  simp only [configurations,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact envelope_sound460
  · exact envelope_sound461
  · exact envelope_sound462
  · exact envelope_sound463
  · exact envelope_sound464
  · exact envelope_sound465
  · exact envelope_sound466
  · exact envelope_sound467
  · exact envelope_sound468
  · exact envelope_sound469
  · exact envelope_sound470
  · exact envelope_sound471
  · exact envelope_sound472
  · exact envelope_sound473
  · exact envelope_sound474
  · exact envelope_sound475
  · exact envelope_sound476
  · exact envelope_sound477
  · exact envelope_sound478
  · exact envelope_sound479

end Cycle12.MajorityCertificates.Inputs023
