import Cycle12.RationalMajorityInputs
import Cycle12.MajorityCertificates.Batch002

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Inputs002

def inputs40 : RatMajorityInputs := ⟨(26773669259310837148893843/12500000000000000000000),(83279938512967/20000000000000),(1001402157180979839/1000000000000000000),(107522427403203859/500000000000000000),(83279938512967/40000000000000),(124680793124273023/1000000000000000000),25⟩
theorem inputs_valid40 : inputs40.Valid := by decide +kernel
def envelope40 : RatMajorityEnvelope := ⟨20,0,inputs40,(2560826323/2156090000),(714451181226179937/1000000000000000000)⟩
theorem envelope_sound40 : envelope40.Sound := by
  apply rat_majority_inputs_envelopes inputs40 inputs_valid40
  · norm_num [envelope40]
  · intro rho hr0 hr1
    have hh := Batch002.bound80 rho hr0 hr1
    norm_num [Batch002.certificate80,envelope40,inputs40,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch002.bound81 rho hr0 hr1
    norm_num [Batch002.certificate81,envelope40,inputs40,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs41 : RatMajorityInputs := ⟨(26773669259310837148893843/12500000000000000000000),(49650151388331/10000000000000),(1001402157180979839/1000000000000000000),(25525938083340001/200000000000000000),(49650151388331/20000000000000),(2088337417640621/25000000000000000),27⟩
theorem inputs_valid41 : inputs41.Valid := by decide +kernel
def envelope41 : RatMajorityEnvelope := ⟨20,1,inputs41,1,(540668774190226511/1000000000000000000)⟩
theorem envelope_sound41 : envelope41.Sound := by
  apply rat_majority_inputs_envelopes inputs41 inputs_valid41
  · norm_num [envelope41]
  · intro rho hr0 hr1
    have hh := Batch002.bound82 rho hr0 hr1
    norm_num [Batch002.certificate82,envelope41,inputs41,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch002.bound83 rho hr0 hr1
    norm_num [Batch002.certificate83,envelope41,inputs41,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs42 : RatMajorityInputs := ⟨(196854897118310236261413603/100000000000000000000000),(103931022595849/25000000000000),(1001525773469427903/1000000000000000000),(21595695640536701/100000000000000000),(103931022595849/50000000000000),(125102678368666967/1000000000000000000),26⟩
theorem inputs_valid42 : inputs42.Valid := by decide +kernel
def envelope42 : RatMajorityEnvelope := ⟨21,0,inputs42,(1277329181/1073755000),(716294502186056659/1000000000000000000)⟩
theorem envelope_sound42 : envelope42.Sound := by
  apply rat_majority_inputs_envelopes inputs42 inputs_valid42
  · norm_num [envelope42]
  · intro rho hr0 hr1
    have hh := Batch002.bound84 rho hr0 hr1
    norm_num [Batch002.certificate84,envelope42,inputs42,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch002.bound85 rho hr0 hr1
    norm_num [Batch002.certificate85,envelope42,inputs42,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs43 : RatMajorityInputs := ⟨(196854897118310236261413603/100000000000000000000000),(495881134448389/100000000000000),(1001525773469427903/1000000000000000000),(64082123929979743/500000000000000000),(495881134448389/200000000000000),(83793011308765653/1000000000000000000),26⟩
theorem inputs_valid43 : inputs43.Valid := by decide +kernel
def envelope43 : RatMajorityEnvelope := ⟨21,1,inputs43,1,(270391485148936349/500000000000000000)⟩
theorem envelope_sound43 : envelope43.Sound := by
  apply rat_majority_inputs_envelopes inputs43 inputs_valid43
  · norm_num [envelope43]
  · intro rho hr0 hr1
    have hh := Batch002.bound86 rho hr0 hr1
    norm_num [Batch002.certificate86,envelope43,inputs43,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch002.bound87 rho hr0 hr1
    norm_num [Batch002.certificate87,envelope43,inputs43,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs44 : RatMajorityInputs := ⟨(11352226535966693939898427/6250000000000000000000),(414739194334703/100000000000000),(6260336141479543/6250000000000000),(43458472552792431/200000000000000000),(414739194334703/200000000000000),(125720263431355959/1000000000000000000),25⟩
theorem inputs_valid44 : inputs44.Valid := by decide +kernel
def envelope44 : RatMajorityEnvelope := ⟨22,0,inputs44,(318377779/267391250),(717482122458769771/1000000000000000000)⟩
theorem envelope_sound44 : envelope44.Sound := by
  apply rat_majority_inputs_envelopes inputs44 inputs_valid44
  · norm_num [envelope44]
  · intro rho hr0 hr1
    have hh := Batch002.bound88 rho hr0 hr1
    norm_num [Batch002.certificate88,envelope44,inputs44,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch002.bound89 rho hr0 hr1
    norm_num [Batch002.certificate89,envelope44,inputs44,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs45 : RatMajorityInputs := ⟨(11352226535966693939898427/6250000000000000000000),(123937561882477/25000000000000),(6260336141479543/6250000000000000),(128277281210955061/1000000000000000000),(123937561882477/50000000000000),(41923933150756253/500000000000000000),27⟩
theorem inputs_valid45 : inputs45.Valid := by decide +kernel
def envelope45 : RatMajorityEnvelope := ⟨22,1,inputs45,1,(540853845065016211/1000000000000000000)⟩
theorem envelope_sound45 : envelope45.Sound := by
  apply rat_majority_inputs_envelopes inputs45 inputs_valid45
  · norm_num [envelope45]
  · intro rho hr0 hr1
    have hh := Batch002.bound90 rho hr0 hr1
    norm_num [Batch002.certificate90,envelope45,inputs45,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch002.bound91 rho hr0 hr1
    norm_num [Batch002.certificate91,envelope45,inputs45,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs46 : RatMajorityInputs := ⟨(21025243652564394653580651/12500000000000000000000),(25842730022811/6250000000000),(500893023828301289/500000000000000000),(21900459753860577/100000000000000000),(25842730022811/12500000000000),(25302392708575191/200000000000000000),25⟩
theorem inputs_valid46 : inputs46.Valid := by decide +kernel
def envelope46 : RatMajorityEnvelope := ⟨23,0,inputs46,(635398141/532740000),(719543974697637517/1000000000000000000)⟩
theorem envelope_sound46 : envelope46.Sound := by
  apply rat_majority_inputs_envelopes inputs46 inputs_valid46
  · norm_num [envelope46]
  · intro rho hr0 hr1
    have hh := Batch002.bound92 rho hr0 hr1
    norm_num [Batch002.certificate92,envelope46,inputs46,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch002.bound93 rho hr0 hr1
    norm_num [Batch002.certificate93,envelope46,inputs46,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs47 : RatMajorityInputs := ⟨(21025243652564394653580651/12500000000000000000000),(61899473020671/12500000000000),(500893023828301289/500000000000000000),(64378546580434863/500000000000000000),(61899473020671/25000000000000),(42040320833124953/500000000000000000),26⟩
theorem inputs_valid47 : inputs47.Valid := by decide +kernel
def envelope47 : RatMajorityEnvelope := ⟨23,1,inputs47,1,(108193218147927273/200000000000000000)⟩
theorem envelope_sound47 : envelope47.Sound := by
  apply rat_majority_inputs_envelopes inputs47 inputs_valid47
  · norm_num [envelope47]
  · intro rho hr0 hr1
    have hh := Batch002.bound94 rho hr0 hr1
    norm_num [Batch002.certificate94,envelope47,inputs47,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch002.bound95 rho hr0 hr1
    norm_num [Batch002.certificate95,envelope47,inputs47,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs48 : RatMajorityInputs := ⟨(156285509123011813420557/100000000000000000000),(516188001197/125000000000),(500961216797485949/500000000000000000),(219735236008387629/1000000000000000000),(516188001197/250000000000),(126849744796937853/1000000000000000000),25⟩
theorem inputs_valid48 : inputs48.Valid := by decide +kernel
def envelope48 : RatMajorityEnvelope := ⟨24,0,inputs48,(13139629/11000000),(90165445508105207/125000000000000000)⟩
theorem envelope_sound48 : envelope48.Sound := by
  apply rat_majority_inputs_envelopes inputs48 inputs_valid48
  · norm_num [envelope48]
  · intro rho hr0 hr1
    have hh := Batch002.bound96 rho hr0 hr1
    norm_num [Batch002.certificate96,envelope48,inputs48,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch002.bound97 rho hr0 hr1
    norm_num [Batch002.certificate97,envelope48,inputs48,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs49 : RatMajorityInputs := ⟨(156285509123011813420557/100000000000000000000),(247293198823/50000000000),(500961216797485949/500000000000000000),(64643133035199377/500000000000000000),(247293198823/100000000000),(4216861020233241/50000000000000000),26⟩
theorem inputs_valid49 : inputs49.Valid := by decide +kernel
def envelope49 : RatMajorityEnvelope := ⟨24,1,inputs49,1,(270542763937645347/500000000000000000)⟩
theorem envelope_sound49 : envelope49.Sound := by
  apply rat_majority_inputs_envelopes inputs49 inputs_valid49
  · norm_num [envelope49]
  · intro rho hr0 hr1
    have hh := Batch002.bound98 rho hr0 hr1
    norm_num [Batch002.certificate98,envelope49,inputs49,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch002.bound99 rho hr0 hr1
    norm_num [Batch002.certificate99,envelope49,inputs49,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs50 : RatMajorityInputs := ⟨(9104120338290301490720121/6250000000000000000000),(5176628914359/1250000000000),(50103140545301121/50000000000000000),(1090606748903911/5000000000000000),(5176628914359/2500000000000),(126103590151858377/1000000000000000000),25⟩
theorem inputs_valid50 : inputs50.Valid := by decide +kernel
def envelope50 : RatMajorityEnvelope := ⟨25,0,inputs50,(315990113/264405000),(721760362590110581/1000000000000000000)⟩
theorem envelope_sound50 : envelope50.Sound := by
  apply rat_majority_inputs_envelopes inputs50 inputs_valid50
  · norm_num [envelope50]
  · intro rho hr0 hr1
    have hh := Batch002.bound100 rho hr0 hr1
    norm_num [Batch002.certificate100,envelope50,inputs50,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch002.bound101 rho hr0 hr1
    norm_num [Batch002.certificate101,envelope50,inputs50,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs51 : RatMajorityInputs := ⟨(9104120338290301490720121/6250000000000000000000),(123559681024737/25000000000000),(50103140545301121/50000000000000000),(129589037041779829/1000000000000000000),(123559681024737/50000000000000),(42241978505818577/500000000000000000),26⟩
theorem inputs_valid51 : inputs51.Valid := by decide +kernel
def envelope51 : RatMajorityEnvelope := ⟨25,1,inputs51,1,(33823900852432337/62500000000000000)⟩
theorem envelope_sound51 : envelope51.Sound := by
  apply rat_majority_inputs_envelopes inputs51 inputs_valid51
  · norm_num [envelope51]
  · intro rho hr0 hr1
    have hh := Batch002.bound102 rho hr0 hr1
    norm_num [Batch002.certificate102,envelope51,inputs51,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch002.bound103 rho hr0 hr1
    norm_num [Batch002.certificate103,envelope51,inputs51,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs52 : RatMajorityInputs := ⟨(68080394890121911262409811/50000000000000000000000),(103402309759103/25000000000000),(1002207059086998663/1000000000000000000),(218832863698886999/1000000000000000000),(103402309759103/50000000000000),(63216282549037893/500000000000000000),25⟩
theorem inputs_valid52 : inputs52.Valid := by decide +kernel
def envelope52 : RatMajorityEnvelope := ⟨26,0,inputs52,(2520852341/2107660000),(9034524144343451/12500000000000000)⟩
theorem envelope_sound52 : envelope52.Sound := by
  apply rat_majority_inputs_envelopes inputs52 inputs_valid52
  · norm_num [envelope52]
  · intro rho hr0 hr1
    have hh := Batch002.bound104 rho hr0 hr1
    norm_num [Batch002.certificate104,envelope52,inputs52,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch002.bound105 rho hr0 hr1
    norm_num [Batch002.certificate105,envelope52,inputs52,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs53 : RatMajorityInputs := ⟨(68080394890121911262409811/50000000000000000000000),(30868894480681/6250000000000),(1002207059086998663/1000000000000000000),(64941299220450341/500000000000000000),(30868894480681/12500000000000),(42313091926194217/500000000000000000),26⟩
theorem inputs_valid53 : inputs53.Valid := by decide +kernel
def envelope53 : RatMajorityEnvelope := ⟨26,1,inputs53,1,(54128005773701011/100000000000000000)⟩
theorem envelope_sound53 : envelope53.Sound := by
  apply rat_majority_inputs_envelopes inputs53 inputs_valid53
  · norm_num [envelope53]
  · intro rho hr0 hr1
    have hh := Batch002.bound106 rho hr0 hr1
    norm_num [Batch002.certificate106,envelope53,inputs53,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch002.bound107 rho hr0 hr1
    norm_num [Batch002.certificate107,envelope53,inputs53,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs54 : RatMajorityInputs := ⟨(6381052442669347188497297/5000000000000000000000),(103261742224277/25000000000000),(501177507253027723/500000000000000000),(219602780565144143/1000000000000000000),(103261742224277/50000000000000),(12678851148865273/100000000000000000),25⟩
theorem inputs_valid54 : inputs54.Valid := by decide +kernel
def envelope54 : RatMajorityEnvelope := ⟨27,0,inputs54,(125795333/105014000),(144916974469389171/200000000000000000)⟩
theorem envelope_sound54 : envelope54.Sound := by
  apply rat_majority_inputs_envelopes inputs54 inputs_valid54
  · norm_num [envelope54]
  · intro rho hr0 hr1
    have hh := Batch002.bound108 rho hr0 hr1
    norm_num [Batch002.certificate108,envelope54,inputs54,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch002.bound109 rho hr0 hr1
    norm_num [Batch002.certificate109,envelope54,inputs54,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs55 : RatMajorityInputs := ⟨(6381052442669347188497297/5000000000000000000000),(123394824677397/25000000000000),(501177507253027723/500000000000000000),(8135313796971789/62500000000000000),(123394824677397/50000000000000),(21190742765620199/250000000000000000),27⟩
theorem inputs_valid55 : inputs55.Valid := by decide +kernel
def envelope55 : RatMajorityEnvelope := ⟨27,1,inputs55,1,(135344543945537547/250000000000000000)⟩
theorem envelope_sound55 : envelope55.Sound := by
  apply rat_majority_inputs_envelopes inputs55 inputs_valid55
  · norm_num [envelope55]
  · intro rho hr0 hr1
    have hh := Batch002.bound110 rho hr0 hr1
    norm_num [Batch002.certificate110,envelope55,inputs55,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch002.bound111 rho hr0 hr1
    norm_num [Batch002.certificate111,envelope55,inputs55,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs56 : RatMajorityInputs := ⟨(4796808628674409999628493/4000000000000000000000),(51663188522167/12500000000000),(200501307914580713/200000000000000000),(8769939402860369/40000000000000000),(51663188522167/25000000000000),(126624718326370229/1000000000000000000),25⟩
theorem inputs_valid56 : inputs56.Valid := by decide +kernel
def envelope56 : RatMajorityEnvelope := ⟨28,0,inputs56,(2508916953/2093090000),(725329278994270723/1000000000000000000)⟩
theorem envelope_sound56 : envelope56.Sound := by
  apply rat_majority_inputs_envelopes inputs56 inputs_valid56
  · norm_num [envelope56]
  · intro rho hr0 hr1
    have hh := Batch002.bound112 rho hr0 hr1
    norm_num [Batch002.certificate112,envelope56,inputs56,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch002.bound113 rho hr0 hr1
    norm_num [Batch002.certificate113,envelope56,inputs56,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs57 : RatMajorityInputs := ⟨(4796808628674409999628493/4000000000000000000000),(246622637038529/50000000000000),(200501307914580713/200000000000000000),(16307205273710247/125000000000000000),(246622637038529/100000000000000),(21226163486196471/250000000000000000),26⟩
theorem inputs_valid57 : inputs57.Valid := by decide +kernel
def envelope57 : RatMajorityEnvelope := ⟨28,1,inputs57,1,(27073949976986831/50000000000000000)⟩
theorem envelope_sound57 : envelope57.Sound := by
  apply rat_majority_inputs_envelopes inputs57 inputs_valid57
  · norm_num [envelope57]
  · intro rho hr0 hr1
    have hh := Batch002.bound114 rho hr0 hr1
    norm_num [Batch002.certificate114,envelope57,inputs57,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch002.bound115 rho hr0 hr1
    norm_num [Batch002.certificate115,envelope57,inputs57,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs58 : RatMajorityInputs := ⟨(3521725422925756269410757/3125000000000000000000),(41211432283617/10000000000000),(200533513923474379/200000000000000000),(13805299116816367/62500000000000000),(41211432283617/20000000000000),(63690568108294027/500000000000000000),25⟩
theorem inputs_valid58 : inputs58.Valid := by decide +kernel
def envelope58 : RatMajorityEnvelope := ⟨29,0,inputs58,(26860951/22380000),(726985747200879771/1000000000000000000)⟩
theorem envelope_sound58 : envelope58.Sound := by
  apply rat_majority_inputs_envelopes inputs58 inputs_valid58
  · norm_num [envelope58]
  · intro rho hr0 hr1
    have hh := Batch002.bound116 rho hr0 hr1
    norm_num [Batch002.certificate116,envelope58,inputs58,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch002.bound117 rho hr0 hr1
    norm_num [Batch002.certificate117,envelope58,inputs58,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs59 : RatMajorityInputs := ⟨(3521725422925756269410757/3125000000000000000000),(246334226164929/50000000000000),(200533513923474379/200000000000000000),(818527096893163/6250000000000000),(246334226164929/100000000000000),(42574940830334293/500000000000000000),26⟩
theorem inputs_valid59 : inputs59.Valid := by decide +kernel
def envelope59 : RatMajorityEnvelope := ⟨29,1,inputs59,1,(27080359254875241/50000000000000000)⟩
theorem envelope_sound59 : envelope59.Sound := by
  apply rat_majority_inputs_envelopes inputs59 inputs_valid59
  · norm_num [envelope59]
  · intro rho hr0 hr1
    have hh := Batch002.bound118 rho hr0 hr1
    norm_num [Batch002.certificate118,envelope59,inputs59,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch002.bound119 rho hr0 hr1
    norm_num [Batch002.certificate119,envelope59,inputs59,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def configurations : List RatMajorityEnvelope := [envelope40,envelope41,envelope42,envelope43,envelope44,envelope45,envelope46,envelope47,envelope48,envelope49,envelope50,envelope51,envelope52,envelope53,envelope54,envelope55,envelope56,envelope57,envelope58,envelope59]
theorem configurations_sound : ∀ s∈configurations, s.Sound := by
  intro s hs
  simp only [configurations,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact envelope_sound40
  · exact envelope_sound41
  · exact envelope_sound42
  · exact envelope_sound43
  · exact envelope_sound44
  · exact envelope_sound45
  · exact envelope_sound46
  · exact envelope_sound47
  · exact envelope_sound48
  · exact envelope_sound49
  · exact envelope_sound50
  · exact envelope_sound51
  · exact envelope_sound52
  · exact envelope_sound53
  · exact envelope_sound54
  · exact envelope_sound55
  · exact envelope_sound56
  · exact envelope_sound57
  · exact envelope_sound58
  · exact envelope_sound59

end Cycle12.MajorityCertificates.Inputs002
