import Cycle12.RationalMajorityInputs
import Cycle12.MajorityCertificates.Batch029

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Inputs029

def inputs580 : RatMajorityInputs := ⟨(8864654274377408447843943/3125000000000000000000),(228759654385971/50000000000000),(1001058441422900177/1000000000000000000),(4132385862153463/25000000000000000),(228759654385971/100000000000000),(25377536018973343/250000000000000000),25⟩
theorem inputs_valid580 : inputs580.Valid := by decide +kernel
def envelope580 : RatMajorityEnvelope := ⟨290,0,inputs580,(2614303031/2211780000),(176072777729745311/250000000000000000)⟩
theorem envelope_sound580 : envelope580.Sound := by
  apply rat_majority_inputs_envelopes inputs580 inputs_valid580
  · norm_num [envelope580]
  · intro rho hr0 hr1
    have hh := Batch029.bound1160 rho hr0 hr1
    norm_num [Batch029.certificate1160,envelope580,inputs580,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch029.bound1161 rho hr0 hr1
    norm_num [Batch029.certificate1161,envelope580,inputs580,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs581 : RatMajorityInputs := ⟨(8864654274377408447843943/3125000000000000000000),(241347886570479/50000000000000),(1001058441422900177/1000000000000000000),(70001731238496887/500000000000000000),(241347886570479/100000000000000),(89503382089590887/1000000000000000000),26⟩
theorem inputs_valid581 : inputs581.Valid := by decide +kernel
def envelope581 : RatMajorityEnvelope := ⟨290,1,inputs581,1,(270931957883717347/500000000000000000)⟩
theorem envelope_sound581 : envelope581.Sound := by
  apply rat_majority_inputs_envelopes inputs581 inputs_valid581
  · norm_num [envelope581]
  · intro rho hr0 hr1
    have hh := Batch029.bound1162 rho hr0 hr1
    norm_num [Batch029.certificate1162,envelope581,inputs581,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch029.bound1163 rho hr0 hr1
    norm_num [Batch029.certificate1163,envelope581,inputs581,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs582 : RatMajorityInputs := ⟨(55881410266118401773298951/20000000000000000000000),(91634276802541/20000000000000),(1001074599661654149/1000000000000000000),(41148370216171769/250000000000000000),(91634276802541/40000000000000),(101179721760929463/1000000000000000000),27⟩
theorem inputs_valid582 : inputs582.Valid := by decide +kernel
def envelope582 : RatMajorityEnvelope := ⟨291,0,inputs582,(2611196259/2210710000),(703484329590074171/1000000000000000000)⟩
theorem envelope_sound582 : envelope582.Sound := by
  apply rat_majority_inputs_envelopes inputs582 inputs_valid582
  · norm_num [envelope582]
  · intro rho hr0 hr1
    have hh := Batch029.bound1164 rho hr0 hr1
    norm_num [Batch029.certificate1164,envelope582,inputs582,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch029.bound1165 rho hr0 hr1
    norm_num [Batch029.certificate1165,envelope582,inputs582,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs583 : RatMajorityInputs := ⟨(55881410266118401773298951/20000000000000000000000),(24144447669297/5000000000000),(1001074599661654149/1000000000000000000),(27964655969106741/200000000000000000),(24144447669297/10000000000000),(44708486200763419/500000000000000000),28⟩
theorem inputs_valid583 : inputs583.Valid := by decide +kernel
def envelope583 : RatMajorityEnvelope := ⟨291,1,inputs583,1,(541851220863881377/1000000000000000000)⟩
theorem envelope_sound583 : envelope583.Sound := by
  apply rat_majority_inputs_envelopes inputs583 inputs_valid583
  · norm_num [envelope583]
  · intro rho hr0 hr1
    have hh := Batch029.bound1166 rho hr0 hr1
    norm_num [Batch029.certificate1166,envelope583,inputs583,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch029.bound1167 rho hr0 hr1
    norm_num [Batch029.certificate1167,envelope583,inputs583,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs584 : RatMajorityInputs := ⟨(11010919799169020364720951/4000000000000000000000),(91795800494211/20000000000000),(250272687928524241/250000000000000000),(16372765439347007/100000000000000000),(91795800494211/40000000000000),(12596496565624759/125000000000000000),26⟩
theorem inputs_valid584 : inputs584.Valid := by decide +kernel
def envelope584 : RatMajorityEnvelope := ⟨292,0,inputs584,(2608086479/2209650000),(702656229126413793/1000000000000000000)⟩
theorem envelope_sound584 : envelope584.Sound := by
  apply rat_majority_inputs_envelopes inputs584 inputs_valid584
  · norm_num [envelope584]
  · intro rho hr0 hr1
    have hh := Batch029.bound1168 rho hr0 hr1
    norm_num [Batch029.certificate1168,envelope584,inputs584,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch029.bound1169 rho hr0 hr1
    norm_num [Batch029.certificate1169,envelope584,inputs584,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs585 : RatMajorityInputs := ⟨(11010919799169020364720951/4000000000000000000000),(48381104895009/10000000000000),(250272687928524241/250000000000000000),(69483015016537663/500000000000000000),(48381104895009/20000000000000),(89005666320829529/1000000000000000000),26⟩
theorem inputs_valid585 : inputs585.Valid := by decide +kernel
def envelope585 : RatMajorityEnvelope := ⟨292,1,inputs585,1,(541763499188655521/1000000000000000000)⟩
theorem envelope_sound585 : envelope585.Sound := by
  apply rat_majority_inputs_envelopes inputs585 inputs_valid585
  · norm_num [envelope585]
  · intro rho hr0 hr1
    have hh := Batch029.bound1170 rho hr0 hr1
    norm_num [Batch029.certificate1170,envelope585,inputs585,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch029.bound1171 rho hr0 hr1
    norm_num [Batch029.certificate1171,envelope585,inputs585,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs586 : RatMajorityInputs := ⟨(135632214694640043674321767/50000000000000000000000),(228198709095533/50000000000000),(20022137679862257/20000000000000000),(166509184678675083/1000000000000000000),(228198709095533/100000000000000),(25520290123991077/250000000000000000),25⟩
theorem inputs_valid586 : inputs586.Valid := by decide +kernel
def envelope586 : RatMajorityEnvelope := ⟨293,0,inputs586,(1303102279/1104310000),(70264293069667101/100000000000000000)⟩
theorem envelope_sound586 : envelope586.Sound := by
  apply rat_majority_inputs_envelopes inputs586 inputs_valid586
  · norm_num [envelope586]
  · intro rho hr0 hr1
    have hh := Batch029.bound1172 rho hr0 hr1
    norm_num [Batch029.certificate1172,envelope586,inputs586,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch029.bound1173 rho hr0 hr1
    norm_num [Batch029.certificate1173,envelope586,inputs586,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs587 : RatMajorityInputs := ⟨(135632214694640043674321767/50000000000000000000000),(121001141806391/25000000000000),(20022137679862257/20000000000000000),(34696677133738987/250000000000000000),(121001141806391/50000000000000),(17783917371429941/200000000000000000),26⟩
theorem inputs_valid587 : inputs587.Valid := by decide +kernel
def envelope587 : RatMajorityEnvelope := ⟨293,1,inputs587,1,(135437738085712947/250000000000000000)⟩
theorem envelope_sound587 : envelope587.Sound := by
  apply rat_majority_inputs_envelopes inputs587 inputs_valid587
  · norm_num [envelope587]
  · intro rho hr0 hr1
    have hh := Batch029.bound1174 rho hr0 hr1
    norm_num [Batch029.certificate1174,envelope587,inputs587,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch029.bound1175 rho hr0 hr1
    norm_num [Batch029.certificate1175,envelope587,inputs587,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs588 : RatMajorityInputs := ⟨(6684326351066391211864911/2500000000000000000000),(460795540593003/100000000000000),(12514037597092049/12500000000000000),(161794557606517229/1000000000000000000),(460795540593003/200000000000000),(99860835926032371/1000000000000000000),26⟩
theorem inputs_valid588 : inputs588.Valid := by decide +kernel
def envelope588 : RatMajorityEnvelope := ⟨294,0,inputs588,(2601879037/2207590000),(700956362445595957/1000000000000000000)⟩
theorem envelope_sound588 : envelope588.Sound := by
  apply rat_majority_inputs_envelopes inputs588 inputs_valid588
  · norm_num [envelope588]
  · intro rho hr0 hr1
    have hh := Batch029.bound1176 rho hr0 hr1
    norm_num [Batch029.certificate1176,envelope588,inputs588,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch029.bound1177 rho hr0 hr1
    norm_num [Batch029.certificate1177,envelope588,inputs588,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs589 : RatMajorityInputs := ⟨(6684326351066391211864911/2500000000000000000000),(48487443402167/10000000000000),(12514037597092049/12500000000000000),(8623947953786319/62500000000000000),(48487443402167/20000000000000),(44266842845677679/500000000000000000),27⟩
theorem inputs_valid589 : inputs589.Valid := by decide +kernel
def envelope589 : RatMajorityEnvelope := ⟨294,1,inputs589,1,(541669420172137427/1000000000000000000)⟩
theorem envelope_sound589 : envelope589.Sound := by
  apply rat_majority_inputs_envelopes inputs589 inputs_valid589
  · norm_num [envelope589]
  · intro rho hr0 hr1
    have hh := Batch029.bound1178 rho hr0 hr1
    norm_num [Batch029.certificate1178,envelope589,inputs589,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch029.bound1179 rho hr0 hr1
    norm_num [Batch029.certificate1179,envelope589,inputs589,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs590 : RatMajorityInputs := ⟨(131799078795259669291588257/50000000000000000000000),(230842691542317/50000000000000),(1001139104212702707/1000000000000000000),(160854842102593353/1000000000000000000),(230842691542317/100000000000000),(49708760391839403/500000000000000000),26⟩
theorem inputs_valid590 : inputs590.Valid := by decide +kernel
def envelope590 : RatMajorityEnvelope := ⟨295,0,inputs590,(2598819493/2206590000),(87513954149018631/125000000000000000)⟩
theorem envelope_sound590 : envelope590.Sound := by
  apply rat_majority_inputs_envelopes inputs590 inputs_valid590
  · norm_num [envelope590]
  · intro rho hr0 hr1
    have hh := Batch029.bound1180 rho hr0 hr1
    norm_num [Batch029.certificate1180,envelope590,inputs590,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch029.bound1181 rho hr0 hr1
    norm_num [Batch029.certificate1181,envelope590,inputs590,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs591 : RatMajorityInputs := ⟨(131799078795259669291588257/50000000000000000000000),(242533538557407/50000000000000),(1001139104212702707/1000000000000000000),(137805767374759209/1000000000000000000),(242533538557407/100000000000000),(17689689946589397/200000000000000000),26⟩
theorem inputs_valid591 : inputs591.Valid := by decide +kernel
def envelope591 : RatMajorityEnvelope := ⟨295,1,inputs591,1,(541657130056756421/1000000000000000000)⟩
theorem envelope_sound591 : envelope591.Sound := by
  apply rat_majority_inputs_envelopes inputs591 inputs_valid591
  · norm_num [envelope591]
  · intro rho hr0 hr1
    have hh := Batch029.bound1182 rho hr0 hr1
    norm_num [Batch029.certificate1182,envelope591,inputs591,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch029.bound1183 rho hr0 hr1
    norm_num [Batch029.certificate1183,envelope591,inputs591,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs592 : RatMajorityInputs := ⟨(254842476808798682750061111/100000000000000000000000),(462406111916257/100000000000000),(500589138267680531/500000000000000000),(8004859233844407/50000000000000000),(462406111916257/200000000000000),(24764975042855007/250000000000000000),26⟩
theorem inputs_valid592 : inputs592.Valid := by decide +kernel
def envelope592 : RatMajorityEnvelope := ⟨296,0,inputs592,(2592284867/2203790000),(698739681585178127/1000000000000000000)⟩
theorem envelope_sound592 : envelope592.Sound := by
  apply rat_majority_inputs_envelopes inputs592 inputs_valid592
  · norm_num [envelope592]
  · intro rho hr0 hr1
    have hh := Batch029.bound1184 rho hr0 hr1
    norm_num [Batch029.certificate1184,envelope592,inputs592,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch029.bound1185 rho hr0 hr1
    norm_num [Batch029.certificate1185,envelope592,inputs592,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs593 : RatMajorityInputs := ⟨(254842476808798682750061111/100000000000000000000000),(97026976578339/20000000000000),(500589138267680531/500000000000000000),(13774337461167837/100000000000000000),(97026976578339/40000000000000),(88418468236290529/1000000000000000000),26⟩
theorem inputs_valid593 : inputs593.Valid := by decide +kernel
def envelope593 : RatMajorityEnvelope := ⟨296,1,inputs593,1,(67708500607370811/125000000000000000)⟩
theorem envelope_sound593 : envelope593.Sound := by
  apply rat_majority_inputs_envelopes inputs593 inputs_valid593
  · norm_num [envelope593]
  · intro rho hr0 hr1
    have hh := Batch029.bound1186 rho hr0 hr1
    norm_num [Batch029.certificate1186,envelope593,inputs593,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch029.bound1187 rho hr0 hr1
    norm_num [Batch029.certificate1187,envelope593,inputs593,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs594 : RatMajorityInputs := ⟨(126459733025690510895174523/50000000000000000000000),(466101139746417/100000000000000),(250296810885410091/250000000000000000),(39065301554912579/250000000000000000),(466101139746417/200000000000000),(1944931143845499/20000000000000000),26⟩
theorem inputs_valid594 : inputs594.Valid := by decide +kernel
def envelope594 : RatMajorityEnvelope := ⟨297,0,inputs594,(2587448847/2203670000),(34824010613830009/50000000000000000)⟩
theorem envelope_sound594 : envelope594.Sound := by
  apply rat_majority_inputs_envelopes inputs594 inputs_valid594
  · norm_num [envelope594]
  · intro rho hr0 hr1
    have hh := Batch029.bound1188 rho hr0 hr1
    norm_num [Batch029.certificate1188,envelope594,inputs594,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch029.bound1189 rho hr0 hr1
    norm_num [Batch029.certificate1189,envelope594,inputs594,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs595 : RatMajorityInputs := ⟨(126459733025690510895174523/50000000000000000000000),(486526467761677/100000000000000),(250296810885410091/250000000000000000),(6823418072256363/50000000000000000),(486526467761677/200000000000000),(87805394556687223/1000000000000000000),26⟩
theorem inputs_valid595 : inputs595.Valid := by decide +kernel
def envelope595 : RatMajorityEnvelope := ⟨297,1,inputs595,1,(270765805377105911/500000000000000000)⟩
theorem envelope_sound595 : envelope595.Sound := by
  apply rat_majority_inputs_envelopes inputs595 inputs_valid595
  · norm_num [envelope595]
  · intro rho hr0 hr1
    have hh := Batch029.bound1190 rho hr0 hr1
    norm_num [Batch029.certificate1190,envelope595,inputs595,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch029.bound1191 rho hr0 hr1
    norm_num [Batch029.certificate1191,envelope595,inputs595,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs596 : RatMajorityInputs := ⟨(249563387125349396345324603/100000000000000000000000),(465714344299667/100000000000000),(1001203224296483923/1000000000000000000),(31331796642584611/200000000000000000),(465714344299667/200000000000000),(24358702950333131/250000000000000000),26⟩
theorem inputs_valid596 : inputs596.Valid := by decide +kernel
def envelope596 : RatMajorityEnvelope := ⟨298,0,inputs596,(646209473/550682500),(17397661652873903/25000000000000000)⟩
theorem envelope_sound596 : envelope596.Sound := by
  apply rat_majority_inputs_envelopes inputs596 inputs_valid596
  · norm_num [envelope596]
  · intro rho hr0 hr1
    have hh := Batch029.bound1192 rho hr0 hr1
    norm_num [Batch029.certificate1192,envelope596,inputs596,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch029.bound1193 rho hr0 hr1
    norm_num [Batch029.certificate1193,envelope596,inputs596,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs597 : RatMajorityInputs := ⟨(249563387125349396345324603/100000000000000000000000),(487380912459033/100000000000000),(1001203224296483923/1000000000000000000),(135690653335733567/1000000000000000000),(487380912459033/200000000000000),(4371553522762427/50000000000000000),26⟩
theorem inputs_valid597 : inputs597.Valid := by decide +kernel
def envelope597 : RatMajorityEnvelope := ⟨298,1,inputs597,1,(541453419687024859/1000000000000000000)⟩
theorem envelope_sound597 : envelope597.Sound := by
  apply rat_majority_inputs_envelopes inputs597 inputs_valid597
  · norm_num [envelope597]
  · intro rho hr0 hr1
    have hh := Batch029.bound1194 rho hr0 hr1
    norm_num [Batch029.certificate1194,envelope597,inputs597,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch029.bound1195 rho hr0 hr1
    norm_num [Batch029.certificate1195,envelope597,inputs597,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs598 : RatMajorityInputs := ⟨(241650020087854068068065401/100000000000000000000000),(466479592178607/100000000000000),(31288833269612019/31250000000000000),(155872858354732877/1000000000000000000),(466479592178607/200000000000000),(97062715205291371/1000000000000000000),26⟩
theorem inputs_valid598 : inputs598.Valid := by decide +kernel
def envelope598 : RatMajorityEnvelope := ⟨299,0,inputs598,(23021617/19643125),(347263098407813301/500000000000000000)⟩
theorem envelope_sound598 : envelope598.Sound := by
  apply rat_majority_inputs_envelopes inputs598 inputs_valid598
  · norm_num [envelope598]
  · intro rho hr0 hr1
    have hh := Batch029.bound1196 rho hr0 hr1
    norm_num [Batch029.certificate1196,envelope598,inputs598,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch029.bound1197 rho hr0 hr1
    norm_num [Batch029.certificate1197,envelope598,inputs598,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs599 : RatMajorityInputs := ⟨(241650020087854068068065401/100000000000000000000000),(243747032117841/50000000000000),(31288833269612019/31250000000000000),(8474247309842029/62500000000000000),(243747032117841/100000000000000),(21845404885108267/250000000000000000),26⟩
theorem inputs_valid599 : inputs599.Valid := by decide +kernel
def envelope599 : RatMajorityEnvelope := ⟨299,1,inputs599,1,(84603137347941/156250000000000)⟩
theorem envelope_sound599 : envelope599.Sound := by
  apply rat_majority_inputs_envelopes inputs599 inputs_valid599
  · norm_num [envelope599]
  · intro rho hr0 hr1
    have hh := Batch029.bound1198 rho hr0 hr1
    norm_num [Batch029.certificate1198,envelope599,inputs599,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch029.bound1199 rho hr0 hr1
    norm_num [Batch029.certificate1199,envelope599,inputs599,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def configurations : List RatMajorityEnvelope := [envelope580,envelope581,envelope582,envelope583,envelope584,envelope585,envelope586,envelope587,envelope588,envelope589,envelope590,envelope591,envelope592,envelope593,envelope594,envelope595,envelope596,envelope597,envelope598,envelope599]
theorem configurations_sound : ∀ s∈configurations, s.Sound := by
  intro s hs
  simp only [configurations,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact envelope_sound580
  · exact envelope_sound581
  · exact envelope_sound582
  · exact envelope_sound583
  · exact envelope_sound584
  · exact envelope_sound585
  · exact envelope_sound586
  · exact envelope_sound587
  · exact envelope_sound588
  · exact envelope_sound589
  · exact envelope_sound590
  · exact envelope_sound591
  · exact envelope_sound592
  · exact envelope_sound593
  · exact envelope_sound594
  · exact envelope_sound595
  · exact envelope_sound596
  · exact envelope_sound597
  · exact envelope_sound598
  · exact envelope_sound599

end Cycle12.MajorityCertificates.Inputs029
