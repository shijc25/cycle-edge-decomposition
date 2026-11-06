import Cycle12.RationalMajorityInputs
import Cycle12.MajorityCertificates.Batch009

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Inputs009

def inputs180 : RatMajorityInputs := ⟨(2302748730722422280281813/5000000000000000000000),(42475219925409/10000000000000),(125818388862992657/125000000000000000),(204030526454865041/1000000000000000000),(42475219925409/20000000000000),(5979051893514333/50000000000000000),26⟩
theorem inputs_valid180 : inputs180.Valid := by decide +kernel
def envelope180 : RatMajorityEnvelope := ⟨90,0,inputs180,(1177007361/987550000),(143977701730210689/200000000000000000)⟩
theorem envelope_sound180 : envelope180.Sound := by
  apply rat_majority_inputs_envelopes inputs180 inputs_valid180
  · norm_num [envelope180]
  · intro rho hr0 hr1
    have hh := Batch009.bound360 rho hr0 hr1
    norm_num [Batch009.certificate360,envelope180,inputs180,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch009.bound361 rho hr0 hr1
    norm_num [Batch009.certificate361,envelope180,inputs180,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs181 : RatMajorityInputs := ⟨(2302748730722422280281813/5000000000000000000000),(49506893086967/10000000000000),(125818388862992657/125000000000000000),(25773418084735321/200000000000000000),(49506893086967/20000000000000),(16826797622978477/200000000000000000),27⟩
theorem inputs_valid181 : inputs181.Valid := by decide +kernel
def envelope181 : RatMajorityEnvelope := ⟨90,1,inputs181,1,(543160277002147041/1000000000000000000)⟩
theorem envelope_sound181 : envelope181.Sound := by
  apply rat_majority_inputs_envelopes inputs181 inputs_valid181
  · norm_num [envelope181]
  · intro rho hr0 hr1
    have hh := Batch009.bound362 rho hr0 hr1
    norm_num [Batch009.certificate362,envelope181,inputs181,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch009.bound363 rho hr0 hr1
    norm_num [Batch009.certificate363,envelope181,inputs181,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs182 : RatMajorityInputs := ⟨(11433073863761591263632771/25000000000000000000000),(212677807888757/50000000000000),(503296771445858017/500000000000000000),(101626701805893173/500000000000000000),(212677807888757/100000000000000),(119220795713033627/1000000000000000000),26⟩
theorem inputs_valid182 : inputs182.Valid := by decide +kernel
def envelope182 : RatMajorityEnvelope := ⟨91,0,inputs182,(1176002033/987115000),(719393837185070627/1000000000000000000)⟩
theorem envelope_sound182 : envelope182.Sound := by
  apply rat_majority_inputs_envelopes inputs182 inputs_valid182
  · norm_num [envelope182]
  · intro rho hr0 hr1
    have hh := Batch009.bound364 rho hr0 hr1
    norm_num [Batch009.certificate364,envelope182,inputs182,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch009.bound365 rho hr0 hr1
    norm_num [Batch009.certificate365,envelope182,inputs182,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs183 : RatMajorityInputs := ⟨(11433073863761591263632771/25000000000000000000000),(30957043221911/6250000000000),(503296771445858017/500000000000000000),(64327896920131441/500000000000000000),(30957043221911/12500000000000),(8403150778811291/100000000000000000),26⟩
theorem inputs_valid183 : inputs183.Valid := by decide +kernel
def envelope183 : RatMajorityEnvelope := ⟨91,1,inputs183,1,(33947462427963641/62500000000000000)⟩
theorem envelope_sound183 : envelope183.Sound := by
  apply rat_majority_inputs_envelopes inputs183 inputs_valid183
  · norm_num [envelope183]
  · intro rho hr0 hr1
    have hh := Batch009.bound366 rho hr0 hr1
    norm_num [Batch009.certificate366,envelope183,inputs183,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch009.bound367 rho hr0 hr1
    norm_num [Batch009.certificate367,envelope183,inputs183,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs184 : RatMajorityInputs := ⟨(5676803740573688114116389/12500000000000000000000),(212888032368291/50000000000000),(201327986135208619/200000000000000000),(50678346507417653/250000000000000000),(212888032368291/100000000000000),(59485213837704339/500000000000000000),25⟩
theorem inputs_valid184 : inputs184.Valid := by decide +kernel
def envelope184 : RatMajorityEnvelope := ⟨92,0,inputs184,(293761301/246671250),(718960528143559193/1000000000000000000)⟩
theorem envelope_sound184 : envelope184.Sound := by
  apply rat_majority_inputs_envelopes inputs184 inputs_valid184
  · norm_num [envelope184]
  · intro rho hr0 hr1
    have hh := Batch009.bound368 rho hr0 hr1
    norm_num [Batch009.certificate368,envelope184,inputs184,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch009.bound369 rho hr0 hr1
    norm_num [Batch009.certificate369,envelope184,inputs184,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs185 : RatMajorityInputs := ⟨(5676803740573688114116389/12500000000000000000000),(495550214988969/100000000000000),(201327986135208619/200000000000000000),(4014068719052681/31250000000000000),(495550214988969/200000000000000),(83931769761817197/1000000000000000000),26⟩
theorem inputs_valid185 : inputs185.Valid := by decide +kernel
def envelope185 : RatMajorityEnvelope := ⟨92,1,inputs185,1,(543159120679799839/1000000000000000000)⟩
theorem envelope_sound185 : envelope185.Sound := by
  apply rat_majority_inputs_envelopes inputs185 inputs_valid185
  · norm_num [envelope185]
  · intro rho hr0 hr1
    have hh := Batch009.bound370 rho hr0 hr1
    norm_num [Batch009.certificate370,envelope185,inputs185,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch009.bound371 rho hr0 hr1
    norm_num [Batch009.certificate371,envelope185,inputs185,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs186 : RatMajorityInputs := ⟨(451012921315056679097233/1000000000000000000000),(4263288497259/1000000000000),(1006686271187079129/1000000000000000000),(12625326750647147/62500000000000000),(4263288497259/2000000000000),(118642056348344823/1000000000000000000),25⟩
theorem inputs_valid186 : inputs186.Valid := by decide +kernel
def envelope186 : RatMajorityEnvelope := ⟨93,0,inputs186,(1174176133/986260000),(718585875430872027/1000000000000000000)⟩
theorem envelope_sound186 : envelope186.Sound := by
  apply rat_majority_inputs_envelopes inputs186 inputs_valid186
  · norm_num [envelope186]
  · intro rho hr0 hr1
    have hh := Batch009.bound372 rho hr0 hr1
    norm_num [Batch009.certificate372,envelope186,inputs186,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch009.bound373 rho hr0 hr1
    norm_num [Batch009.certificate373,envelope186,inputs186,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs187 : RatMajorityInputs := ⟨(451012921315056679097233/1000000000000000000000),(30984756071489/6250000000000),(1006686271187079129/1000000000000000000),(64136113813181183/500000000000000000),(30984756071489/12500000000000),(41922706974574123/500000000000000000),26⟩
theorem inputs_valid187 : inputs187.Valid := by decide +kernel
def envelope187 : RatMajorityEnvelope := ⟨93,1,inputs187,1,(543161734877320369/1000000000000000000)⟩
theorem envelope_sound187 : envelope187.Sound := by
  apply rat_majority_inputs_envelopes inputs187 inputs_valid187
  · norm_num [envelope187]
  · intro rho hr0 hr1
    have hh := Batch009.bound374 rho hr0 hr1
    norm_num [Batch009.certificate374,envelope187,inputs187,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch009.bound375 rho hr0 hr1
    norm_num [Batch009.certificate375,envelope187,inputs187,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs188 : RatMajorityInputs := ⟨(2799549886086935532269951/6250000000000000000000),(1333642367997/312500000000),(1006732561354449649/1000000000000000000),(100723620252334271/500000000000000000),(1333642367997/625000000000),(23676655856168971/200000000000000000),25⟩
theorem inputs_valid188 : inputs188.Valid := by decide +kernel
def envelope188 : RatMajorityEnvelope := ⟨94,0,inputs188,(2346459861/1971680000),(22442159997599889/31250000000000000)⟩
theorem envelope_sound188 : envelope188.Sound := by
  apply rat_majority_inputs_envelopes inputs188 inputs_valid188
  · norm_num [envelope188]
  · intro rho hr0 hr1
    have hh := Batch009.bound376 rho hr0 hr1
    norm_num [Batch009.certificate376,envelope188,inputs188,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch009.bound377 rho hr0 hr1
    norm_num [Batch009.certificate377,envelope188,inputs188,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs189 : RatMajorityInputs := ⟨(2799549886086935532269951/6250000000000000000000),(30990993499621/6250000000000),(1006732561354449649/1000000000000000000),(16023254600789523/125000000000000000),(30990993499621/12500000000000),(41901793003235583/500000000000000000),26⟩
theorem inputs_valid189 : inputs189.Valid := by decide +kernel
def envelope189 : RatMajorityEnvelope := ⟨94,1,inputs189,1,(135793486916568483/250000000000000000)⟩
theorem envelope_sound189 : envelope189.Sound := by
  apply rat_majority_inputs_envelopes inputs189 inputs_valid189
  · norm_num [envelope189]
  · intro rho hr0 hr1
    have hh := Batch009.bound378 rho hr0 hr1
    norm_num [Batch009.certificate378,envelope189,inputs189,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch009.bound379 rho hr0 hr1
    norm_num [Batch009.certificate379,envelope189,inputs189,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs190 : RatMajorityInputs := ⟨(8897773220485717009409583/20000000000000000000000),(85417975512219/20000000000000),(50338939905374079/50000000000000000),(40206737974830103/200000000000000000),(85417975512219/40000000000000),(118191464637580479/1000000000000000000),25⟩
theorem inputs_valid190 : inputs190.Valid := by decide +kernel
def envelope190 : RatMajorityEnvelope := ⟨95,0,inputs190,(1172313469/985425000),(35887381389168721/50000000000000000)⟩
theorem envelope_sound190 : envelope190.Sound := by
  apply rat_majority_inputs_envelopes inputs190 inputs_valid190
  · norm_num [envelope190]
  · intro rho hr0 hr1
    have hh := Batch009.bound380 rho hr0 hr1
    norm_num [Batch009.certificate380,envelope190,inputs190,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch009.bound381 rho hr0 hr1
    norm_num [Batch009.certificate381,envelope190,inputs190,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs191 : RatMajorityInputs := ⟨(8897773220485717009409583/20000000000000000000000),(99221593143561/20000000000000),(50338939905374079/50000000000000000),(127968566345581911/1000000000000000000),(99221593143561/40000000000000),(83698030804700839/1000000000000000000),27⟩
theorem inputs_valid191 : inputs191.Valid := by decide +kernel
def envelope191 : RatMajorityEnvelope := ⟨95,1,inputs191,1,(271586206084381021/500000000000000000)⟩
theorem envelope_sound191 : envelope191.Sound := by
  apply rat_majority_inputs_envelopes inputs191 inputs_valid191
  · norm_num [envelope191]
  · intro rho hr0 hr1
    have hh := Batch009.bound382 rho hr0 hr1
    norm_num [Batch009.certificate382,envelope191,inputs191,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch009.bound383 rho hr0 hr1
    norm_num [Batch009.certificate383,envelope191,inputs191,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs192 : RatMajorityInputs := ⟨(22094595762106791577634279/50000000000000000000000),(213784788418409/50000000000000),(503412506601695323/500000000000000000),(10021165800739733/50000000000000000),(213784788418409/100000000000000),(29477080632765139/250000000000000000),25⟩
theorem inputs_valid192 : inputs192.Valid := by decide +kernel
def envelope192 : RatMajorityEnvelope := ⟨96,0,inputs192,(234272457/197002000),(717295267440054247/1000000000000000000)⟩
theorem envelope_sound192 : envelope192.Sound := by
  apply rat_majority_inputs_envelopes inputs192 inputs_valid192
  · norm_num [envelope192]
  · intro rho hr0 hr1
    have hh := Batch009.bound384 rho hr0 hr1
    norm_num [Batch009.certificate384,envelope192,inputs192,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch009.bound385 rho hr0 hr1
    norm_num [Batch009.certificate385,envelope192,inputs192,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs193 : RatMajorityInputs := ⟨(22094595762106791577634279/50000000000000000000000),(124034482115037/25000000000000),(503412506601695323/500000000000000000),(63971369029055029/500000000000000000),(124034482115037/50000000000000),(10460686578907669/125000000000000000),26⟩
theorem inputs_valid193 : inputs193.Valid := by decide +kernel
def envelope193 : RatMajorityEnvelope := ⟨96,1,inputs193,1,(271595459703532359/500000000000000000)⟩
theorem envelope_sound193 : envelope193.Sound := by
  apply rat_majority_inputs_envelopes inputs193 inputs_valid193
  · norm_num [envelope193]
  · intro rho hr0 hr1
    have hh := Batch009.bound386 rho hr0 hr1
    norm_num [Batch009.certificate386,envelope193,inputs193,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch009.bound387 rho hr0 hr1
    norm_num [Batch009.certificate387,envelope193,inputs193,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs194 : RatMajorityInputs := ⟨(43894146225985538128570693/100000000000000000000000),(212563124450421/50000000000000),(1006871134166732153/1000000000000000000),(40709701229420267/200000000000000000),(212563124450421/100000000000000),(4774304026083147/40000000000000000),25⟩
theorem inputs_valid194 : inputs194.Valid := by decide +kernel
def envelope194 : RatMajorityEnvelope := ⟨97,0,inputs194,(146391168/123075625),(143569468055618217/200000000000000000)⟩
theorem envelope_sound194 : envelope194.Sound := by
  apply rat_majority_inputs_envelopes inputs194 inputs_valid194
  · norm_num [envelope194]
  · intro rho hr0 hr1
    have hh := Batch009.bound388 rho hr0 hr1
    norm_num [Batch009.certificate388,envelope194,inputs194,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch009.bound389 rho hr0 hr1
    norm_num [Batch009.certificate389,envelope194,inputs194,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs195 : RatMajorityInputs := ⟨(43894146225985538128570693/100000000000000000000000),(9928018957013/2000000000000),(1006871134166732153/1000000000000000000),(127716209958237997/1000000000000000000),(9928018957013/4000000000000),(20893877607353231/250000000000000000),26⟩
theorem inputs_valid195 : inputs195.Valid := by decide +kernel
def envelope195 : RatMajorityEnvelope := ⟨97,1,inputs195,1,(27159420811396637/50000000000000000)⟩
theorem envelope_sound195 : envelope195.Sound := by
  apply rat_majority_inputs_envelopes inputs195 inputs_valid195
  · norm_num [envelope195]
  · intro rho hr0 hr1
    have hh := Batch009.bound390 rho hr0 hr1
    norm_num [Batch009.certificate390,envelope195,inputs195,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch009.bound391 rho hr0 hr1
    norm_num [Batch009.certificate391,envelope195,inputs195,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs196 : RatMajorityInputs := ⟨(1090080162582280521334207/2500000000000000000000),(5352836730297/1250000000000),(1006917227834088743/1000000000000000000),(199589410245961201/1000000000000000000),(5352836730297/2500000000000),(117521416711870701/1000000000000000000),26⟩
theorem inputs_valid196 : inputs196.Valid := by decide +kernel
def envelope196 : RatMajorityEnvelope := ⟨98,0,inputs196,(83539471/70300000),(358244793242618757/500000000000000000)⟩
theorem envelope_sound196 : envelope196.Sound := by
  apply rat_majority_inputs_envelopes inputs196 inputs_valid196
  · norm_num [envelope196]
  · intro rho hr0 hr1
    have hh := Batch009.bound392 rho hr0 hr1
    norm_num [Batch009.certificate392,envelope196,inputs196,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch009.bound393 rho hr0 hr1
    norm_num [Batch009.certificate393,envelope196,inputs196,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs197 : RatMajorityInputs := ⟨(1090080162582280521334207/2500000000000000000000),(2482148753539/500000000000),(1006917227834088743/1000000000000000000),(127691424810666417/1000000000000000000),(2482148753539/1000000000000),(10445434403576683/125000000000000000),27⟩
theorem inputs_valid197 : inputs197.Valid := by decide +kernel
def envelope197 : RatMajorityEnvelope := ⟨98,1,inputs197,1,(543206986209270123/1000000000000000000)⟩
theorem envelope_sound197 : envelope197.Sound := by
  apply rat_majority_inputs_envelopes inputs197 inputs_valid197
  · norm_num [envelope197]
  · intro rho hr0 hr1
    have hh := Batch009.bound394 rho hr0 hr1
    norm_num [Batch009.certificate394,envelope197,inputs197,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch009.bound395 rho hr0 hr1
    norm_num [Batch009.certificate395,envelope197,inputs197,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs198 : RatMajorityInputs := ⟨(427109404455461552879279/1000000000000000000000),(1322182048617/312500000000),(201412505479139843/200000000000000000),(103086674505972079/500000000000000000),(1322182048617/625000000000),(60287019826437797/500000000000000000),25⟩
theorem inputs_valid198 : inputs198.Valid := by decide +kernel
def envelope198 : RatMajorityEnvelope := ⟨99,0,inputs198,(467761509/391540000),(722934843658550579/1000000000000000000)⟩
theorem envelope_sound198 : envelope198.Sound := by
  apply rat_majority_inputs_envelopes inputs198 inputs_valid198
  · norm_num [envelope198]
  · intro rho hr0 hr1
    have hh := Batch009.bound396 rho hr0 hr1
    norm_num [Batch009.certificate396,envelope198,inputs198,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch009.bound397 rho hr0 hr1
    norm_num [Batch009.certificate397,envelope198,inputs198,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def inputs199 : RatMajorityInputs := ⟨(427109404455461552879279/1000000000000000000000),(49464599854811/10000000000000),(201412505479139843/200000000000000000),(25846885126672961/200000000000000000),(49464599854811/20000000000000),(21078022819264909/250000000000000000),26⟩
theorem inputs_valid199 : inputs199.Valid := by decide +kernel
def envelope199 : RatMajorityEnvelope := ⟨99,1,inputs199,1,(543434996254649989/1000000000000000000)⟩
theorem envelope_sound199 : envelope199.Sound := by
  apply rat_majority_inputs_envelopes inputs199 inputs_valid199
  · norm_num [envelope199]
  · intro rho hr0 hr1
    have hh := Batch009.bound398 rho hr0 hr1
    norm_num [Batch009.certificate398,envelope199,inputs199,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh
  · intro rho hr0 hr1
    have hh := Batch009.bound399 rho hr0 hr1
    norm_num [Batch009.certificate399,envelope199,inputs199,Rat.cast_zero,Rat.cast_one,
      Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at hh ⊢
    exact hh

def configurations : List RatMajorityEnvelope := [envelope180,envelope181,envelope182,envelope183,envelope184,envelope185,envelope186,envelope187,envelope188,envelope189,envelope190,envelope191,envelope192,envelope193,envelope194,envelope195,envelope196,envelope197,envelope198,envelope199]
theorem configurations_sound : ∀ s∈configurations, s.Sound := by
  intro s hs
  simp only [configurations,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact envelope_sound180
  · exact envelope_sound181
  · exact envelope_sound182
  · exact envelope_sound183
  · exact envelope_sound184
  · exact envelope_sound185
  · exact envelope_sound186
  · exact envelope_sound187
  · exact envelope_sound188
  · exact envelope_sound189
  · exact envelope_sound190
  · exact envelope_sound191
  · exact envelope_sound192
  · exact envelope_sound193
  · exact envelope_sound194
  · exact envelope_sound195
  · exact envelope_sound196
  · exact envelope_sound197
  · exact envelope_sound198
  · exact envelope_sound199

end Cycle12.MajorityCertificates.Inputs009
