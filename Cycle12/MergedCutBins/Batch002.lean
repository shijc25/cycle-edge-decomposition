import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch004
import Cycle12.MergedCutProfiles.Batch005
import Cycle12.MergedCutProfiles.Batch006

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch002

def retention24 : RatCutRetentionCertificate := ⟨(1/250),(1/200),(16000000000000000000/597512157261602792499),(4132049451178336111/1000000000000000000),(13/10),(3499013977893065230838110673144355968071/1652819780471334444400000000000000000000),true,MergedCutProfiles.Batch004.profile165,![MergedCutProfiles.Batch004.profile165,MergedCutProfiles.Batch004.profile166,MergedCutProfiles.Batch004.profile167,MergedCutProfiles.Batch004.profile168,MergedCutProfiles.Batch004.profile169,MergedCutProfiles.Batch004.profile170,MergedCutProfiles.Batch004.profile171,MergedCutProfiles.Batch004.profile172,MergedCutProfiles.Batch004.profile173,MergedCutProfiles.Batch004.profile174,MergedCutProfiles.Batch004.profile175,MergedCutProfiles.Batch004.profile176,MergedCutProfiles.Batch004.profile177,MergedCutProfiles.Batch004.profile178,MergedCutProfiles.Batch004.profile179,MergedCutProfiles.Batch004.profile180]⟩
theorem profilesValid24 : retention24.ProfilesValid := by
  change ∀ j : Fin 16, (retention24.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch004.valid165
  · exact MergedCutProfiles.Batch004.valid166
  · exact MergedCutProfiles.Batch004.valid167
  · exact MergedCutProfiles.Batch004.valid168
  · exact MergedCutProfiles.Batch004.valid169
  · exact MergedCutProfiles.Batch004.valid170
  · exact MergedCutProfiles.Batch004.valid171
  · exact MergedCutProfiles.Batch004.valid172
  · exact MergedCutProfiles.Batch004.valid173
  · exact MergedCutProfiles.Batch004.valid174
  · exact MergedCutProfiles.Batch004.valid175
  · exact MergedCutProfiles.Batch004.valid176
  · exact MergedCutProfiles.Batch004.valid177
  · exact MergedCutProfiles.Batch004.valid178
  · exact MergedCutProfiles.Batch004.valid179
  · exact MergedCutProfiles.Batch004.valid180
theorem numericValid24 : retention24.NumericValid := by decide +kernel
def certificate24 : RatCutBinCertificate := ⟨⟨retention24,(1807485279528674747/1000000000000000000),(249776479000013/250000000000000000),(6999655320721799937/1000000000000000000),(525086275949533264257/31250000000000000),(2116661281714248387/1000000000000000000)⟩,(999892497830050613/1000000000000000000),(24752635943835879/100000000000000000),(406777468862893033/1000000000000000000),(101639774675782211/200000000000000000)⟩
theorem valid24 : certificate24.Valid := by decide +kernel
theorem sound24 : certificate24.Sound := rat_cut_bin_certificate_sound certificate24 profilesValid24 numericValid24 valid24

def retention25 : RatCutRetentionCertificate := ⟨(1/250),(1/200),(1/2),64,1,(63842214036820242051452344238848143879/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch004.profile181,(fun _ => MergedCutProfiles.Batch004.profile181)⟩
theorem profilesValid25 : retention25.ProfilesValid := by
  exact MergedCutProfiles.Batch004.valid181
theorem numericValid25 : retention25.NumericValid := by decide +kernel
def certificate25 : RatCutBinCertificate := ⟨⟨retention25,(1807485279528674747/1000000000000000000),(249776479000013/250000000000000000),(6999655320721799937/1000000000000000000),(525086275949533264257/31250000000000000),(997276600302068909/1000000000000000000)⟩,(999892497830050613/1000000000000000000),(206214138017448161/500000000000000000),(55571495537106389/250000000000000000),(21825561767475433/100000000000000000)⟩
theorem valid25 : certificate25.Valid := by decide +kernel
theorem sound25 : certificate25.Sound := rat_cut_bin_certificate_sound certificate25 profilesValid25 numericValid25 valid25

def retention26 : RatCutRetentionCertificate := ⟨(1/250),(1/200),(16000000000000000000/597512157261602792499),(3278349187592359123/1000000000000000000),(27/20),(10924120273965118435466757960954000484599/5245358700147774596800000000000000000000),false,MergedCutProfiles.Batch004.profile182,(fun _ => MergedCutProfiles.Batch004.profile182)⟩
theorem profilesValid26 : retention26.ProfilesValid := by
  exact MergedCutProfiles.Batch004.valid182
theorem numericValid26 : retention26.NumericValid := by decide +kernel
def certificate26 : RatCutBinCertificate := ⟨⟨retention26,(2134582522528674747/1000000000000000000),(249776479000013/250000000000000000),(6999655320721799937/1000000000000000000),(525086275949533264257/31250000000000000),(130138415795011911/62500000000000000)⟩,(49993652168054857/50000000000000000),(23286606484000443/125000000000000000),(500238456460512133/1000000000000000000),(572082136505392171/1000000000000000000)⟩
theorem valid26 : certificate26.Valid := by decide +kernel
theorem sound26 : certificate26.Sound := rat_cut_bin_certificate_sound certificate26 profilesValid26 numericValid26 valid26

def retention27 : RatCutRetentionCertificate := ⟨(1/250),(1/200),(1/2),64,1,(63842214036820242051452344238848143879/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch004.profile181,(fun _ => MergedCutProfiles.Batch004.profile181)⟩
theorem profilesValid27 : retention27.ProfilesValid := by
  exact MergedCutProfiles.Batch004.valid181
theorem numericValid27 : retention27.NumericValid := by decide +kernel
def certificate27 : RatCutBinCertificate := ⟨⟨retention27,(2134582522528674747/1000000000000000000),(249776479000013/250000000000000000),(6999655320721799937/1000000000000000000),(525086275949533264257/31250000000000000),(997229911604423361/1000000000000000000)⟩,(49993652168054857/50000000000000000),(194489606334025033/500000000000000000),(48746663304387519/200000000000000000),(239298393139500339/1000000000000000000)⟩
theorem valid27 : certificate27.Valid := by decide +kernel
theorem sound27 : certificate27.Sound := rat_cut_bin_certificate_sound certificate27 profilesValid27 numericValid27 valid27

def retention28 : RatCutRetentionCertificate := ⟨(1/200),(3/500),(608263054744114373/1652480283922975324656),(35813207031428853/62500000000000000),4,(77634062879477862996602968685281447/35262234615560716800000000000000000),true,MergedCutProfiles.Batch004.profile183,![MergedCutProfiles.Batch004.profile183,MergedCutProfiles.Batch004.profile184,MergedCutProfiles.Batch004.profile185,MergedCutProfiles.Batch004.profile186,MergedCutProfiles.Batch004.profile187,MergedCutProfiles.Batch004.profile188,MergedCutProfiles.Batch004.profile189,MergedCutProfiles.Batch004.profile190,MergedCutProfiles.Batch004.profile191,MergedCutProfiles.Batch004.profile192,MergedCutProfiles.Batch004.profile193,MergedCutProfiles.Batch004.profile194,MergedCutProfiles.Batch004.profile195,MergedCutProfiles.Batch004.profile196,MergedCutProfiles.Batch004.profile197,MergedCutProfiles.Batch004.profile198]⟩
theorem profilesValid28 : retention28.ProfilesValid := by
  change ∀ j : Fin 16, (retention28.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch004.valid183
  · exact MergedCutProfiles.Batch004.valid184
  · exact MergedCutProfiles.Batch004.valid185
  · exact MergedCutProfiles.Batch004.valid186
  · exact MergedCutProfiles.Batch004.valid187
  · exact MergedCutProfiles.Batch004.valid188
  · exact MergedCutProfiles.Batch004.valid189
  · exact MergedCutProfiles.Batch004.valid190
  · exact MergedCutProfiles.Batch004.valid191
  · exact MergedCutProfiles.Batch004.valid192
  · exact MergedCutProfiles.Batch004.valid193
  · exact MergedCutProfiles.Batch004.valid194
  · exact MergedCutProfiles.Batch004.valid195
  · exact MergedCutProfiles.Batch004.valid196
  · exact MergedCutProfiles.Batch004.valid197
  · exact MergedCutProfiles.Batch004.valid198
theorem numericValid28 : retention28.NumericValid := by decide +kernel
def certificate28 : RatCutBinCertificate := ⟨⟨retention28,(1816334932941726221/1000000000000000000),(721626522366223/500000000000000000),(7083163478073821627/1000000000000000000),(11756323027834685309923/1000000000000000000),(440028049633523603/200000000000000000)⟩,(999845655780480699/1000000000000000000),(575781662548957899/1000000000000000000),(53185727913887257/500000000000000000),(47176124865003003/1000000000000000000)⟩
theorem valid28 : certificate28.Valid := by decide +kernel
theorem sound28 : certificate28.Sound := rat_cut_bin_certificate_sound certificate28 profilesValid28 numericValid28 valid28

def retention29 : RatCutRetentionCertificate := ⟨(1/200),(3/500),(80888921312500000/103280017745185957791),(608263054744114373/1000000000000000000),4,(578912399857719560357/256000000000000000000),true,MergedCutProfiles.Batch004.profile199,![MergedCutProfiles.Batch004.profile199,MergedCutProfiles.Batch005.profile200,MergedCutProfiles.Batch004.profile188,MergedCutProfiles.Batch005.profile201,MergedCutProfiles.Batch004.profile193,MergedCutProfiles.Batch004.profile195,MergedCutProfiles.Batch005.profile202,MergedCutProfiles.Batch005.profile203,MergedCutProfiles.Batch005.profile204,MergedCutProfiles.Batch005.profile205,MergedCutProfiles.Batch005.profile206,MergedCutProfiles.Batch005.profile207,MergedCutProfiles.Batch005.profile208,MergedCutProfiles.Batch005.profile209,MergedCutProfiles.Batch005.profile210,MergedCutProfiles.Batch005.profile211]⟩
theorem profilesValid29 : retention29.ProfilesValid := by
  change ∀ j : Fin 16, (retention29.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch004.valid199
  · exact MergedCutProfiles.Batch005.valid200
  · exact MergedCutProfiles.Batch004.valid188
  · exact MergedCutProfiles.Batch005.valid201
  · exact MergedCutProfiles.Batch004.valid193
  · exact MergedCutProfiles.Batch004.valid195
  · exact MergedCutProfiles.Batch005.valid202
  · exact MergedCutProfiles.Batch005.valid203
  · exact MergedCutProfiles.Batch005.valid204
  · exact MergedCutProfiles.Batch005.valid205
  · exact MergedCutProfiles.Batch005.valid206
  · exact MergedCutProfiles.Batch005.valid207
  · exact MergedCutProfiles.Batch005.valid208
  · exact MergedCutProfiles.Batch005.valid209
  · exact MergedCutProfiles.Batch005.valid210
  · exact MergedCutProfiles.Batch005.valid211
theorem numericValid29 : retention29.NumericValid := by decide +kernel
def certificate29 : RatCutBinCertificate := ⟨⟨retention29,(1816334932941726221/1000000000000000000),(721626522366223/500000000000000000),(7083163478073821627/1000000000000000000),(11756323027834685309923/1000000000000000000),(141243511806803769/62500000000000000)⟩,(999845655780480699/1000000000000000000),(269241013572775441/500000000000000000),(128196961877388451/1000000000000000000),(14692065615262807/250000000000000000)⟩
theorem valid29 : certificate29.Valid := by decide +kernel
theorem sound29 : certificate29.Sound := rat_cut_bin_certificate_sound certificate29 profilesValid29 numericValid29 valid29

def retention30 : RatCutRetentionCertificate := ⟨(1/200),(3/500),(52532195172969433/45902230108971536796),(1294222741/1000000000),(12/5),(750017589850108048666679656714002039/323555685250000000000000000000000000),true,MergedCutProfiles.Batch004.profile185,![MergedCutProfiles.Batch004.profile185,MergedCutProfiles.Batch004.profile188,MergedCutProfiles.Batch005.profile212,MergedCutProfiles.Batch004.profile194,MergedCutProfiles.Batch004.profile197,MergedCutProfiles.Batch005.profile204,MergedCutProfiles.Batch005.profile205,MergedCutProfiles.Batch005.profile213,MergedCutProfiles.Batch005.profile208,MergedCutProfiles.Batch005.profile214,MergedCutProfiles.Batch005.profile211,MergedCutProfiles.Batch005.profile215,MergedCutProfiles.Batch005.profile216,MergedCutProfiles.Batch005.profile217,MergedCutProfiles.Batch005.profile218,MergedCutProfiles.Batch005.profile219]⟩
theorem profilesValid30 : retention30.ProfilesValid := by
  change ∀ j : Fin 16, (retention30.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch004.valid185
  · exact MergedCutProfiles.Batch004.valid188
  · exact MergedCutProfiles.Batch005.valid212
  · exact MergedCutProfiles.Batch004.valid194
  · exact MergedCutProfiles.Batch004.valid197
  · exact MergedCutProfiles.Batch005.valid204
  · exact MergedCutProfiles.Batch005.valid205
  · exact MergedCutProfiles.Batch005.valid213
  · exact MergedCutProfiles.Batch005.valid208
  · exact MergedCutProfiles.Batch005.valid214
  · exact MergedCutProfiles.Batch005.valid211
  · exact MergedCutProfiles.Batch005.valid215
  · exact MergedCutProfiles.Batch005.valid216
  · exact MergedCutProfiles.Batch005.valid217
  · exact MergedCutProfiles.Batch005.valid218
  · exact MergedCutProfiles.Batch005.valid219
theorem numericValid30 : retention30.NumericValid := by decide +kernel
def certificate30 : RatCutBinCertificate := ⟨⟨retention30,(1816334932941726221/1000000000000000000),(721626522366223/500000000000000000),(7083163478073821627/1000000000000000000),(11756323027834685309923/1000000000000000000),(579289929187020833/250000000000000000)⟩,(999845655780480699/1000000000000000000),(67938421574876723/200000000000000000),(29352924217304959/100000000000000000),(108079480149580587/500000000000000000)⟩
theorem valid30 : certificate30.Valid := by decide +kernel
theorem sound30 : certificate30.Sound := rat_cut_bin_certificate_sound certificate30 profilesValid30 numericValid30 valid30

def retention31 : RatCutRetentionCertificate := ⟨(1/200),(3/500),(4000000000000000000/103280017745185957791),(472789756556724897/250000000000000000),(19/10),(667709980940563959669/320000000000000000000),true,MergedCutProfiles.Batch005.profile220,![MergedCutProfiles.Batch005.profile220,MergedCutProfiles.Batch005.profile221,MergedCutProfiles.Batch005.profile222,MergedCutProfiles.Batch005.profile223,MergedCutProfiles.Batch005.profile224,MergedCutProfiles.Batch005.profile225,MergedCutProfiles.Batch005.profile226,MergedCutProfiles.Batch005.profile227,MergedCutProfiles.Batch005.profile228,MergedCutProfiles.Batch005.profile229,MergedCutProfiles.Batch005.profile230,MergedCutProfiles.Batch005.profile231,MergedCutProfiles.Batch005.profile232,MergedCutProfiles.Batch005.profile233,MergedCutProfiles.Batch005.profile234,MergedCutProfiles.Batch005.profile235]⟩
theorem profilesValid31 : retention31.ProfilesValid := by
  change ∀ j : Fin 16, (retention31.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch005.valid220
  · exact MergedCutProfiles.Batch005.valid221
  · exact MergedCutProfiles.Batch005.valid222
  · exact MergedCutProfiles.Batch005.valid223
  · exact MergedCutProfiles.Batch005.valid224
  · exact MergedCutProfiles.Batch005.valid225
  · exact MergedCutProfiles.Batch005.valid226
  · exact MergedCutProfiles.Batch005.valid227
  · exact MergedCutProfiles.Batch005.valid228
  · exact MergedCutProfiles.Batch005.valid229
  · exact MergedCutProfiles.Batch005.valid230
  · exact MergedCutProfiles.Batch005.valid231
  · exact MergedCutProfiles.Batch005.valid232
  · exact MergedCutProfiles.Batch005.valid233
  · exact MergedCutProfiles.Batch005.valid234
  · exact MergedCutProfiles.Batch005.valid235
theorem numericValid31 : retention31.NumericValid := by decide +kernel
def certificate31 : RatCutBinCertificate := ⟨⟨retention31,(1816334932941726221/1000000000000000000),(721626522366223/500000000000000000),(7083163478073821627/1000000000000000000),(11756323027834685309923/1000000000000000000),(2085890513258923499/1000000000000000000)⟩,(999845655780480699/1000000000000000000),(19980216972191871/62500000000000000),(315728337536281133/1000000000000000000),(26545391229584649/100000000000000000)⟩
theorem valid31 : certificate31.Valid := by decide +kernel
theorem sound31 : certificate31.Sound := rat_cut_bin_certificate_sound certificate31 profilesValid31 numericValid31 valid31

def retention32 : RatCutRetentionCertificate := ⟨(1/200),(3/500),(1/2),64,1,(63842211595158023048219618863822294719/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch005.profile236,(fun _ => MergedCutProfiles.Batch005.profile236)⟩
theorem profilesValid32 : retention32.ProfilesValid := by
  exact MergedCutProfiles.Batch005.valid236
theorem numericValid32 : retention32.NumericValid := by decide +kernel
def certificate32 : RatCutBinCertificate := ⟨⟨retention32,(1816334932941726221/1000000000000000000),(721626522366223/500000000000000000),(7083163478073821627/1000000000000000000),(11756323027834685309923/1000000000000000000),(997164462933468733/1000000000000000000)⟩,(999845655780480699/1000000000000000000),(25930810154402891/62500000000000000),(220110444029556569/1000000000000000000),(1728683105138413/8000000000000000)⟩
theorem valid32 : certificate32.Valid := by decide +kernel
theorem sound32 : certificate32.Sound := rat_cut_bin_certificate_sound certificate32 profilesValid32 numericValid32 valid32

def retention33 : RatCutRetentionCertificate := ⟨(1/200),(3/500),(4000000000000000000/103280017745185957791),(1654446731702632883/500000000000000000),(27/20),(2696600148518916500327603086523900277839/1323557385362106306400000000000000000000),false,MergedCutProfiles.Batch005.profile237,(fun _ => MergedCutProfiles.Batch005.profile237)⟩
theorem profilesValid33 : retention33.ProfilesValid := by
  exact MergedCutProfiles.Batch005.valid237
theorem numericValid33 : retention33.NumericValid := by decide +kernel
def certificate33 : RatCutBinCertificate := ⟨⟨retention33,(2145584197941726221/1000000000000000000),(721626522366223/500000000000000000),(7083163478073821627/1000000000000000000),(11756323027834685309923/1000000000000000000),(1018398984101756751/500000000000000000)⟩,(499908838804533121/500000000000000000),(188728841760166117/1000000000000000000),(496184836024568979/1000000000000000000),(55949570590555101/100000000000000000)⟩
theorem valid33 : certificate33.Valid := by decide +kernel
theorem sound33 : certificate33.Sound := rat_cut_bin_certificate_sound certificate33 profilesValid33 numericValid33 valid33

def retention34 : RatCutRetentionCertificate := ⟨(1/200),(3/500),(1/2),64,1,(63842211595158023048219618863822294719/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch005.profile236,(fun _ => MergedCutProfiles.Batch005.profile236)⟩
theorem profilesValid34 : retention34.ProfilesValid := by
  exact MergedCutProfiles.Batch005.valid236
theorem numericValid34 : retention34.NumericValid := by decide +kernel
def certificate34 : RatCutBinCertificate := ⟨⟨retention34,(2145584197941726221/1000000000000000000),(721626522366223/500000000000000000),(7083163478073821627/1000000000000000000),(11756323027834685309923/1000000000000000000),(997097375676966799/1000000000000000000)⟩,(499908838804533121/500000000000000000),(385521545653977347/1000000000000000000),(123506678943919449/500000000000000000),(242473491493423423/1000000000000000000)⟩
theorem valid34 : certificate34.Valid := by decide +kernel
theorem sound34 : certificate34.Sound := rat_cut_bin_certificate_sound certificate34 profilesValid34 numericValid34 valid34

def retention35 : RatCutRetentionCertificate := ⟨(3/500),(7/1000),(117582184303574573/241743031286248836892),(576326753767153087/1000000000000000000),4,(565099429790963365023/256000000000000000000),true,MergedCutProfiles.Batch005.profile238,![MergedCutProfiles.Batch005.profile238,MergedCutProfiles.Batch005.profile239,MergedCutProfiles.Batch006.profile240,MergedCutProfiles.Batch006.profile241,MergedCutProfiles.Batch006.profile242,MergedCutProfiles.Batch006.profile243,MergedCutProfiles.Batch006.profile244,MergedCutProfiles.Batch006.profile245,MergedCutProfiles.Batch006.profile246,MergedCutProfiles.Batch006.profile247,MergedCutProfiles.Batch006.profile248,MergedCutProfiles.Batch006.profile249,MergedCutProfiles.Batch006.profile250,MergedCutProfiles.Batch006.profile251,MergedCutProfiles.Batch006.profile252,MergedCutProfiles.Batch006.profile253]⟩
theorem profilesValid35 : retention35.ProfilesValid := by
  change ∀ j : Fin 16, (retention35.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch005.valid238
  · exact MergedCutProfiles.Batch005.valid239
  · exact MergedCutProfiles.Batch006.valid240
  · exact MergedCutProfiles.Batch006.valid241
  · exact MergedCutProfiles.Batch006.valid242
  · exact MergedCutProfiles.Batch006.valid243
  · exact MergedCutProfiles.Batch006.valid244
  · exact MergedCutProfiles.Batch006.valid245
  · exact MergedCutProfiles.Batch006.valid246
  · exact MergedCutProfiles.Batch006.valid247
  · exact MergedCutProfiles.Batch006.valid248
  · exact MergedCutProfiles.Batch006.valid249
  · exact MergedCutProfiles.Batch006.valid250
  · exact MergedCutProfiles.Batch006.valid251
  · exact MergedCutProfiles.Batch006.valid252
  · exact MergedCutProfiles.Batch006.valid253
theorem numericValid35 : retention35.NumericValid := by decide +kernel
def certificate35 : RatCutBinCertificate := ⟨⟨retention35,(1825187020779274317/1000000000000000000),(1970684370264843/1000000000000000000),(56001757170388503/7812500000000000),(8702706377686016146887/1000000000000000000),(1102706264929660789/500000000000000000)⟩,(199958115250891559/200000000000000000),(569781668258932099/1000000000000000000),(109714983338763491/1000000000000000000),(1220105891647007/25000000000000000)⟩
theorem valid35 : certificate35.Valid := by decide +kernel
theorem sound35 : certificate35.Sound := rat_cut_bin_certificate_sound certificate35 profilesValid35 numericValid35 valid35

def certificates : List RatCutBinCertificate := [certificate24,certificate25,certificate26,certificate27,certificate28,certificate29,certificate30,certificate31,certificate32,certificate33,certificate34,certificate35]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound24,List.forall_mem_cons.mpr ⟨sound25,List.forall_mem_cons.mpr ⟨sound26,List.forall_mem_cons.mpr ⟨sound27,List.forall_mem_cons.mpr ⟨sound28,List.forall_mem_cons.mpr ⟨sound29,List.forall_mem_cons.mpr ⟨sound30,List.forall_mem_cons.mpr ⟨sound31,List.forall_mem_cons.mpr ⟨sound32,List.forall_mem_cons.mpr ⟨sound33,List.forall_mem_cons.mpr ⟨sound34,List.forall_mem_cons.mpr ⟨sound35,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch002
