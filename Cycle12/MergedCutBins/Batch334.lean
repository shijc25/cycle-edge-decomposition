import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch359
import Cycle12.MergedCutProfiles.Batch360
import Cycle12.MergedCutProfiles.Batch361
import Cycle12.MergedCutProfiles.Batch362
import Cycle12.MergedCutProfiles.Batch364
import Cycle12.MergedCutProfiles.Batch478
import Cycle12.MergedCutProfiles.Batch479
import Cycle12.MergedCutProfiles.Batch480
import Cycle12.MergedCutProfiles.Batch605
import Cycle12.MergedCutProfiles.Batch606

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch334

def retention4008 : RatCutRetentionCertificate := ⟨(43/1000),(11/250),(1124115987932125479/509598721095730805365),(277521149/250000000),(14/5),(10501291274251407522673380664517123319/4440338384000000000000000000000000000),true,MergedCutProfiles.Batch605.profile24213,![MergedCutProfiles.Batch605.profile24213,MergedCutProfiles.Batch605.profile24234,MergedCutProfiles.Batch605.profile24228,MergedCutProfiles.Batch605.profile24235,MergedCutProfiles.Batch479.profile19170,MergedCutProfiles.Batch605.profile24221,MergedCutProfiles.Batch478.profile19145,MergedCutProfiles.Batch605.profile24224,MergedCutProfiles.Batch360.profile14400,MergedCutProfiles.Batch605.profile24236,MergedCutProfiles.Batch605.profile24231,MergedCutProfiles.Batch479.profile19164,MergedCutProfiles.Batch605.profile24232,MergedCutProfiles.Batch478.profile19146,MergedCutProfiles.Batch605.profile24237,MergedCutProfiles.Batch605.profile24238]⟩
theorem profilesValid4008 : retention4008.ProfilesValid := by
  change ∀ j : Fin 16, (retention4008.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch605.valid24213
  · exact MergedCutProfiles.Batch605.valid24234
  · exact MergedCutProfiles.Batch605.valid24228
  · exact MergedCutProfiles.Batch605.valid24235
  · exact MergedCutProfiles.Batch479.valid19170
  · exact MergedCutProfiles.Batch605.valid24221
  · exact MergedCutProfiles.Batch478.valid19145
  · exact MergedCutProfiles.Batch605.valid24224
  · exact MergedCutProfiles.Batch360.valid14400
  · exact MergedCutProfiles.Batch605.valid24236
  · exact MergedCutProfiles.Batch605.valid24231
  · exact MergedCutProfiles.Batch479.valid19164
  · exact MergedCutProfiles.Batch605.valid24232
  · exact MergedCutProfiles.Batch478.valid19146
  · exact MergedCutProfiles.Batch605.valid24237
  · exact MergedCutProfiles.Batch605.valid24238
theorem numericValid4008 : retention4008.NumericValid := by decide +kernel
def certificate4008 : RatCutBinCertificate := ⟨⟨retention4008,(189524127631560059/100000000000000000),(5622540848385301/62500000000000000),(11894089317798289217/1000000000000000000),(243784539652001747163/40000000000000000),(145302396872369831/62500000000000000)⟩,(999715612519901377/1000000000000000000),(228341048916901437/500000000000000000),(46346243509951437/250000000000000000),(30358847152100361/250000000000000000)⟩
theorem valid4008 : certificate4008.Valid := by decide +kernel
theorem sound4008 : certificate4008.Sound := rat_cut_bin_certificate_sound certificate4008 profilesValid4008 numericValid4008 valid4008

def retention4009 : RatCutRetentionCertificate := ⟨(43/1000),(11/250),(1759028779049966116/509598721095730805365),(1124115987932125479/1000000000000000000),(14/5),(752826641686322861203/320000000000000000000),true,MergedCutProfiles.Batch605.profile24214,![MergedCutProfiles.Batch605.profile24214,MergedCutProfiles.Batch605.profile24239,MergedCutProfiles.Batch605.profile24220,MergedCutProfiles.Batch606.profile24240,MergedCutProfiles.Batch478.profile19134,MergedCutProfiles.Batch606.profile24241,MergedCutProfiles.Batch605.profile24231,MergedCutProfiles.Batch606.profile24242,MergedCutProfiles.Batch359.profile14370,MergedCutProfiles.Batch478.profile19136,MergedCutProfiles.Batch606.profile24243,MergedCutProfiles.Batch606.profile24244,MergedCutProfiles.Batch606.profile24245,MergedCutProfiles.Batch606.profile24246,MergedCutProfiles.Batch478.profile19137,MergedCutProfiles.Batch359.profile14387]⟩
theorem profilesValid4009 : retention4009.ProfilesValid := by
  change ∀ j : Fin 16, (retention4009.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch605.valid24214
  · exact MergedCutProfiles.Batch605.valid24239
  · exact MergedCutProfiles.Batch605.valid24220
  · exact MergedCutProfiles.Batch606.valid24240
  · exact MergedCutProfiles.Batch478.valid19134
  · exact MergedCutProfiles.Batch606.valid24241
  · exact MergedCutProfiles.Batch605.valid24231
  · exact MergedCutProfiles.Batch606.valid24242
  · exact MergedCutProfiles.Batch359.valid14370
  · exact MergedCutProfiles.Batch478.valid19136
  · exact MergedCutProfiles.Batch606.valid24243
  · exact MergedCutProfiles.Batch606.valid24244
  · exact MergedCutProfiles.Batch606.valid24245
  · exact MergedCutProfiles.Batch606.valid24246
  · exact MergedCutProfiles.Batch478.valid19137
  · exact MergedCutProfiles.Batch359.valid14387
theorem numericValid4009 : retention4009.NumericValid := by decide +kernel
def certificate4009 : RatCutBinCertificate := ⟨⟨retention4009,(189524127631560059/100000000000000000),(5622540848385301/62500000000000000),(11894089317798289217/1000000000000000000),(243784539652001747163/40000000000000000),(2312446156165801927/1000000000000000000)⟩,(999715612519901377/1000000000000000000),(114057623397458849/250000000000000000),(185739146884966247/1000000000000000000),(30368337672663899/250000000000000000)⟩
theorem valid4009 : certificate4009.Valid := by decide +kernel
theorem sound4009 : certificate4009.Sound := rat_cut_bin_certificate_sound certificate4009 profilesValid4009 numericValid4009 valid4009

def retention4010 : RatCutRetentionCertificate := ⟨(43/1000),(11/250),(12800000000000000000/101919744219146161073),(439757194762491529/250000000000000000),2,(12931812588061437613219150264689803959/7036115116199864464000000000000000000),false,MergedCutProfiles.Batch606.profile24247,(fun _ => MergedCutProfiles.Batch606.profile24247)⟩
theorem profilesValid4010 : retention4010.ProfilesValid := by
  exact MergedCutProfiles.Batch606.valid24247
theorem numericValid4010 : retention4010.NumericValid := by decide +kernel
def certificate4010 : RatCutBinCertificate := ⟨⟨retention4010,(189524127631560059/100000000000000000),(5622540848385301/62500000000000000),(11894089317798289217/1000000000000000000),(243784539652001747163/40000000000000000),(1809250074053662227/1000000000000000000)⟩,(999715612519901377/1000000000000000000),(477314201325314843/1000000000000000000),(169673505619285251/1000000000000000000),(122055881990787417/1000000000000000000)⟩
theorem valid4010 : certificate4010.Valid := by decide +kernel
theorem sound4010 : certificate4010.Sound := rat_cut_bin_certificate_sound certificate4010 profilesValid4010 numericValid4010 valid4010

def retention4011 : RatCutRetentionCertificate := ⟨(43/1000),(11/250),(1/2),64,1,(408619070903733134070802307191487799/409600000000000000000000000000000000),false,MergedCutProfiles.Batch361.profile14446,(fun _ => MergedCutProfiles.Batch361.profile14446)⟩
theorem profilesValid4011 : retention4011.ProfilesValid := by
  exact MergedCutProfiles.Batch361.valid14446
theorem numericValid4011 : retention4011.NumericValid := by decide +kernel
def certificate4011 : RatCutBinCertificate := ⟨⟨retention4011,(189524127631560059/100000000000000000),(5622540848385301/62500000000000000),(11894089317798289217/1000000000000000000),(243784539652001747163/40000000000000000),(245817634809975469/250000000000000000)⟩,(999715612519901377/1000000000000000000),(135764364758971487/250000000000000000),(2507682997991961/20000000000000000),(24277242159178393/200000000000000000)⟩
theorem valid4011 : certificate4011.Valid := by decide +kernel
theorem sound4011 : certificate4011.Sound := rat_cut_bin_certificate_sound certificate4011 profilesValid4011 numericValid4011 valid4011

def retention4012 : RatCutRetentionCertificate := ⟨(43/1000),(11/250),(12800000000000000000/101919744219146161073),(12234337433095010959/500000000000000000),1,(35318621445082930801531866385008117051/19574939892952017534400000000000000000),false,MergedCutProfiles.Batch606.profile24247,(fun _ => MergedCutProfiles.Batch606.profile24247)⟩
theorem profilesValid4012 : retention4012.ProfilesValid := by
  exact MergedCutProfiles.Batch606.valid24247
theorem numericValid4012 : retention4012.NumericValid := by decide +kernel
def certificate4012 : RatCutBinCertificate := ⟨⟨retention4012,(184111463131560059/100000000000000000),(5622540848385301/62500000000000000),(11894089317798289217/1000000000000000000),(243784539652001747163/40000000000000000),(895176077696371579/500000000000000000)⟩,(62482733413698533/62500000000000000),(32248665278441347/1000000000000000000),(418871595659599093/500000000000000000),(69859944945521281/50000000000000000)⟩
theorem valid4012 : certificate4012.Valid := by decide +kernel
theorem sound4012 : certificate4012.Sound := rat_cut_bin_certificate_sound certificate4012 profilesValid4012 numericValid4012 valid4012

def retention4013 : RatCutRetentionCertificate := ⟨(43/1000),(11/250),(1/2),64,1,(408619070903733134070802307191487799/409600000000000000000000000000000000),false,MergedCutProfiles.Batch361.profile14446,(fun _ => MergedCutProfiles.Batch361.profile14446)⟩
theorem profilesValid4013 : retention4013.ProfilesValid := by
  exact MergedCutProfiles.Batch361.valid14446
theorem numericValid4013 : retention4013.NumericValid := by decide +kernel
def certificate4013 : RatCutBinCertificate := ⟨⟨retention4013,(184111463131560059/100000000000000000),(5622540848385301/62500000000000000),(11894089317798289217/1000000000000000000),(243784539652001747163/40000000000000000),(983679924889605831/1000000000000000000)⟩,(62482733413698533/62500000000000000),(14673590953956923/250000000000000000),(765444090038348637/1000000000000000000),(741347389790416029/1000000000000000000)⟩
theorem valid4013 : certificate4013.Valid := by decide +kernel
theorem sound4013 : certificate4013.Sound := rat_cut_bin_certificate_sound certificate4013 profilesValid4013 numericValid4013 valid4013

def retention4014 : RatCutRetentionCertificate := ⟨(11/250),(9/200),(615791338985707748/484514731338689850595),(603657816866687331/1000000000000000000),4,(9089260040050481633/4000000000000000000),true,MergedCutProfiles.Batch606.profile24248,![MergedCutProfiles.Batch606.profile24248,MergedCutProfiles.Batch606.profile24249,MergedCutProfiles.Batch606.profile24250,MergedCutProfiles.Batch606.profile24251,MergedCutProfiles.Batch479.profile19195,MergedCutProfiles.Batch606.profile24252,MergedCutProfiles.Batch606.profile24253,MergedCutProfiles.Batch606.profile24254,MergedCutProfiles.Batch606.profile24255,MergedCutProfiles.Batch479.profile19196,MergedCutProfiles.Batch606.profile24256,MergedCutProfiles.Batch606.profile24257,MergedCutProfiles.Batch361.profile14450,MergedCutProfiles.Batch606.profile24258,MergedCutProfiles.Batch606.profile24259,MergedCutProfiles.Batch606.profile24260]⟩
theorem profilesValid4014 : retention4014.ProfilesValid := by
  change ∀ j : Fin 16, (retention4014.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch606.valid24248
  · exact MergedCutProfiles.Batch606.valid24249
  · exact MergedCutProfiles.Batch606.valid24250
  · exact MergedCutProfiles.Batch606.valid24251
  · exact MergedCutProfiles.Batch479.valid19195
  · exact MergedCutProfiles.Batch606.valid24252
  · exact MergedCutProfiles.Batch606.valid24253
  · exact MergedCutProfiles.Batch606.valid24254
  · exact MergedCutProfiles.Batch606.valid24255
  · exact MergedCutProfiles.Batch479.valid19196
  · exact MergedCutProfiles.Batch606.valid24256
  · exact MergedCutProfiles.Batch606.valid24257
  · exact MergedCutProfiles.Batch361.valid14450
  · exact MergedCutProfiles.Batch606.valid24258
  · exact MergedCutProfiles.Batch606.valid24259
  · exact MergedCutProfiles.Batch606.valid24260
theorem numericValid4014 : retention4014.NumericValid := by decide +kernel
def certificate4014 : RatCutBinCertificate := ⟨⟨retention4014,(1902675774734127217/1000000000000000000),(11819389720817643/125000000000000000),(12083395261939574679/1000000000000000000),(1177409762622282378903/200000000000000000),(221275925610252623/100000000000000000)⟩,(199941173913169537/200000000000000000),(683008333719045993/1000000000000000000),(56595956258792223/1000000000000000000),(509269544911099/20000000000000000)⟩
theorem valid4014 : certificate4014.Valid := by decide +kernel
theorem sound4014 : certificate4014.Sound := rat_cut_bin_certificate_sound certificate4014 profilesValid4014 numericValid4014 valid4014

def retention4015 : RatCutRetentionCertificate := ⟨(11/250),(9/200),(223732688600000000/96902946267737970119),(153947834746426937/250000000000000000),4,(146141406515005969829/64000000000000000000),true,MergedCutProfiles.Batch606.profile24261,![MergedCutProfiles.Batch606.profile24261,MergedCutProfiles.Batch606.profile24262,MergedCutProfiles.Batch606.profile24263,MergedCutProfiles.Batch480.profile19207,MergedCutProfiles.Batch480.profile19214,MergedCutProfiles.Batch606.profile24256,MergedCutProfiles.Batch361.profile14450,MergedCutProfiles.Batch479.profile19197,MergedCutProfiles.Batch606.profile24260,MergedCutProfiles.Batch606.profile24264,MergedCutProfiles.Batch606.profile24265,MergedCutProfiles.Batch480.profile19208,MergedCutProfiles.Batch606.profile24266,MergedCutProfiles.Batch606.profile24267,MergedCutProfiles.Batch480.profile19216,MergedCutProfiles.Batch480.profile19200]⟩
theorem profilesValid4015 : retention4015.ProfilesValid := by
  change ∀ j : Fin 16, (retention4015.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch606.valid24261
  · exact MergedCutProfiles.Batch606.valid24262
  · exact MergedCutProfiles.Batch606.valid24263
  · exact MergedCutProfiles.Batch480.valid19207
  · exact MergedCutProfiles.Batch480.valid19214
  · exact MergedCutProfiles.Batch606.valid24256
  · exact MergedCutProfiles.Batch361.valid14450
  · exact MergedCutProfiles.Batch479.valid19197
  · exact MergedCutProfiles.Batch606.valid24260
  · exact MergedCutProfiles.Batch606.valid24264
  · exact MergedCutProfiles.Batch606.valid24265
  · exact MergedCutProfiles.Batch480.valid19208
  · exact MergedCutProfiles.Batch606.valid24266
  · exact MergedCutProfiles.Batch606.valid24267
  · exact MergedCutProfiles.Batch480.valid19216
  · exact MergedCutProfiles.Batch480.valid19200
theorem numericValid4015 : retention4015.NumericValid := by decide +kernel
def certificate4015 : RatCutBinCertificate := ⟨⟨retention4015,(1902675774734127217/1000000000000000000),(11819389720817643/125000000000000000),(12083395261939574679/1000000000000000000),(1177409762622282378903/200000000000000000),(2223903730692553879/1000000000000000000)⟩,(199941173913169537/200000000000000000),(670853558091945651/1000000000000000000),(30669371475813849/500000000000000000),(27812913460524303/1000000000000000000)⟩
theorem valid4015 : certificate4015.Valid := by decide +kernel
theorem sound4015 : certificate4015.Sound := rat_cut_bin_certificate_sound certificate4015 profilesValid4015 numericValid4015 valid4015

def retention4016 : RatCutRetentionCertificate := ⟨(11/250),(9/200),(1682256939023806777/484514731338689850595),(1118663443/1000000000),(14/5),(376431621482539077/160000000000000000),true,MergedCutProfiles.Batch606.profile24268,![MergedCutProfiles.Batch606.profile24268,MergedCutProfiles.Batch606.profile24263,MergedCutProfiles.Batch606.profile24269,MergedCutProfiles.Batch606.profile24256,MergedCutProfiles.Batch606.profile24270,MergedCutProfiles.Batch606.profile24260,MergedCutProfiles.Batch606.profile24271,MergedCutProfiles.Batch480.profile19208,MergedCutProfiles.Batch479.profile19199,MergedCutProfiles.Batch480.profile19216,MergedCutProfiles.Batch361.profile14467,MergedCutProfiles.Batch362.profile14482,MergedCutProfiles.Batch606.profile24272,MergedCutProfiles.Batch606.profile24273,MergedCutProfiles.Batch606.profile24274,MergedCutProfiles.Batch480.profile19201]⟩
theorem profilesValid4016 : retention4016.ProfilesValid := by
  change ∀ j : Fin 16, (retention4016.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch606.valid24268
  · exact MergedCutProfiles.Batch606.valid24263
  · exact MergedCutProfiles.Batch606.valid24269
  · exact MergedCutProfiles.Batch606.valid24256
  · exact MergedCutProfiles.Batch606.valid24270
  · exact MergedCutProfiles.Batch606.valid24260
  · exact MergedCutProfiles.Batch606.valid24271
  · exact MergedCutProfiles.Batch480.valid19208
  · exact MergedCutProfiles.Batch479.valid19199
  · exact MergedCutProfiles.Batch480.valid19216
  · exact MergedCutProfiles.Batch361.valid14467
  · exact MergedCutProfiles.Batch362.valid14482
  · exact MergedCutProfiles.Batch606.valid24272
  · exact MergedCutProfiles.Batch606.valid24273
  · exact MergedCutProfiles.Batch606.valid24274
  · exact MergedCutProfiles.Batch480.valid19201
theorem numericValid4016 : retention4016.NumericValid := by decide +kernel
def certificate4016 : RatCutBinCertificate := ⟨⟨retention4016,(1902675774734127217/1000000000000000000),(11819389720817643/125000000000000000),(12083395261939574679/1000000000000000000),(1177409762622282378903/200000000000000000),(144438041878835381/62500000000000000)⟩,(199941173913169537/200000000000000000),(2288196421379773/5000000000000000),(18463577155698311/100000000000000000),(60284386474340909/500000000000000000)⟩
theorem valid4016 : certificate4016.Valid := by decide +kernel
theorem sound4016 : certificate4016.Sound := rat_cut_bin_certificate_sound certificate4016 profilesValid4016 numericValid4016 valid4016

def retention4017 : RatCutRetentionCertificate := ⟨(11/250),(9/200),(55296103083184324153/484514731338689850595),(1682256939023806777/1000000000000000000),(41/20),(5035693516544668053416006796795858029271/2691611102438090843200000000000000000000),false,MergedCutProfiles.Batch606.profile24275,(fun _ => MergedCutProfiles.Batch606.profile24275)⟩
theorem profilesValid4017 : retention4017.ProfilesValid := by
  exact MergedCutProfiles.Batch606.valid24275
theorem numericValid4017 : retention4017.NumericValid := by decide +kernel
def certificate4017 : RatCutBinCertificate := ⟨⟨retention4017,(1902675774734127217/1000000000000000000),(11819389720817643/125000000000000000),(12083395261939574679/1000000000000000000),(1177409762622282378903/200000000000000000),(57511320195911799/31250000000000000)⟩,(199941173913169537/200000000000000000),(477859252421961/1000000000000000),(8463535485769873/50000000000000000),(60266363569097141/500000000000000000)⟩
theorem valid4017 : certificate4017.Valid := by decide +kernel
theorem sound4017 : certificate4017.Sound := rat_cut_bin_certificate_sound certificate4017 profilesValid4017 numericValid4017 valid4017

def retention4018 : RatCutRetentionCertificate := ⟨(11/250),(9/200),(12800000000000000000/96902946267737970119),(55296103083184324153/1000000000000000000),1,(2496995726492448713325550465944695229/1382402577079608103825000000000000000),false,MergedCutProfiles.Batch606.profile24276,(fun _ => MergedCutProfiles.Batch606.profile24276)⟩
theorem profilesValid4018 : retention4018.ProfilesValid := by
  exact MergedCutProfiles.Batch606.valid24276
theorem numericValid4018 : retention4018.NumericValid := by decide +kernel
def certificate4018 : RatCutBinCertificate := ⟨⟨retention4018,(1902675774734127217/1000000000000000000),(11819389720817643/125000000000000000),(12083395261939574679/1000000000000000000),(1177409762622282378903/200000000000000000),(1791383632786063419/1000000000000000000)⟩,(199941173913169537/200000000000000000),(299511171723400443/1000000000000000000),(13574951260904111/40000000000000000),(294348158817465119/500000000000000000)⟩
theorem valid4018 : certificate4018.Valid := by decide +kernel
theorem sound4018 : certificate4018.Sound := rat_cut_bin_certificate_sound certificate4018 profilesValid4018 numericValid4018 valid4018

def retention4019 : RatCutRetentionCertificate := ⟨(11/250),(9/200),(1/2),64,1,(249402263071399035807503415845231079/250000000000000000000000000000000000),false,MergedCutProfiles.Batch364.profile14563,(fun _ => MergedCutProfiles.Batch364.profile14563)⟩
theorem profilesValid4019 : retention4019.ProfilesValid := by
  exact MergedCutProfiles.Batch364.valid14563
theorem numericValid4019 : retention4019.NumericValid := by decide +kernel
def certificate4019 : RatCutBinCertificate := ⟨⟨retention4019,(1902675774734127217/1000000000000000000),(11819389720817643/125000000000000000),(12083395261939574679/1000000000000000000),(1177409762622282378903/200000000000000000),(982720209108533621/1000000000000000000)⟩,(199941173913169537/200000000000000000),(136121193222603239/250000000000000000),(62257296049533289/500000000000000000),(120476744406373921/1000000000000000000)⟩
theorem valid4019 : certificate4019.Valid := by decide +kernel
theorem sound4019 : certificate4019.Sound := rat_cut_bin_certificate_sound certificate4019 profilesValid4019 numericValid4019 valid4019

def certificates : List RatCutBinCertificate := [certificate4008,certificate4009,certificate4010,certificate4011,certificate4012,certificate4013,certificate4014,certificate4015,certificate4016,certificate4017,certificate4018,certificate4019]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4008,List.forall_mem_cons.mpr ⟨sound4009,List.forall_mem_cons.mpr ⟨sound4010,List.forall_mem_cons.mpr ⟨sound4011,List.forall_mem_cons.mpr ⟨sound4012,List.forall_mem_cons.mpr ⟨sound4013,List.forall_mem_cons.mpr ⟨sound4014,List.forall_mem_cons.mpr ⟨sound4015,List.forall_mem_cons.mpr ⟨sound4016,List.forall_mem_cons.mpr ⟨sound4017,List.forall_mem_cons.mpr ⟨sound4018,List.forall_mem_cons.mpr ⟨sound4019,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch334
