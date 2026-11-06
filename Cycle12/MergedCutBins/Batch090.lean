import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch180
import Cycle12.MergedCutProfiles.Batch181
import Cycle12.MergedCutProfiles.Batch182

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch090

def retention1080 : RatCutRetentionCertificate := ⟨(213/4000),(107/2000),(1/2),64,1,(63849665351748933296377500448309661191/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch180.profile7220,(fun _ => MergedCutProfiles.Batch180.profile7220)⟩
theorem profilesValid1080 : retention1080.ProfilesValid := by
  exact MergedCutProfiles.Batch180.valid7220
theorem numericValid1080 : retention1080.NumericValid := by decide +kernel
def certificate1080 : RatCutBinCertificate := ⟨⟨retention1080,(2218850897971299201/1000000000000000000),(17460968802135489/125000000000000000),(14073406348625911771/1000000000000000000),(28767052000251793197/125000000000000000),(975627267787237491/1000000000000000000)⟩,(495839751853237429/500000000000000000),(55293865062893101/125000000000000000),(196844408765270117/1000000000000000000),(187574803790600313/1000000000000000000)⟩
theorem valid1080 : certificate1080.Valid := by decide +kernel
theorem sound1080 : certificate1080.Sound := rat_cut_bin_certificate_sound certificate1080 profilesValid1080 numericValid1080 valid1080

def retention1081 : RatCutRetentionCertificate := ⟨(213/4000),(107/2000),(3719917646425499801/8164330071884685950),(3634330415175817653/1000000000000000000),(6/5),(393192066095815386859266944675699032511/363433041517581765300000000000000000000),false,MergedCutProfiles.Batch180.profile7221,(fun _ => MergedCutProfiles.Batch180.profile7221)⟩
theorem profilesValid1081 : retention1081.ProfilesValid := by
  exact MergedCutProfiles.Batch180.valid7221
theorem numericValid1081 : retention1081.NumericValid := by decide +kernel
def certificate1081 : RatCutBinCertificate := ⟨⟨retention1081,(2572429548971299201/1000000000000000000),(17460968802135489/125000000000000000),(14073406348625911771/1000000000000000000),(28767052000251793197/125000000000000000),(210247836961177367/200000000000000000)⟩,(990351564019419111/1000000000000000000),(387638224127060697/1000000000000000000),(245001755127445679/1000000000000000000),(88417654614776861/500000000000000000)⟩
theorem valid1081 : certificate1081.Valid := by decide +kernel
theorem sound1081 : certificate1081.Sound := rat_cut_bin_certificate_sound certificate1081 profilesValid1081 numericValid1081 valid1081

def retention1082 : RatCutRetentionCertificate := ⟨(213/4000),(107/2000),(2014068883908038996/4082165035942342975),(3719917646425499801/500000000000000000),(21/20),(2978762308781782846926898809090635050559/2975934117140399840800000000000000000000),false,MergedCutProfiles.Batch180.profile7222,(fun _ => MergedCutProfiles.Batch180.profile7222)⟩
theorem profilesValid1082 : retention1082.ProfilesValid := by
  exact MergedCutProfiles.Batch180.valid7222
theorem numericValid1082 : retention1082.NumericValid := by decide +kernel
def certificate1082 : RatCutBinCertificate := ⟨⟨retention1082,(2572429548971299201/1000000000000000000),(17460968802135489/125000000000000000),(14073406348625911771/1000000000000000000),(28767052000251793197/125000000000000000),(974138575443543417/1000000000000000000)⟩,(990351564019419111/1000000000000000000),(4183188111048681/10000000000000000),(217110797156422387/1000000000000000000),(178203523349705383/1000000000000000000)⟩
theorem valid1082 : certificate1082.Valid := by decide +kernel
theorem sound1082 : certificate1082.Sound := rat_cut_bin_certificate_sound certificate1082 profilesValid1082 numericValid1082 valid1082

def retention1083 : RatCutRetentionCertificate := ⟨(213/4000),(107/2000),(2034209572747119386/4082165035942342975),(503517220977009749/62500000000000000),(21/20),(50034104835312851378826018749450100359/50351722097700974900000000000000000000),false,MergedCutProfiles.Batch180.profile7223,(fun _ => MergedCutProfiles.Batch180.profile7223)⟩
theorem profilesValid1083 : retention1083.ProfilesValid := by
  exact MergedCutProfiles.Batch180.valid7223
theorem numericValid1083 : retention1083.NumericValid := by decide +kernel
def certificate1083 : RatCutBinCertificate := ⟨⟨retention1083,(2572429548971299201/1000000000000000000),(17460968802135489/125000000000000000),(14073406348625911771/1000000000000000000),(28767052000251793197/125000000000000000),(966880408401005067/1000000000000000000)⟩,(990351564019419111/1000000000000000000),(421459042080337333/1000000000000000000),(107192939284826173/500000000000000000),(88111371045264143/500000000000000000)⟩
theorem valid1083 : certificate1083.Valid := by decide +kernel
theorem sound1083 : certificate1083.Sound := rat_cut_bin_certificate_sound certificate1083 profilesValid1083 numericValid1083 valid1083

def retention1084 : RatCutRetentionCertificate := ⟨(213/4000),(107/2000),(1/2),(1017104786373559693/125000000000000000),(21/20),(50382401056055591034764919689430466659/50855239318677984650000000000000000000),false,MergedCutProfiles.Batch180.profile7220,(fun _ => MergedCutProfiles.Batch180.profile7220)⟩
theorem profilesValid1084 : retention1084.ProfilesValid := by
  exact MergedCutProfiles.Batch180.valid7220
theorem numericValid1084 : retention1084.NumericValid := by decide +kernel
def certificate1084 : RatCutBinCertificate := ⟨⟨retention1084,(2572429548971299201/1000000000000000000),(17460968802135489/125000000000000000),(14073406348625911771/1000000000000000000),(28767052000251793197/125000000000000000),(963890670056980519/1000000000000000000)⟩,(990351564019419111/1000000000000000000),(422766298491968491/1000000000000000000),(213258419441148897/1000000000000000000),(21872176572648367/125000000000000000)⟩
theorem valid1084 : certificate1084.Valid := by decide +kernel
theorem sound1084 : certificate1084.Sound := rat_cut_bin_certificate_sound certificate1084 profilesValid1084 numericValid1084 valid1084

def retention1085 : RatCutRetentionCertificate := ⟨(107/2000),(43/800),(84528509139273902/1468493008080894107),(425082802043160739/500000000000000000),(57/20),(1299949933682463685091/640000000000000000000),true,MergedCutProfiles.Batch180.profile7224,![MergedCutProfiles.Batch180.profile7224,MergedCutProfiles.Batch180.profile7225,MergedCutProfiles.Batch180.profile7226,MergedCutProfiles.Batch180.profile7227,MergedCutProfiles.Batch180.profile7228,MergedCutProfiles.Batch180.profile7229,MergedCutProfiles.Batch180.profile7230,MergedCutProfiles.Batch180.profile7231,MergedCutProfiles.Batch180.profile7232,MergedCutProfiles.Batch180.profile7233,MergedCutProfiles.Batch180.profile7234,MergedCutProfiles.Batch180.profile7235,MergedCutProfiles.Batch180.profile7236,MergedCutProfiles.Batch180.profile7237,MergedCutProfiles.Batch180.profile7238,MergedCutProfiles.Batch180.profile7239]⟩
theorem profilesValid1085 : retention1085.ProfilesValid := by
  change ∀ j : Fin 16, (retention1085.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch180.valid7224
  · exact MergedCutProfiles.Batch180.valid7225
  · exact MergedCutProfiles.Batch180.valid7226
  · exact MergedCutProfiles.Batch180.valid7227
  · exact MergedCutProfiles.Batch180.valid7228
  · exact MergedCutProfiles.Batch180.valid7229
  · exact MergedCutProfiles.Batch180.valid7230
  · exact MergedCutProfiles.Batch180.valid7231
  · exact MergedCutProfiles.Batch180.valid7232
  · exact MergedCutProfiles.Batch180.valid7233
  · exact MergedCutProfiles.Batch180.valid7234
  · exact MergedCutProfiles.Batch180.valid7235
  · exact MergedCutProfiles.Batch180.valid7236
  · exact MergedCutProfiles.Batch180.valid7237
  · exact MergedCutProfiles.Batch180.valid7238
  · exact MergedCutProfiles.Batch180.valid7239
theorem numericValid1085 : retention1085.NumericValid := by decide +kernel
def certificate1085 : RatCutBinCertificate := ⟨⟨retention1085,(222324745821655737/100000000000000000),(141191287371203791/1000000000000000000),(2826808495791424153/200000000000000000),(9145923414009625841/40000000000000000),(1967859945565654019/1000000000000000000)⟩,(198324611552135299/200000000000000000),(91193337513695103/250000000000000000),(267356549667484097/1000000000000000000),(142230454398138909/1000000000000000000)⟩
theorem valid1085 : certificate1085.Valid := by decide +kernel
theorem sound1085 : certificate1085.Sound := rat_cut_bin_certificate_sound certificate1085 profilesValid1085 numericValid1085 valid1085

def retention1086 : RatCutRetentionCertificate := ⟨(107/2000),(43/800),(1499069734161536987/16153423088889835177),(464906800266006461/500000000000000000),(13/5),(307153750091111726349/160000000000000000000),true,MergedCutProfiles.Batch181.profile7240,![MergedCutProfiles.Batch181.profile7240,MergedCutProfiles.Batch181.profile7241,MergedCutProfiles.Batch181.profile7242,MergedCutProfiles.Batch181.profile7243,MergedCutProfiles.Batch181.profile7244,MergedCutProfiles.Batch181.profile7245,MergedCutProfiles.Batch181.profile7246,MergedCutProfiles.Batch181.profile7247,MergedCutProfiles.Batch181.profile7248,MergedCutProfiles.Batch181.profile7249,MergedCutProfiles.Batch181.profile7250,MergedCutProfiles.Batch181.profile7251,MergedCutProfiles.Batch181.profile7252,MergedCutProfiles.Batch181.profile7253,MergedCutProfiles.Batch181.profile7254,MergedCutProfiles.Batch181.profile7255]⟩
theorem profilesValid1086 : retention1086.ProfilesValid := by
  change ∀ j : Fin 16, (retention1086.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch181.valid7240
  · exact MergedCutProfiles.Batch181.valid7241
  · exact MergedCutProfiles.Batch181.valid7242
  · exact MergedCutProfiles.Batch181.valid7243
  · exact MergedCutProfiles.Batch181.valid7244
  · exact MergedCutProfiles.Batch181.valid7245
  · exact MergedCutProfiles.Batch181.valid7246
  · exact MergedCutProfiles.Batch181.valid7247
  · exact MergedCutProfiles.Batch181.valid7248
  · exact MergedCutProfiles.Batch181.valid7249
  · exact MergedCutProfiles.Batch181.valid7250
  · exact MergedCutProfiles.Batch181.valid7251
  · exact MergedCutProfiles.Batch181.valid7252
  · exact MergedCutProfiles.Batch181.valid7253
  · exact MergedCutProfiles.Batch181.valid7254
  · exact MergedCutProfiles.Batch181.valid7255
theorem numericValid1086 : retention1086.NumericValid := by decide +kernel
def certificate1086 : RatCutBinCertificate := ⟨⟨retention1086,(222324745821655737/100000000000000000),(141191287371203791/1000000000000000000),(2826808495791424153/200000000000000000),(9145923414009625841/40000000000000000),(465488186992790391/250000000000000000)⟩,(198324611552135299/200000000000000000),(186076688662921837/500000000000000000),(16249302375163463/62500000000000000),(142206342047537223/1000000000000000000)⟩
theorem valid1086 : certificate1086.Valid := by decide +kernel
theorem sound1086 : certificate1086.Sound := rat_cut_bin_certificate_sound certificate1086 profilesValid1086 numericValid1086 valid1086

def retention1087 : RatCutRetentionCertificate := ⟨(107/2000),(43/800),(4095251593709649821/16153423088889835177),(1499069734161536987/1000000000000000000),(9/5),(1929659286235587473703/1280000000000000000000),true,MergedCutProfiles.Batch181.profile7256,![MergedCutProfiles.Batch181.profile7256,MergedCutProfiles.Batch181.profile7257,MergedCutProfiles.Batch181.profile7258,MergedCutProfiles.Batch181.profile7259,MergedCutProfiles.Batch181.profile7260,MergedCutProfiles.Batch181.profile7261,MergedCutProfiles.Batch181.profile7262,MergedCutProfiles.Batch181.profile7263,MergedCutProfiles.Batch181.profile7264,MergedCutProfiles.Batch181.profile7265,MergedCutProfiles.Batch181.profile7266,MergedCutProfiles.Batch181.profile7267,MergedCutProfiles.Batch181.profile7268,MergedCutProfiles.Batch181.profile7269,MergedCutProfiles.Batch181.profile7270,MergedCutProfiles.Batch181.profile7271]⟩
theorem profilesValid1087 : retention1087.ProfilesValid := by
  change ∀ j : Fin 16, (retention1087.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch181.valid7256
  · exact MergedCutProfiles.Batch181.valid7257
  · exact MergedCutProfiles.Batch181.valid7258
  · exact MergedCutProfiles.Batch181.valid7259
  · exact MergedCutProfiles.Batch181.valid7260
  · exact MergedCutProfiles.Batch181.valid7261
  · exact MergedCutProfiles.Batch181.valid7262
  · exact MergedCutProfiles.Batch181.valid7263
  · exact MergedCutProfiles.Batch181.valid7264
  · exact MergedCutProfiles.Batch181.valid7265
  · exact MergedCutProfiles.Batch181.valid7266
  · exact MergedCutProfiles.Batch181.valid7267
  · exact MergedCutProfiles.Batch181.valid7268
  · exact MergedCutProfiles.Batch181.valid7269
  · exact MergedCutProfiles.Batch181.valid7270
  · exact MergedCutProfiles.Batch181.valid7271
theorem numericValid1087 : retention1087.NumericValid := by decide +kernel
def certificate1087 : RatCutBinCertificate := ⟨⟨retention1087,(222324745821655737/100000000000000000),(141191287371203791/1000000000000000000),(2826808495791424153/200000000000000000),(9145923414009625841/40000000000000000),(1467560940725507863/1000000000000000000)⟩,(198324611552135299/200000000000000000),(403418018270098941/1000000000000000000),(46073031857023601/200000000000000000),(8926546518474879/62500000000000000)⟩
theorem valid1087 : certificate1087.Valid := by decide +kernel
theorem sound1087 : certificate1087.Sound := rat_cut_bin_certificate_sound certificate1087 profilesValid1087 numericValid1087 valid1087

def retention1088 : RatCutRetentionCertificate := ⟨(107/2000),(43/800),(549963880340082487/1242571006837679629),(4095251593709649821/1000000000000000000),(21/20),(1377070891096880038389/1280000000000000000000),true,MergedCutProfiles.Batch181.profile7272,![MergedCutProfiles.Batch181.profile7272,MergedCutProfiles.Batch181.profile7273,MergedCutProfiles.Batch181.profile7274,MergedCutProfiles.Batch181.profile7275,MergedCutProfiles.Batch181.profile7276,MergedCutProfiles.Batch181.profile7277,MergedCutProfiles.Batch181.profile7278,MergedCutProfiles.Batch181.profile7279,MergedCutProfiles.Batch182.profile7280,MergedCutProfiles.Batch182.profile7281,MergedCutProfiles.Batch182.profile7282,MergedCutProfiles.Batch182.profile7283,MergedCutProfiles.Batch182.profile7284,MergedCutProfiles.Batch182.profile7285,MergedCutProfiles.Batch182.profile7286,MergedCutProfiles.Batch182.profile7287]⟩
theorem profilesValid1088 : retention1088.ProfilesValid := by
  change ∀ j : Fin 16, (retention1088.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch181.valid7272
  · exact MergedCutProfiles.Batch181.valid7273
  · exact MergedCutProfiles.Batch181.valid7274
  · exact MergedCutProfiles.Batch181.valid7275
  · exact MergedCutProfiles.Batch181.valid7276
  · exact MergedCutProfiles.Batch181.valid7277
  · exact MergedCutProfiles.Batch181.valid7278
  · exact MergedCutProfiles.Batch181.valid7279
  · exact MergedCutProfiles.Batch182.valid7280
  · exact MergedCutProfiles.Batch182.valid7281
  · exact MergedCutProfiles.Batch182.valid7282
  · exact MergedCutProfiles.Batch182.valid7283
  · exact MergedCutProfiles.Batch182.valid7284
  · exact MergedCutProfiles.Batch182.valid7285
  · exact MergedCutProfiles.Batch182.valid7286
  · exact MergedCutProfiles.Batch182.valid7287
theorem numericValid1088 : retention1088.NumericValid := by decide +kernel
def certificate1088 : RatCutBinCertificate := ⟨⟨retention1088,(222324745821655737/100000000000000000),(141191287371203791/1000000000000000000),(2826808495791424153/200000000000000000),(9145923414009625841/40000000000000000),(1052513818426472831/1000000000000000000)⟩,(198324611552135299/200000000000000000),(463242547944304121/1000000000000000000),(180290046541532611/1000000000000000000),(145191761370356951/1000000000000000000)⟩
theorem valid1088 : certificate1088.Valid := by decide +kernel
theorem sound1088 : certificate1088.Sound := rat_cut_bin_certificate_sound certificate1088 profilesValid1088 numericValid1088 valid1088

def retention1089 : RatCutRetentionCertificate := ⟨(107/2000),(43/800),(7897529515208518480/16153423088889835177),(7149530444421072331/1000000000000000000),(21/20),(11534162334730529632971795451924176778319/11439248711073715729600000000000000000000),false,MergedCutProfiles.Batch182.profile7288,(fun _ => MergedCutProfiles.Batch182.profile7288)⟩
theorem profilesValid1089 : retention1089.ProfilesValid := by
  exact MergedCutProfiles.Batch182.valid7288
theorem numericValid1089 : retention1089.NumericValid := by decide +kernel
def certificate1089 : RatCutBinCertificate := ⟨⟨retention1089,(222324745821655737/100000000000000000),(141191287371203791/1000000000000000000),(2826808495791424153/200000000000000000),(9145923414009625841/40000000000000000),(984975805682142781/1000000000000000000)⟩,(198324611552135299/200000000000000000),(117210783684195711/250000000000000000),(8800706024817703/50000000000000000),(2909142460543297/20000000000000000)⟩
theorem valid1089 : certificate1089.Valid := by decide +kernel
theorem sound1089 : certificate1089.Sound := rat_cut_bin_certificate_sound certificate1089 profilesValid1089 numericValid1089 valid1089

def retention1090 : RatCutRetentionCertificate := ⟨(107/2000),(43/800),(8056269858464209702/16153423088889835177),(98719118940106481/12500000000000000),(21/20),(6269734279043799119904341061612204931/6318023612166814784000000000000000000),false,MergedCutProfiles.Batch182.profile7289,(fun _ => MergedCutProfiles.Batch182.profile7289)⟩
theorem profilesValid1090 : retention1090.ProfilesValid := by
  exact MergedCutProfiles.Batch182.valid7289
theorem numericValid1090 : retention1090.NumericValid := by decide +kernel
def certificate1090 : RatCutBinCertificate := ⟨⟨retention1090,(222324745821655737/100000000000000000),(141191287371203791/1000000000000000000),(2826808495791424153/200000000000000000),(9145923414009625841/40000000000000000),(193807137925137417/200000000000000000)⟩,(198324611552135299/200000000000000000),(473178150500505467/1000000000000000000),(172750402348607649/1000000000000000000),(71091959386123667/500000000000000000)⟩
theorem valid1090 : certificate1090.Valid := by decide +kernel
theorem sound1090 : certificate1090.Sound := rat_cut_bin_certificate_sound certificate1090 profilesValid1090 numericValid1090 valid1090

def retention1091 : RatCutRetentionCertificate := ⟨(107/2000),(43/800),(1/2),(4028134929232104851/500000000000000000),(21/20),(3191718916012853948869011308693947348479/3222507943385683880800000000000000000000),false,MergedCutProfiles.Batch182.profile7290,(fun _ => MergedCutProfiles.Batch182.profile7290)⟩
theorem profilesValid1091 : retention1091.ProfilesValid := by
  exact MergedCutProfiles.Batch182.valid7290
theorem numericValid1091 : retention1091.NumericValid := by decide +kernel
def certificate1091 : RatCutBinCertificate := ⟨⟨retention1091,(222324745821655737/100000000000000000),(141191287371203791/1000000000000000000),(2826808495791424153/200000000000000000),(9145923414009625841/40000000000000000),(967124463071809281/1000000000000000000)⟩,(198324611552135299/200000000000000000),(473475942430632399/1000000000000000000),(172527664598534171/1000000000000000000),(8876853261755483/62500000000000000)⟩
theorem valid1091 : certificate1091.Valid := by decide +kernel
theorem sound1091 : certificate1091.Sound := rat_cut_bin_certificate_sound certificate1091 profilesValid1091 numericValid1091 valid1091

def certificates : List RatCutBinCertificate := [certificate1080,certificate1081,certificate1082,certificate1083,certificate1084,certificate1085,certificate1086,certificate1087,certificate1088,certificate1089,certificate1090,certificate1091]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1080,List.forall_mem_cons.mpr ⟨sound1081,List.forall_mem_cons.mpr ⟨sound1082,List.forall_mem_cons.mpr ⟨sound1083,List.forall_mem_cons.mpr ⟨sound1084,List.forall_mem_cons.mpr ⟨sound1085,List.forall_mem_cons.mpr ⟨sound1086,List.forall_mem_cons.mpr ⟨sound1087,List.forall_mem_cons.mpr ⟨sound1088,List.forall_mem_cons.mpr ⟨sound1089,List.forall_mem_cons.mpr ⟨sound1090,List.forall_mem_cons.mpr ⟨sound1091,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch090
