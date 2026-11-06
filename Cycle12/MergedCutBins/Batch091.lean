import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch182
import Cycle12.MergedCutProfiles.Batch183
import Cycle12.MergedCutProfiles.Batch184

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch091

def retention1092 : RatCutRetentionCertificate := ⟨(107/2000),(43/800),(1/2),64,1,(63849746992852456848041125225493792271/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch182.profile7290,(fun _ => MergedCutProfiles.Batch182.profile7290)⟩
theorem profilesValid1092 : retention1092.ProfilesValid := by
  exact MergedCutProfiles.Batch182.valid7290
theorem numericValid1092 : retention1092.NumericValid := by decide +kernel
def certificate1092 : RatCutBinCertificate := ⟨⟨retention1092,(222324745821655737/100000000000000000),(141191287371203791/1000000000000000000),(2826808495791424153/200000000000000000),(9145923414009625841/40000000000000000),(975443066818220459/1000000000000000000)⟩,(198324611552135299/200000000000000000),(88391837068301809/200000000000000000),(197164097200618751/1000000000000000000),(37566738500714853/200000000000000000)⟩
theorem valid1092 : certificate1092.Valid := by decide +kernel
theorem sound1092 : certificate1092.Sound := rat_cut_bin_certificate_sound certificate1092 profilesValid1092 numericValid1092 valid1092

def retention1093 : RatCutRetentionCertificate := ⟨(107/2000),(43/800),(7380896770018767869/16153423088889835177),(3641594569279167081/1000000000000000000),(6/5),(2090974951980735249865047947188305883/1937018387914450575000000000000000000),false,MergedCutProfiles.Batch182.profile7291,(fun _ => MergedCutProfiles.Batch182.profile7291)⟩
theorem profilesValid1093 : retention1093.ProfilesValid := by
  exact MergedCutProfiles.Batch182.valid7291
theorem numericValid1093 : retention1093.NumericValid := by decide +kernel
def certificate1093 : RatCutBinCertificate := ⟨⟨retention1093,(257521979521655737/100000000000000000),(141191287371203791/1000000000000000000),(2826808495791424153/200000000000000000),(9145923414009625841/40000000000000000),(1048606817019970917/1000000000000000000)⟩,(123786847130967443/125000000000000000),(387362574433485357/1000000000000000000),(245263065574825921/1000000000000000000),(88351111057537573/500000000000000000)⟩
theorem valid1093 : certificate1093.Valid := by decide +kernel
theorem sound1093 : certificate1093.Sound := rat_cut_bin_certificate_sound certificate1093 profilesValid1093 numericValid1093 valid1093

def retention1094 : RatCutRetentionCertificate := ⟨(107/2000),(43/800),(726586687360314559/1468493008080894107),(7380896770018767869/1000000000000000000),(21/20),(11786091481751743290008136732533910895839/11809434832030028590400000000000000000000),false,MergedCutProfiles.Batch182.profile7292,(fun _ => MergedCutProfiles.Batch182.profile7292)⟩
theorem profilesValid1094 : retention1094.ProfilesValid := by
  exact MergedCutProfiles.Batch182.valid7292
theorem numericValid1094 : retention1094.NumericValid := by decide +kernel
def certificate1094 : RatCutBinCertificate := ⟨⟨retention1094,(257521979521655737/100000000000000000),(141191287371203791/1000000000000000000),(2826808495791424153/200000000000000000),(9145923414009625841/40000000000000000),(242752475455994713/250000000000000000)⟩,(123786847130967443/125000000000000000),(52289764945542167/125000000000000000),(13569462489124359/62500000000000000),(177530447302752227/1000000000000000000)⟩
theorem valid1094 : certificate1094.Valid := by decide +kernel
theorem sound1094 : certificate1094.Sound := rat_cut_bin_certificate_sound certificate1094 profilesValid1094 numericValid1094 valid1094

def retention1095 : RatCutRetentionCertificate := ⟨(107/2000),(43/800),(8072378096573094751/16153423088889835177),(7992453560963460149/1000000000000000000),(21/20),(12669690002544352489456450146515665124679/12787925697541536238400000000000000000000),false,MergedCutProfiles.Batch182.profile7293,(fun _ => MergedCutProfiles.Batch182.profile7293)⟩
theorem profilesValid1095 : retention1095.ProfilesValid := by
  exact MergedCutProfiles.Batch182.valid7293
theorem numericValid1095 : retention1095.NumericValid := by decide +kernel
def certificate1095 : RatCutBinCertificate := ⟨⟨retention1095,(257521979521655737/100000000000000000),(141191287371203791/1000000000000000000),(2826808495791424153/200000000000000000),(9145923414009625841/40000000000000000),(963740850698266173/1000000000000000000)⟩,(123786847130967443/125000000000000000),(421473299502722227/1000000000000000000),(214373560241450239/1000000000000000000),(8777385554824727/50000000000000000)⟩
theorem valid1095 : certificate1095.Valid := by decide +kernel
theorem sound1095 : certificate1095.Sound := rat_cut_bin_certificate_sound certificate1095 profilesValid1095 numericValid1095 valid1095

def retention1096 : RatCutRetentionCertificate := ⟨(107/2000),(43/800),(1/2),(8072378096573094751/1000000000000000000),(21/20),(12793074867826734206063944354434511770159/12915804954516951601600000000000000000000),false,MergedCutProfiles.Batch182.profile7290,(fun _ => MergedCutProfiles.Batch182.profile7290)⟩
theorem profilesValid1096 : retention1096.ProfilesValid := by
  exact MergedCutProfiles.Batch182.valid7290
theorem numericValid1096 : retention1096.NumericValid := by decide +kernel
def certificate1096 : RatCutBinCertificate := ⟨⟨retention1096,(257521979521655737/100000000000000000),(141191287371203791/1000000000000000000),(2826808495791424153/200000000000000000),(9145923414009625841/40000000000000000),(48174221883821467/50000000000000000)⟩,(123786847130967443/125000000000000000),(421585466589312293/1000000000000000000),(214276665362157053/1000000000000000000),(175598490165540053/1000000000000000000)⟩
theorem valid1096 : certificate1096.Valid := by decide +kernel
theorem sound1096 : certificate1096.Sound := rat_cut_bin_certificate_sound certificate1096 profilesValid1096 numericValid1096 valid1096

def retention1097 : RatCutRetentionCertificate := ⟨(43/800),(27/500),(430249988577009907/7990359840914203949),(843544728118831303/1000000000000000000),(57/20),(81574329337677575313/40000000000000000000),true,MergedCutProfiles.Batch182.profile7294,![MergedCutProfiles.Batch182.profile7294,MergedCutProfiles.Batch182.profile7295,MergedCutProfiles.Batch182.profile7296,MergedCutProfiles.Batch182.profile7297,MergedCutProfiles.Batch182.profile7298,MergedCutProfiles.Batch182.profile7299,MergedCutProfiles.Batch182.profile7300,MergedCutProfiles.Batch182.profile7301,MergedCutProfiles.Batch182.profile7302,MergedCutProfiles.Batch182.profile7303,MergedCutProfiles.Batch182.profile7304,MergedCutProfiles.Batch182.profile7305,MergedCutProfiles.Batch182.profile7306,MergedCutProfiles.Batch182.profile7307,MergedCutProfiles.Batch182.profile7308,MergedCutProfiles.Batch182.profile7309]⟩
theorem profilesValid1097 : retention1097.ProfilesValid := by
  change ∀ j : Fin 16, (retention1097.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch182.valid7294
  · exact MergedCutProfiles.Batch182.valid7295
  · exact MergedCutProfiles.Batch182.valid7296
  · exact MergedCutProfiles.Batch182.valid7297
  · exact MergedCutProfiles.Batch182.valid7298
  · exact MergedCutProfiles.Batch182.valid7299
  · exact MergedCutProfiles.Batch182.valid7300
  · exact MergedCutProfiles.Batch182.valid7301
  · exact MergedCutProfiles.Batch182.valid7302
  · exact MergedCutProfiles.Batch182.valid7303
  · exact MergedCutProfiles.Batch182.valid7304
  · exact MergedCutProfiles.Batch182.valid7305
  · exact MergedCutProfiles.Batch182.valid7306
  · exact MergedCutProfiles.Batch182.valid7307
  · exact MergedCutProfiles.Batch182.valid7308
  · exact MergedCutProfiles.Batch182.valid7309
theorem numericValid1097 : retention1097.NumericValid := by decide +kernel
def certificate1097 : RatCutBinCertificate := ⟨⟨retention1097,(1113526092303454291/500000000000000000),(142705547327693923/1000000000000000000),(2839015555850207423/200000000000000000),(227180872034970018037/1000000000000000000),(1975533090969388211/1000000000000000000)⟩,(495784529389865187/500000000000000000),(365271381626671529/1000000000000000000),(266854689479128419/1000000000000000000),(8883435357695713/62500000000000000)⟩
theorem valid1097 : certificate1097.Valid := by decide +kernel
theorem sound1097 : certificate1097.Sound := rat_cut_bin_certificate_sound certificate1097 profilesValid1097 numericValid1097 valid1097

def retention1098 : RatCutRetentionCertificate := ⟨(43/800),(27/500),(489664620905994508/7990359840914203949),(430249988577009907/500000000000000000),(14/5),(1290361987130799536159/640000000000000000000),true,MergedCutProfiles.Batch182.profile7310,![MergedCutProfiles.Batch182.profile7310,MergedCutProfiles.Batch182.profile7311,MergedCutProfiles.Batch182.profile7312,MergedCutProfiles.Batch182.profile7313,MergedCutProfiles.Batch182.profile7314,MergedCutProfiles.Batch182.profile7315,MergedCutProfiles.Batch182.profile7316,MergedCutProfiles.Batch182.profile7317,MergedCutProfiles.Batch182.profile7318,MergedCutProfiles.Batch182.profile7319,MergedCutProfiles.Batch183.profile7320,MergedCutProfiles.Batch183.profile7321,MergedCutProfiles.Batch183.profile7322,MergedCutProfiles.Batch183.profile7323,MergedCutProfiles.Batch183.profile7324,MergedCutProfiles.Batch183.profile7325]⟩
theorem profilesValid1098 : retention1098.ProfilesValid := by
  change ∀ j : Fin 16, (retention1098.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch182.valid7310
  · exact MergedCutProfiles.Batch182.valid7311
  · exact MergedCutProfiles.Batch182.valid7312
  · exact MergedCutProfiles.Batch182.valid7313
  · exact MergedCutProfiles.Batch182.valid7314
  · exact MergedCutProfiles.Batch182.valid7315
  · exact MergedCutProfiles.Batch182.valid7316
  · exact MergedCutProfiles.Batch182.valid7317
  · exact MergedCutProfiles.Batch182.valid7318
  · exact MergedCutProfiles.Batch182.valid7319
  · exact MergedCutProfiles.Batch183.valid7320
  · exact MergedCutProfiles.Batch183.valid7321
  · exact MergedCutProfiles.Batch183.valid7322
  · exact MergedCutProfiles.Batch183.valid7323
  · exact MergedCutProfiles.Batch183.valid7324
  · exact MergedCutProfiles.Batch183.valid7325
theorem numericValid1098 : retention1098.NumericValid := by decide +kernel
def certificate1098 : RatCutBinCertificate := ⟨⟨retention1098,(1113526092303454291/500000000000000000),(142705547327693923/1000000000000000000),(2839015555850207423/200000000000000000),(227180872034970018037/1000000000000000000),(976742618887271331/500000000000000000)⟩,(495784529389865187/500000000000000000),(366405618935475503/1000000000000000000),(265714262752807331/1000000000000000000),(142311376955694583/1000000000000000000)⟩
theorem valid1098 : certificate1098.Valid := by decide +kernel
theorem sound1098 : certificate1098.Sound := rat_cut_bin_certificate_sound certificate1098 profilesValid1098 numericValid1098 valid1098

def retention1099 : RatCutRetentionCertificate := ⟨(43/800),(27/500),(125823493663869456/1141479977273457707),(122416155226498627/125000000000000000),(5/2),(11966561737479834293/6400000000000000000),true,MergedCutProfiles.Batch183.profile7326,![MergedCutProfiles.Batch183.profile7326,MergedCutProfiles.Batch183.profile7327,MergedCutProfiles.Batch183.profile7328,MergedCutProfiles.Batch183.profile7329,MergedCutProfiles.Batch182.profile7318,MergedCutProfiles.Batch183.profile7330,MergedCutProfiles.Batch183.profile7331,MergedCutProfiles.Batch183.profile7332,MergedCutProfiles.Batch183.profile7333,MergedCutProfiles.Batch183.profile7334,MergedCutProfiles.Batch183.profile7335,MergedCutProfiles.Batch183.profile7336,MergedCutProfiles.Batch183.profile7337,MergedCutProfiles.Batch183.profile7338,MergedCutProfiles.Batch183.profile7339,MergedCutProfiles.Batch183.profile7340]⟩
theorem profilesValid1099 : retention1099.ProfilesValid := by
  change ∀ j : Fin 16, (retention1099.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch183.valid7326
  · exact MergedCutProfiles.Batch183.valid7327
  · exact MergedCutProfiles.Batch183.valid7328
  · exact MergedCutProfiles.Batch183.valid7329
  · exact MergedCutProfiles.Batch182.valid7318
  · exact MergedCutProfiles.Batch183.valid7330
  · exact MergedCutProfiles.Batch183.valid7331
  · exact MergedCutProfiles.Batch183.valid7332
  · exact MergedCutProfiles.Batch183.valid7333
  · exact MergedCutProfiles.Batch183.valid7334
  · exact MergedCutProfiles.Batch183.valid7335
  · exact MergedCutProfiles.Batch183.valid7336
  · exact MergedCutProfiles.Batch183.valid7337
  · exact MergedCutProfiles.Batch183.valid7338
  · exact MergedCutProfiles.Batch183.valid7339
  · exact MergedCutProfiles.Batch183.valid7340
theorem numericValid1099 : retention1099.NumericValid := by decide +kernel
def certificate1099 : RatCutBinCertificate := ⟨⟨retention1099,(1113526092303454291/500000000000000000),(142705547327693923/1000000000000000000),(2839015555850207423/200000000000000000),(227180872034970018037/1000000000000000000),(72551542741884111/40000000000000000)⟩,(495784529389865187/500000000000000000),(46899581423229577/125000000000000000),(256993387109646661/1000000000000000000),(142391028068624633/1000000000000000000)⟩
theorem valid1099 : certificate1099.Valid := by decide +kernel
theorem sound1099 : certificate1099.Sound := rat_cut_bin_certificate_sound certificate1099 profilesValid1099 numericValid1099 valid1099

def retention1100 : RatCutRetentionCertificate := ⟨(43/800),(27/500),(4812253837796265459/15980719681828407898),(55047778477942887/31250000000000000),(8/5),(112006527054971203797/80000000000000000000),true,MergedCutProfiles.Batch183.profile7341,![MergedCutProfiles.Batch183.profile7341,MergedCutProfiles.Batch183.profile7342,MergedCutProfiles.Batch183.profile7343,MergedCutProfiles.Batch183.profile7344,MergedCutProfiles.Batch183.profile7345,MergedCutProfiles.Batch183.profile7346,MergedCutProfiles.Batch183.profile7347,MergedCutProfiles.Batch183.profile7348,MergedCutProfiles.Batch183.profile7349,MergedCutProfiles.Batch183.profile7350,MergedCutProfiles.Batch183.profile7351,MergedCutProfiles.Batch183.profile7352,MergedCutProfiles.Batch183.profile7353,MergedCutProfiles.Batch183.profile7354,MergedCutProfiles.Batch183.profile7355,MergedCutProfiles.Batch183.profile7356]⟩
theorem profilesValid1100 : retention1100.ProfilesValid := by
  change ∀ j : Fin 16, (retention1100.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch183.valid7341
  · exact MergedCutProfiles.Batch183.valid7342
  · exact MergedCutProfiles.Batch183.valid7343
  · exact MergedCutProfiles.Batch183.valid7344
  · exact MergedCutProfiles.Batch183.valid7345
  · exact MergedCutProfiles.Batch183.valid7346
  · exact MergedCutProfiles.Batch183.valid7347
  · exact MergedCutProfiles.Batch183.valid7348
  · exact MergedCutProfiles.Batch183.valid7349
  · exact MergedCutProfiles.Batch183.valid7350
  · exact MergedCutProfiles.Batch183.valid7351
  · exact MergedCutProfiles.Batch183.valid7352
  · exact MergedCutProfiles.Batch183.valid7353
  · exact MergedCutProfiles.Batch183.valid7354
  · exact MergedCutProfiles.Batch183.valid7355
  · exact MergedCutProfiles.Batch183.valid7356
theorem numericValid1100 : retention1100.NumericValid := by decide +kernel
def certificate1100 : RatCutBinCertificate := ⟨⟨retention1100,(1113526092303454291/500000000000000000),(142705547327693923/1000000000000000000),(2839015555850207423/200000000000000000),(227180872034970018037/1000000000000000000),(682125652631088377/500000000000000000)⟩,(495784529389865187/500000000000000000),(207883096294222641/500000000000000000),(219343174221550409/1000000000000000000),(142179039537518571/1000000000000000000)⟩
theorem valid1100 : certificate1100.Valid := by decide +kernel
theorem sound1100 : certificate1100.Sound := rat_cut_bin_certificate_sound certificate1100 profilesValid1100 numericValid1100 valid1100

def retention1101 : RatCutRetentionCertificate := ⟨(43/800),(27/500),(3654401249627747939/7990359840914203949),(4812253837796265459/1000000000000000000),1,(265500503812292551539/256000000000000000000),true,MergedCutProfiles.Batch183.profile7357,![MergedCutProfiles.Batch183.profile7357,MergedCutProfiles.Batch183.profile7358,MergedCutProfiles.Batch183.profile7359,MergedCutProfiles.Batch184.profile7360,MergedCutProfiles.Batch184.profile7361,MergedCutProfiles.Batch184.profile7362,MergedCutProfiles.Batch184.profile7363,MergedCutProfiles.Batch184.profile7364,MergedCutProfiles.Batch184.profile7365,MergedCutProfiles.Batch184.profile7366,MergedCutProfiles.Batch184.profile7367,MergedCutProfiles.Batch184.profile7368,MergedCutProfiles.Batch184.profile7369,MergedCutProfiles.Batch184.profile7370,MergedCutProfiles.Batch184.profile7371,MergedCutProfiles.Batch184.profile7372]⟩
theorem profilesValid1101 : retention1101.ProfilesValid := by
  change ∀ j : Fin 16, (retention1101.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch183.valid7357
  · exact MergedCutProfiles.Batch183.valid7358
  · exact MergedCutProfiles.Batch183.valid7359
  · exact MergedCutProfiles.Batch184.valid7360
  · exact MergedCutProfiles.Batch184.valid7361
  · exact MergedCutProfiles.Batch184.valid7362
  · exact MergedCutProfiles.Batch184.valid7363
  · exact MergedCutProfiles.Batch184.valid7364
  · exact MergedCutProfiles.Batch184.valid7365
  · exact MergedCutProfiles.Batch184.valid7366
  · exact MergedCutProfiles.Batch184.valid7367
  · exact MergedCutProfiles.Batch184.valid7368
  · exact MergedCutProfiles.Batch184.valid7369
  · exact MergedCutProfiles.Batch184.valid7370
  · exact MergedCutProfiles.Batch184.valid7371
  · exact MergedCutProfiles.Batch184.valid7372
theorem numericValid1101 : retention1101.NumericValid := by decide +kernel
def certificate1101 : RatCutBinCertificate := ⟨⟨retention1101,(1113526092303454291/500000000000000000),(142705547327693923/1000000000000000000),(2839015555850207423/200000000000000000),(227180872034970018037/1000000000000000000),(1014719483602999623/1000000000000000000)⟩,(495784529389865187/500000000000000000),(470344077297823071/1000000000000000000),(174879583322329123/1000000000000000000),(72594891826766947/500000000000000000)⟩
theorem valid1101 : certificate1101.Valid := by decide +kernel
theorem sound1101 : certificate1101.Sound := rat_cut_bin_certificate_sound certificate1101 profilesValid1101 numericValid1101 valid1101

def retention1102 : RatCutRetentionCertificate := ⟨(43/800),(27/500),(3957192898215042314/7990359840914203949),(3654401249627747939/500000000000000000),(21/20),(2914287817017174535931968947768621135999/2923520999702198351200000000000000000000),false,MergedCutProfiles.Batch184.profile7373,(fun _ => MergedCutProfiles.Batch184.profile7373)⟩
theorem profilesValid1102 : retention1102.ProfilesValid := by
  exact MergedCutProfiles.Batch184.valid7373
theorem numericValid1102 : retention1102.NumericValid := by decide +kernel
def certificate1102 : RatCutBinCertificate := ⟨⟨retention1102,(1113526092303454291/500000000000000000),(142705547327693923/1000000000000000000),(2839015555850207423/200000000000000000),(227180872034970018037/1000000000000000000),(194666290284130689/200000000000000000)⟩,(495784529389865187/500000000000000000),(236059194194166451/500000000000000000),(173544587587358693/1000000000000000000),(142241043683719207/1000000000000000000)⟩
theorem valid1102 : certificate1102.Valid := by decide +kernel
theorem sound1102 : certificate1102.Sound := rat_cut_bin_certificate_sound certificate1102 profilesValid1102 numericValid1102 valid1102

def retention1103 : RatCutRetentionCertificate := ⟨(43/800),(27/500),(1/2),(1978596449107521157/250000000000000000),(21/20),(783506376563390423088641750318931819951/791438579643008462800000000000000000000),false,MergedCutProfiles.Batch184.profile7374,(fun _ => MergedCutProfiles.Batch184.profile7374)⟩
theorem profilesValid1103 : retention1103.ProfilesValid := by
  exact MergedCutProfiles.Batch184.valid7374
theorem numericValid1103 : retention1103.NumericValid := by decide +kernel
def certificate1103 : RatCutBinCertificate := ⟨⟨retention1103,(1113526092303454291/500000000000000000),(142705547327693923/1000000000000000000),(2839015555850207423/200000000000000000),(227180872034970018037/1000000000000000000),(966467326717642277/1000000000000000000)⟩,(495784529389865187/500000000000000000),(472764294240516171/1000000000000000000),(8653013165008541/50000000000000000),(142121172124547113/1000000000000000000)⟩
theorem valid1103 : certificate1103.Valid := by decide +kernel
theorem sound1103 : certificate1103.Sound := rat_cut_bin_certificate_sound certificate1103 profilesValid1103 numericValid1103 valid1103

def certificates : List RatCutBinCertificate := [certificate1092,certificate1093,certificate1094,certificate1095,certificate1096,certificate1097,certificate1098,certificate1099,certificate1100,certificate1101,certificate1102,certificate1103]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1092,List.forall_mem_cons.mpr ⟨sound1093,List.forall_mem_cons.mpr ⟨sound1094,List.forall_mem_cons.mpr ⟨sound1095,List.forall_mem_cons.mpr ⟨sound1096,List.forall_mem_cons.mpr ⟨sound1097,List.forall_mem_cons.mpr ⟨sound1098,List.forall_mem_cons.mpr ⟨sound1099,List.forall_mem_cons.mpr ⟨sound1100,List.forall_mem_cons.mpr ⟨sound1101,List.forall_mem_cons.mpr ⟨sound1102,List.forall_mem_cons.mpr ⟨sound1103,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch091
