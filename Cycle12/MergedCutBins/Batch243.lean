import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch025
import Cycle12.MergedCutProfiles.Batch026
import Cycle12.MergedCutProfiles.Batch027
import Cycle12.MergedCutProfiles.Batch028
import Cycle12.MergedCutProfiles.Batch320
import Cycle12.MergedCutProfiles.Batch321
import Cycle12.MergedCutProfiles.Batch322
import Cycle12.MergedCutProfiles.Batch323
import Cycle12.MergedCutProfiles.Batch456
import Cycle12.MergedCutProfiles.Batch457

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch243

def retention2916 : RatCutRetentionCertificate := ⟨(1/50),(21/1000),(259390849385119924/125904482924188692167),(190357/156250),(5/2),(37029274038386875071/16000000000000000000),true,MergedCutProfiles.Batch456.profile18262,![MergedCutProfiles.Batch456.profile18262,MergedCutProfiles.Batch456.profile18263,MergedCutProfiles.Batch456.profile18264,MergedCutProfiles.Batch456.profile18265,MergedCutProfiles.Batch320.profile12837,MergedCutProfiles.Batch321.profile12868,MergedCutProfiles.Batch321.profile12850,MergedCutProfiles.Batch456.profile18266,MergedCutProfiles.Batch025.profile1027,MergedCutProfiles.Batch321.profile12841,MergedCutProfiles.Batch321.profile12842,MergedCutProfiles.Batch456.profile18267,MergedCutProfiles.Batch025.profile1014,MergedCutProfiles.Batch321.profile12853,MergedCutProfiles.Batch456.profile18261,MergedCutProfiles.Batch456.profile18268]⟩
theorem profilesValid2916 : retention2916.ProfilesValid := by
  change ∀ j : Fin 16, (retention2916.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch456.valid18262
  · exact MergedCutProfiles.Batch456.valid18263
  · exact MergedCutProfiles.Batch456.valid18264
  · exact MergedCutProfiles.Batch456.valid18265
  · exact MergedCutProfiles.Batch320.valid12837
  · exact MergedCutProfiles.Batch321.valid12868
  · exact MergedCutProfiles.Batch321.valid12850
  · exact MergedCutProfiles.Batch456.valid18266
  · exact MergedCutProfiles.Batch025.valid1027
  · exact MergedCutProfiles.Batch321.valid12841
  · exact MergedCutProfiles.Batch321.valid12842
  · exact MergedCutProfiles.Batch456.valid18267
  · exact MergedCutProfiles.Batch025.valid1014
  · exact MergedCutProfiles.Batch321.valid12853
  · exact MergedCutProfiles.Batch456.valid18261
  · exact MergedCutProfiles.Batch456.valid18268
theorem numericValid2916 : retention2916.NumericValid := by decide +kernel
def certificate2916 : RatCutBinCertificate := ⟨⟨retention2916,(9325183963945551/5000000000000000),(1860584005120499/100000000000000000),(8545935999271191049/1000000000000000000),(5405667221822570221929/1000000000000000000),(288022302939852237/125000000000000000)⟩,(199932156846395979/200000000000000000),(376516206288966217/1000000000000000000),(255702245246490461/1000000000000000000),(180853670047557851/1000000000000000000)⟩
theorem valid2916 : certificate2916.Valid := by decide +kernel
theorem sound2916 : certificate2916.Sound := rat_cut_bin_certificate_sound certificate2916 profilesValid2916 numericValid2916 valid2916

def retention2917 : RatCutRetentionCertificate := ⟨(1/50),(21/1000),(7253077533896046073/629522414620943460835),(64847712346279981/50000000000000000),(49/20),(35898224629823530807/16000000000000000000),true,MergedCutProfiles.Batch456.profile18269,![MergedCutProfiles.Batch456.profile18269,MergedCutProfiles.Batch321.profile12842,MergedCutProfiles.Batch456.profile18270,MergedCutProfiles.Batch025.profile1029,MergedCutProfiles.Batch321.profile12857,MergedCutProfiles.Batch025.profile1022,MergedCutProfiles.Batch456.profile18271,MergedCutProfiles.Batch025.profile1033,MergedCutProfiles.Batch456.profile18272,MergedCutProfiles.Batch456.profile18273,MergedCutProfiles.Batch026.profile1044,MergedCutProfiles.Batch025.profile1038,MergedCutProfiles.Batch456.profile18274,MergedCutProfiles.Batch456.profile18275,MergedCutProfiles.Batch456.profile18276,MergedCutProfiles.Batch456.profile18277]⟩
theorem profilesValid2917 : retention2917.ProfilesValid := by
  change ∀ j : Fin 16, (retention2917.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch456.valid18269
  · exact MergedCutProfiles.Batch321.valid12842
  · exact MergedCutProfiles.Batch456.valid18270
  · exact MergedCutProfiles.Batch025.valid1029
  · exact MergedCutProfiles.Batch321.valid12857
  · exact MergedCutProfiles.Batch025.valid1022
  · exact MergedCutProfiles.Batch456.valid18271
  · exact MergedCutProfiles.Batch025.valid1033
  · exact MergedCutProfiles.Batch456.valid18272
  · exact MergedCutProfiles.Batch456.valid18273
  · exact MergedCutProfiles.Batch026.valid1044
  · exact MergedCutProfiles.Batch025.valid1038
  · exact MergedCutProfiles.Batch456.valid18274
  · exact MergedCutProfiles.Batch456.valid18275
  · exact MergedCutProfiles.Batch456.valid18276
  · exact MergedCutProfiles.Batch456.valid18277
theorem numericValid2917 : retention2917.NumericValid := by decide +kernel
def certificate2917 : RatCutBinCertificate := ⟨⟨retention2917,(9325183963945551/5000000000000000),(1860584005120499/100000000000000000),(8545935999271191049/1000000000000000000),(5405667221822570221929/1000000000000000000),(1116845430013811149/500000000000000000)⟩,(199932156846395979/200000000000000000),(188480493063773829/500000000000000000),(63817021143576117/250000000000000000),(225966153806797/1250000000000000)⟩
theorem valid2917 : certificate2917.Valid := by decide +kernel
theorem sound2917 : certificate2917.Sound := rat_cut_bin_certificate_sound certificate2917 profilesValid2917 numericValid2917 valid2917

def retention2918 : RatCutRetentionCertificate := ⟨(1/50),(21/1000),(12800000000000000000/125904482924188692167),(7253077533896046073/1000000000000000000),(11/10),(2366066465770788390949/1280000000000000000000),true,MergedCutProfiles.Batch025.profile1034,![MergedCutProfiles.Batch025.profile1034,MergedCutProfiles.Batch456.profile18278,MergedCutProfiles.Batch456.profile18279,MergedCutProfiles.Batch457.profile18280,MergedCutProfiles.Batch457.profile18281,MergedCutProfiles.Batch457.profile18282,MergedCutProfiles.Batch457.profile18283,MergedCutProfiles.Batch457.profile18284,MergedCutProfiles.Batch457.profile18285,MergedCutProfiles.Batch457.profile18286,MergedCutProfiles.Batch457.profile18287,MergedCutProfiles.Batch457.profile18288,MergedCutProfiles.Batch457.profile18289,MergedCutProfiles.Batch457.profile18290,MergedCutProfiles.Batch457.profile18291,MergedCutProfiles.Batch457.profile18292]⟩
theorem profilesValid2918 : retention2918.ProfilesValid := by
  change ∀ j : Fin 16, (retention2918.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch025.valid1034
  · exact MergedCutProfiles.Batch456.valid18278
  · exact MergedCutProfiles.Batch456.valid18279
  · exact MergedCutProfiles.Batch457.valid18280
  · exact MergedCutProfiles.Batch457.valid18281
  · exact MergedCutProfiles.Batch457.valid18282
  · exact MergedCutProfiles.Batch457.valid18283
  · exact MergedCutProfiles.Batch457.valid18284
  · exact MergedCutProfiles.Batch457.valid18285
  · exact MergedCutProfiles.Batch457.valid18286
  · exact MergedCutProfiles.Batch457.valid18287
  · exact MergedCutProfiles.Batch457.valid18288
  · exact MergedCutProfiles.Batch457.valid18289
  · exact MergedCutProfiles.Batch457.valid18290
  · exact MergedCutProfiles.Batch457.valid18291
  · exact MergedCutProfiles.Batch457.valid18292
theorem numericValid2918 : retention2918.NumericValid := by decide +kernel
def certificate2918 : RatCutBinCertificate := ⟨⟨retention2918,(9325183963945551/5000000000000000),(1860584005120499/100000000000000000),(8545935999271191049/1000000000000000000),(5405667221822570221929/1000000000000000000),(922011449898370979/500000000000000000)⟩,(199932156846395979/200000000000000000),(28044315605274963/100000000000000000),(181483605999497429/500000000000000000),(7853772329489421/15625000000000000)⟩
theorem valid2918 : certificate2918.Valid := by decide +kernel
theorem sound2918 : certificate2918.Sound := rat_cut_bin_certificate_sound certificate2918 profilesValid2918 numericValid2918 valid2918

def retention2919 : RatCutRetentionCertificate := ⟨(1/50),(21/1000),(1/2),64,1,(3990181166188230871926367807584118119/4000000000000000000000000000000000000),false,MergedCutProfiles.Batch026.profile1066,(fun _ => MergedCutProfiles.Batch026.profile1066)⟩
theorem profilesValid2919 : retention2919.ProfilesValid := by
  exact MergedCutProfiles.Batch026.valid1066
theorem numericValid2919 : retention2919.NumericValid := by decide +kernel
def certificate2919 : RatCutBinCertificate := ⟨⟨retention2919,(9325183963945551/5000000000000000),(1860584005120499/100000000000000000),(8545935999271191049/1000000000000000000),(5405667221822570221929/1000000000000000000),(62092800897826587/62500000000000000)⟩,(199932156846395979/200000000000000000),(457399627352353281/1000000000000000000),(184823166176944843/1000000000000000000),(180750366000245629/1000000000000000000)⟩
theorem valid2919 : certificate2919.Valid := by decide +kernel
theorem sound2919 : certificate2919.Sound := rat_cut_bin_certificate_sound certificate2919 profilesValid2919 numericValid2919 valid2919

def retention2920 : RatCutRetentionCertificate := ⟨(1/50),(21/1000),(12800000000000000000/125904482924188692167),(4353332037583947943/500000000000000000),1,(62376524425799762667157762771103643759/34826656300671583544000000000000000000),false,MergedCutProfiles.Batch457.profile18293,(fun _ => MergedCutProfiles.Batch457.profile18293)⟩
theorem profilesValid2920 : retention2920.ProfilesValid := by
  exact MergedCutProfiles.Batch457.valid18293
theorem numericValid2920 : retention2920.NumericValid := by decide +kernel
def certificate2920 : RatCutBinCertificate := ⟨⟨retention2920,(10089930348945551/5000000000000000),(1860584005120499/100000000000000000),(8545935999271191049/1000000000000000000),(5405667221822570221929/1000000000000000000),(178666346568232291/100000000000000000)⟩,(999632965406989739/1000000000000000000),(77277801296231091/1000000000000000000),(143794202614677481/200000000000000000),(4261725340496123/4000000000000000)⟩
theorem valid2920 : certificate2920.Valid := by decide +kernel
theorem sound2920 : certificate2920.Sound := rat_cut_bin_certificate_sound certificate2920 profilesValid2920 numericValid2920 valid2920

def retention2921 : RatCutRetentionCertificate := ⟨(1/50),(21/1000),(1/2),64,1,(3990181166188230871926367807584118119/4000000000000000000000000000000000000),false,MergedCutProfiles.Batch026.profile1066,(fun _ => MergedCutProfiles.Batch026.profile1066)⟩
theorem profilesValid2921 : retention2921.ProfilesValid := by
  exact MergedCutProfiles.Batch026.valid1066
theorem numericValid2921 : retention2921.NumericValid := by decide +kernel
def certificate2921 : RatCutBinCertificate := ⟨⟨retention2921,(10089930348945551/5000000000000000),(1860584005120499/100000000000000000),(8545935999271191049/1000000000000000000),(5405667221822570221929/1000000000000000000),(198630363967153523/200000000000000000)⟩,(999632965406989739/1000000000000000000),(34755367086541203/250000000000000000),(146340875010582979/250000000000000000),(143064860524626033/250000000000000000)⟩
theorem valid2921 : certificate2921.Valid := by decide +kernel
theorem sound2921 : certificate2921.Sound := rat_cut_bin_certificate_sound certificate2921 profilesValid2921 numericValid2921 valid2921

def retention2922 : RatCutRetentionCertificate := ⟨(21/1000),(11/500),(624961810023148581/570839276390788985155),(600576015484649707/1000000000000000000),4,(9011595832018999111/4000000000000000000),true,MergedCutProfiles.Batch457.profile18294,![MergedCutProfiles.Batch457.profile18294,MergedCutProfiles.Batch457.profile18295,MergedCutProfiles.Batch457.profile18296,MergedCutProfiles.Batch457.profile18297,MergedCutProfiles.Batch322.profile12908,MergedCutProfiles.Batch457.profile18298,MergedCutProfiles.Batch323.profile12920,MergedCutProfiles.Batch457.profile18299,MergedCutProfiles.Batch457.profile18300,MergedCutProfiles.Batch457.profile18301,MergedCutProfiles.Batch457.profile18302,MergedCutProfiles.Batch457.profile18303,MergedCutProfiles.Batch457.profile18304,MergedCutProfiles.Batch323.profile12921,MergedCutProfiles.Batch457.profile18305,MergedCutProfiles.Batch457.profile18306]⟩
theorem profilesValid2922 : retention2922.ProfilesValid := by
  change ∀ j : Fin 16, (retention2922.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch457.valid18294
  · exact MergedCutProfiles.Batch457.valid18295
  · exact MergedCutProfiles.Batch457.valid18296
  · exact MergedCutProfiles.Batch457.valid18297
  · exact MergedCutProfiles.Batch322.valid12908
  · exact MergedCutProfiles.Batch457.valid18298
  · exact MergedCutProfiles.Batch323.valid12920
  · exact MergedCutProfiles.Batch457.valid18299
  · exact MergedCutProfiles.Batch457.valid18300
  · exact MergedCutProfiles.Batch457.valid18301
  · exact MergedCutProfiles.Batch457.valid18302
  · exact MergedCutProfiles.Batch457.valid18303
  · exact MergedCutProfiles.Batch457.valid18304
  · exact MergedCutProfiles.Batch323.valid12921
  · exact MergedCutProfiles.Batch457.valid18305
  · exact MergedCutProfiles.Batch457.valid18306
theorem numericValid2922 : retention2922.NumericValid := by decide +kernel
def certificate2922 : RatCutBinCertificate := ⟨⟨retention2922,(9352566312895587/5000000000000000),(10247703429141591/500000000000000000),(8659647871970517101/1000000000000000000),(4967120072758941344351/1000000000000000000),(447038123693435243/200000000000000000)⟩,(249907606236639761/250000000000000000),(581226628389595691/1000000000000000000),(103391354397127629/1000000000000000000),(11712855372517927/250000000000000000)⟩
theorem valid2922 : certificate2922.Valid := by decide +kernel
theorem sound2922 : certificate2922.Sound := rat_cut_bin_certificate_sound certificate2922 profilesValid2922 numericValid2922 valid2922

def retention2923 : RatCutRetentionCertificate := ⟨(21/1000),(11/500),(244948959600000000/114167855278157797031),(624961810023148581/1000000000000000000),4,(145877979932897329821/64000000000000000000),true,MergedCutProfiles.Batch457.profile18295,![MergedCutProfiles.Batch457.profile18295,MergedCutProfiles.Batch457.profile18297,MergedCutProfiles.Batch457.profile18298,MergedCutProfiles.Batch457.profile18299,MergedCutProfiles.Batch457.profile18301,MergedCutProfiles.Batch457.profile18303,MergedCutProfiles.Batch322.profile12902,MergedCutProfiles.Batch457.profile18306,MergedCutProfiles.Batch322.profile12893,MergedCutProfiles.Batch322.profile12911,MergedCutProfiles.Batch026.profile1072,MergedCutProfiles.Batch457.profile18307,MergedCutProfiles.Batch322.profile12895,MergedCutProfiles.Batch026.profile1073,MergedCutProfiles.Batch322.profile12913,MergedCutProfiles.Batch027.profile1102]⟩
theorem profilesValid2923 : retention2923.ProfilesValid := by
  change ∀ j : Fin 16, (retention2923.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch457.valid18295
  · exact MergedCutProfiles.Batch457.valid18297
  · exact MergedCutProfiles.Batch457.valid18298
  · exact MergedCutProfiles.Batch457.valid18299
  · exact MergedCutProfiles.Batch457.valid18301
  · exact MergedCutProfiles.Batch457.valid18303
  · exact MergedCutProfiles.Batch322.valid12902
  · exact MergedCutProfiles.Batch457.valid18306
  · exact MergedCutProfiles.Batch322.valid12893
  · exact MergedCutProfiles.Batch322.valid12911
  · exact MergedCutProfiles.Batch026.valid1072
  · exact MergedCutProfiles.Batch457.valid18307
  · exact MergedCutProfiles.Batch322.valid12895
  · exact MergedCutProfiles.Batch026.valid1073
  · exact MergedCutProfiles.Batch322.valid12913
  · exact MergedCutProfiles.Batch027.valid1102
theorem numericValid2923 : retention2923.NumericValid := by decide +kernel
def certificate2923 : RatCutBinCertificate := ⟨⟨retention2923,(9352566312895587/5000000000000000),(10247703429141591/500000000000000000),(8659647871970517101/1000000000000000000),(4967120072758941344351/1000000000000000000),(452327019620153213/200000000000000000)⟩,(249907606236639761/250000000000000000),(111949663944240431/200000000000000000),(23089524558713737/200000000000000000),(2128455599607431/40000000000000000)⟩
theorem valid2923 : certificate2923.Valid := by decide +kernel
theorem sound2923 : certificate2923.Sound := rat_cut_bin_certificate_sound certificate2923 profilesValid2923 numericValid2923 valid2923

def retention2924 : RatCutRetentionCertificate := ⟨(21/1000),(11/500),(1904791055630093651/570839276390788985155),(612372399/500000000),(5/2),(4603127693398795879/2000000000000000000),true,MergedCutProfiles.Batch457.profile18296,![MergedCutProfiles.Batch457.profile18296,MergedCutProfiles.Batch457.profile18298,MergedCutProfiles.Batch027.profile1085,MergedCutProfiles.Batch457.profile18308,MergedCutProfiles.Batch322.profile12892,MergedCutProfiles.Batch027.profile1086,MergedCutProfiles.Batch026.profile1072,MergedCutProfiles.Batch322.profile12912,MergedCutProfiles.Batch026.profile1073,MergedCutProfiles.Batch322.profile12897,MergedCutProfiles.Batch322.profile12914,MergedCutProfiles.Batch027.profile1087,MergedCutProfiles.Batch457.profile18309,MergedCutProfiles.Batch457.profile18310,MergedCutProfiles.Batch027.profile1088,MergedCutProfiles.Batch026.profile1077]⟩
theorem profilesValid2924 : retention2924.ProfilesValid := by
  change ∀ j : Fin 16, (retention2924.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch457.valid18296
  · exact MergedCutProfiles.Batch457.valid18298
  · exact MergedCutProfiles.Batch027.valid1085
  · exact MergedCutProfiles.Batch457.valid18308
  · exact MergedCutProfiles.Batch322.valid12892
  · exact MergedCutProfiles.Batch027.valid1086
  · exact MergedCutProfiles.Batch026.valid1072
  · exact MergedCutProfiles.Batch322.valid12912
  · exact MergedCutProfiles.Batch026.valid1073
  · exact MergedCutProfiles.Batch322.valid12897
  · exact MergedCutProfiles.Batch322.valid12914
  · exact MergedCutProfiles.Batch027.valid1087
  · exact MergedCutProfiles.Batch457.valid18309
  · exact MergedCutProfiles.Batch457.valid18310
  · exact MergedCutProfiles.Batch027.valid1088
  · exact MergedCutProfiles.Batch026.valid1077
theorem numericValid2924 : retention2924.NumericValid := by decide +kernel
def certificate2924 : RatCutBinCertificate := ⟨⟨retention2924,(9352566312895587/5000000000000000),(10247703429141591/500000000000000000),(8659647871970517101/1000000000000000000),(4967120072758941344351/1000000000000000000),(572624034645840537/250000000000000000)⟩,(249907606236639761/250000000000000000),(2951919036825499/7812500000000000),(248443469898027/976562500000000),(175125103196019/976562500000000)⟩
theorem valid2924 : certificate2924.Valid := by decide +kernel
theorem sound2924 : certificate2924.Sound := rat_cut_bin_certificate_sound certificate2924 profilesValid2924 numericValid2924 valid2924

def retention2925 : RatCutRetentionCertificate := ⟨(21/1000),(11/500),(12800000000000000000/114167855278157797031),(1904791055630093651/1000000000000000000),(19/10),(1418108316707029769337184414008149770719/761916422252037460400000000000000000000),false,MergedCutProfiles.Batch457.profile18311,(fun _ => MergedCutProfiles.Batch457.profile18311)⟩
theorem profilesValid2925 : retention2925.ProfilesValid := by
  exact MergedCutProfiles.Batch457.valid18311
theorem numericValid2925 : retention2925.NumericValid := by decide +kernel
def certificate2925 : RatCutBinCertificate := ⟨⟨retention2925,(9352566312895587/5000000000000000),(10247703429141591/500000000000000000),(8659647871970517101/1000000000000000000),(4967120072758941344351/1000000000000000000),(1852827224475311769/1000000000000000000)⟩,(249907606236639761/250000000000000000),(386689156127415267/1000000000000000000),(122951138749315409/500000000000000000),(188819936350500433/1000000000000000000)⟩
theorem valid2925 : certificate2925.Valid := by decide +kernel
theorem sound2925 : certificate2925.Sound := rat_cut_bin_certificate_sound certificate2925 profilesValid2925 numericValid2925 valid2925

def retention2926 : RatCutRetentionCertificate := ⟨(21/1000),(11/500),(1/2),64,1,(15960748357185807596877500066049185271/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch028.profile1132,(fun _ => MergedCutProfiles.Batch028.profile1132)⟩
theorem profilesValid2926 : retention2926.ProfilesValid := by
  exact MergedCutProfiles.Batch028.valid1132
theorem numericValid2926 : retention2926.NumericValid := by decide +kernel
def certificate2926 : RatCutBinCertificate := ⟨⟨retention2926,(9352566312895587/5000000000000000),(10247703429141591/500000000000000000),(8659647871970517101/1000000000000000000),(4967120072758941344351/1000000000000000000),(496559847379138689/500000000000000000)⟩,(249907606236639761/250000000000000000),(459294773670533731/1000000000000000000),(22918090107341953/125000000000000000),(89617059806089809/500000000000000000)⟩
theorem valid2926 : certificate2926.Valid := by decide +kernel
theorem sound2926 : certificate2926.Sound := rat_cut_bin_certificate_sound certificate2926 profilesValid2926 numericValid2926 valid2926

def retention2927 : RatCutRetentionCertificate := ⟨(21/1000),(11/500),(12800000000000000000/114167855278157797031),(4416050031998661749/500000000000000000),1,(1782387032857257342542154521195284629/1009382864456836971200000000000000000),false,MergedCutProfiles.Batch457.profile18311,(fun _ => MergedCutProfiles.Batch457.profile18311)⟩
theorem profilesValid2927 : retention2927.ProfilesValid := by
  exact MergedCutProfiles.Batch457.valid18311
theorem numericValid2927 : retention2927.NumericValid := by decide +kernel
def certificate2927 : RatCutBinCertificate := ⟨⟨retention2927,(10108927032895587/5000000000000000),(10247703429141591/500000000000000000),(8659647871970517101/1000000000000000000),(4967120072758941344351/1000000000000000000),(880516745106877337/500000000000000000)⟩,(499800268223694363/500000000000000000),(15503170570065157/200000000000000000),(718396787232385541/1000000000000000000),(263590402135577583/250000000000000000)⟩
theorem valid2927 : certificate2927.Valid := by decide +kernel
theorem sound2927 : certificate2927.Sound := rat_cut_bin_certificate_sound certificate2927 profilesValid2927 numericValid2927 valid2927

def certificates : List RatCutBinCertificate := [certificate2916,certificate2917,certificate2918,certificate2919,certificate2920,certificate2921,certificate2922,certificate2923,certificate2924,certificate2925,certificate2926,certificate2927]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2916,List.forall_mem_cons.mpr ⟨sound2917,List.forall_mem_cons.mpr ⟨sound2918,List.forall_mem_cons.mpr ⟨sound2919,List.forall_mem_cons.mpr ⟨sound2920,List.forall_mem_cons.mpr ⟨sound2921,List.forall_mem_cons.mpr ⟨sound2922,List.forall_mem_cons.mpr ⟨sound2923,List.forall_mem_cons.mpr ⟨sound2924,List.forall_mem_cons.mpr ⟨sound2925,List.forall_mem_cons.mpr ⟨sound2926,List.forall_mem_cons.mpr ⟨sound2927,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch243
