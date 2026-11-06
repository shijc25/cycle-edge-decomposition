import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch023
import Cycle12.MergedCutProfiles.Batch024
import Cycle12.MergedCutProfiles.Batch025
import Cycle12.MergedCutProfiles.Batch320
import Cycle12.MergedCutProfiles.Batch321
import Cycle12.MergedCutProfiles.Batch455
import Cycle12.MergedCutProfiles.Batch456

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch242

def retention2904 : RatCutRetentionCertificate := ⟨(9/500),(19/1000),(1/2),64,1,(255370911039032911357452645744173379951/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch023.profile947,(fun _ => MergedCutProfiles.Batch023.profile947)⟩
theorem profilesValid2904 : retention2904.ProfilesValid := by
  exact MergedCutProfiles.Batch023.valid947
theorem numericValid2904 : retention2904.NumericValid := by decide +kernel
def certificate2904 : RatCutBinCertificate := ⟨⟨retention2904,(1855866918952946473/1000000000000000000),(15120529320228081/1000000000000000000),(8325288334521964189/1000000000000000000),(259777396068867272681/40000000000000000),(198834392854492597/200000000000000000)⟩,(999718100457292219/1000000000000000000),(451725851890840539/1000000000000000000),(94648236174684101/500000000000000000),(185261894973321641/1000000000000000000)⟩
theorem valid2904 : certificate2904.Valid := by decide +kernel
theorem sound2904 : certificate2904.Sound := rat_cut_bin_certificate_sound certificate2904 profilesValid2904 numericValid2904 valid2904

def retention2905 : RatCutRetentionCertificate := ⟨(9/500),(19/1000),(64000000000000000000/776403571869755913701),(8547582761192461613/1000000000000000000),1,(62932366636616960773927251928212560707/34190331044769846452000000000000000000),false,MergedCutProfiles.Batch455.profile18211,(fun _ => MergedCutProfiles.Batch455.profile18211)⟩
theorem profilesValid2905 : retention2905.ProfilesValid := by
  exact MergedCutProfiles.Batch455.valid18211
theorem numericValid2905 : retention2905.NumericValid := by decide +kernel
def certificate2905 : RatCutBinCertificate := ⟨⟨retention2905,(2007499135952946473/1000000000000000000),(15120529320228081/1000000000000000000),(8325288334521964189/1000000000000000000),(259777396068867272681/40000000000000000),(918501004457087811/500000000000000000)⟩,(3905058859257651/3906250000000000),(75768683298053473/1000000000000000000),(90327909855498611/125000000000000000),(546143504643941539/500000000000000000)⟩
theorem valid2905 : certificate2905.Valid := by decide +kernel
theorem sound2905 : certificate2905.Sound := rat_cut_bin_certificate_sound certificate2905 profilesValid2905 numericValid2905 valid2905

def retention2906 : RatCutRetentionCertificate := ⟨(9/500),(19/1000),(1/2),64,1,(255370911039032911357452645744173379951/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch023.profile947,(fun _ => MergedCutProfiles.Batch023.profile947)⟩
theorem profilesValid2906 : retention2906.ProfilesValid := by
  exact MergedCutProfiles.Batch023.valid947
theorem numericValid2906 : retention2906.NumericValid := by decide +kernel
def certificate2906 : RatCutBinCertificate := ⟨⟨retention2906,(2007499135952946473/1000000000000000000),(15120529320228081/1000000000000000000),(8325288334521964189/1000000000000000000),(259777396068867272681/40000000000000000),(99389656726826077/100000000000000000)⟩,(3905058859257651/3906250000000000),(140041960114485847/1000000000000000000),(291692755670054961/500000000000000000),(570782610554180143/1000000000000000000)⟩
theorem valid2906 : certificate2906.Valid := by decide +kernel
theorem sound2906 : certificate2906.Sound := rat_cut_bin_certificate_sound certificate2906 profilesValid2906 numericValid2906 valid2906

def retention2907 : RatCutRetentionCertificate := ⟨(19/1000),(1/50),(77957052894514298/87172255218264550371),(296693843744298931/500000000000000000),4,(224128738525930541/100000000000000000),true,MergedCutProfiles.Batch455.profile18212,![MergedCutProfiles.Batch455.profile18212,MergedCutProfiles.Batch455.profile18213,MergedCutProfiles.Batch455.profile18214,MergedCutProfiles.Batch455.profile18215,MergedCutProfiles.Batch320.profile12807,MergedCutProfiles.Batch455.profile18216,MergedCutProfiles.Batch455.profile18217,MergedCutProfiles.Batch455.profile18218,MergedCutProfiles.Batch455.profile18219,MergedCutProfiles.Batch320.profile12808,MergedCutProfiles.Batch455.profile18220,MergedCutProfiles.Batch024.profile990,MergedCutProfiles.Batch455.profile18221,MergedCutProfiles.Batch455.profile18222,MergedCutProfiles.Batch024.profile966,MergedCutProfiles.Batch455.profile18223]⟩
theorem profilesValid2907 : retention2907.ProfilesValid := by
  change ∀ j : Fin 16, (retention2907.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch455.valid18212
  · exact MergedCutProfiles.Batch455.valid18213
  · exact MergedCutProfiles.Batch455.valid18214
  · exact MergedCutProfiles.Batch455.valid18215
  · exact MergedCutProfiles.Batch320.valid12807
  · exact MergedCutProfiles.Batch455.valid18216
  · exact MergedCutProfiles.Batch455.valid18217
  · exact MergedCutProfiles.Batch455.valid18218
  · exact MergedCutProfiles.Batch455.valid18219
  · exact MergedCutProfiles.Batch320.valid12808
  · exact MergedCutProfiles.Batch455.valid18220
  · exact MergedCutProfiles.Batch024.valid990
  · exact MergedCutProfiles.Batch455.valid18221
  · exact MergedCutProfiles.Batch455.valid18222
  · exact MergedCutProfiles.Batch024.valid966
  · exact MergedCutProfiles.Batch455.valid18223
theorem numericValid2907 : retention2907.NumericValid := by decide +kernel
def certificate2907 : RatCutBinCertificate := ⟨⟨retention2907,(929760302240947141/500000000000000000),(16814618099358171/1000000000000000000),(4217251540245806783/500000000000000000),(236403677302909347931/40000000000000000),(27830739568861221/12500000000000000)⟩,(999690121167456411/1000000000000000000),(589508513909689167/1000000000000000000),(19791241908976963/200000000000000000),(44600944250877661/1000000000000000000)⟩
theorem valid2907 : certificate2907.Valid := by decide +kernel
theorem sound2907 : certificate2907.Sound := rat_cut_bin_certificate_sound certificate2907 profilesValid2907 numericValid2907 valid2907

def retention2908 : RatCutRetentionCertificate := ⟨(19/1000),(1/50),(155318614750000000/87172255218264550371),(38978526447257149/62500000000000000),4,(4559845106047796397/2000000000000000000),true,MergedCutProfiles.Batch455.profile18213,![MergedCutProfiles.Batch455.profile18213,MergedCutProfiles.Batch455.profile18215,MergedCutProfiles.Batch455.profile18216,MergedCutProfiles.Batch455.profile18218,MergedCutProfiles.Batch320.profile12808,MergedCutProfiles.Batch455.profile18224,MergedCutProfiles.Batch455.profile18222,MergedCutProfiles.Batch455.profile18223,MergedCutProfiles.Batch320.profile12810,MergedCutProfiles.Batch320.profile12811,MergedCutProfiles.Batch455.profile18225,MergedCutProfiles.Batch455.profile18226,MergedCutProfiles.Batch455.profile18227,MergedCutProfiles.Batch320.profile12813,MergedCutProfiles.Batch455.profile18228,MergedCutProfiles.Batch023.profile954]⟩
theorem profilesValid2908 : retention2908.ProfilesValid := by
  change ∀ j : Fin 16, (retention2908.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch455.valid18213
  · exact MergedCutProfiles.Batch455.valid18215
  · exact MergedCutProfiles.Batch455.valid18216
  · exact MergedCutProfiles.Batch455.valid18218
  · exact MergedCutProfiles.Batch320.valid12808
  · exact MergedCutProfiles.Batch455.valid18224
  · exact MergedCutProfiles.Batch455.valid18222
  · exact MergedCutProfiles.Batch455.valid18223
  · exact MergedCutProfiles.Batch320.valid12810
  · exact MergedCutProfiles.Batch320.valid12811
  · exact MergedCutProfiles.Batch455.valid18225
  · exact MergedCutProfiles.Batch455.valid18226
  · exact MergedCutProfiles.Batch455.valid18227
  · exact MergedCutProfiles.Batch320.valid12813
  · exact MergedCutProfiles.Batch455.valid18228
  · exact MergedCutProfiles.Batch023.valid954
theorem numericValid2908 : retention2908.NumericValid := by decide +kernel
def certificate2908 : RatCutBinCertificate := ⟨⟨retention2908,(929760302240947141/500000000000000000),(16814618099358171/1000000000000000000),(4217251540245806783/500000000000000000),(236403677302909347931/40000000000000000),(283136791767016813/125000000000000000)⟩,(999690121167456411/1000000000000000000),(56085786173325663/100000000000000000),(5740244511126387/50000000000000000),(52964396142476047/1000000000000000000)⟩
theorem valid2908 : certificate2908.Valid := by decide +kernel
theorem sound2908 : certificate2908.Sound := rat_cut_bin_certificate_sound certificate2908 profilesValid2908 numericValid2908 valid2908

def retention2909 : RatCutRetentionCertificate := ⟨(19/1000),(1/50),(317080194516860896/87172255218264550371),(621274459/500000000),(5/2),(18418586864735715073/8000000000000000000),true,MergedCutProfiles.Batch455.profile18215,![MergedCutProfiles.Batch455.profile18215,MergedCutProfiles.Batch455.profile18218,MergedCutProfiles.Batch024.profile990,MergedCutProfiles.Batch455.profile18223,MergedCutProfiles.Batch455.profile18229,MergedCutProfiles.Batch024.profile991,MergedCutProfiles.Batch024.profile980,MergedCutProfiles.Batch320.profile12814,MergedCutProfiles.Batch024.profile992,MergedCutProfiles.Batch320.profile12816,MergedCutProfiles.Batch455.profile18230,MergedCutProfiles.Batch024.profile993,MergedCutProfiles.Batch023.profile958,MergedCutProfiles.Batch024.profile981,MergedCutProfiles.Batch024.profile971,MergedCutProfiles.Batch455.profile18231]⟩
theorem profilesValid2909 : retention2909.ProfilesValid := by
  change ∀ j : Fin 16, (retention2909.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch455.valid18215
  · exact MergedCutProfiles.Batch455.valid18218
  · exact MergedCutProfiles.Batch024.valid990
  · exact MergedCutProfiles.Batch455.valid18223
  · exact MergedCutProfiles.Batch455.valid18229
  · exact MergedCutProfiles.Batch024.valid991
  · exact MergedCutProfiles.Batch024.valid980
  · exact MergedCutProfiles.Batch320.valid12814
  · exact MergedCutProfiles.Batch024.valid992
  · exact MergedCutProfiles.Batch320.valid12816
  · exact MergedCutProfiles.Batch455.valid18230
  · exact MergedCutProfiles.Batch024.valid993
  · exact MergedCutProfiles.Batch023.valid958
  · exact MergedCutProfiles.Batch024.valid981
  · exact MergedCutProfiles.Batch024.valid971
  · exact MergedCutProfiles.Batch455.valid18231
theorem numericValid2909 : retention2909.NumericValid := by decide +kernel
def certificate2909 : RatCutBinCertificate := ⟨⟨retention2909,(929760302240947141/500000000000000000),(16814618099358171/1000000000000000000),(4217251540245806783/500000000000000000),(236403677302909347931/40000000000000000),(143315982710537517/62500000000000000)⟩,(999690121167456411/1000000000000000000),(187329184407015931/500000000000000000),(128760704924441143/500000000000000000),(182294705553824589/1000000000000000000)⟩
theorem valid2909 : certificate2909.Valid := by decide +kernel
theorem sound2909 : certificate2909.Sound := rat_cut_bin_certificate_sound certificate2909 profilesValid2909 numericValid2909 valid2909

def retention2910 : RatCutRetentionCertificate := ⟨(19/1000),(1/50),(8000000000000000000/87172255218264550371),(9908756078651903/3906250000000000),(8/5),(152615313028681638019/80000000000000000000),true,MergedCutProfiles.Batch024.profile985,![MergedCutProfiles.Batch024.profile985,MergedCutProfiles.Batch455.profile18232,MergedCutProfiles.Batch455.profile18233,MergedCutProfiles.Batch455.profile18234,MergedCutProfiles.Batch455.profile18235,MergedCutProfiles.Batch455.profile18236,MergedCutProfiles.Batch455.profile18237,MergedCutProfiles.Batch455.profile18238,MergedCutProfiles.Batch455.profile18239,MergedCutProfiles.Batch456.profile18240,MergedCutProfiles.Batch456.profile18241,MergedCutProfiles.Batch456.profile18242,MergedCutProfiles.Batch456.profile18243,MergedCutProfiles.Batch456.profile18244,MergedCutProfiles.Batch456.profile18245,MergedCutProfiles.Batch456.profile18246]⟩
theorem profilesValid2910 : retention2910.ProfilesValid := by
  change ∀ j : Fin 16, (retention2910.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch024.valid985
  · exact MergedCutProfiles.Batch455.valid18232
  · exact MergedCutProfiles.Batch455.valid18233
  · exact MergedCutProfiles.Batch455.valid18234
  · exact MergedCutProfiles.Batch455.valid18235
  · exact MergedCutProfiles.Batch455.valid18236
  · exact MergedCutProfiles.Batch455.valid18237
  · exact MergedCutProfiles.Batch455.valid18238
  · exact MergedCutProfiles.Batch455.valid18239
  · exact MergedCutProfiles.Batch456.valid18240
  · exact MergedCutProfiles.Batch456.valid18241
  · exact MergedCutProfiles.Batch456.valid18242
  · exact MergedCutProfiles.Batch456.valid18243
  · exact MergedCutProfiles.Batch456.valid18244
  · exact MergedCutProfiles.Batch456.valid18245
  · exact MergedCutProfiles.Batch456.valid18246
theorem numericValid2910 : retention2910.NumericValid := by decide +kernel
def certificate2910 : RatCutBinCertificate := ⟨⟨retention2910,(929760302240947141/500000000000000000),(16814618099358171/1000000000000000000),(4217251540245806783/500000000000000000),(236403677302909347931/40000000000000000),(1901760127910131187/1000000000000000000)⟩,(999690121167456411/1000000000000000000),(170283601633822527/500000000000000000),(29258570226203559/100000000000000000),(268899057543823567/1000000000000000000)⟩
theorem valid2910 : certificate2910.Valid := by decide +kernel
theorem sound2910 : certificate2910.Sound := rat_cut_bin_certificate_sound certificate2910 profilesValid2910 numericValid2910 valid2910

def retention2911 : RatCutRetentionCertificate := ⟨(19/1000),(1/50),(1/2),64,1,(3990175631981414592578765135707307871/4000000000000000000000000000000000000),false,MergedCutProfiles.Batch025.profile1008,(fun _ => MergedCutProfiles.Batch025.profile1008)⟩
theorem profilesValid2911 : retention2911.ProfilesValid := by
  exact MergedCutProfiles.Batch025.valid1008
theorem numericValid2911 : retention2911.NumericValid := by decide +kernel
def certificate2911 : RatCutBinCertificate := ⟨⟨retention2911,(929760302240947141/500000000000000000),(16814618099358171/1000000000000000000),(4217251540245806783/500000000000000000),(236403677302909347931/40000000000000000),(496918428668216427/500000000000000000)⟩,(999690121167456411/1000000000000000000),(56939636338599831/125000000000000000),(7451981901100273/40000000000000000),(9113159090055077/50000000000000000)⟩
theorem valid2911 : certificate2911.Valid := by decide +kernel
theorem sound2911 : certificate2911.Sound := rat_cut_bin_certificate_sound certificate2911 profilesValid2911 numericValid2911 valid2911

def retention2912 : RatCutRetentionCertificate := ⟨(19/1000),(1/50),(8000000000000000000/87172255218264550371),(1073010322479108783/125000000000000000),1,(20780634286721501307278740512174171501/11445443439777160352000000000000000000),false,MergedCutProfiles.Batch456.profile18247,(fun _ => MergedCutProfiles.Batch456.profile18247)⟩
theorem profilesValid2912 : retention2912.ProfilesValid := by
  exact MergedCutProfiles.Batch456.valid18247
theorem numericValid2912 : retention2912.NumericValid := by decide +kernel
def certificate2912 : RatCutBinCertificate := ⟨⟨retention2912,(1007068670240947141/500000000000000000),(16814618099358171/1000000000000000000),(4217251540245806783/500000000000000000),(236403677302909347931/40000000000000000),(905804901350799303/500000000000000000)⟩,(199932871002016143/200000000000000000),(7708641126680247/100000000000000000),(17985826375110777/25000000000000000),(1075827233964612307/1000000000000000000)⟩
theorem valid2912 : certificate2912.Valid := by decide +kernel
theorem sound2912 : certificate2912.Sound := rat_cut_bin_certificate_sound certificate2912 profilesValid2912 numericValid2912 valid2912

def retention2913 : RatCutRetentionCertificate := ⟨(19/1000),(1/50),(1/2),64,1,(3990175631981414592578765135707307871/4000000000000000000000000000000000000),false,MergedCutProfiles.Batch025.profile1008,(fun _ => MergedCutProfiles.Batch025.profile1008)⟩
theorem profilesValid2913 : retention2913.ProfilesValid := by
  exact MergedCutProfiles.Batch025.valid1008
theorem numericValid2913 : retention2913.NumericValid := by decide +kernel
def certificate2913 : RatCutBinCertificate := ⟨⟨retention2913,(1007068670240947141/500000000000000000),(16814618099358171/1000000000000000000),(4217251540245806783/500000000000000000),(236403677302909347931/40000000000000000),(993528620863178673/1000000000000000000)⟩,(199932871002016143/200000000000000000),(35140029027220629/250000000000000000),(291191868815236271/500000000000000000),(56957712124251957/100000000000000000)⟩
theorem valid2913 : certificate2913.Valid := by decide +kernel
theorem sound2913 : certificate2913.Sound := rat_cut_bin_certificate_sound certificate2913 profilesValid2913 numericValid2913 valid2913

def retention2914 : RatCutRetentionCertificate := ⟨(1/50),(21/1000),(608835893609079062/629522414620943460835),(298419710621056299/500000000000000000),4,(561759469306645941/250000000000000000),true,MergedCutProfiles.Batch456.profile18248,![MergedCutProfiles.Batch456.profile18248,MergedCutProfiles.Batch456.profile18249,MergedCutProfiles.Batch456.profile18250,MergedCutProfiles.Batch456.profile18251,MergedCutProfiles.Batch321.profile12849,MergedCutProfiles.Batch321.profile12867,MergedCutProfiles.Batch456.profile18252,MergedCutProfiles.Batch456.profile18253,MergedCutProfiles.Batch456.profile18254,MergedCutProfiles.Batch321.profile12862,MergedCutProfiles.Batch025.profile1011,MergedCutProfiles.Batch456.profile18255,MergedCutProfiles.Batch320.profile12838,MergedCutProfiles.Batch456.profile18256,MergedCutProfiles.Batch321.profile12850,MergedCutProfiles.Batch320.profile12839]⟩
theorem profilesValid2914 : retention2914.ProfilesValid := by
  change ∀ j : Fin 16, (retention2914.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch456.valid18248
  · exact MergedCutProfiles.Batch456.valid18249
  · exact MergedCutProfiles.Batch456.valid18250
  · exact MergedCutProfiles.Batch456.valid18251
  · exact MergedCutProfiles.Batch321.valid12849
  · exact MergedCutProfiles.Batch321.valid12867
  · exact MergedCutProfiles.Batch456.valid18252
  · exact MergedCutProfiles.Batch456.valid18253
  · exact MergedCutProfiles.Batch456.valid18254
  · exact MergedCutProfiles.Batch321.valid12862
  · exact MergedCutProfiles.Batch025.valid1011
  · exact MergedCutProfiles.Batch456.valid18255
  · exact MergedCutProfiles.Batch320.valid12838
  · exact MergedCutProfiles.Batch456.valid18256
  · exact MergedCutProfiles.Batch321.valid12850
  · exact MergedCutProfiles.Batch320.valid12839
theorem numericValid2914 : retention2914.NumericValid := by decide +kernel
def certificate2914 : RatCutBinCertificate := ⟨⟨retention2914,(9325183963945551/5000000000000000),(1860584005120499/100000000000000000),(8545935999271191049/1000000000000000000),(5405667221822570221929/1000000000000000000),(557698986489093771/250000000000000000)⟩,(199932156846395979/200000000000000000),(585477848693779291/1000000000000000000),(25275022564646267/250000000000000000),(22843891997684093/500000000000000000)⟩
theorem valid2914 : certificate2914.Valid := by decide +kernel
theorem sound2914 : certificate2914.Sound := rat_cut_bin_certificate_sound certificate2914 profilesValid2914 numericValid2914 valid2914

def retention2915 : RatCutRetentionCertificate := ⟨(1/50),(21/1000),(243656960000000000/125904482924188692167),(304417946804539531/500000000000000000),4,(288991098557081632891/128000000000000000000),true,MergedCutProfiles.Batch456.profile18249,![MergedCutProfiles.Batch456.profile18249,MergedCutProfiles.Batch456.profile18251,MergedCutProfiles.Batch321.profile12867,MergedCutProfiles.Batch456.profile18253,MergedCutProfiles.Batch321.profile12862,MergedCutProfiles.Batch456.profile18255,MergedCutProfiles.Batch456.profile18256,MergedCutProfiles.Batch320.profile12839,MergedCutProfiles.Batch456.profile18257,MergedCutProfiles.Batch456.profile18258,MergedCutProfiles.Batch025.profile1013,MergedCutProfiles.Batch321.profile12852,MergedCutProfiles.Batch321.profile12843,MergedCutProfiles.Batch456.profile18259,MergedCutProfiles.Batch456.profile18260,MergedCutProfiles.Batch456.profile18261]⟩
theorem profilesValid2915 : retention2915.ProfilesValid := by
  change ∀ j : Fin 16, (retention2915.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch456.valid18249
  · exact MergedCutProfiles.Batch456.valid18251
  · exact MergedCutProfiles.Batch321.valid12867
  · exact MergedCutProfiles.Batch456.valid18253
  · exact MergedCutProfiles.Batch321.valid12862
  · exact MergedCutProfiles.Batch456.valid18255
  · exact MergedCutProfiles.Batch456.valid18256
  · exact MergedCutProfiles.Batch320.valid12839
  · exact MergedCutProfiles.Batch456.valid18257
  · exact MergedCutProfiles.Batch456.valid18258
  · exact MergedCutProfiles.Batch025.valid1013
  · exact MergedCutProfiles.Batch321.valid12852
  · exact MergedCutProfiles.Batch321.valid12843
  · exact MergedCutProfiles.Batch456.valid18259
  · exact MergedCutProfiles.Batch456.valid18260
  · exact MergedCutProfiles.Batch456.valid18261
theorem numericValid2915 : retention2915.NumericValid := by decide +kernel
def certificate2915 : RatCutBinCertificate := ⟨⟨retention2915,(9325183963945551/5000000000000000),(1860584005120499/100000000000000000),(8545935999271191049/1000000000000000000),(5405667221822570221929/1000000000000000000),(2241501026668386527/1000000000000000000)⟩,(199932156846395979/200000000000000000),(11502493393203673/20000000000000000),(6670906773213509/62500000000000000),(6075448413940361/125000000000000000)⟩
theorem valid2915 : certificate2915.Valid := by decide +kernel
theorem sound2915 : certificate2915.Sound := rat_cut_bin_certificate_sound certificate2915 profilesValid2915 numericValid2915 valid2915

def certificates : List RatCutBinCertificate := [certificate2904,certificate2905,certificate2906,certificate2907,certificate2908,certificate2909,certificate2910,certificate2911,certificate2912,certificate2913,certificate2914,certificate2915]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2904,List.forall_mem_cons.mpr ⟨sound2905,List.forall_mem_cons.mpr ⟨sound2906,List.forall_mem_cons.mpr ⟨sound2907,List.forall_mem_cons.mpr ⟨sound2908,List.forall_mem_cons.mpr ⟨sound2909,List.forall_mem_cons.mpr ⟨sound2910,List.forall_mem_cons.mpr ⟨sound2911,List.forall_mem_cons.mpr ⟨sound2912,List.forall_mem_cons.mpr ⟨sound2913,List.forall_mem_cons.mpr ⟨sound2914,List.forall_mem_cons.mpr ⟨sound2915,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch242
