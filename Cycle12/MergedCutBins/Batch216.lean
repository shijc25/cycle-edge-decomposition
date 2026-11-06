import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch404
import Cycle12.MergedCutProfiles.Batch405
import Cycle12.MergedCutProfiles.Batch406
import Cycle12.MergedCutProfiles.Batch407
import Cycle12.MergedCutProfiles.Batch408

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch216

def retention2592 : RatCutRetentionCertificate := ⟨(121/2000),(61/1000),(641118321948012534/12006982453999286597),(999847671360378109/1000000000000000000),(5/2),(32691318634343004067/16000000000000000000),true,MergedCutProfiles.Batch405.profile16229,![MergedCutProfiles.Batch405.profile16229,MergedCutProfiles.Batch405.profile16230,MergedCutProfiles.Batch405.profile16231,MergedCutProfiles.Batch405.profile16232,MergedCutProfiles.Batch405.profile16233,MergedCutProfiles.Batch405.profile16234,MergedCutProfiles.Batch405.profile16222,MergedCutProfiles.Batch404.profile16192,MergedCutProfiles.Batch405.profile16235,MergedCutProfiles.Batch405.profile16236,MergedCutProfiles.Batch405.profile16237,MergedCutProfiles.Batch405.profile16238,MergedCutProfiles.Batch405.profile16239,MergedCutProfiles.Batch406.profile16240,MergedCutProfiles.Batch406.profile16241,MergedCutProfiles.Batch406.profile16242]⟩
theorem profilesValid2592 : retention2592.ProfilesValid := by
  change ∀ j : Fin 16, (retention2592.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch405.valid16229
  · exact MergedCutProfiles.Batch405.valid16230
  · exact MergedCutProfiles.Batch405.valid16231
  · exact MergedCutProfiles.Batch405.valid16232
  · exact MergedCutProfiles.Batch405.valid16233
  · exact MergedCutProfiles.Batch405.valid16234
  · exact MergedCutProfiles.Batch405.valid16222
  · exact MergedCutProfiles.Batch404.valid16192
  · exact MergedCutProfiles.Batch405.valid16235
  · exact MergedCutProfiles.Batch405.valid16236
  · exact MergedCutProfiles.Batch405.valid16237
  · exact MergedCutProfiles.Batch405.valid16238
  · exact MergedCutProfiles.Batch405.valid16239
  · exact MergedCutProfiles.Batch406.valid16240
  · exact MergedCutProfiles.Batch406.valid16241
  · exact MergedCutProfiles.Batch406.valid16242
theorem numericValid2592 : retention2592.NumericValid := by decide +kernel
def certificate2592 : RatCutBinCertificate := ⟨⟨retention2592,(1138008499066886571/500000000000000000),(9485872639178457/50000000000000000),(16012521855722338481/1000000000000000000),(192854032378345754617/500000000000000000),(987889068267467911/500000000000000000)⟩,(248797892784723967/250000000000000000),(74547558972930301/250000000000000000),(340968385970149667/1000000000000000000),(40712470866993941/200000000000000000)⟩
theorem valid2592 : certificate2592.Valid := by decide +kernel
theorem sound2592 : certificate2592.Sound := rat_cut_bin_certificate_sound certificate2592 profilesValid2592 numericValid2592 valid2592

def retention2593 : RatCutRetentionCertificate := ⟨(121/2000),(61/1000),(1734105703500506664/12006982453999286597),(320559160974006267/250000000000000000),(41/20),(568142674193646578763/320000000000000000000),true,MergedCutProfiles.Batch406.profile16243,![MergedCutProfiles.Batch406.profile16243,MergedCutProfiles.Batch406.profile16244,MergedCutProfiles.Batch406.profile16245,MergedCutProfiles.Batch406.profile16246,MergedCutProfiles.Batch406.profile16247,MergedCutProfiles.Batch406.profile16248,MergedCutProfiles.Batch406.profile16249,MergedCutProfiles.Batch406.profile16250,MergedCutProfiles.Batch406.profile16251,MergedCutProfiles.Batch406.profile16252,MergedCutProfiles.Batch406.profile16253,MergedCutProfiles.Batch406.profile16254,MergedCutProfiles.Batch406.profile16255,MergedCutProfiles.Batch406.profile16256,MergedCutProfiles.Batch406.profile16257,MergedCutProfiles.Batch406.profile16258]⟩
theorem profilesValid2593 : retention2593.ProfilesValid := by
  change ∀ j : Fin 16, (retention2593.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch406.valid16243
  · exact MergedCutProfiles.Batch406.valid16244
  · exact MergedCutProfiles.Batch406.valid16245
  · exact MergedCutProfiles.Batch406.valid16246
  · exact MergedCutProfiles.Batch406.valid16247
  · exact MergedCutProfiles.Batch406.valid16248
  · exact MergedCutProfiles.Batch406.valid16249
  · exact MergedCutProfiles.Batch406.valid16250
  · exact MergedCutProfiles.Batch406.valid16251
  · exact MergedCutProfiles.Batch406.valid16252
  · exact MergedCutProfiles.Batch406.valid16253
  · exact MergedCutProfiles.Batch406.valid16254
  · exact MergedCutProfiles.Batch406.valid16255
  · exact MergedCutProfiles.Batch406.valid16256
  · exact MergedCutProfiles.Batch406.valid16257
  · exact MergedCutProfiles.Batch406.valid16258
theorem numericValid2593 : retention2593.NumericValid := by decide +kernel
def certificate2593 : RatCutBinCertificate := ⟨⟨retention2593,(1138008499066886571/500000000000000000),(9485872639178457/50000000000000000),(16012521855722338481/1000000000000000000),(192854032378345754617/500000000000000000),(1720154382512825547/1000000000000000000)⟩,(248797892784723967/250000000000000000),(313768247316414263/1000000000000000000),(64505380831165307/200000000000000000),(101988436536347883/500000000000000000)⟩
theorem valid2593 : certificate2593.Valid := by decide +kernel
theorem sound2593 : certificate2593.Sound := rat_cut_bin_certificate_sound certificate2593 profilesValid2593 numericValid2593 valid2593

def retention2594 : RatCutRetentionCertificate := ⟨(121/2000),(61/1000),(9569421587171807937/24013964907998573194),(216763212937563333/62500000000000000),(23/20),(23577201193722957609/20000000000000000000),true,MergedCutProfiles.Batch406.profile16259,![MergedCutProfiles.Batch406.profile16259,MergedCutProfiles.Batch406.profile16260,MergedCutProfiles.Batch406.profile16261,MergedCutProfiles.Batch406.profile16262,MergedCutProfiles.Batch406.profile16263,MergedCutProfiles.Batch406.profile16264,MergedCutProfiles.Batch406.profile16265,MergedCutProfiles.Batch406.profile16266,MergedCutProfiles.Batch406.profile16267,MergedCutProfiles.Batch406.profile16268,MergedCutProfiles.Batch406.profile16269,MergedCutProfiles.Batch406.profile16270,MergedCutProfiles.Batch406.profile16271,MergedCutProfiles.Batch406.profile16272,MergedCutProfiles.Batch406.profile16273,MergedCutProfiles.Batch406.profile16274]⟩
theorem profilesValid2594 : retention2594.ProfilesValid := by
  change ∀ j : Fin 16, (retention2594.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch406.valid16259
  · exact MergedCutProfiles.Batch406.valid16260
  · exact MergedCutProfiles.Batch406.valid16261
  · exact MergedCutProfiles.Batch406.valid16262
  · exact MergedCutProfiles.Batch406.valid16263
  · exact MergedCutProfiles.Batch406.valid16264
  · exact MergedCutProfiles.Batch406.valid16265
  · exact MergedCutProfiles.Batch406.valid16266
  · exact MergedCutProfiles.Batch406.valid16267
  · exact MergedCutProfiles.Batch406.valid16268
  · exact MergedCutProfiles.Batch406.valid16269
  · exact MergedCutProfiles.Batch406.valid16270
  · exact MergedCutProfiles.Batch406.valid16271
  · exact MergedCutProfiles.Batch406.valid16272
  · exact MergedCutProfiles.Batch406.valid16273
  · exact MergedCutProfiles.Batch406.valid16274
theorem numericValid2594 : retention2594.NumericValid := by decide +kernel
def certificate2594 : RatCutBinCertificate := ⟨⟨retention2594,(1138008499066886571/500000000000000000),(9485872639178457/50000000000000000),(16012521855722338481/1000000000000000000),(192854032378345754617/500000000000000000),(1147844869659548769/1000000000000000000)⟩,(248797892784723967/250000000000000000),(187056680483579943/500000000000000000),(129028408456719217/500000000000000000),(102449372580020571/500000000000000000)⟩
theorem valid2594 : certificate2594.Valid := by decide +kernel
theorem sound2594 : certificate2594.Sound := rat_cut_bin_certificate_sound certificate2594 profilesValid2594 numericValid2594 valid2594

def retention2595 : RatCutRetentionCertificate := ⟨(121/2000),(61/1000),(5838256454365052215/12006982453999286597),(9569421587171807937/1000000000000000000),(21/20),(15637323537539695529625891835530735611591/15311074539474892699200000000000000000000),false,MergedCutProfiles.Batch406.profile16275,(fun _ => MergedCutProfiles.Batch406.profile16275)⟩
theorem profilesValid2595 : retention2595.ProfilesValid := by
  exact MergedCutProfiles.Batch406.valid16275
theorem numericValid2595 : retention2595.NumericValid := by decide +kernel
def certificate2595 : RatCutBinCertificate := ⟨⟨retention2595,(1138008499066886571/500000000000000000),(9485872639178457/50000000000000000),(16012521855722338481/1000000000000000000),(192854032378345754617/500000000000000000),(248247982355491367/250000000000000000)⟩,(248797892784723967/250000000000000000),(195455514179341667/500000000000000000),(48382826699344869/200000000000000000),(104017667646473691/500000000000000000)⟩
theorem valid2595 : certificate2595.Valid := by decide +kernel
theorem sound2595 : certificate2595.Sound := rat_cut_bin_certificate_sound certificate2595 profilesValid2595 numericValid2595 valid2595

def retention2596 : RatCutRetentionCertificate := ⟨(121/2000),(61/1000),(5955605409097789765/12006982453999286597),(1167651290873010443/100000000000000000),(21/20),(187893294807748057775070368014808766119/186824206539681670880000000000000000000),false,MergedCutProfiles.Batch406.profile16276,(fun _ => MergedCutProfiles.Batch406.profile16276)⟩
theorem profilesValid2596 : retention2596.ProfilesValid := by
  exact MergedCutProfiles.Batch406.valid16276
theorem numericValid2596 : retention2596.NumericValid := by decide +kernel
def certificate2596 : RatCutBinCertificate := ⟨⟨retention2596,(1138008499066886571/500000000000000000),(9485872639178457/50000000000000000),(16012521855722338481/1000000000000000000),(192854032378345754617/500000000000000000),(48870328399690031/50000000000000000)⟩,(248797892784723967/250000000000000000),(196407434247815611/500000000000000000),(30016328752714271/125000000000000000),(51676888188599009/250000000000000000)⟩
theorem valid2596 : certificate2596.Valid := by decide +kernel
theorem sound2596 : certificate2596.Sound := rat_cut_bin_certificate_sound certificate2596 profilesValid2596 numericValid2596 valid2596

def retention2597 : RatCutRetentionCertificate := ⟨(121/2000),(61/1000),(1/2),(1191121081819557953/100000000000000000),(21/20),(190226732210551697587593002814885044111/190579373091129272480000000000000000000),false,MergedCutProfiles.Batch406.profile16277,(fun _ => MergedCutProfiles.Batch406.profile16277)⟩
theorem profilesValid2597 : retention2597.ProfilesValid := by
  exact MergedCutProfiles.Batch406.valid16277
theorem numericValid2597 : retention2597.NumericValid := by decide +kernel
def certificate2597 : RatCutBinCertificate := ⟨⟨retention2597,(1138008499066886571/500000000000000000),(9485872639178457/50000000000000000),(16012521855722338481/1000000000000000000),(192854032378345754617/500000000000000000),(969833799053753521/1000000000000000000)⟩,(248797892784723967/250000000000000000),(395491637542021637/1000000000000000000),(237638640444263263/1000000000000000000),(40674025482344447/200000000000000000)⟩
theorem valid2597 : certificate2597.Valid := by decide +kernel
theorem sound2597 : certificate2597.Sound := rat_cut_bin_certificate_sound certificate2597 profilesValid2597 numericValid2597 valid2597

def retention2598 : RatCutRetentionCertificate := ⟨(121/2000),(61/1000),(5447531926120325481/12006982453999286597),(2531943457363765793/500000000000000000),(21/20),(2147176785025435440819454366917452628071/2025554765891012634400000000000000000000),false,MergedCutProfiles.Batch406.profile16278,(fun _ => MergedCutProfiles.Batch406.profile16278)⟩
theorem profilesValid2598 : retention2598.ProfilesValid := by
  exact MergedCutProfiles.Batch406.valid16278
theorem numericValid2598 : retention2598.NumericValid := by decide +kernel
def certificate2598 : RatCutBinCertificate := ⟨⟨retention2598,(1266985556066886571/500000000000000000),(9485872639178457/50000000000000000),(16012521855722338481/1000000000000000000),(192854032378345754617/500000000000000000),(3214115920937237/3125000000000000)⟩,(497322968681306963/500000000000000000),(226444236764451517/1000000000000000000),(437074003323590747/1000000000000000000),(359416299203525199/1000000000000000000)⟩
theorem valid2598 : certificate2598.Valid := by decide +kernel
theorem sound2598 : certificate2598.Sound := rat_cut_bin_certificate_sound certificate2598 profilesValid2598 numericValid2598 valid2598

def retention2599 : RatCutRetentionCertificate := ⟨(121/2000),(61/1000),(11915770880151339875/24013964907998573194),(5447531926120325481/500000000000000000),1,(335653651832839459965790902287593129/340470745382520342562500000000000000),false,MergedCutProfiles.Batch406.profile16279,(fun _ => MergedCutProfiles.Batch406.profile16279)⟩
theorem profilesValid2599 : retention2599.ProfilesValid := by
  exact MergedCutProfiles.Batch406.valid16279
theorem numericValid2599 : retention2599.NumericValid := by decide +kernel
def certificate2599 : RatCutBinCertificate := ⟨⟨retention2599,(1266985556066886571/500000000000000000),(9485872639178457/50000000000000000),(16012521855722338481/1000000000000000000),(192854032378345754617/500000000000000000),(955827648565328931/1000000000000000000)⟩,(497322968681306963/500000000000000000),(243665025654042031/1000000000000000000),(82437951997848541/200000000000000000),(180086239574458417/500000000000000000)⟩
theorem valid2599 : certificate2599.Valid := by decide +kernel
theorem sound2599 : certificate2599.Sound := rat_cut_bin_certificate_sound certificate2599 profilesValid2599 numericValid2599 valid2599

def retention2600 : RatCutRetentionCertificate := ⟨(121/2000),(61/1000),(1/2),(95326167041210719/8000000000000000),1,(46736606044411013826487491791047244931/47663083520605359500000000000000000000),false,MergedCutProfiles.Batch406.profile16277,(fun _ => MergedCutProfiles.Batch406.profile16277)⟩
theorem profilesValid2600 : retention2600.ProfilesValid := by
  exact MergedCutProfiles.Batch406.valid16277
theorem numericValid2600 : retention2600.NumericValid := by decide +kernel
def certificate2600 : RatCutBinCertificate := ⟨⟨retention2600,(1266985556066886571/500000000000000000),(9485872639178457/50000000000000000),(16012521855722338481/1000000000000000000),(192854032378345754617/500000000000000000),(38021521851254317/40000000000000000)⟩,(497322968681306963/500000000000000000),(12251049256768779/50000000000000000),(102570585150971869/250000000000000000),(44894635540321171/125000000000000000)⟩
theorem valid2600 : certificate2600.Valid := by decide +kernel
theorem sound2600 : certificate2600.Sound := rat_cut_bin_certificate_sound certificate2600 profilesValid2600 numericValid2600 valid2600

def retention2601 : RatCutRetentionCertificate := ⟨(61/1000),(123/2000),(311136962418548471/7850772678944933952),(46208459765130961/50000000000000000),(53/20),(133435054975400193701/64000000000000000000),true,MergedCutProfiles.Batch407.profile16280,![MergedCutProfiles.Batch407.profile16280,MergedCutProfiles.Batch407.profile16281,MergedCutProfiles.Batch407.profile16282,MergedCutProfiles.Batch407.profile16283,MergedCutProfiles.Batch407.profile16284,MergedCutProfiles.Batch407.profile16285,MergedCutProfiles.Batch407.profile16286,MergedCutProfiles.Batch407.profile16287,MergedCutProfiles.Batch407.profile16288,MergedCutProfiles.Batch407.profile16289,MergedCutProfiles.Batch407.profile16290,MergedCutProfiles.Batch407.profile16291,MergedCutProfiles.Batch407.profile16292,MergedCutProfiles.Batch407.profile16293,MergedCutProfiles.Batch407.profile16294,MergedCutProfiles.Batch407.profile16295]⟩
theorem profilesValid2601 : retention2601.ProfilesValid := by
  change ∀ j : Fin 16, (retention2601.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch407.valid16280
  · exact MergedCutProfiles.Batch407.valid16281
  · exact MergedCutProfiles.Batch407.valid16282
  · exact MergedCutProfiles.Batch407.valid16283
  · exact MergedCutProfiles.Batch407.valid16284
  · exact MergedCutProfiles.Batch407.valid16285
  · exact MergedCutProfiles.Batch407.valid16286
  · exact MergedCutProfiles.Batch407.valid16287
  · exact MergedCutProfiles.Batch407.valid16288
  · exact MergedCutProfiles.Batch407.valid16289
  · exact MergedCutProfiles.Batch407.valid16290
  · exact MergedCutProfiles.Batch407.valid16291
  · exact MergedCutProfiles.Batch407.valid16292
  · exact MergedCutProfiles.Batch407.valid16293
  · exact MergedCutProfiles.Batch407.valid16294
  · exact MergedCutProfiles.Batch407.valid16295
theorem numericValid2601 : retention2601.NumericValid := by decide +kernel
def certificate2601 : RatCutBinCertificate := ⟨⟨retention2601,(2285611066785509667/1000000000000000000),(19343761517970331/100000000000000000),(2020094325706112533/125000000000000000),(190899570021150208329/500000000000000000),(503102372549230469/250000000000000000)⟩,(497571832670278607/500000000000000000),(74976451427376277/250000000000000000),(169449257020229297/500000000000000000),(195300623876840531/1000000000000000000)⟩
theorem valid2601 : certificate2601.Valid := by decide +kernel
theorem sound2601 : certificate2601.Sound := rat_cut_bin_certificate_sound certificate2601 profilesValid2601 numericValid2601 valid2601

def retention2602 : RatCutRetentionCertificate := ⟨(61/1000),(123/2000),(1685502250000000/40889441036171531),(933410887255645413/1000000000000000000),(53/20),(83413118270628277857/40000000000000000000),true,MergedCutProfiles.Batch407.profile16296,![MergedCutProfiles.Batch407.profile16296,MergedCutProfiles.Batch407.profile16297,MergedCutProfiles.Batch407.profile16298,MergedCutProfiles.Batch407.profile16299,MergedCutProfiles.Batch407.profile16300,MergedCutProfiles.Batch407.profile16301,MergedCutProfiles.Batch407.profile16302,MergedCutProfiles.Batch407.profile16303,MergedCutProfiles.Batch407.profile16304,MergedCutProfiles.Batch407.profile16305,MergedCutProfiles.Batch407.profile16306,MergedCutProfiles.Batch407.profile16307,MergedCutProfiles.Batch407.profile16308,MergedCutProfiles.Batch407.profile16309,MergedCutProfiles.Batch407.profile16310,MergedCutProfiles.Batch407.profile16311]⟩
theorem profilesValid2602 : retention2602.ProfilesValid := by
  change ∀ j : Fin 16, (retention2602.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch407.valid16296
  · exact MergedCutProfiles.Batch407.valid16297
  · exact MergedCutProfiles.Batch407.valid16298
  · exact MergedCutProfiles.Batch407.valid16299
  · exact MergedCutProfiles.Batch407.valid16300
  · exact MergedCutProfiles.Batch407.valid16301
  · exact MergedCutProfiles.Batch407.valid16302
  · exact MergedCutProfiles.Batch407.valid16303
  · exact MergedCutProfiles.Batch407.valid16304
  · exact MergedCutProfiles.Batch407.valid16305
  · exact MergedCutProfiles.Batch407.valid16306
  · exact MergedCutProfiles.Batch407.valid16307
  · exact MergedCutProfiles.Batch407.valid16308
  · exact MergedCutProfiles.Batch407.valid16309
  · exact MergedCutProfiles.Batch407.valid16310
  · exact MergedCutProfiles.Batch407.valid16311
theorem numericValid2602 : retention2602.NumericValid := by decide +kernel
def certificate2602 : RatCutBinCertificate := ⟨⟨retention2602,(2285611066785509667/1000000000000000000),(19343761517970331/100000000000000000),(2020094325706112533/125000000000000000),(190899570021150208329/500000000000000000),(503203715366999319/250000000000000000)⟩,(497571832670278607/500000000000000000),(298658246608469391/1000000000000000000),(340402749065446267/1000000000000000000),(98330019927389291/500000000000000000)⟩
theorem valid2602 : certificate2602.Valid := by decide +kernel
theorem sound2602 : certificate2602.Sound := rat_cut_bin_certificate_sound certificate2602 profilesValid2602 numericValid2602 valid2602

def retention2603 : RatCutRetentionCertificate := ⟨(61/1000),(123/2000),(495417232806112877/11776159018417400928),(60678081/62500000),(51/20),(8304498469544859459/4000000000000000000),true,MergedCutProfiles.Batch407.profile16312,![MergedCutProfiles.Batch407.profile16312,MergedCutProfiles.Batch407.profile16313,MergedCutProfiles.Batch407.profile16314,MergedCutProfiles.Batch407.profile16315,MergedCutProfiles.Batch407.profile16316,MergedCutProfiles.Batch407.profile16317,MergedCutProfiles.Batch407.profile16318,MergedCutProfiles.Batch407.profile16319,MergedCutProfiles.Batch408.profile16320,MergedCutProfiles.Batch408.profile16321,MergedCutProfiles.Batch408.profile16322,MergedCutProfiles.Batch408.profile16323,MergedCutProfiles.Batch408.profile16324,MergedCutProfiles.Batch408.profile16325,MergedCutProfiles.Batch408.profile16326,MergedCutProfiles.Batch408.profile16327]⟩
theorem profilesValid2603 : retention2603.ProfilesValid := by
  change ∀ j : Fin 16, (retention2603.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch407.valid16312
  · exact MergedCutProfiles.Batch407.valid16313
  · exact MergedCutProfiles.Batch407.valid16314
  · exact MergedCutProfiles.Batch407.valid16315
  · exact MergedCutProfiles.Batch407.valid16316
  · exact MergedCutProfiles.Batch407.valid16317
  · exact MergedCutProfiles.Batch407.valid16318
  · exact MergedCutProfiles.Batch407.valid16319
  · exact MergedCutProfiles.Batch408.valid16320
  · exact MergedCutProfiles.Batch408.valid16321
  · exact MergedCutProfiles.Batch408.valid16322
  · exact MergedCutProfiles.Batch408.valid16323
  · exact MergedCutProfiles.Batch408.valid16324
  · exact MergedCutProfiles.Batch408.valid16325
  · exact MergedCutProfiles.Batch408.valid16326
  · exact MergedCutProfiles.Batch408.valid16327
theorem numericValid2603 : retention2603.NumericValid := by decide +kernel
def certificate2603 : RatCutBinCertificate := ⟨⟨retention2603,(2285611066785509667/1000000000000000000),(19343761517970331/100000000000000000),(2020094325706112533/125000000000000000),(190899570021150208329/500000000000000000),(2006347877583223441/1000000000000000000)⟩,(497571832670278607/500000000000000000),(147514078162767277/500000000000000000),(172404638959594119/500000000000000000),(204672177976927181/1000000000000000000)⟩
theorem valid2603 : certificate2603.Valid := by decide +kernel
theorem sound2603 : certificate2603.Sound := rat_cut_bin_certificate_sound certificate2603 profilesValid2603 numericValid2603 valid2603

def certificates : List RatCutBinCertificate := [certificate2592,certificate2593,certificate2594,certificate2595,certificate2596,certificate2597,certificate2598,certificate2599,certificate2600,certificate2601,certificate2602,certificate2603]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2592,List.forall_mem_cons.mpr ⟨sound2593,List.forall_mem_cons.mpr ⟨sound2594,List.forall_mem_cons.mpr ⟨sound2595,List.forall_mem_cons.mpr ⟨sound2596,List.forall_mem_cons.mpr ⟨sound2597,List.forall_mem_cons.mpr ⟨sound2598,List.forall_mem_cons.mpr ⟨sound2599,List.forall_mem_cons.mpr ⟨sound2600,List.forall_mem_cons.mpr ⟨sound2601,List.forall_mem_cons.mpr ⟨sound2602,List.forall_mem_cons.mpr ⟨sound2603,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch216
