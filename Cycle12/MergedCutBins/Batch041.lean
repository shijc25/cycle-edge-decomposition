import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch081
import Cycle12.MergedCutProfiles.Batch082
import Cycle12.MergedCutProfiles.Batch083

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch041

def retention492 : RatCutRetentionCertificate := ⟨(79/2000),(1/25),(788820487749520844/31509510832091315197),(781010383910416677/1000000000000000000),(13/4),(3454270296120386199/1600000000000000000),true,MergedCutProfiles.Batch081.profile3245,![MergedCutProfiles.Batch081.profile3245,MergedCutProfiles.Batch081.profile3246,MergedCutProfiles.Batch081.profile3247,MergedCutProfiles.Batch081.profile3248,MergedCutProfiles.Batch081.profile3249,MergedCutProfiles.Batch081.profile3250,MergedCutProfiles.Batch081.profile3251,MergedCutProfiles.Batch081.profile3252,MergedCutProfiles.Batch081.profile3253,MergedCutProfiles.Batch081.profile3254,MergedCutProfiles.Batch081.profile3255,MergedCutProfiles.Batch081.profile3256,MergedCutProfiles.Batch081.profile3257,MergedCutProfiles.Batch081.profile3258,MergedCutProfiles.Batch081.profile3259,MergedCutProfiles.Batch081.profile3260]⟩
theorem profilesValid492 : retention492.ProfilesValid := by
  change ∀ j : Fin 16, (retention492.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch081.valid3245
  · exact MergedCutProfiles.Batch081.valid3246
  · exact MergedCutProfiles.Batch081.valid3247
  · exact MergedCutProfiles.Batch081.valid3248
  · exact MergedCutProfiles.Batch081.valid3249
  · exact MergedCutProfiles.Batch081.valid3250
  · exact MergedCutProfiles.Batch081.valid3251
  · exact MergedCutProfiles.Batch081.valid3252
  · exact MergedCutProfiles.Batch081.valid3253
  · exact MergedCutProfiles.Batch081.valid3254
  · exact MergedCutProfiles.Batch081.valid3255
  · exact MergedCutProfiles.Batch081.valid3256
  · exact MergedCutProfiles.Batch081.valid3257
  · exact MergedCutProfiles.Batch081.valid3258
  · exact MergedCutProfiles.Batch081.valid3259
  · exact MergedCutProfiles.Batch081.valid3260
theorem numericValid492 : retention492.NumericValid := by decide +kernel
def certificate492 : RatCutBinCertificate := ⟨⟨retention492,(64470631172576803/31250000000000000),(1140020255178431/15625000000000000),(11265131442284212681/1000000000000000000),(71182583261338560763/200000000000000000),(211548925674346253/100000000000000000)⟩,(971301455568609/976562500000000),(407192034210338059/1000000000000000000),(9078276231605917/40000000000000000),(29208577061419527/250000000000000000)⟩
theorem valid492 : certificate492.Valid := by decide +kernel
theorem sound492 : certificate492.Sound := rat_cut_bin_certificate_sound certificate492 profilesValid492 numericValid492 valid492

def retention493 : RatCutRetentionCertificate := ⟨(79/2000),(1/25),(880062049383236518/31509510832091315197),(197205121937380211/250000000000000000),(13/4),(137675847722673664391/64000000000000000000),true,MergedCutProfiles.Batch081.profile3261,![MergedCutProfiles.Batch081.profile3261,MergedCutProfiles.Batch081.profile3262,MergedCutProfiles.Batch081.profile3263,MergedCutProfiles.Batch081.profile3264,MergedCutProfiles.Batch081.profile3265,MergedCutProfiles.Batch081.profile3266,MergedCutProfiles.Batch081.profile3267,MergedCutProfiles.Batch081.profile3268,MergedCutProfiles.Batch081.profile3254,MergedCutProfiles.Batch081.profile3269,MergedCutProfiles.Batch081.profile3270,MergedCutProfiles.Batch081.profile3271,MergedCutProfiles.Batch081.profile3272,MergedCutProfiles.Batch081.profile3273,MergedCutProfiles.Batch081.profile3274,MergedCutProfiles.Batch081.profile3275]⟩
theorem profilesValid493 : retention493.ProfilesValid := by
  change ∀ j : Fin 16, (retention493.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch081.valid3261
  · exact MergedCutProfiles.Batch081.valid3262
  · exact MergedCutProfiles.Batch081.valid3263
  · exact MergedCutProfiles.Batch081.valid3264
  · exact MergedCutProfiles.Batch081.valid3265
  · exact MergedCutProfiles.Batch081.valid3266
  · exact MergedCutProfiles.Batch081.valid3267
  · exact MergedCutProfiles.Batch081.valid3268
  · exact MergedCutProfiles.Batch081.valid3254
  · exact MergedCutProfiles.Batch081.valid3269
  · exact MergedCutProfiles.Batch081.valid3270
  · exact MergedCutProfiles.Batch081.valid3271
  · exact MergedCutProfiles.Batch081.valid3272
  · exact MergedCutProfiles.Batch081.valid3273
  · exact MergedCutProfiles.Batch081.valid3274
  · exact MergedCutProfiles.Batch081.valid3275
theorem numericValid493 : retention493.NumericValid := by decide +kernel
def certificate493 : RatCutBinCertificate := ⟨⟨retention493,(64470631172576803/31250000000000000),(1140020255178431/15625000000000000),(11265131442284212681/1000000000000000000),(71182583261338560763/200000000000000000),(65867358658116253/31250000000000000)⟩,(971301455568609/976562500000000),(406803195290286591/1000000000000000000),(113653219415943199/500000000000000000),(29227469168011221/250000000000000000)⟩
theorem valid493 : certificate493.Valid := by decide +kernel
theorem sound493 : certificate493.Sound := rat_cut_bin_certificate_sound certificate493 profilesValid493 numericValid493 valid493

def retention494 : RatCutRetentionCertificate := ⟨(79/2000),(1/25),(927870406000000000/31509510832091315197),(440031024691618259/500000000000000000),(59/20),(1368210180774285620387/640000000000000000000),true,MergedCutProfiles.Batch081.profile3276,![MergedCutProfiles.Batch081.profile3276,MergedCutProfiles.Batch081.profile3277,MergedCutProfiles.Batch081.profile3278,MergedCutProfiles.Batch081.profile3279,MergedCutProfiles.Batch082.profile3280,MergedCutProfiles.Batch082.profile3281,MergedCutProfiles.Batch082.profile3282,MergedCutProfiles.Batch082.profile3283,MergedCutProfiles.Batch082.profile3284,MergedCutProfiles.Batch082.profile3285,MergedCutProfiles.Batch082.profile3286,MergedCutProfiles.Batch082.profile3287,MergedCutProfiles.Batch082.profile3288,MergedCutProfiles.Batch082.profile3289,MergedCutProfiles.Batch082.profile3290,MergedCutProfiles.Batch082.profile3291]⟩
theorem profilesValid494 : retention494.ProfilesValid := by
  change ∀ j : Fin 16, (retention494.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch081.valid3276
  · exact MergedCutProfiles.Batch081.valid3277
  · exact MergedCutProfiles.Batch081.valid3278
  · exact MergedCutProfiles.Batch081.valid3279
  · exact MergedCutProfiles.Batch082.valid3280
  · exact MergedCutProfiles.Batch082.valid3281
  · exact MergedCutProfiles.Batch082.valid3282
  · exact MergedCutProfiles.Batch082.valid3283
  · exact MergedCutProfiles.Batch082.valid3284
  · exact MergedCutProfiles.Batch082.valid3285
  · exact MergedCutProfiles.Batch082.valid3286
  · exact MergedCutProfiles.Batch082.valid3287
  · exact MergedCutProfiles.Batch082.valid3288
  · exact MergedCutProfiles.Batch082.valid3289
  · exact MergedCutProfiles.Batch082.valid3290
  · exact MergedCutProfiles.Batch082.valid3291
theorem numericValid494 : retention494.NumericValid := by decide +kernel
def certificate494 : RatCutBinCertificate := ⟨⟨retention494,(64470631172576803/31250000000000000),(1140020255178431/15625000000000000),(11265131442284212681/1000000000000000000),(71182583261338560763/200000000000000000),(1049203846754496311/500000000000000000)⟩,(971301455568609/976562500000000),(389007125173058553/1000000000000000000),(24370696327425209/100000000000000000),(135215530228636591/1000000000000000000)⟩
theorem valid494 : certificate494.Valid := by decide +kernel
theorem sound494 : certificate494.Sound := rat_cut_bin_certificate_sound certificate494 profilesValid494 numericValid494 valid494

def retention495 : RatCutRetentionCertificate := ⟨(79/2000),(1/25),(991675945314268520/31509510832091315197),(463935203/500000000),(14/5),(16985905659078261667/8000000000000000000),true,MergedCutProfiles.Batch082.profile3292,![MergedCutProfiles.Batch082.profile3292,MergedCutProfiles.Batch082.profile3293,MergedCutProfiles.Batch082.profile3294,MergedCutProfiles.Batch081.profile3249,MergedCutProfiles.Batch082.profile3295,MergedCutProfiles.Batch082.profile3296,MergedCutProfiles.Batch082.profile3297,MergedCutProfiles.Batch081.profile3254,MergedCutProfiles.Batch082.profile3298,MergedCutProfiles.Batch082.profile3299,MergedCutProfiles.Batch082.profile3300,MergedCutProfiles.Batch082.profile3301,MergedCutProfiles.Batch082.profile3302,MergedCutProfiles.Batch082.profile3303,MergedCutProfiles.Batch082.profile3291,MergedCutProfiles.Batch082.profile3304]⟩
theorem profilesValid495 : retention495.ProfilesValid := by
  change ∀ j : Fin 16, (retention495.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch082.valid3292
  · exact MergedCutProfiles.Batch082.valid3293
  · exact MergedCutProfiles.Batch082.valid3294
  · exact MergedCutProfiles.Batch081.valid3249
  · exact MergedCutProfiles.Batch082.valid3295
  · exact MergedCutProfiles.Batch082.valid3296
  · exact MergedCutProfiles.Batch082.valid3297
  · exact MergedCutProfiles.Batch081.valid3254
  · exact MergedCutProfiles.Batch082.valid3298
  · exact MergedCutProfiles.Batch082.valid3299
  · exact MergedCutProfiles.Batch082.valid3300
  · exact MergedCutProfiles.Batch082.valid3301
  · exact MergedCutProfiles.Batch082.valid3302
  · exact MergedCutProfiles.Batch082.valid3303
  · exact MergedCutProfiles.Batch082.valid3291
  · exact MergedCutProfiles.Batch082.valid3304
theorem numericValid495 : retention495.NumericValid := by decide +kernel
def certificate495 : RatCutBinCertificate := ⟨⟨retention495,(64470631172576803/31250000000000000),(1140020255178431/15625000000000000),(11265131442284212681/1000000000000000000),(71182583261338560763/200000000000000000),(260727742328058201/125000000000000000)⟩,(971301455568609/976562500000000),(191283556930903159/500000000000000000),(249840558593605003/1000000000000000000),(71866271629644929/500000000000000000)⟩
theorem valid495 : certificate495.Valid := by decide +kernel
theorem sound495 : certificate495.Sound := rat_cut_bin_certificate_sound certificate495 profilesValid495 numericValid495 valid495

def retention496 : RatCutRetentionCertificate := ⟨(79/2000),(1/25),(1680360984606390959/31509510832091315197),(24791898632856713/25000000000000000),(53/20),(8176881451847749967/4000000000000000000),true,MergedCutProfiles.Batch082.profile3305,![MergedCutProfiles.Batch082.profile3305,MergedCutProfiles.Batch082.profile3306,MergedCutProfiles.Batch082.profile3307,MergedCutProfiles.Batch082.profile3308,MergedCutProfiles.Batch082.profile3309,MergedCutProfiles.Batch082.profile3310,MergedCutProfiles.Batch082.profile3311,MergedCutProfiles.Batch082.profile3312,MergedCutProfiles.Batch082.profile3313,MergedCutProfiles.Batch082.profile3314,MergedCutProfiles.Batch082.profile3315,MergedCutProfiles.Batch082.profile3316,MergedCutProfiles.Batch082.profile3317,MergedCutProfiles.Batch082.profile3318,MergedCutProfiles.Batch082.profile3319,MergedCutProfiles.Batch083.profile3320]⟩
theorem profilesValid496 : retention496.ProfilesValid := by
  change ∀ j : Fin 16, (retention496.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch082.valid3305
  · exact MergedCutProfiles.Batch082.valid3306
  · exact MergedCutProfiles.Batch082.valid3307
  · exact MergedCutProfiles.Batch082.valid3308
  · exact MergedCutProfiles.Batch082.valid3309
  · exact MergedCutProfiles.Batch082.valid3310
  · exact MergedCutProfiles.Batch082.valid3311
  · exact MergedCutProfiles.Batch082.valid3312
  · exact MergedCutProfiles.Batch082.valid3313
  · exact MergedCutProfiles.Batch082.valid3314
  · exact MergedCutProfiles.Batch082.valid3315
  · exact MergedCutProfiles.Batch082.valid3316
  · exact MergedCutProfiles.Batch082.valid3317
  · exact MergedCutProfiles.Batch082.valid3318
  · exact MergedCutProfiles.Batch082.valid3319
  · exact MergedCutProfiles.Batch083.valid3320
theorem numericValid496 : retention496.NumericValid := by decide +kernel
def certificate496 : RatCutBinCertificate := ⟨⟨retention496,(64470631172576803/31250000000000000),(1140020255178431/15625000000000000),(11265131442284212681/1000000000000000000),(71182583261338560763/200000000000000000),(2008808568964020411/1000000000000000000)⟩,(971301455568609/976562500000000),(193213638120880723/500000000000000000),(30768896443412523/125000000000000000),(28782009257738627/200000000000000000)⟩
theorem valid496 : certificate496.Valid := by decide +kernel
theorem sound496 : certificate496.Sound := rat_cut_bin_certificate_sound certificate496 profilesValid496 numericValid496 valid496

def retention497 : RatCutRetentionCertificate := ⟨(79/2000),(1/25),(7183286058563881795/31509510832091315197),(1680360984606390959/1000000000000000000),(9/5),(263744146194801253784913344842366607259/168036098460639095900000000000000000000),false,MergedCutProfiles.Batch083.profile3321,(fun _ => MergedCutProfiles.Batch083.profile3321)⟩
theorem profilesValid497 : retention497.ProfilesValid := by
  exact MergedCutProfiles.Batch083.valid3321
theorem numericValid497 : retention497.NumericValid := by decide +kernel
def certificate497 : RatCutBinCertificate := ⟨⟨retention497,(64470631172576803/31250000000000000),(1140020255178431/15625000000000000),(11265131442284212681/1000000000000000000),(71182583261338560763/200000000000000000),(1545515328186400931/1000000000000000000)⟩,(971301455568609/976562500000000),(418550239059789501/1000000000000000000),(108454587275053353/500000000000000000),(144168898551878937/1000000000000000000)⟩
theorem valid497 : certificate497.Valid := by decide +kernel
theorem sound497 : certificate497.Sound := rat_cut_bin_certificate_sound certificate497 profilesValid497 numericValid497 valid497

def retention498 : RatCutRetentionCertificate := ⟨(79/2000),(1/25),(14415155327031255033/31509510832091315197),(1436657211712776359/200000000000000000),1,(53567403291242339207/51200000000000000000),true,MergedCutProfiles.Batch083.profile3322,![MergedCutProfiles.Batch083.profile3322,MergedCutProfiles.Batch083.profile3323,MergedCutProfiles.Batch083.profile3324,MergedCutProfiles.Batch083.profile3325,MergedCutProfiles.Batch083.profile3326,MergedCutProfiles.Batch083.profile3327,MergedCutProfiles.Batch083.profile3328,MergedCutProfiles.Batch083.profile3329,MergedCutProfiles.Batch083.profile3330,MergedCutProfiles.Batch083.profile3331,MergedCutProfiles.Batch083.profile3332,MergedCutProfiles.Batch083.profile3333,MergedCutProfiles.Batch083.profile3334,MergedCutProfiles.Batch083.profile3335,MergedCutProfiles.Batch083.profile3336,MergedCutProfiles.Batch083.profile3337]⟩
theorem profilesValid498 : retention498.ProfilesValid := by
  change ∀ j : Fin 16, (retention498.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch083.valid3322
  · exact MergedCutProfiles.Batch083.valid3323
  · exact MergedCutProfiles.Batch083.valid3324
  · exact MergedCutProfiles.Batch083.valid3325
  · exact MergedCutProfiles.Batch083.valid3326
  · exact MergedCutProfiles.Batch083.valid3327
  · exact MergedCutProfiles.Batch083.valid3328
  · exact MergedCutProfiles.Batch083.valid3329
  · exact MergedCutProfiles.Batch083.valid3330
  · exact MergedCutProfiles.Batch083.valid3331
  · exact MergedCutProfiles.Batch083.valid3332
  · exact MergedCutProfiles.Batch083.valid3333
  · exact MergedCutProfiles.Batch083.valid3334
  · exact MergedCutProfiles.Batch083.valid3335
  · exact MergedCutProfiles.Batch083.valid3336
  · exact MergedCutProfiles.Batch083.valid3337
theorem numericValid498 : retention498.NumericValid := by decide +kernel
def certificate498 : RatCutBinCertificate := ⟨⟨retention498,(64470631172576803/31250000000000000),(1140020255178431/15625000000000000),(11265131442284212681/1000000000000000000),(71182583261338560763/200000000000000000),(516438032698835513/500000000000000000)⟩,(971301455568609/976562500000000),(122026331762439991/250000000000000000),(40453427591036379/250000000000000000),(5811276674245439/40000000000000000)⟩
theorem valid498 : certificate498.Valid := by decide +kernel
theorem sound498 : certificate498.Sound := rat_cut_bin_certificate_sound certificate498 profilesValid498 numericValid498 valid498

def retention499 : RatCutRetentionCertificate := ⟨(79/2000),(1/25),(15609547608546134460/31509510832091315197),(14415155327031255033/1000000000000000000),(21/20),(7759486794879432020604432636252928549077/7688082841083336017600000000000000000000),false,MergedCutProfiles.Batch083.profile3338,(fun _ => MergedCutProfiles.Batch083.profile3338)⟩
theorem profilesValid499 : retention499.ProfilesValid := by
  exact MergedCutProfiles.Batch083.valid3338
theorem numericValid499 : retention499.NumericValid := by decide +kernel
def certificate499 : RatCutBinCertificate := ⟨⟨retention499,(64470631172576803/31250000000000000),(1140020255178431/15625000000000000),(11265131442284212681/1000000000000000000),(71182583261338560763/200000000000000000),(995257431265920349/1000000000000000000)⟩,(971301455568609/976562500000000),(96917237181062939/200000000000000000),(32870085957584231/200000000000000000),(145783958562550979/1000000000000000000)⟩
theorem valid499 : certificate499.Valid := by decide +kernel
theorem sound499 : certificate499.Sound := rat_cut_bin_certificate_sound certificate499 profilesValid499 numericValid499 valid499

def retention500 : RatCutRetentionCertificate := ⟨(79/2000),(1/25),(1/2),(780477380427306723/50000000000000000),(21/20),(12496731217523767721576033127786362539/12487638086836907568000000000000000000),false,MergedCutProfiles.Batch083.profile3339,(fun _ => MergedCutProfiles.Batch083.profile3339)⟩
theorem profilesValid500 : retention500.ProfilesValid := by
  exact MergedCutProfiles.Batch083.valid3339
theorem numericValid500 : retention500.NumericValid := by decide +kernel
def certificate500 : RatCutBinCertificate := ⟨⟨retention500,(64470631172576803/31250000000000000),(1140020255178431/15625000000000000),(11265131442284212681/1000000000000000000),(71182583261338560763/200000000000000000),(246674500337657503/250000000000000000)⟩,(971301455568609/976562500000000),(121776433782451451/250000000000000000),(162531663242205007/1000000000000000000),(143647686352102597/1000000000000000000)⟩
theorem valid500 : certificate500.Valid := by decide +kernel
theorem sound500 : certificate500.Sound := rat_cut_bin_certificate_sound certificate500 profilesValid500 numericValid500 valid500

def retention501 : RatCutRetentionCertificate := ⟨(79/2000),(1/25),(13631221781261138628/31509510832091315197),(3701986394800524983/1000000000000000000),(5/4),(268819349737312660849904300594939562079/236927129267233598912000000000000000000),false,MergedCutProfiles.Batch083.profile3340,(fun _ => MergedCutProfiles.Batch083.profile3340)⟩
theorem profilesValid501 : retention501.ProfilesValid := by
  exact MergedCutProfiles.Batch083.valid3340
theorem numericValid501 : retention501.NumericValid := by decide +kernel
def certificate501 : RatCutBinCertificate := ⟨⟨retention501,(76790988516326803/31250000000000000),(1140020255178431/15625000000000000),(11265131442284212681/1000000000000000000),(71182583261338560763/200000000000000000),(278678158902867843/250000000000000000)⟩,(19871653384653949/20000000000000000),(22934302636608177/62500000000000000),(265169318007200707/1000000000000000000),(6152564203062981/31250000000000000)⟩
theorem valid501 : certificate501.Valid := by decide +kernel
theorem sound501 : certificate501.Sound := rat_cut_bin_certificate_sound certificate501 profilesValid501 numericValid501 valid501

def retention502 : RatCutRetentionCertificate := ⟨(79/2000),(1/25),(15513601913349195957/31509510832091315197),(3407805445315284657/250000000000000000),1,(2720491685892190322018603422255898587/2726244356252227725600000000000000000),false,MergedCutProfiles.Batch083.profile3341,(fun _ => MergedCutProfiles.Batch083.profile3341)⟩
theorem profilesValid502 : retention502.ProfilesValid := by
  exact MergedCutProfiles.Batch083.valid3341
theorem numericValid502 : retention502.NumericValid := by decide +kernel
def certificate502 : RatCutBinCertificate := ⟨⟨retention502,(76790988516326803/31250000000000000),(1140020255178431/15625000000000000),(11265131442284212681/1000000000000000000),(71182583261338560763/200000000000000000),(39278971630688947/40000000000000000)⟩,(19871653384653949/20000000000000000),(83310228150239247/200000000000000000),(54663759719537017/250000000000000000),(4973968977937289/25000000000000000)⟩
theorem valid502 : certificate502.Valid := by decide +kernel
theorem sound502 : certificate502.Sound := rat_cut_bin_certificate_sound certificate502 profilesValid502 numericValid502 valid502

def retention503 : RatCutRetentionCertificate := ⟨(79/2000),(1/25),(15668737932482687917/31509510832091315197),(15513601913349195957/1000000000000000000),1,(10977420945099887547694367293241653/11081144223820854255000000000000000),false,MergedCutProfiles.Batch083.profile3342,(fun _ => MergedCutProfiles.Batch083.profile3342)⟩
theorem profilesValid503 : retention503.ProfilesValid := by
  exact MergedCutProfiles.Batch083.valid3342
theorem numericValid503 : retention503.NumericValid := by decide +kernel
def certificate503 : RatCutBinCertificate := ⟨⟨retention503,(76790988516326803/31250000000000000),(1140020255178431/15625000000000000),(11265131442284212681/1000000000000000000),(71182583261338560763/200000000000000000),(974724087823613911/1000000000000000000)⟩,(19871653384653949/20000000000000000),(419649535819673133/1000000000000000000),(107976600407286097/500000000000000000),(39348805144679189/200000000000000000)⟩
theorem valid503 : certificate503.Valid := by decide +kernel
theorem sound503 : certificate503.Sound := rat_cut_bin_certificate_sound certificate503 profilesValid503 numericValid503 valid503

def certificates : List RatCutBinCertificate := [certificate492,certificate493,certificate494,certificate495,certificate496,certificate497,certificate498,certificate499,certificate500,certificate501,certificate502,certificate503]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound492,List.forall_mem_cons.mpr ⟨sound493,List.forall_mem_cons.mpr ⟨sound494,List.forall_mem_cons.mpr ⟨sound495,List.forall_mem_cons.mpr ⟨sound496,List.forall_mem_cons.mpr ⟨sound497,List.forall_mem_cons.mpr ⟨sound498,List.forall_mem_cons.mpr ⟨sound499,List.forall_mem_cons.mpr ⟨sound500,List.forall_mem_cons.mpr ⟨sound501,List.forall_mem_cons.mpr ⟨sound502,List.forall_mem_cons.mpr ⟨sound503,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch041
