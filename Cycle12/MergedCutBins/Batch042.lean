import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch083
import Cycle12.MergedCutProfiles.Batch084
import Cycle12.MergedCutProfiles.Batch085

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch042

def retention504 : RatCutRetentionCertificate := ⟨(79/2000),(1/25),(1/2),(15668737932482687917/1000000000000000000),1,(193020647468994408056108210098204107/195859224156033598962500000000000000),false,MergedCutProfiles.Batch083.profile3339,(fun _ => MergedCutProfiles.Batch083.profile3339)⟩
theorem profilesValid504 : retention504.ProfilesValid := by
  exact MergedCutProfiles.Batch083.valid3339
theorem numericValid504 : retention504.NumericValid := by decide +kernel
def certificate504 : RatCutBinCertificate := ⟨⟨retention504,(76790988516326803/31250000000000000),(1140020255178431/15625000000000000),(11265131442284212681/1000000000000000000),(71182583261338560763/200000000000000000),(969591486425076457/1000000000000000000)⟩,(19871653384653949/20000000000000000),(421870980443104329/1000000000000000000),(214030160503079819/1000000000000000000),(24267382412829039/125000000000000000)⟩
theorem valid504 : certificate504.Valid := by decide +kernel
theorem sound504 : certificate504.Sound := rat_cut_bin_certificate_sound certificate504 profilesValid504 numericValid504 valid504

def retention505 : RatCutRetentionCertificate := ⟨(1/25),(81/2000),(797357917602472465/30653648054070669896),(24670727648591351/31250000000000000),(16/5),(21516435173112769481/10000000000000000000),true,MergedCutProfiles.Batch083.profile3343,![MergedCutProfiles.Batch083.profile3343,MergedCutProfiles.Batch083.profile3344,MergedCutProfiles.Batch083.profile3345,MergedCutProfiles.Batch083.profile3346,MergedCutProfiles.Batch083.profile3347,MergedCutProfiles.Batch083.profile3348,MergedCutProfiles.Batch083.profile3349,MergedCutProfiles.Batch083.profile3350,MergedCutProfiles.Batch083.profile3351,MergedCutProfiles.Batch083.profile3352,MergedCutProfiles.Batch083.profile3353,MergedCutProfiles.Batch083.profile3354,MergedCutProfiles.Batch083.profile3355,MergedCutProfiles.Batch083.profile3356,MergedCutProfiles.Batch083.profile3357,MergedCutProfiles.Batch083.profile3358]⟩
theorem profilesValid505 : retention505.ProfilesValid := by
  change ∀ j : Fin 16, (retention505.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch083.valid3343
  · exact MergedCutProfiles.Batch083.valid3344
  · exact MergedCutProfiles.Batch083.valid3345
  · exact MergedCutProfiles.Batch083.valid3346
  · exact MergedCutProfiles.Batch083.valid3347
  · exact MergedCutProfiles.Batch083.valid3348
  · exact MergedCutProfiles.Batch083.valid3349
  · exact MergedCutProfiles.Batch083.valid3350
  · exact MergedCutProfiles.Batch083.valid3351
  · exact MergedCutProfiles.Batch083.valid3352
  · exact MergedCutProfiles.Batch083.valid3353
  · exact MergedCutProfiles.Batch083.valid3354
  · exact MergedCutProfiles.Batch083.valid3355
  · exact MergedCutProfiles.Batch083.valid3356
  · exact MergedCutProfiles.Batch083.valid3357
  · exact MergedCutProfiles.Batch083.valid3358
theorem numericValid505 : retention505.NumericValid := by decide +kernel
def certificate505 : RatCutBinCertificate := ⟨⟨retention505,(206814955857401211/100000000000000000),(14993777272926573/200000000000000000),(11351624961498016857/1000000000000000000),(21806684937427826307/62500000000000000),(84317296104864599/40000000000000000)⟩,(124312818874368129/125000000000000000),(12601374730549157/31250000000000000),(230523168869806759/1000000000000000000),(119667453170922919/1000000000000000000)⟩
theorem valid505 : certificate505.Valid := by decide +kernel
theorem sound505 : certificate505.Sound := rat_cut_bin_certificate_sound certificate505 profilesValid505 numericValid505 valid505

def retention506 : RatCutRetentionCertificate := ⟨(1/25),(81/2000),(111198373704006271/3831706006758833737),(159471583520494493/200000000000000000),(16/5),(548854521066417660537/256000000000000000000),true,MergedCutProfiles.Batch083.profile3359,![MergedCutProfiles.Batch083.profile3359,MergedCutProfiles.Batch084.profile3360,MergedCutProfiles.Batch084.profile3361,MergedCutProfiles.Batch084.profile3362,MergedCutProfiles.Batch084.profile3363,MergedCutProfiles.Batch084.profile3364,MergedCutProfiles.Batch084.profile3365,MergedCutProfiles.Batch084.profile3366,MergedCutProfiles.Batch083.profile3352,MergedCutProfiles.Batch084.profile3367,MergedCutProfiles.Batch084.profile3368,MergedCutProfiles.Batch084.profile3369,MergedCutProfiles.Batch084.profile3370,MergedCutProfiles.Batch084.profile3371,MergedCutProfiles.Batch084.profile3372,MergedCutProfiles.Batch084.profile3373]⟩
theorem profilesValid506 : retention506.ProfilesValid := by
  change ∀ j : Fin 16, (retention506.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch083.valid3359
  · exact MergedCutProfiles.Batch084.valid3360
  · exact MergedCutProfiles.Batch084.valid3361
  · exact MergedCutProfiles.Batch084.valid3362
  · exact MergedCutProfiles.Batch084.valid3363
  · exact MergedCutProfiles.Batch084.valid3364
  · exact MergedCutProfiles.Batch084.valid3365
  · exact MergedCutProfiles.Batch084.valid3366
  · exact MergedCutProfiles.Batch083.valid3352
  · exact MergedCutProfiles.Batch084.valid3367
  · exact MergedCutProfiles.Batch084.valid3368
  · exact MergedCutProfiles.Batch084.valid3369
  · exact MergedCutProfiles.Batch084.valid3370
  · exact MergedCutProfiles.Batch084.valid3371
  · exact MergedCutProfiles.Batch084.valid3372
  · exact MergedCutProfiles.Batch084.valid3373
theorem numericValid506 : retention506.NumericValid := by decide +kernel
def certificate506 : RatCutBinCertificate := ⟨⟨retention506,(206814955857401211/100000000000000000),(14993777272926573/200000000000000000),(11351624961498016857/1000000000000000000),(21806684937427826307/62500000000000000),(2100251895032410173/1000000000000000000)⟩,(124312818874368129/125000000000000000),(80576537605387177/200000000000000000),(230851457883245921/1000000000000000000),(119736581623805993/1000000000000000000)⟩
theorem valid506 : certificate506.Valid := by decide +kernel
theorem sound506 : certificate506.Sound := rat_cut_bin_certificate_sound certificate506 profilesValid506 numericValid506 valid506

def retention507 : RatCutRetentionCertificate := ⟨(1/25),(81/2000),(114441922000000000/3831706006758833737),(111198373704006271/125000000000000000),(29/10),(341077267188172810591/160000000000000000000),true,MergedCutProfiles.Batch084.profile3374,![MergedCutProfiles.Batch084.profile3374,MergedCutProfiles.Batch084.profile3375,MergedCutProfiles.Batch084.profile3376,MergedCutProfiles.Batch084.profile3377,MergedCutProfiles.Batch084.profile3378,MergedCutProfiles.Batch084.profile3379,MergedCutProfiles.Batch084.profile3380,MergedCutProfiles.Batch084.profile3381,MergedCutProfiles.Batch084.profile3382,MergedCutProfiles.Batch084.profile3383,MergedCutProfiles.Batch084.profile3384,MergedCutProfiles.Batch084.profile3385,MergedCutProfiles.Batch083.profile3357,MergedCutProfiles.Batch084.profile3386,MergedCutProfiles.Batch084.profile3387,MergedCutProfiles.Batch084.profile3388]⟩
theorem profilesValid507 : retention507.ProfilesValid := by
  change ∀ j : Fin 16, (retention507.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch084.valid3374
  · exact MergedCutProfiles.Batch084.valid3375
  · exact MergedCutProfiles.Batch084.valid3376
  · exact MergedCutProfiles.Batch084.valid3377
  · exact MergedCutProfiles.Batch084.valid3378
  · exact MergedCutProfiles.Batch084.valid3379
  · exact MergedCutProfiles.Batch084.valid3380
  · exact MergedCutProfiles.Batch084.valid3381
  · exact MergedCutProfiles.Batch084.valid3382
  · exact MergedCutProfiles.Batch084.valid3383
  · exact MergedCutProfiles.Batch084.valid3384
  · exact MergedCutProfiles.Batch084.valid3385
  · exact MergedCutProfiles.Batch083.valid3357
  · exact MergedCutProfiles.Batch084.valid3386
  · exact MergedCutProfiles.Batch084.valid3387
  · exact MergedCutProfiles.Batch084.valid3388
theorem numericValid507 : retention507.NumericValid := by decide +kernel
def certificate507 : RatCutBinCertificate := ⟨⟨retention507,(206814955857401211/100000000000000000),(14993777272926573/200000000000000000),(11351624961498016857/1000000000000000000),(21806684937427826307/62500000000000000),(1046059896064702393/500000000000000000)⟩,(124312818874368129/125000000000000000),(385340319096607301/1000000000000000000),(49437225375448189/200000000000000000),(138459546944159891/1000000000000000000)⟩
theorem valid507 : certificate507.Valid := by decide +kernel
theorem sound507 : certificate507.Sound := rat_cut_bin_certificate_sound certificate507 profilesValid507 numericValid507 valid507

def retention508 : RatCutRetentionCertificate := ⟨(1/25),(81/2000),(467482433270744615/15326824027035334948),(57220961/62500000),(57/20),(4262434747826515103/2000000000000000000),true,MergedCutProfiles.Batch084.profile3389,![MergedCutProfiles.Batch084.profile3389,MergedCutProfiles.Batch084.profile3390,MergedCutProfiles.Batch084.profile3391,MergedCutProfiles.Batch084.profile3392,MergedCutProfiles.Batch084.profile3393,MergedCutProfiles.Batch084.profile3394,MergedCutProfiles.Batch084.profile3395,MergedCutProfiles.Batch084.profile3396,MergedCutProfiles.Batch084.profile3397,MergedCutProfiles.Batch084.profile3398,MergedCutProfiles.Batch084.profile3399,MergedCutProfiles.Batch085.profile3400,MergedCutProfiles.Batch085.profile3401,MergedCutProfiles.Batch085.profile3402,MergedCutProfiles.Batch085.profile3403,MergedCutProfiles.Batch085.profile3404]⟩
theorem profilesValid508 : retention508.ProfilesValid := by
  change ∀ j : Fin 16, (retention508.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch084.valid3389
  · exact MergedCutProfiles.Batch084.valid3390
  · exact MergedCutProfiles.Batch084.valid3391
  · exact MergedCutProfiles.Batch084.valid3392
  · exact MergedCutProfiles.Batch084.valid3393
  · exact MergedCutProfiles.Batch084.valid3394
  · exact MergedCutProfiles.Batch084.valid3395
  · exact MergedCutProfiles.Batch084.valid3396
  · exact MergedCutProfiles.Batch084.valid3397
  · exact MergedCutProfiles.Batch084.valid3398
  · exact MergedCutProfiles.Batch084.valid3399
  · exact MergedCutProfiles.Batch085.valid3400
  · exact MergedCutProfiles.Batch085.valid3401
  · exact MergedCutProfiles.Batch085.valid3402
  · exact MergedCutProfiles.Batch085.valid3403
  · exact MergedCutProfiles.Batch085.valid3404
theorem numericValid508 : retention508.NumericValid := by decide +kernel
def certificate508 : RatCutBinCertificate := ⟨⟨retention508,(206814955857401211/100000000000000000),(14993777272926573/200000000000000000),(11351624961498016857/1000000000000000000),(21806684937427826307/62500000000000000),(418457453540207479/200000000000000000)⟩,(124312818874368129/125000000000000000),(380627707658197379/1000000000000000000),(125854415024237343/500000000000000000),(71643841653829201/500000000000000000)⟩
theorem valid508 : certificate508.Valid := by decide +kernel
theorem sound508 : certificate508.Sound := rat_cut_bin_certificate_sound certificate508 profilesValid508 numericValid508 valid508

def retention509 : RatCutRetentionCertificate := ⟨(1/25),(81/2000),(570417408927602613/15326824027035334948),(93496486654148923/100000000000000000),(14/5),(269489203716991185887/128000000000000000000),true,MergedCutProfiles.Batch085.profile3405,![MergedCutProfiles.Batch085.profile3405,MergedCutProfiles.Batch085.profile3406,MergedCutProfiles.Batch085.profile3407,MergedCutProfiles.Batch084.profile3378,MergedCutProfiles.Batch085.profile3408,MergedCutProfiles.Batch085.profile3409,MergedCutProfiles.Batch083.profile3352,MergedCutProfiles.Batch084.profile3383,MergedCutProfiles.Batch084.profile3399,MergedCutProfiles.Batch085.profile3410,MergedCutProfiles.Batch085.profile3411,MergedCutProfiles.Batch084.profile3387,MergedCutProfiles.Batch085.profile3412,MergedCutProfiles.Batch085.profile3413,MergedCutProfiles.Batch085.profile3414,MergedCutProfiles.Batch085.profile3415]⟩
theorem profilesValid509 : retention509.ProfilesValid := by
  change ∀ j : Fin 16, (retention509.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch085.valid3405
  · exact MergedCutProfiles.Batch085.valid3406
  · exact MergedCutProfiles.Batch085.valid3407
  · exact MergedCutProfiles.Batch084.valid3378
  · exact MergedCutProfiles.Batch085.valid3408
  · exact MergedCutProfiles.Batch085.valid3409
  · exact MergedCutProfiles.Batch083.valid3352
  · exact MergedCutProfiles.Batch084.valid3383
  · exact MergedCutProfiles.Batch084.valid3399
  · exact MergedCutProfiles.Batch085.valid3410
  · exact MergedCutProfiles.Batch085.valid3411
  · exact MergedCutProfiles.Batch084.valid3387
  · exact MergedCutProfiles.Batch085.valid3412
  · exact MergedCutProfiles.Batch085.valid3413
  · exact MergedCutProfiles.Batch085.valid3414
  · exact MergedCutProfiles.Batch085.valid3415
theorem numericValid509 : retention509.NumericValid := by decide +kernel
def certificate509 : RatCutBinCertificate := ⟨⟨retention509,(206814955857401211/100000000000000000),(14993777272926573/200000000000000000),(11351624961498016857/1000000000000000000),(21806684937427826307/62500000000000000),(2067137292523021337/1000000000000000000)⟩,(124312818874368129/125000000000000000),(381882614547201837/1000000000000000000),(250498827016216851/1000000000000000000),(4479013675169303/31250000000000000)⟩
theorem valid509 : certificate509.Valid := by decide +kernel
theorem sound509 : certificate509.Sound := rat_cut_bin_certificate_sound certificate509 profilesValid509 numericValid509 valid509

def retention510 : RatCutRetentionCertificate := ⟨(1/25),(81/2000),(3211039445433240635/30653648054070669896),(570417408927602613/500000000000000000),(47/20),(1202788222117959299469/640000000000000000000),true,MergedCutProfiles.Batch083.profile3346,![MergedCutProfiles.Batch083.profile3346,MergedCutProfiles.Batch084.profile3380,MergedCutProfiles.Batch085.profile3416,MergedCutProfiles.Batch084.profile3386,MergedCutProfiles.Batch085.profile3417,MergedCutProfiles.Batch085.profile3418,MergedCutProfiles.Batch085.profile3419,MergedCutProfiles.Batch085.profile3420,MergedCutProfiles.Batch085.profile3421,MergedCutProfiles.Batch085.profile3422,MergedCutProfiles.Batch085.profile3423,MergedCutProfiles.Batch085.profile3424,MergedCutProfiles.Batch085.profile3425,MergedCutProfiles.Batch085.profile3426,MergedCutProfiles.Batch085.profile3427,MergedCutProfiles.Batch085.profile3428]⟩
theorem profilesValid510 : retention510.ProfilesValid := by
  change ∀ j : Fin 16, (retention510.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch083.valid3346
  · exact MergedCutProfiles.Batch084.valid3380
  · exact MergedCutProfiles.Batch085.valid3416
  · exact MergedCutProfiles.Batch084.valid3386
  · exact MergedCutProfiles.Batch085.valid3417
  · exact MergedCutProfiles.Batch085.valid3418
  · exact MergedCutProfiles.Batch085.valid3419
  · exact MergedCutProfiles.Batch085.valid3420
  · exact MergedCutProfiles.Batch085.valid3421
  · exact MergedCutProfiles.Batch085.valid3422
  · exact MergedCutProfiles.Batch085.valid3423
  · exact MergedCutProfiles.Batch085.valid3424
  · exact MergedCutProfiles.Batch085.valid3425
  · exact MergedCutProfiles.Batch085.valid3426
  · exact MergedCutProfiles.Batch085.valid3427
  · exact MergedCutProfiles.Batch085.valid3428
theorem numericValid510 : retention510.NumericValid := by decide +kernel
def certificate510 : RatCutBinCertificate := ⟨⟨retention510,(206814955857401211/100000000000000000),(14993777272926573/200000000000000000),(11351624961498016857/1000000000000000000),(21806684937427826307/62500000000000000),(369451280943514167/200000000000000000)⟩,(124312818874368129/125000000000000000),(98803581891870787/250000000000000000),(59473991155689421/250000000000000000),(35920121063622667/250000000000000000)⟩
theorem valid510 : certificate510.Valid := by decide +kernel
theorem sound510 : certificate510.Sound := rat_cut_bin_certificate_sound certificate510 profilesValid510 numericValid510 valid510

def retention511 : RatCutRetentionCertificate := ⟨(1/25),(81/2000),(2897629585498137325/7663412013517667474),(642207889086648127/200000000000000000),(13/10),(63887657154608572950303127644218254311/51376631126931850160000000000000000000),false,MergedCutProfiles.Batch085.profile3429,(fun _ => MergedCutProfiles.Batch085.profile3429)⟩
theorem profilesValid511 : retention511.ProfilesValid := by
  exact MergedCutProfiles.Batch085.valid3429
theorem numericValid511 : retention511.NumericValid := by decide +kernel
def certificate511 : RatCutBinCertificate := ⟨⟨retention511,(206814955857401211/100000000000000000),(14993777272926573/200000000000000000),(11351624961498016857/1000000000000000000),(21806684937427826307/62500000000000000),(306439711346919339/250000000000000000)⟩,(124312818874368129/125000000000000000),(226924916769438371/500000000000000000),(187613590380648321/1000000000000000000),(1792801173942033/12500000000000000)⟩
theorem valid511 : certificate511.Valid := by decide +kernel
theorem sound511 : certificate511.Sound := rat_cut_bin_certificate_sound certificate511 profilesValid511 numericValid511 valid511

def retention512 : RatCutRetentionCertificate := ⟨(1/25),(81/2000),(15012692076211397237/30653648054070669896),(115905183419925493/10000000000000000),(21/20),(1887564193334858312425924006350855791/1854482934718807888000000000000000000),false,MergedCutProfiles.Batch085.profile3430,(fun _ => MergedCutProfiles.Batch085.profile3430)⟩
theorem profilesValid512 : retention512.ProfilesValid := by
  exact MergedCutProfiles.Batch085.valid3430
theorem numericValid512 : retention512.NumericValid := by decide +kernel
def certificate512 : RatCutBinCertificate := ⟨⟨retention512,(206814955857401211/100000000000000000),(14993777272926573/200000000000000000),(11351624961498016857/1000000000000000000),(21806684937427826307/62500000000000000),(100349679200739997/100000000000000000)⟩,(124312818874368129/125000000000000000),(30336859745031097/62500000000000000),(40942235940874241/250000000000000000),(144287774269893079/1000000000000000000)⟩
theorem valid512 : certificate512.Valid := by decide +kernel
theorem sound512 : certificate512.Sound := rat_cut_bin_certificate_sound certificate512 profilesValid512 numericValid512 valid512

def retention513 : RatCutRetentionCertificate := ⟨(1/25),(81/2000),(7581409498486755605/15326824027035334948),(15012692076211397237/1000000000000000000),(21/20),(24286833503818535607793942113190135337271/24020307321938235579200000000000000000000),false,MergedCutProfiles.Batch085.profile3431,(fun _ => MergedCutProfiles.Batch085.profile3431)⟩
theorem profilesValid513 : retention513.ProfilesValid := by
  exact MergedCutProfiles.Batch085.valid3431
theorem numericValid513 : retention513.NumericValid := by decide +kernel
def certificate513 : RatCutBinCertificate := ⟨⟨retention513,(206814955857401211/100000000000000000),(14993777272926573/200000000000000000),(11351624961498016857/1000000000000000000),(21806684937427826307/62500000000000000),(498377091864629883/500000000000000000)⟩,(124312818874368129/125000000000000000),(241303362488080351/500000000000000000),(82894256123639271/500000000000000000),(147598542587477269/1000000000000000000)⟩
theorem valid513 : certificate513.Valid := by decide +kernel
theorem sound513 : certificate513.Sound := rat_cut_bin_certificate_sound certificate513 profilesValid513 numericValid513 valid513

def retention514 : RatCutRetentionCertificate := ⟨(1/25),(81/2000),(15314447186943246323/30653648054070669896),(1516281899697351121/100000000000000000),(21/20),(242929735882741045354901533939974312119/242605103951576179360000000000000000000),false,MergedCutProfiles.Batch085.profile3432,(fun _ => MergedCutProfiles.Batch085.profile3432)⟩
theorem profilesValid514 : retention514.ProfilesValid := by
  exact MergedCutProfiles.Batch085.valid3432
theorem numericValid514 : retention514.NumericValid := by decide +kernel
def certificate514 : RatCutBinCertificate := ⟨⟨retention514,(206814955857401211/100000000000000000),(14993777272926573/200000000000000000),(11351624961498016857/1000000000000000000),(21806684937427826307/62500000000000000),(986996425142560949/1000000000000000000)⟩,(124312818874368129/125000000000000000),(15224140180981489/31250000000000000),(162483655981198943/1000000000000000000),(143399998531963363/1000000000000000000)⟩
theorem valid514 : certificate514.Valid := by decide +kernel
theorem sound514 : certificate514.Sound := rat_cut_bin_certificate_sound certificate514 profilesValid514 numericValid514 valid514

def retention515 : RatCutRetentionCertificate := ⟨(1/25),(81/2000),(1/2),(15314447186943246323/1000000000000000000),(21/20),(24517934875549711371089886461576510620271/24503115499109194116800000000000000000000),false,MergedCutProfiles.Batch085.profile3433,(fun _ => MergedCutProfiles.Batch085.profile3433)⟩
theorem profilesValid515 : retention515.ProfilesValid := by
  exact MergedCutProfiles.Batch085.valid3433
theorem numericValid515 : retention515.NumericValid := by decide +kernel
def certificate515 : RatCutBinCertificate := ⟨⟨retention515,(206814955857401211/100000000000000000),(14993777272926573/200000000000000000),(11351624961498016857/1000000000000000000),(21806684937427826307/62500000000000000),(15410361160058439/15625000000000000)⟩,(124312818874368129/125000000000000000),(487331151573486769/1000000000000000000),(40592394953554521/250000000000000000),(14327806048014777/100000000000000000)⟩
theorem valid515 : certificate515.Valid := by decide +kernel
theorem sound515 : certificate515.Sound := rat_cut_bin_certificate_sound certificate515 profilesValid515 numericValid515 valid515

def certificates : List RatCutBinCertificate := [certificate504,certificate505,certificate506,certificate507,certificate508,certificate509,certificate510,certificate511,certificate512,certificate513,certificate514,certificate515]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound504,List.forall_mem_cons.mpr ⟨sound505,List.forall_mem_cons.mpr ⟨sound506,List.forall_mem_cons.mpr ⟨sound507,List.forall_mem_cons.mpr ⟨sound508,List.forall_mem_cons.mpr ⟨sound509,List.forall_mem_cons.mpr ⟨sound510,List.forall_mem_cons.mpr ⟨sound511,List.forall_mem_cons.mpr ⟨sound512,List.forall_mem_cons.mpr ⟨sound513,List.forall_mem_cons.mpr ⟨sound514,List.forall_mem_cons.mpr ⟨sound515,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch042
