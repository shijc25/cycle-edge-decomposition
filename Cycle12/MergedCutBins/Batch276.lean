import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch508
import Cycle12.MergedCutProfiles.Batch509
import Cycle12.MergedCutProfiles.Batch510

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch276

def retention3312 : RatCutRetentionCertificate := ⟨(11/200),(7/125),(36129594194857420289/73424105109331892356),(26805373943513364641/1000000000000000000),1,(108061096850855020709207738879280367923/107221495774053458564000000000000000000),false,MergedCutProfiles.Batch508.profile20329,(fun _ => MergedCutProfiles.Batch508.profile20329)⟩
theorem profilesValid3312 : retention3312.ProfilesValid := by
  exact MergedCutProfiles.Batch508.valid20329
theorem numericValid3312 : retention3312.NumericValid := by decide +kernel
def certificate3312 : RatCutBinCertificate := ⟨⟨retention3312,(10728847932270571/5000000000000000),(155212952940275013/1000000000000000000),(14510522890331406119/1000000000000000000),(535882737577125299899/500000000000000000),(246219502934031893/250000000000000000)⟩,(998295452455399649/1000000000000000000),(215755575309378239/500000000000000000),(51454912520315853/250000000000000000),(97591252348808137/500000000000000000)⟩
theorem valid3312 : certificate3312.Valid := by decide +kernel
theorem sound3312 : certificate3312.Sound := rat_cut_bin_certificate_sound certificate3312 profilesValid3312 numericValid3312 valid3312

def retention3313 : RatCutRetentionCertificate := ⟨(11/200),(7/125),(9122722534201498623/18356026277332973089),(36129594194857420289/1000000000000000000),1,(28920709444451053056096003283892391927/28903675355885936231200000000000000000),false,MergedCutProfiles.Batch508.profile20330,(fun _ => MergedCutProfiles.Batch508.profile20330)⟩
theorem profilesValid3313 : retention3313.ProfilesValid := by
  exact MergedCutProfiles.Batch508.valid20330
theorem numericValid3313 : retention3313.NumericValid := by decide +kernel
def certificate3313 : RatCutBinCertificate := ⟨⟨retention3313,(10728847932270571/5000000000000000),(155212952940275013/1000000000000000000),(14510522890331406119/1000000000000000000),(535882737577125299899/500000000000000000),(488818427100758613/500000000000000000)⟩,(998295452455399649/1000000000000000000),(21568279764580317/50000000000000000),(102971003000279683/500000000000000000),(4892304802599563/25000000000000000)⟩
theorem valid3313 : certificate3313.Valid := by decide +kernel
theorem sound3313 : certificate3313.Sound := rat_cut_bin_certificate_sound certificate3313 profilesValid3313 numericValid3313 valid3313

def retention3314 : RatCutRetentionCertificate := ⟨(11/200),(7/125),(1/2),(9122722534201498623/250000000000000000),1,(36297700645586110016610154518930257663/36490890136805994492000000000000000000),false,MergedCutProfiles.Batch508.profile20331,(fun _ => MergedCutProfiles.Batch508.profile20331)⟩
theorem profilesValid3314 : retention3314.ProfilesValid := by
  exact MergedCutProfiles.Batch508.valid20331
theorem numericValid3314 : retention3314.NumericValid := by decide +kernel
def certificate3314 : RatCutBinCertificate := ⟨⟨retention3314,(10728847932270571/5000000000000000),(155212952940275013/1000000000000000000),(14510522890331406119/1000000000000000000),(535882737577125299899/500000000000000000),(971753331108799753/1000000000000000000)⟩,(998295452455399649/1000000000000000000),(17355265028869379/40000000000000000),(203833891879441861/1000000000000000000),(19260388906120387/100000000000000000)⟩
theorem valid3314 : certificate3314.Valid := by decide +kernel
theorem sound3314 : certificate3314.Sound := rat_cut_bin_certificate_sound certificate3314 profilesValid3314 numericValid3314 valid3314

def retention3315 : RatCutRetentionCertificate := ⟨(11/200),(7/125),(16881286734727783063/36712052554665946178),(4866691573994780971/500000000000000000),1,(8194810592372043234628152131619404499/7786706518391649553600000000000000000),false,MergedCutProfiles.Batch508.profile20332,(fun _ => MergedCutProfiles.Batch508.profile20332)⟩
theorem profilesValid3315 : retention3315.ProfilesValid := by
  exact MergedCutProfiles.Batch508.valid20332
theorem numericValid3315 : retention3315.NumericValid := by decide +kernel
def certificate3315 : RatCutBinCertificate := ⟨⟨retention3315,(11185268662270571/5000000000000000),(155212952940275013/1000000000000000000),(14510522890331406119/1000000000000000000),(535882737577125299899/500000000000000000),(1028481179929596979/1000000000000000000)⟩,(199644583198987763/200000000000000000),(119323131484800847/1000000000000000000),(624900207990524519/1000000000000000000),(72523258978759013/125000000000000000)⟩
theorem valid3315 : certificate3315.Valid := by decide +kernel
theorem sound3315 : certificate3315.Sound := rat_cut_bin_certificate_sound certificate3315 profilesValid3315 numericValid3315 valid3315

def retention3316 : RatCutRetentionCertificate := ⟨(11/200),(7/125),(36560029080660673005/73424105109331892356),(16881286734727783063/500000000000000000),1,(1053220761900234586915970992997730501/1055080420920486441437500000000000000),false,MergedCutProfiles.Batch508.profile20333,(fun _ => MergedCutProfiles.Batch508.profile20333)⟩
theorem profilesValid3316 : retention3316.ProfilesValid := by
  exact MergedCutProfiles.Batch508.valid20333
theorem numericValid3316 : retention3316.NumericValid := by decide +kernel
def certificate3316 : RatCutBinCertificate := ⟨⟨retention3316,(11185268662270571/5000000000000000),(155212952940275013/1000000000000000000),(14510522890331406119/1000000000000000000),(535882737577125299899/500000000000000000),(974308499999956933/1000000000000000000)⟩,(199644583198987763/200000000000000000),(125957635658918959/1000000000000000000),(152822229042374857/250000000000000000),(72229028615085861/125000000000000000)⟩
theorem valid3316 : certificate3316.Valid := by decide +kernel
theorem sound3316 : certificate3316.Sound := rat_cut_bin_certificate_sound certificate3316 profilesValid3316 numericValid3316 valid3316

def retention3317 : RatCutRetentionCertificate := ⟨(11/200),(7/125),(1/2),(7312005816132134601/200000000000000000),1,(36366948724325448437732713395067538729/36560029080660673005000000000000000000),false,MergedCutProfiles.Batch508.profile20331,(fun _ => MergedCutProfiles.Batch508.profile20331)⟩
theorem profilesValid3317 : retention3317.ProfilesValid := by
  exact MergedCutProfiles.Batch508.valid20331
theorem numericValid3317 : retention3317.NumericValid := by decide +kernel
def certificate3317 : RatCutBinCertificate := ⟨⟨retention3317,(11185268662270571/5000000000000000),(155212952940275013/1000000000000000000),(14510522890331406119/1000000000000000000),(535882737577125299899/500000000000000000),(121348737037759727/125000000000000000)⟩,(199644583198987763/200000000000000000),(126414165958929081/1000000000000000000),(305181785496184923/500000000000000000),(288082841653617547/500000000000000000)⟩
theorem valid3317 : certificate3317.Valid := by decide +kernel
theorem sound3317 : certificate3317.Sound := rat_cut_bin_certificate_sound certificate3317 profilesValid3317 numericValid3317 valid3317

def retention3318 : RatCutRetentionCertificate := ⟨(7/125),(113/2000),(847785735573740626/71915481072141101315),(419695908699871597/500000000000000000),(16/5),(90540801885174309493/40000000000000000000),true,MergedCutProfiles.Batch508.profile20334,![MergedCutProfiles.Batch508.profile20334,MergedCutProfiles.Batch508.profile20335,MergedCutProfiles.Batch508.profile20336,MergedCutProfiles.Batch508.profile20337,MergedCutProfiles.Batch508.profile20338,MergedCutProfiles.Batch508.profile20339,MergedCutProfiles.Batch508.profile20340,MergedCutProfiles.Batch508.profile20341,MergedCutProfiles.Batch508.profile20342,MergedCutProfiles.Batch508.profile20343,MergedCutProfiles.Batch508.profile20344,MergedCutProfiles.Batch508.profile20345,MergedCutProfiles.Batch508.profile20346,MergedCutProfiles.Batch508.profile20347,MergedCutProfiles.Batch508.profile20348,MergedCutProfiles.Batch508.profile20349]⟩
theorem profilesValid3318 : retention3318.ProfilesValid := by
  change ∀ j : Fin 16, (retention3318.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch508.valid20334
  · exact MergedCutProfiles.Batch508.valid20335
  · exact MergedCutProfiles.Batch508.valid20336
  · exact MergedCutProfiles.Batch508.valid20337
  · exact MergedCutProfiles.Batch508.valid20338
  · exact MergedCutProfiles.Batch508.valid20339
  · exact MergedCutProfiles.Batch508.valid20340
  · exact MergedCutProfiles.Batch508.valid20341
  · exact MergedCutProfiles.Batch508.valid20342
  · exact MergedCutProfiles.Batch508.valid20343
  · exact MergedCutProfiles.Batch508.valid20344
  · exact MergedCutProfiles.Batch508.valid20345
  · exact MergedCutProfiles.Batch508.valid20346
  · exact MergedCutProfiles.Batch508.valid20347
  · exact MergedCutProfiles.Batch508.valid20348
  · exact MergedCutProfiles.Batch508.valid20349
theorem numericValid3318 : retention3318.NumericValid := by decide +kernel
def certificate3318 : RatCutBinCertificate := ⟨⟨retention3318,(2157109970855523329/1000000000000000000),(39612838789917267/250000000000000000),(7383734865585826093/500000000000000000),(266295555735450815613/250000000000000000),(2189451097852731601/1000000000000000000)⟩,(998288672261469089/1000000000000000000),(367889266294743461/1000000000000000000),(132113906071836577/500000000000000000),(17973856945674571/125000000000000000)⟩
theorem valid3318 : certificate3318.Valid := by decide +kernel
theorem sound3318 : certificate3318.Sound := rat_cut_bin_certificate_sound certificate3318 profilesValid3318 numericValid3318 valid3318

def retention3319 : RatCutRetentionCertificate := ⟨(7/125),(113/2000),(1024217535204989134/71915481072141101315),(423892867786870313/500000000000000000),(16/5),(1443345888019653157709/640000000000000000000),true,MergedCutProfiles.Batch508.profile20350,![MergedCutProfiles.Batch508.profile20350,MergedCutProfiles.Batch508.profile20351,MergedCutProfiles.Batch508.profile20352,MergedCutProfiles.Batch508.profile20353,MergedCutProfiles.Batch508.profile20339,MergedCutProfiles.Batch508.profile20354,MergedCutProfiles.Batch508.profile20355,MergedCutProfiles.Batch508.profile20356,MergedCutProfiles.Batch508.profile20357,MergedCutProfiles.Batch508.profile20358,MergedCutProfiles.Batch508.profile20359,MergedCutProfiles.Batch509.profile20360,MergedCutProfiles.Batch509.profile20361,MergedCutProfiles.Batch509.profile20362,MergedCutProfiles.Batch509.profile20363,MergedCutProfiles.Batch509.profile20364]⟩
theorem profilesValid3319 : retention3319.ProfilesValid := by
  change ∀ j : Fin 16, (retention3319.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch508.valid20350
  · exact MergedCutProfiles.Batch508.valid20351
  · exact MergedCutProfiles.Batch508.valid20352
  · exact MergedCutProfiles.Batch508.valid20353
  · exact MergedCutProfiles.Batch508.valid20339
  · exact MergedCutProfiles.Batch508.valid20354
  · exact MergedCutProfiles.Batch508.valid20355
  · exact MergedCutProfiles.Batch508.valid20356
  · exact MergedCutProfiles.Batch508.valid20357
  · exact MergedCutProfiles.Batch508.valid20358
  · exact MergedCutProfiles.Batch508.valid20359
  · exact MergedCutProfiles.Batch509.valid20360
  · exact MergedCutProfiles.Batch509.valid20361
  · exact MergedCutProfiles.Batch509.valid20362
  · exact MergedCutProfiles.Batch509.valid20363
  · exact MergedCutProfiles.Batch509.valid20364
theorem numericValid3319 : retention3319.NumericValid := by decide +kernel
def certificate3319 : RatCutBinCertificate := ⟨⟨retention3319,(2157109970855523329/1000000000000000000),(39612838789917267/250000000000000000),(7383734865585826093/500000000000000000),(266295555735450815613/250000000000000000),(545289760341373673/250000000000000000)⟩,(998288672261469089/1000000000000000000),(367484081590590451/1000000000000000000),(13231658406086071/50000000000000000),(143865056922141711/1000000000000000000)⟩
theorem valid3319 : certificate3319.Valid := by decide +kernel
theorem sound3319 : certificate3319.Sound := rat_cut_bin_certificate_sound certificate3319 profilesValid3319 numericValid3319 valid3319

def retention3320 : RatCutRetentionCertificate := ⟨(7/125),(113/2000),(220106657800000000/14383096214428220263),(512108767602494567/500000000000000000),(27/10),(89229277019830545903/40000000000000000000),true,MergedCutProfiles.Batch509.profile20365,![MergedCutProfiles.Batch509.profile20365,MergedCutProfiles.Batch509.profile20366,MergedCutProfiles.Batch509.profile20367,MergedCutProfiles.Batch509.profile20368,MergedCutProfiles.Batch509.profile20369,MergedCutProfiles.Batch509.profile20370,MergedCutProfiles.Batch509.profile20371,MergedCutProfiles.Batch509.profile20372,MergedCutProfiles.Batch509.profile20373,MergedCutProfiles.Batch508.profile20346,MergedCutProfiles.Batch509.profile20374,MergedCutProfiles.Batch509.profile20375,MergedCutProfiles.Batch509.profile20362,MergedCutProfiles.Batch509.profile20363,MergedCutProfiles.Batch509.profile20376,MergedCutProfiles.Batch509.profile20377]⟩
theorem profilesValid3320 : retention3320.ProfilesValid := by
  change ∀ j : Fin 16, (retention3320.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch509.valid20365
  · exact MergedCutProfiles.Batch509.valid20366
  · exact MergedCutProfiles.Batch509.valid20367
  · exact MergedCutProfiles.Batch509.valid20368
  · exact MergedCutProfiles.Batch509.valid20369
  · exact MergedCutProfiles.Batch509.valid20370
  · exact MergedCutProfiles.Batch509.valid20371
  · exact MergedCutProfiles.Batch509.valid20372
  · exact MergedCutProfiles.Batch509.valid20373
  · exact MergedCutProfiles.Batch508.valid20346
  · exact MergedCutProfiles.Batch509.valid20374
  · exact MergedCutProfiles.Batch509.valid20375
  · exact MergedCutProfiles.Batch509.valid20362
  · exact MergedCutProfiles.Batch509.valid20363
  · exact MergedCutProfiles.Batch509.valid20376
  · exact MergedCutProfiles.Batch509.valid20377
theorem numericValid3320 : retention3320.NumericValid := by decide +kernel
def certificate3320 : RatCutBinCertificate := ⟨⟨retention3320,(2157109970855523329/1000000000000000000),(39612838789917267/250000000000000000),(7383734865585826093/500000000000000000),(266295555735450815613/250000000000000000),(1084118174414353373/500000000000000000)⟩,(998288672261469089/1000000000000000000),(10575536580816701/31250000000000000),(73726981368468119/250000000000000000),(11447502816821111/62500000000000000)⟩
theorem valid3320 : certificate3320.Valid := by decide +kernel
theorem sound3320 : certificate3320.Sound := rat_cut_bin_certificate_sound certificate3320 profilesValid3320 numericValid3320 valid3320

def retention3321 : RatCutRetentionCertificate := ⟨(7/125),(113/2000),(1394295398829896598/71915481072141101315),(1100533289/1000000000),(51/20),(35321603850214637827/16000000000000000000),true,MergedCutProfiles.Batch509.profile20378,![MergedCutProfiles.Batch509.profile20378,MergedCutProfiles.Batch509.profile20379,MergedCutProfiles.Batch509.profile20380,MergedCutProfiles.Batch509.profile20381,MergedCutProfiles.Batch509.profile20382,MergedCutProfiles.Batch509.profile20383,MergedCutProfiles.Batch509.profile20384,MergedCutProfiles.Batch509.profile20385,MergedCutProfiles.Batch509.profile20386,MergedCutProfiles.Batch509.profile20387,MergedCutProfiles.Batch509.profile20363,MergedCutProfiles.Batch509.profile20388,MergedCutProfiles.Batch509.profile20389,MergedCutProfiles.Batch509.profile20390,MergedCutProfiles.Batch509.profile20391,MergedCutProfiles.Batch509.profile20392]⟩
theorem profilesValid3321 : retention3321.ProfilesValid := by
  change ∀ j : Fin 16, (retention3321.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch509.valid20378
  · exact MergedCutProfiles.Batch509.valid20379
  · exact MergedCutProfiles.Batch509.valid20380
  · exact MergedCutProfiles.Batch509.valid20381
  · exact MergedCutProfiles.Batch509.valid20382
  · exact MergedCutProfiles.Batch509.valid20383
  · exact MergedCutProfiles.Batch509.valid20384
  · exact MergedCutProfiles.Batch509.valid20385
  · exact MergedCutProfiles.Batch509.valid20386
  · exact MergedCutProfiles.Batch509.valid20387
  · exact MergedCutProfiles.Batch509.valid20363
  · exact MergedCutProfiles.Batch509.valid20388
  · exact MergedCutProfiles.Batch509.valid20389
  · exact MergedCutProfiles.Batch509.valid20390
  · exact MergedCutProfiles.Batch509.valid20391
  · exact MergedCutProfiles.Batch509.valid20392
theorem numericValid3321 : retention3321.NumericValid := by decide +kernel
def certificate3321 : RatCutBinCertificate := ⟨⟨retention3321,(2157109970855523329/1000000000000000000),(39612838789917267/250000000000000000),(7383734865585826093/500000000000000000),(266295555735450815613/250000000000000000),(429715337360961087/200000000000000000)⟩,(998288672261469089/1000000000000000000),(331003179226228519/1000000000000000000),(6060415485154019/20000000000000000),(195968548299199621/1000000000000000000)⟩
theorem valid3321 : certificate3321.Valid := by decide +kernel
theorem sound3321 : certificate3321.Sound := rat_cut_bin_certificate_sound certificate3321 profilesValid3321 numericValid3321 valid3321

def retention3322 : RatCutRetentionCertificate := ⟨(7/125),(113/2000),(6783490570522077322/71915481072141101315),(697147699414948299/500000000000000000),(21/10),(1231506111022114510407/640000000000000000000),true,MergedCutProfiles.Batch508.profile20341,![MergedCutProfiles.Batch508.profile20341,MergedCutProfiles.Batch508.profile20349,MergedCutProfiles.Batch509.profile20393,MergedCutProfiles.Batch509.profile20394,MergedCutProfiles.Batch509.profile20395,MergedCutProfiles.Batch509.profile20396,MergedCutProfiles.Batch509.profile20397,MergedCutProfiles.Batch509.profile20398,MergedCutProfiles.Batch509.profile20399,MergedCutProfiles.Batch510.profile20400,MergedCutProfiles.Batch510.profile20401,MergedCutProfiles.Batch510.profile20402,MergedCutProfiles.Batch510.profile20403,MergedCutProfiles.Batch510.profile20404,MergedCutProfiles.Batch510.profile20405,MergedCutProfiles.Batch510.profile20406]⟩
theorem profilesValid3322 : retention3322.ProfilesValid := by
  change ∀ j : Fin 16, (retention3322.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch508.valid20341
  · exact MergedCutProfiles.Batch508.valid20349
  · exact MergedCutProfiles.Batch509.valid20393
  · exact MergedCutProfiles.Batch509.valid20394
  · exact MergedCutProfiles.Batch509.valid20395
  · exact MergedCutProfiles.Batch509.valid20396
  · exact MergedCutProfiles.Batch509.valid20397
  · exact MergedCutProfiles.Batch509.valid20398
  · exact MergedCutProfiles.Batch509.valid20399
  · exact MergedCutProfiles.Batch510.valid20400
  · exact MergedCutProfiles.Batch510.valid20401
  · exact MergedCutProfiles.Batch510.valid20402
  · exact MergedCutProfiles.Batch510.valid20403
  · exact MergedCutProfiles.Batch510.valid20404
  · exact MergedCutProfiles.Batch510.valid20405
  · exact MergedCutProfiles.Batch510.valid20406
theorem numericValid3322 : retention3322.NumericValid := by decide +kernel
def certificate3322 : RatCutBinCertificate := ⟨⟨retention3322,(2157109970855523329/1000000000000000000),(39612838789917267/250000000000000000),(7383734865585826093/500000000000000000),(266295555735450815613/250000000000000000),(937810386476450859/500000000000000000)⟩,(998288672261469089/1000000000000000000),(13805151696665837/40000000000000000),(287703544827094957/1000000000000000000),(39301642228283951/200000000000000000)⟩
theorem valid3322 : certificate3322.Valid := by decide +kernel
theorem sound3322 : certificate3322.Sound := rat_cut_bin_certificate_sound certificate3322 profilesValid3322 numericValid3322 valid3322

def retention3323 : RatCutRetentionCertificate := ⟨(7/125),(113/2000),(31090192738247238247/71915481072141101315),(3391745285261038661/500000000000000000),(21/20),(3025494456288334314743707117785771711239/2713396228208830928800000000000000000000),false,MergedCutProfiles.Batch510.profile20407,(fun _ => MergedCutProfiles.Batch510.profile20407)⟩
theorem profilesValid3323 : retention3323.ProfilesValid := by
  exact MergedCutProfiles.Batch510.valid20407
theorem numericValid3323 : retention3323.NumericValid := by decide +kernel
def certificate3323 : RatCutBinCertificate := ⟨⟨retention3323,(2157109970855523329/1000000000000000000),(39612838789917267/250000000000000000),(7383734865585826093/500000000000000000),(266295555735450815613/250000000000000000),(68169888446989361/62500000000000000)⟩,(998288672261469089/1000000000000000000),(104811338282058997/250000000000000000),(216304352324580961/1000000000000000000),(97866085899784629/500000000000000000)⟩
theorem valid3323 : certificate3323.Valid := by decide +kernel
theorem sound3323 : certificate3323.Sound := rat_cut_bin_certificate_sound certificate3323 profilesValid3323 numericValid3323 valid3323

def certificates : List RatCutBinCertificate := [certificate3312,certificate3313,certificate3314,certificate3315,certificate3316,certificate3317,certificate3318,certificate3319,certificate3320,certificate3321,certificate3322,certificate3323]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3312,List.forall_mem_cons.mpr ⟨sound3313,List.forall_mem_cons.mpr ⟨sound3314,List.forall_mem_cons.mpr ⟨sound3315,List.forall_mem_cons.mpr ⟨sound3316,List.forall_mem_cons.mpr ⟨sound3317,List.forall_mem_cons.mpr ⟨sound3318,List.forall_mem_cons.mpr ⟨sound3319,List.forall_mem_cons.mpr ⟨sound3320,List.forall_mem_cons.mpr ⟨sound3321,List.forall_mem_cons.mpr ⟨sound3322,List.forall_mem_cons.mpr ⟨sound3323,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch276
