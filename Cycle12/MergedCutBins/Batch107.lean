import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch210
import Cycle12.MergedCutProfiles.Batch211
import Cycle12.MergedCutProfiles.Batch212

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch107

def retention1284 : RatCutRetentionCertificate := ⟨(29/500),(233/4000),(1164449760379617458/13390269966443149833),(445054983136799719/500000000000000000),(53/20),(310087418360109577129/160000000000000000000),true,MergedCutProfiles.Batch210.profile8421,![MergedCutProfiles.Batch210.profile8421,MergedCutProfiles.Batch210.profile8422,MergedCutProfiles.Batch210.profile8423,MergedCutProfiles.Batch210.profile8424,MergedCutProfiles.Batch210.profile8425,MergedCutProfiles.Batch210.profile8426,MergedCutProfiles.Batch210.profile8427,MergedCutProfiles.Batch210.profile8428,MergedCutProfiles.Batch210.profile8429,MergedCutProfiles.Batch210.profile8430,MergedCutProfiles.Batch210.profile8431,MergedCutProfiles.Batch210.profile8432,MergedCutProfiles.Batch210.profile8433,MergedCutProfiles.Batch210.profile8434,MergedCutProfiles.Batch210.profile8435,MergedCutProfiles.Batch210.profile8436]⟩
theorem profilesValid1284 : retention1284.ProfilesValid := by
  change ∀ j : Fin 16, (retention1284.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch210.valid8421
  · exact MergedCutProfiles.Batch210.valid8422
  · exact MergedCutProfiles.Batch210.valid8423
  · exact MergedCutProfiles.Batch210.valid8424
  · exact MergedCutProfiles.Batch210.valid8425
  · exact MergedCutProfiles.Batch210.valid8426
  · exact MergedCutProfiles.Batch210.valid8427
  · exact MergedCutProfiles.Batch210.valid8428
  · exact MergedCutProfiles.Batch210.valid8429
  · exact MergedCutProfiles.Batch210.valid8430
  · exact MergedCutProfiles.Batch210.valid8431
  · exact MergedCutProfiles.Batch210.valid8432
  · exact MergedCutProfiles.Batch210.valid8433
  · exact MergedCutProfiles.Batch210.valid8434
  · exact MergedCutProfiles.Batch210.valid8435
  · exact MergedCutProfiles.Batch210.valid8436
theorem numericValid1284 : retention1284.NumericValid := by decide +kernel
def certificate1284 : RatCutBinCertificate := ⟨⟨retention1284,(2290464292249505967/1000000000000000000),(17014879615267021/100000000000000000),(15297248449517538051/1000000000000000000),(12821490825172820533/62500000000000000),(233813750740169591/125000000000000000)⟩,(990697354959467891/1000000000000000000),(35979648268124581/100000000000000000),(68102284156679059/250000000000000000),(146343101864057787/1000000000000000000)⟩
theorem valid1284 : certificate1284.Valid := by decide +kernel
theorem sound1284 : certificate1284.Sound := rat_cut_bin_certificate_sound certificate1284 profilesValid1284 numericValid1284 valid1284

def retention1285 : RatCutRetentionCertificate := ⟨(29/500),(233/4000),(2505339219792763469/13390269966443149833),(582224880189808729/500000000000000000),(21/10),(1064798592776920927797/640000000000000000000),true,MergedCutProfiles.Batch210.profile8437,![MergedCutProfiles.Batch210.profile8437,MergedCutProfiles.Batch210.profile8438,MergedCutProfiles.Batch210.profile8439,MergedCutProfiles.Batch211.profile8440,MergedCutProfiles.Batch211.profile8441,MergedCutProfiles.Batch211.profile8442,MergedCutProfiles.Batch211.profile8443,MergedCutProfiles.Batch211.profile8444,MergedCutProfiles.Batch211.profile8445,MergedCutProfiles.Batch211.profile8446,MergedCutProfiles.Batch211.profile8447,MergedCutProfiles.Batch211.profile8448,MergedCutProfiles.Batch211.profile8449,MergedCutProfiles.Batch211.profile8450,MergedCutProfiles.Batch211.profile8451,MergedCutProfiles.Batch211.profile8452]⟩
theorem profilesValid1285 : retention1285.ProfilesValid := by
  change ∀ j : Fin 16, (retention1285.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch210.valid8437
  · exact MergedCutProfiles.Batch210.valid8438
  · exact MergedCutProfiles.Batch210.valid8439
  · exact MergedCutProfiles.Batch211.valid8440
  · exact MergedCutProfiles.Batch211.valid8441
  · exact MergedCutProfiles.Batch211.valid8442
  · exact MergedCutProfiles.Batch211.valid8443
  · exact MergedCutProfiles.Batch211.valid8444
  · exact MergedCutProfiles.Batch211.valid8445
  · exact MergedCutProfiles.Batch211.valid8446
  · exact MergedCutProfiles.Batch211.valid8447
  · exact MergedCutProfiles.Batch211.valid8448
  · exact MergedCutProfiles.Batch211.valid8449
  · exact MergedCutProfiles.Batch211.valid8450
  · exact MergedCutProfiles.Batch211.valid8451
  · exact MergedCutProfiles.Batch211.valid8452
theorem numericValid1285 : retention1285.NumericValid := by decide +kernel
def certificate1285 : RatCutBinCertificate := ⟨⟨retention1285,(2290464292249505967/1000000000000000000),(17014879615267021/100000000000000000),(15297248449517538051/1000000000000000000),(12821490825172820533/62500000000000000),(805114544188576887/500000000000000000)⟩,(990697354959467891/1000000000000000000),(378653929305575103/1000000000000000000),(253620351672361887/1000000000000000000),(73204036359982621/500000000000000000)⟩
theorem valid1285 : certificate1285.Valid := by decide +kernel
theorem sound1285 : certificate1285.Sound := rat_cut_bin_certificate_sound certificate1285 profilesValid1285 numericValid1285 valid1285

def retention1286 : RatCutRetentionCertificate := ⟨(29/500),(233/4000),(1743921541700963765/4463423322147716611),(2505339219792763469/1000000000000000000),(5/4),(61234715400605780381/51200000000000000000),true,MergedCutProfiles.Batch211.profile8453,![MergedCutProfiles.Batch211.profile8453,MergedCutProfiles.Batch210.profile8429,MergedCutProfiles.Batch211.profile8454,MergedCutProfiles.Batch211.profile8455,MergedCutProfiles.Batch211.profile8456,MergedCutProfiles.Batch211.profile8457,MergedCutProfiles.Batch211.profile8458,MergedCutProfiles.Batch211.profile8459,MergedCutProfiles.Batch211.profile8460,MergedCutProfiles.Batch211.profile8461,MergedCutProfiles.Batch211.profile8462,MergedCutProfiles.Batch211.profile8463,MergedCutProfiles.Batch211.profile8464,MergedCutProfiles.Batch211.profile8465,MergedCutProfiles.Batch211.profile8466,MergedCutProfiles.Batch211.profile8467]⟩
theorem profilesValid1286 : retention1286.ProfilesValid := by
  change ∀ j : Fin 16, (retention1286.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch211.valid8453
  · exact MergedCutProfiles.Batch210.valid8429
  · exact MergedCutProfiles.Batch211.valid8454
  · exact MergedCutProfiles.Batch211.valid8455
  · exact MergedCutProfiles.Batch211.valid8456
  · exact MergedCutProfiles.Batch211.valid8457
  · exact MergedCutProfiles.Batch211.valid8458
  · exact MergedCutProfiles.Batch211.valid8459
  · exact MergedCutProfiles.Batch211.valid8460
  · exact MergedCutProfiles.Batch211.valid8461
  · exact MergedCutProfiles.Batch211.valid8462
  · exact MergedCutProfiles.Batch211.valid8463
  · exact MergedCutProfiles.Batch211.valid8464
  · exact MergedCutProfiles.Batch211.valid8465
  · exact MergedCutProfiles.Batch211.valid8466
  · exact MergedCutProfiles.Batch211.valid8467
theorem numericValid1286 : retention1286.NumericValid := by decide +kernel
def certificate1286 : RatCutBinCertificate := ⟨⟨retention1286,(2290464292249505967/1000000000000000000),(17014879615267021/100000000000000000),(15297248449517538051/1000000000000000000),(12821490825172820533/62500000000000000),(1164136525682801477/1000000000000000000)⟩,(990697354959467891/1000000000000000000),(85870750937925249/200000000000000000),(103819112757288623/500000000000000000),(73727510872862397/500000000000000000)⟩
theorem valid1286 : certificate1286.Valid := by decide +kernel
theorem sound1286 : certificate1286.Sound := rat_cut_bin_certificate_sound certificate1286 profilesValid1286 numericValid1286 valid1286

def retention1287 : RatCutRetentionCertificate := ⟨(29/500),(233/4000),(2127915695634218873/4463423322147716611),(1046352925020578259/200000000000000000),1,(51306159345439625139/51200000000000000000),true,MergedCutProfiles.Batch211.profile8468,![MergedCutProfiles.Batch211.profile8468,MergedCutProfiles.Batch211.profile8469,MergedCutProfiles.Batch211.profile8470,MergedCutProfiles.Batch211.profile8471,MergedCutProfiles.Batch211.profile8472,MergedCutProfiles.Batch211.profile8473,MergedCutProfiles.Batch211.profile8474,MergedCutProfiles.Batch211.profile8475,MergedCutProfiles.Batch211.profile8476,MergedCutProfiles.Batch211.profile8477,MergedCutProfiles.Batch211.profile8478,MergedCutProfiles.Batch211.profile8479,MergedCutProfiles.Batch212.profile8480,MergedCutProfiles.Batch212.profile8481,MergedCutProfiles.Batch212.profile8482,MergedCutProfiles.Batch212.profile8483]⟩
theorem profilesValid1287 : retention1287.ProfilesValid := by
  change ∀ j : Fin 16, (retention1287.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch211.valid8468
  · exact MergedCutProfiles.Batch211.valid8469
  · exact MergedCutProfiles.Batch211.valid8470
  · exact MergedCutProfiles.Batch211.valid8471
  · exact MergedCutProfiles.Batch211.valid8472
  · exact MergedCutProfiles.Batch211.valid8473
  · exact MergedCutProfiles.Batch211.valid8474
  · exact MergedCutProfiles.Batch211.valid8475
  · exact MergedCutProfiles.Batch211.valid8476
  · exact MergedCutProfiles.Batch211.valid8477
  · exact MergedCutProfiles.Batch211.valid8478
  · exact MergedCutProfiles.Batch211.valid8479
  · exact MergedCutProfiles.Batch212.valid8480
  · exact MergedCutProfiles.Batch212.valid8481
  · exact MergedCutProfiles.Batch212.valid8482
  · exact MergedCutProfiles.Batch212.valid8483
theorem numericValid1287 : retention1287.NumericValid := by decide +kernel
def certificate1287 : RatCutBinCertificate := ⟨⟨retention1287,(2290464292249505967/1000000000000000000),(17014879615267021/100000000000000000),(15297248449517538051/1000000000000000000),(12821490825172820533/62500000000000000),(24414823139734107/25000000000000000)⟩,(990697354959467891/1000000000000000000),(230440676420325391/500000000000000000),(36422601985487279/200000000000000000),(148342295225444217/1000000000000000000)⟩
theorem valid1287 : certificate1287.Valid := by decide +kernel
theorem sound1287 : certificate1287.Sound := rat_cut_bin_certificate_sound certificate1287 profilesValid1287 numericValid1287 valid1287

def retention1288 : RatCutRetentionCertificate := ⟨(29/500),(233/4000),(6642952817456722960/13390269966443149833),(6383747086902656619/1000000000000000000),(21/20),(10119508099302768749311814114544588194999/10213995339044250590400000000000000000000),false,MergedCutProfiles.Batch212.profile8484,(fun _ => MergedCutProfiles.Batch212.profile8484)⟩
theorem profilesValid1288 : retention1288.ProfilesValid := by
  exact MergedCutProfiles.Batch212.valid8484
theorem numericValid1288 : retention1288.NumericValid := by decide +kernel
def certificate1288 : RatCutBinCertificate := ⟨⟨retention1288,(2290464292249505967/1000000000000000000),(17014879615267021/100000000000000000),(15297248449517538051/1000000000000000000),(12821490825172820533/62500000000000000),(120499455590100607/125000000000000000)⟩,(990697354959467891/1000000000000000000),(229174602950854077/500000000000000000),(36816279936224249/200000000000000000),(147150147545886717/1000000000000000000)⟩
theorem valid1288 : certificate1288.Valid := by decide +kernel
theorem sound1288 : certificate1288.Sound := rat_cut_bin_certificate_sound certificate1288 profilesValid1288 numericValid1288 valid1288

def retention1289 : RatCutRetentionCertificate := ⟨(29/500),(233/4000),(1/2),(83036910218209037/12500000000000000),(21/20),(26166043428068768286702013697323955759/26571811269826891840000000000000000000),false,MergedCutProfiles.Batch212.profile8485,(fun _ => MergedCutProfiles.Batch212.profile8485)⟩
theorem profilesValid1289 : retention1289.ProfilesValid := by
  exact MergedCutProfiles.Batch212.valid8485
theorem numericValid1289 : retention1289.NumericValid := by decide +kernel
def certificate1289 : RatCutBinCertificate := ⟨⟨retention1289,(2290464292249505967/1000000000000000000),(17014879615267021/100000000000000000),(15297248449517538051/1000000000000000000),(12821490825172820533/62500000000000000),(95797592303972871/100000000000000000)⟩,(990697354959467891/1000000000000000000),(28731490996143473/62500000000000000),(9151330697557501/50000000000000000),(146189926247871279/1000000000000000000)⟩
theorem valid1289 : certificate1289.Valid := by decide +kernel
theorem sound1289 : certificate1289.Sound := rat_cut_bin_certificate_sound certificate1289 profilesValid1289 numericValid1289 valid1289

def retention1290 : RatCutRetentionCertificate := ⟨(29/500),(233/4000),(1/2),64,1,(255405226968424874360437455012529674631/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch212.profile8485,(fun _ => MergedCutProfiles.Batch212.profile8485)⟩
theorem profilesValid1290 : retention1290.ProfilesValid := by
  exact MergedCutProfiles.Batch212.valid8485
theorem numericValid1290 : retention1290.NumericValid := by decide +kernel
def certificate1290 : RatCutBinCertificate := ⟨⟨retention1290,(2290464292249505967/1000000000000000000),(17014879615267021/100000000000000000),(15297248449517538051/1000000000000000000),(12821490825172820533/62500000000000000),(38887995097529089/40000000000000000)⟩,(990697354959467891/1000000000000000000),(104949923407835841/250000000000000000),(26977855471490477/125000000000000000),(25592809240738737/125000000000000000)⟩
theorem valid1290 : certificate1290.Valid := by decide +kernel
theorem sound1290 : certificate1290.Sound := rat_cut_bin_certificate_sound certificate1290 profilesValid1290 numericValid1290 valid1290

def retention1291 : RatCutRetentionCertificate := ⟨(29/500),(233/4000),(6220180013845922351/13390269966443149833),(3562919594914194107/1000000000000000000),(6/5),(379060296310305379089679229378084794431/356291959491419410700000000000000000000),false,MergedCutProfiles.Batch212.profile8486,(fun _ => MergedCutProfiles.Batch212.profile8486)⟩
theorem profilesValid1291 : retention1291.ProfilesValid := by
  exact MergedCutProfiles.Batch212.valid8486
theorem numericValid1291 : retention1291.NumericValid := by decide +kernel
def certificate1291 : RatCutBinCertificate := ⟨⟨retention1291,(2623176350249505967/1000000000000000000),(17014879615267021/100000000000000000),(15297248449517538051/1000000000000000000),(12821490825172820533/62500000000000000),(1028884207560985567/1000000000000000000)⟩,(494671570088442229/500000000000000000),(78245672099135123/200000000000000000),(120808108361254297/500000000000000000),(85263934405201063/500000000000000000)⟩
theorem valid1291 : certificate1291.Valid := by decide +kernel
theorem sound1291 : certificate1291.Sound := rat_cut_bin_certificate_sound certificate1291 profilesValid1291 numericValid1291 valid1291

def retention1292 : RatCutRetentionCertificate := ⟨(29/500),(233/4000),(2200948808354351254/4463423322147716611),(6220180013845922351/1000000000000000000),(21/20),(9907227510014777904424069994517471260079/9952288022153475761600000000000000000000),false,MergedCutProfiles.Batch212.profile8487,(fun _ => MergedCutProfiles.Batch212.profile8487)⟩
theorem profilesValid1292 : retention1292.ProfilesValid := by
  exact MergedCutProfiles.Batch212.valid8487
theorem numericValid1292 : retention1292.NumericValid := by decide +kernel
def certificate1292 : RatCutBinCertificate := ⟨⟨retention1292,(2623176350249505967/1000000000000000000),(17014879615267021/100000000000000000),(15297248449517538051/1000000000000000000),(12821490825172820533/62500000000000000),(964832435678200609/1000000000000000000)⟩,(494671570088442229/500000000000000000),(16688024439436723/40000000000000000),(218086790099157441/1000000000000000000),(17367405690407359/100000000000000000)⟩
theorem valid1292 : certificate1292.Valid := by decide +kernel
theorem sound1292 : certificate1292.Sound := rat_cut_bin_certificate_sound certificate1292 profilesValid1292 numericValid1292 valid1292

def retention1293 : RatCutRetentionCertificate := ⟨(29/500),(233/4000),(6668874889313684300/13390269966443149833),(3301423212531526881/500000000000000000),(21/20),(153536271580110848333175632584352140327/155361092354424794400000000000000000000),false,MergedCutProfiles.Batch212.profile8488,(fun _ => MergedCutProfiles.Batch212.profile8488)⟩
theorem profilesValid1293 : retention1293.ProfilesValid := by
  exact MergedCutProfiles.Batch212.valid8488
theorem numericValid1293 : retention1293.NumericValid := by decide +kernel
def certificate1293 : RatCutBinCertificate := ⟨⟨retention1293,(2623176350249505967/1000000000000000000),(17014879615267021/100000000000000000),(15297248449517538051/1000000000000000000),(12821490825172820533/62500000000000000),(478807320248608217/500000000000000000)⟩,(494671570088442229/500000000000000000),(10508629062285803/25000000000000000),(21534975558625691/100000000000000000),(85796910382536673/500000000000000000)⟩
theorem valid1293 : certificate1293.Valid := by decide +kernel
theorem sound1293 : certificate1293.Sound := rat_cut_bin_certificate_sound certificate1293 profilesValid1293 numericValid1293 valid1293

def retention1294 : RatCutRetentionCertificate := ⟨(29/500),(233/4000),(1/2),(66688748893136843/10000000000000000),(21/20),(205247115674410512676946420040684447/208402340291052634375000000000000000),false,MergedCutProfiles.Batch212.profile8485,(fun _ => MergedCutProfiles.Batch212.profile8485)⟩
theorem profilesValid1294 : retention1294.ProfilesValid := by
  exact MergedCutProfiles.Batch212.valid8485
theorem numericValid1294 : retention1294.NumericValid := by decide +kernel
def certificate1294 : RatCutBinCertificate := ⟨⟨retention1294,(2623176350249505967/1000000000000000000),(17014879615267021/100000000000000000),(15297248449517538051/1000000000000000000),(12821490825172820533/62500000000000000),(954220287720786509/1000000000000000000)⟩,(494671570088442229/500000000000000000),(210920207232986609/500000000000000000),(107028270548361891/500000000000000000),(170225217646613883/1000000000000000000)⟩
theorem valid1294 : certificate1294.Valid := by decide +kernel
theorem sound1294 : certificate1294.Sound := rat_cut_bin_certificate_sound certificate1294 profilesValid1294 numericValid1294 valid1294

def retention1295 : RatCutRetentionCertificate := ⟨(233/4000),(117/2000),(931200739807056869/13256000331978180397),(425716960383630721/500000000000000000),(11/4),(254091424117722579453/128000000000000000000),true,MergedCutProfiles.Batch212.profile8489,![MergedCutProfiles.Batch212.profile8489,MergedCutProfiles.Batch212.profile8490,MergedCutProfiles.Batch212.profile8491,MergedCutProfiles.Batch212.profile8492,MergedCutProfiles.Batch212.profile8493,MergedCutProfiles.Batch212.profile8494,MergedCutProfiles.Batch212.profile8495,MergedCutProfiles.Batch212.profile8496,MergedCutProfiles.Batch212.profile8497,MergedCutProfiles.Batch212.profile8498,MergedCutProfiles.Batch212.profile8499,MergedCutProfiles.Batch212.profile8500,MergedCutProfiles.Batch212.profile8501,MergedCutProfiles.Batch212.profile8502,MergedCutProfiles.Batch212.profile8503,MergedCutProfiles.Batch212.profile8504]⟩
theorem profilesValid1295 : retention1295.ProfilesValid := by
  change ∀ j : Fin 16, (retention1295.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch212.valid8489
  · exact MergedCutProfiles.Batch212.valid8490
  · exact MergedCutProfiles.Batch212.valid8491
  · exact MergedCutProfiles.Batch212.valid8492
  · exact MergedCutProfiles.Batch212.valid8493
  · exact MergedCutProfiles.Batch212.valid8494
  · exact MergedCutProfiles.Batch212.valid8495
  · exact MergedCutProfiles.Batch212.valid8496
  · exact MergedCutProfiles.Batch212.valid8497
  · exact MergedCutProfiles.Batch212.valid8498
  · exact MergedCutProfiles.Batch212.valid8499
  · exact MergedCutProfiles.Batch212.valid8500
  · exact MergedCutProfiles.Batch212.valid8501
  · exact MergedCutProfiles.Batch212.valid8502
  · exact MergedCutProfiles.Batch212.valid8503
  · exact MergedCutProfiles.Batch212.valid8504
theorem numericValid1295 : retention1295.NumericValid := by decide +kernel
def certificate1295 : RatCutBinCertificate := ⟨⟨retention1295,(1146738186914770071/500000000000000000),(42966716513336319/250000000000000000),(15366096952548243309/1000000000000000000),(204001344332391525971/1000000000000000000),(239315075519586667/125000000000000000)⟩,(990651851972591847/1000000000000000000),(177860971123607759/500000000000000000),(69149203810317607/250000000000000000),(146763097434154519/1000000000000000000)⟩
theorem valid1295 : certificate1295.Valid := by decide +kernel
theorem sound1295 : certificate1295.Sound := rat_cut_bin_certificate_sound certificate1295 profilesValid1295 numericValid1295 valid1295

def certificates : List RatCutBinCertificate := [certificate1284,certificate1285,certificate1286,certificate1287,certificate1288,certificate1289,certificate1290,certificate1291,certificate1292,certificate1293,certificate1294,certificate1295]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1284,List.forall_mem_cons.mpr ⟨sound1285,List.forall_mem_cons.mpr ⟨sound1286,List.forall_mem_cons.mpr ⟨sound1287,List.forall_mem_cons.mpr ⟨sound1288,List.forall_mem_cons.mpr ⟨sound1289,List.forall_mem_cons.mpr ⟨sound1290,List.forall_mem_cons.mpr ⟨sound1291,List.forall_mem_cons.mpr ⟨sound1292,List.forall_mem_cons.mpr ⟨sound1293,List.forall_mem_cons.mpr ⟨sound1294,List.forall_mem_cons.mpr ⟨sound1295,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch107
