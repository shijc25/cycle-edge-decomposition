import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch034
import Cycle12.MergedCutProfiles.Batch035
import Cycle12.MergedCutProfiles.Batch036
import Cycle12.MergedCutProfiles.Batch037

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch018

def retention216 : RatCutRetentionCertificate := ⟨(1/40),(13/500),(438605636777466791/40079938802876286037),(352374104773788123/500000000000000000),(15/4),(287539018446738177847/128000000000000000000),true,MergedCutProfiles.Batch035.profile1406,![MergedCutProfiles.Batch035.profile1406,MergedCutProfiles.Batch035.profile1407,MergedCutProfiles.Batch035.profile1408,MergedCutProfiles.Batch034.profile1394,MergedCutProfiles.Batch035.profile1409,MergedCutProfiles.Batch035.profile1410,MergedCutProfiles.Batch035.profile1411,MergedCutProfiles.Batch034.profile1399,MergedCutProfiles.Batch035.profile1412,MergedCutProfiles.Batch035.profile1413,MergedCutProfiles.Batch035.profile1414,MergedCutProfiles.Batch035.profile1404,MergedCutProfiles.Batch035.profile1415,MergedCutProfiles.Batch035.profile1416,MergedCutProfiles.Batch035.profile1417,MergedCutProfiles.Batch035.profile1418]⟩
theorem profilesValid216 : retention216.ProfilesValid := by
  change ∀ j : Fin 16, (retention216.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch035.valid1406
  · exact MergedCutProfiles.Batch035.valid1407
  · exact MergedCutProfiles.Batch035.valid1408
  · exact MergedCutProfiles.Batch034.valid1394
  · exact MergedCutProfiles.Batch035.valid1409
  · exact MergedCutProfiles.Batch035.valid1410
  · exact MergedCutProfiles.Batch035.valid1411
  · exact MergedCutProfiles.Batch034.valid1399
  · exact MergedCutProfiles.Batch035.valid1412
  · exact MergedCutProfiles.Batch035.valid1413
  · exact MergedCutProfiles.Batch035.valid1414
  · exact MergedCutProfiles.Batch035.valid1404
  · exact MergedCutProfiles.Batch035.valid1415
  · exact MergedCutProfiles.Batch035.valid1416
  · exact MergedCutProfiles.Batch035.valid1417
  · exact MergedCutProfiles.Batch035.valid1418
theorem numericValid216 : retention216.NumericValid := by decide +kernel
def certificate216 : RatCutBinCertificate := ⟨⟨retention216,(24470022261850779/12500000000000000),(14531335098101001/500000000000000000),(1142303834011931957/125000000000000000),(73615407029209521159/100000000000000000),(138940740934134871/62500000000000000)⟩,(997411765385071471/1000000000000000000),(227560243386191431/500000000000000000),(186611575586605451/1000000000000000000),(45042358660333243/500000000000000000)⟩
theorem valid216 : certificate216.Valid := by decide +kernel
theorem sound216 : certificate216.Sound := rat_cut_bin_certificate_sound certificate216 profilesValid216 numericValid216 valid216

def retention217 : RatCutRetentionCertificate := ⟨(1/40),(13/500),(544141925000000000/40079938802876286037),(438605636777466791/500000000000000000),(31/10),(1420282581147567468579/640000000000000000000),true,MergedCutProfiles.Batch035.profile1419,![MergedCutProfiles.Batch035.profile1419,MergedCutProfiles.Batch035.profile1420,MergedCutProfiles.Batch035.profile1421,MergedCutProfiles.Batch035.profile1409,MergedCutProfiles.Batch035.profile1422,MergedCutProfiles.Batch035.profile1423,MergedCutProfiles.Batch035.profile1424,MergedCutProfiles.Batch035.profile1425,MergedCutProfiles.Batch035.profile1426,MergedCutProfiles.Batch035.profile1427,MergedCutProfiles.Batch035.profile1428,MergedCutProfiles.Batch035.profile1429,MergedCutProfiles.Batch035.profile1430,MergedCutProfiles.Batch035.profile1431,MergedCutProfiles.Batch035.profile1432,MergedCutProfiles.Batch035.profile1433]⟩
theorem profilesValid217 : retention217.ProfilesValid := by
  change ∀ j : Fin 16, (retention217.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch035.valid1419
  · exact MergedCutProfiles.Batch035.valid1420
  · exact MergedCutProfiles.Batch035.valid1421
  · exact MergedCutProfiles.Batch035.valid1409
  · exact MergedCutProfiles.Batch035.valid1422
  · exact MergedCutProfiles.Batch035.valid1423
  · exact MergedCutProfiles.Batch035.valid1424
  · exact MergedCutProfiles.Batch035.valid1425
  · exact MergedCutProfiles.Batch035.valid1426
  · exact MergedCutProfiles.Batch035.valid1427
  · exact MergedCutProfiles.Batch035.valid1428
  · exact MergedCutProfiles.Batch035.valid1429
  · exact MergedCutProfiles.Batch035.valid1430
  · exact MergedCutProfiles.Batch035.valid1431
  · exact MergedCutProfiles.Batch035.valid1432
  · exact MergedCutProfiles.Batch035.valid1433
theorem numericValid217 : retention217.NumericValid := by decide +kernel
def certificate217 : RatCutBinCertificate := ⟨⟨retention217,(24470022261850779/12500000000000000),(14531335098101001/500000000000000000),(1142303834011931957/125000000000000000),(73615407029209521159/100000000000000000),(2199891580445748139/1000000000000000000)⟩,(997411765385071471/1000000000000000000),(2052435329075541/5000000000000000),(224009817352141681/1000000000000000000),(62845243344387849/500000000000000000)⟩
theorem valid217 : certificate217.Valid := by decide +kernel
theorem sound217 : certificate217.Sound := rat_cut_bin_certificate_sound certificate217 profilesValid217 numericValid217 valid217

def retention218 : RatCutRetentionCertificate := ⟨(1/40),(13/500),(1267637371885183647/80159877605752572074),(21765677/20000000),(13/5),(7028336787331412241/3200000000000000000),true,MergedCutProfiles.Batch035.profile1434,![MergedCutProfiles.Batch035.profile1434,MergedCutProfiles.Batch035.profile1435,MergedCutProfiles.Batch035.profile1436,MergedCutProfiles.Batch035.profile1437,MergedCutProfiles.Batch035.profile1438,MergedCutProfiles.Batch035.profile1424,MergedCutProfiles.Batch035.profile1439,MergedCutProfiles.Batch036.profile1440,MergedCutProfiles.Batch035.profile1415,MergedCutProfiles.Batch036.profile1441,MergedCutProfiles.Batch036.profile1442,MergedCutProfiles.Batch035.profile1431,MergedCutProfiles.Batch036.profile1443,MergedCutProfiles.Batch036.profile1444,MergedCutProfiles.Batch036.profile1445,MergedCutProfiles.Batch036.profile1446]⟩
theorem profilesValid218 : retention218.ProfilesValid := by
  change ∀ j : Fin 16, (retention218.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch035.valid1434
  · exact MergedCutProfiles.Batch035.valid1435
  · exact MergedCutProfiles.Batch035.valid1436
  · exact MergedCutProfiles.Batch035.valid1437
  · exact MergedCutProfiles.Batch035.valid1438
  · exact MergedCutProfiles.Batch035.valid1424
  · exact MergedCutProfiles.Batch035.valid1439
  · exact MergedCutProfiles.Batch036.valid1440
  · exact MergedCutProfiles.Batch035.valid1415
  · exact MergedCutProfiles.Batch036.valid1441
  · exact MergedCutProfiles.Batch036.valid1442
  · exact MergedCutProfiles.Batch035.valid1431
  · exact MergedCutProfiles.Batch036.valid1443
  · exact MergedCutProfiles.Batch036.valid1444
  · exact MergedCutProfiles.Batch036.valid1445
  · exact MergedCutProfiles.Batch036.valid1446
theorem numericValid218 : retention218.NumericValid := by decide +kernel
def certificate218 : RatCutBinCertificate := ⟨⟨retention218,(24470022261850779/12500000000000000),(14531335098101001/500000000000000000),(1142303834011931957/125000000000000000),(73615407029209521159/100000000000000000),(272521024771851463/125000000000000000)⟩,(997411765385071471/1000000000000000000),(374674479730824009/1000000000000000000),(64376398699836297/250000000000000000),(10379358938478981/62500000000000000)⟩
theorem valid218 : certificate218.Valid := by decide +kernel
theorem sound218 : certificate218.Sound := rat_cut_bin_certificate_sound certificate218 profilesValid218 numericValid218 valid218

def retention219 : RatCutRetentionCertificate := ⟨(1/40),(13/500),(4857138584864465845/80159877605752572074),(1267637371885183647/1000000000000000000),(23/10),(2574528653295797808723/1280000000000000000000),true,MergedCutProfiles.Batch036.profile1447,![MergedCutProfiles.Batch036.profile1447,MergedCutProfiles.Batch035.profile1426,MergedCutProfiles.Batch036.profile1448,MergedCutProfiles.Batch036.profile1449,MergedCutProfiles.Batch036.profile1450,MergedCutProfiles.Batch036.profile1451,MergedCutProfiles.Batch036.profile1452,MergedCutProfiles.Batch036.profile1453,MergedCutProfiles.Batch036.profile1454,MergedCutProfiles.Batch036.profile1455,MergedCutProfiles.Batch036.profile1456,MergedCutProfiles.Batch036.profile1457,MergedCutProfiles.Batch036.profile1458,MergedCutProfiles.Batch036.profile1459,MergedCutProfiles.Batch036.profile1460,MergedCutProfiles.Batch036.profile1461]⟩
theorem profilesValid219 : retention219.ProfilesValid := by
  change ∀ j : Fin 16, (retention219.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch036.valid1447
  · exact MergedCutProfiles.Batch035.valid1426
  · exact MergedCutProfiles.Batch036.valid1448
  · exact MergedCutProfiles.Batch036.valid1449
  · exact MergedCutProfiles.Batch036.valid1450
  · exact MergedCutProfiles.Batch036.valid1451
  · exact MergedCutProfiles.Batch036.valid1452
  · exact MergedCutProfiles.Batch036.valid1453
  · exact MergedCutProfiles.Batch036.valid1454
  · exact MergedCutProfiles.Batch036.valid1455
  · exact MergedCutProfiles.Batch036.valid1456
  · exact MergedCutProfiles.Batch036.valid1457
  · exact MergedCutProfiles.Batch036.valid1458
  · exact MergedCutProfiles.Batch036.valid1459
  · exact MergedCutProfiles.Batch036.valid1460
  · exact MergedCutProfiles.Batch036.valid1461
theorem numericValid219 : retention219.NumericValid := by decide +kernel
def certificate219 : RatCutBinCertificate := ⟨⟨retention219,(24470022261850779/12500000000000000),(14531335098101001/500000000000000000),(1142303834011931957/125000000000000000),(73615407029209521159/100000000000000000),(1997031204708350467/1000000000000000000)⟩,(997411765385071471/1000000000000000000),(76732112621137929/200000000000000000),(124395774926316961/500000000000000000),(20744662930422251/125000000000000000)⟩
theorem valid219 : certificate219.Valid := by decide +kernel
theorem sound219 : certificate219.Sound := rat_cut_bin_certificate_sound certificate219 profilesValid219 numericValid219 valid219

def retention220 : RatCutRetentionCertificate := ⟨(1/40),(13/500),(31223198666239172481/80159877605752572074),(971427716972893169/200000000000000000),(6/5),(23748754062047708298627922963591024679/19428554339457863380000000000000000000),false,MergedCutProfiles.Batch036.profile1462,(fun _ => MergedCutProfiles.Batch036.profile1462)⟩
theorem profilesValid220 : retention220.ProfilesValid := by
  exact MergedCutProfiles.Batch036.valid1462
theorem numericValid220 : retention220.NumericValid := by decide +kernel
def certificate220 : RatCutBinCertificate := ⟨⟨retention220,(24470022261850779/12500000000000000),(14531335098101001/500000000000000000),(1142303834011931957/125000000000000000),(73615407029209521159/100000000000000000),(1214892525068447457/1000000000000000000)⟩,(997411765385071471/1000000000000000000),(221814492001841233/500000000000000000),(48950953256238499/250000000000000000),(33685027780887837/200000000000000000)⟩
theorem valid220 : certificate220.Valid := by decide +kernel
theorem sound220 : certificate220.Sound := rat_cut_bin_certificate_sound certificate220 profilesValid220 numericValid220 valid220

def retention221 : RatCutRetentionCertificate := ⟨(1/40),(13/500),(39645177184519336303/80159877605752572074),(31223198666239172481/1000000000000000000),1,(10450765405428418245699390648687047487/10407732888746390827000000000000000000),false,MergedCutProfiles.Batch036.profile1463,(fun _ => MergedCutProfiles.Batch036.profile1463)⟩
theorem profilesValid221 : retention221.ProfilesValid := by
  exact MergedCutProfiles.Batch036.valid1463
theorem numericValid221 : retention221.NumericValid := by decide +kernel
def certificate221 : RatCutBinCertificate := ⟨⟨retention221,(24470022261850779/12500000000000000),(14531335098101001/500000000000000000),(1142303834011931957/125000000000000000),(73615407029209521159/100000000000000000),(124738619877517597/125000000000000000)⟩,(997411765385071471/1000000000000000000),(47218842735287869/100000000000000000),(43373006767538481/250000000000000000),(41831455574565051/250000000000000000)⟩
theorem valid221 : certificate221.Valid := by decide +kernel
theorem sound221 : certificate221.Sound := rat_cut_bin_certificate_sound certificate221 profilesValid221 numericValid221 valid221

def retention222 : RatCutRetentionCertificate := ⟨(1/40),(13/500),(40041628956364529667/80159877605752572074),(39645177184519336303/1000000000000000000),1,(39490248253131584589377335409180694333/39645177184519336303000000000000000000),false,MergedCutProfiles.Batch036.profile1464,(fun _ => MergedCutProfiles.Batch036.profile1464)⟩
theorem profilesValid222 : retention222.ProfilesValid := by
  exact MergedCutProfiles.Batch036.valid1464
theorem numericValid222 : retention222.NumericValid := by decide +kernel
def certificate222 : RatCutBinCertificate := ⟨⟨retention222,(24470022261850779/12500000000000000),(14531335098101001/500000000000000000),(1142303834011931957/125000000000000000),(73615407029209521159/100000000000000000),(494933202269447159/500000000000000000)⟩,(997411765385071471/1000000000000000000),(473345991171620361/1000000000000000000),(86312420235144561/500000000000000000),(33255157811876479/200000000000000000)⟩
theorem valid222 : certificate222.Valid := by decide +kernel
theorem sound222 : certificate222.Sound := rat_cut_bin_certificate_sound certificate222 profilesValid222 numericValid222 valid222

def retention223 : RatCutRetentionCertificate := ⟨(1/40),(13/500),(1/2),(40041628956364529667/1000000000000000000),1,(159399244786841503751117041048034548331/160166515825458118668000000000000000000),false,MergedCutProfiles.Batch036.profile1465,(fun _ => MergedCutProfiles.Batch036.profile1465)⟩
theorem profilesValid223 : retention223.ProfilesValid := by
  exact MergedCutProfiles.Batch036.valid1465
theorem numericValid223 : retention223.NumericValid := by decide +kernel
def certificate223 : RatCutBinCertificate := ⟨⟨retention223,(24470022261850779/12500000000000000),(14531335098101001/500000000000000000),(1142303834011931957/125000000000000000),(73615407029209521159/100000000000000000),(988983834638124603/1000000000000000000)⟩,(997411765385071471/1000000000000000000),(473669984394547083/1000000000000000000),(86191314454422511/500000000000000000),(82969043653698077/500000000000000000)⟩
theorem valid223 : certificate223.Valid := by decide +kernel
theorem sound223 : certificate223.Sound := rat_cut_bin_certificate_sound certificate223 profilesValid223 numericValid223 valid223

def retention224 : RatCutRetentionCertificate := ⟨(1/40),(13/500),(33047829495607556011/80159877605752572074),(181454593129484529/50000000000000000),(5/4),(17039933745688931314527561233190660359/14516367450358762320000000000000000000),false,MergedCutProfiles.Batch036.profile1466,(fun _ => MergedCutProfiles.Batch036.profile1466)⟩
theorem profilesValid224 : retention224.ProfilesValid := by
  exact MergedCutProfiles.Batch036.valid1466
theorem numericValid224 : retention224.NumericValid := by decide +kernel
def certificate224 : RatCutBinCertificate := ⟨⟨retention224,(29276663611850779/12500000000000000),(14531335098101001/500000000000000000),(1142303834011931957/125000000000000000),(73615407029209521159/100000000000000000),(116453197448980579/100000000000000000)⟩,(498451657851112927/500000000000000000),(86011460316975333/250000000000000000),(462171397397809/1600000000000000),(222508399171747899/1000000000000000000)⟩
theorem valid224 : certificate224.Valid := by decide +kernel
theorem sound224 : certificate224.Sound := rat_cut_bin_certificate_sound certificate224 profilesValid224 numericValid224 valid224

def retention225 : RatCutRetentionCertificate := ⟨(1/40),(13/500),(19962689303187613907/40079938802876286037),(33047829495607556011/1000000000000000000),1,(824285900692191412670629650303860703/826195737390188900275000000000000000),false,MergedCutProfiles.Batch036.profile1467,(fun _ => MergedCutProfiles.Batch036.profile1467)⟩
theorem profilesValid225 : retention225.ProfilesValid := by
  exact MergedCutProfiles.Batch036.valid1467
theorem numericValid225 : retention225.NumericValid := by decide +kernel
def certificate225 : RatCutBinCertificate := ⟨⟨retention225,(29276663611850779/12500000000000000),(14531335098101001/500000000000000000),(1142303834011931957/125000000000000000),(73615407029209521159/100000000000000000),(990239774039674543/1000000000000000000)⟩,(498451657851112927/500000000000000000),(404601383776231827/1000000000000000000),(114646349108661297/500000000000000000),(219757530403121839/1000000000000000000)⟩
theorem valid225 : certificate225.Valid := by decide +kernel
theorem sound225 : certificate225.Sound := rat_cut_bin_certificate_sound certificate225 profilesValid225 numericValid225 valid225

def retention226 : RatCutRetentionCertificate := ⟨(1/40),(13/500),(1/2),(19962689303187613907/500000000000000000),1,(158933559169374237558693487704894538543/159701514425500911256000000000000000000),false,MergedCutProfiles.Batch036.profile1465,(fun _ => MergedCutProfiles.Batch036.profile1465)⟩
theorem profilesValid226 : retention226.ProfilesValid := by
  exact MergedCutProfiles.Batch036.valid1465
theorem numericValid226 : retention226.NumericValid := by decide +kernel
def certificate226 : RatCutBinCertificate := ⟨⟨retention226,(29276663611850779/12500000000000000),(14531335098101001/500000000000000000),(1142303834011931957/125000000000000000),(73615407029209521159/100000000000000000),(30866958988307789/31250000000000000)⟩,(498451657851112927/500000000000000000),(101406061483919601/250000000000000000),(114184243078110291/500000000000000000),(219434335204234119/1000000000000000000)⟩
theorem valid226 : certificate226.Valid := by decide +kernel
theorem sound226 : certificate226.Sound := rat_cut_bin_certificate_sound certificate226 profilesValid226 numericValid226 valid226

def retention227 : RatCutRetentionCertificate := ⟨(13/500),(27/1000),(352374104545851217/36982266783461289640),(2725666031449963/3906250000000000),(19/5),(11296215475040369141/5000000000000000000),true,MergedCutProfiles.Batch036.profile1468,![MergedCutProfiles.Batch036.profile1468,MergedCutProfiles.Batch036.profile1469,MergedCutProfiles.Batch036.profile1470,MergedCutProfiles.Batch036.profile1471,MergedCutProfiles.Batch036.profile1472,MergedCutProfiles.Batch036.profile1473,MergedCutProfiles.Batch036.profile1474,MergedCutProfiles.Batch036.profile1475,MergedCutProfiles.Batch036.profile1476,MergedCutProfiles.Batch036.profile1477,MergedCutProfiles.Batch036.profile1478,MergedCutProfiles.Batch036.profile1479,MergedCutProfiles.Batch037.profile1480,MergedCutProfiles.Batch037.profile1481,MergedCutProfiles.Batch037.profile1482,MergedCutProfiles.Batch037.profile1483]⟩
theorem profilesValid227 : retention227.ProfilesValid := by
  change ∀ j : Fin 16, (retention227.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch036.valid1468
  · exact MergedCutProfiles.Batch036.valid1469
  · exact MergedCutProfiles.Batch036.valid1470
  · exact MergedCutProfiles.Batch036.valid1471
  · exact MergedCutProfiles.Batch036.valid1472
  · exact MergedCutProfiles.Batch036.valid1473
  · exact MergedCutProfiles.Batch036.valid1474
  · exact MergedCutProfiles.Batch036.valid1475
  · exact MergedCutProfiles.Batch036.valid1476
  · exact MergedCutProfiles.Batch036.valid1477
  · exact MergedCutProfiles.Batch036.valid1478
  · exact MergedCutProfiles.Batch036.valid1479
  · exact MergedCutProfiles.Batch037.valid1480
  · exact MergedCutProfiles.Batch037.valid1481
  · exact MergedCutProfiles.Batch037.valid1482
  · exact MergedCutProfiles.Batch037.valid1483
theorem numericValid227 : retention227.NumericValid := by decide +kernel
def certificate227 : RatCutBinCertificate := ⟨⟨retention227,(492840193330873023/250000000000000000),(31463473579235007/1000000000000000000),(28951570700090931/3125000000000000),(172162408772343592041/250000000000000000),(2233801651489457217/1000000000000000000)⟩,(997220316340344303/1000000000000000000),(90658204541384927/200000000000000000),(47013846084933149/250000000000000000),(18038573101275291/200000000000000000)⟩
theorem valid227 : certificate227.Valid := by decide +kernel
theorem sound227 : certificate227.Sound := rat_cut_bin_certificate_sound certificate227 profilesValid227 numericValid227 valid227

def certificates : List RatCutBinCertificate := [certificate216,certificate217,certificate218,certificate219,certificate220,certificate221,certificate222,certificate223,certificate224,certificate225,certificate226,certificate227]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound216,List.forall_mem_cons.mpr ⟨sound217,List.forall_mem_cons.mpr ⟨sound218,List.forall_mem_cons.mpr ⟨sound219,List.forall_mem_cons.mpr ⟨sound220,List.forall_mem_cons.mpr ⟨sound221,List.forall_mem_cons.mpr ⟨sound222,List.forall_mem_cons.mpr ⟨sound223,List.forall_mem_cons.mpr ⟨sound224,List.forall_mem_cons.mpr ⟨sound225,List.forall_mem_cons.mpr ⟨sound226,List.forall_mem_cons.mpr ⟨sound227,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch018
