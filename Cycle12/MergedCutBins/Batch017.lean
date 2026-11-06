import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch032
import Cycle12.MergedCutProfiles.Batch033
import Cycle12.MergedCutProfiles.Batch034
import Cycle12.MergedCutProfiles.Batch035

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch017

def retention204 : RatCutRetentionCertificate := ⟨(3/125),(1/40),(368917822691186768/29043069902553804151),(548242777/500000000),(13/5),(35438968081392700409/16000000000000000000),true,MergedCutProfiles.Batch033.profile1330,![MergedCutProfiles.Batch033.profile1330,MergedCutProfiles.Batch033.profile1331,MergedCutProfiles.Batch033.profile1332,MergedCutProfiles.Batch032.profile1319,MergedCutProfiles.Batch032.profile1307,MergedCutProfiles.Batch033.profile1344,MergedCutProfiles.Batch033.profile1345,MergedCutProfiles.Batch033.profile1346,MergedCutProfiles.Batch033.profile1347,MergedCutProfiles.Batch032.profile1315,MergedCutProfiles.Batch033.profile1348,MergedCutProfiles.Batch033.profile1328,MergedCutProfiles.Batch033.profile1349,MergedCutProfiles.Batch033.profile1350,MergedCutProfiles.Batch033.profile1351,MergedCutProfiles.Batch033.profile1352]⟩
theorem profilesValid204 : retention204.ProfilesValid := by
  change ∀ j : Fin 16, (retention204.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch033.valid1330
  · exact MergedCutProfiles.Batch033.valid1331
  · exact MergedCutProfiles.Batch033.valid1332
  · exact MergedCutProfiles.Batch032.valid1319
  · exact MergedCutProfiles.Batch032.valid1307
  · exact MergedCutProfiles.Batch033.valid1344
  · exact MergedCutProfiles.Batch033.valid1345
  · exact MergedCutProfiles.Batch033.valid1346
  · exact MergedCutProfiles.Batch033.valid1347
  · exact MergedCutProfiles.Batch032.valid1315
  · exact MergedCutProfiles.Batch033.valid1348
  · exact MergedCutProfiles.Batch033.valid1328
  · exact MergedCutProfiles.Batch033.valid1349
  · exact MergedCutProfiles.Batch033.valid1350
  · exact MergedCutProfiles.Batch033.valid1351
  · exact MergedCutProfiles.Batch033.valid1352
theorem numericValid204 : retention204.NumericValid := by decide +kernel
def certificate204 : RatCutBinCertificate := ⟨⟨retention204,(24398007666006109/12500000000000000),(5353370290855499/200000000000000000),(4507486493507919757/500000000000000000),(789324760767518664023/1000000000000000000),(2199867501207332137/1000000000000000000)⟩,(498793911335631743/500000000000000000),(46469399716114039/125000000000000000),(65095648876048233/250000000000000000),(169419738801083499/1000000000000000000)⟩
theorem valid204 : certificate204.Valid := by decide +kernel
theorem sound204 : certificate204.Sound := rat_cut_bin_certificate_sound certificate204 profilesValid204 numericValid204 valid204

def retention205 : RatCutRetentionCertificate := ⟨(3/125),(1/40),(1297755481858299184/87129209707661412453),(69172091754597519/62500000000000000),(51/20),(87840929750375916679/40000000000000000000),true,MergedCutProfiles.Batch033.profile1353,![MergedCutProfiles.Batch033.profile1353,MergedCutProfiles.Batch033.profile1354,MergedCutProfiles.Batch033.profile1355,MergedCutProfiles.Batch033.profile1356,MergedCutProfiles.Batch033.profile1357,MergedCutProfiles.Batch033.profile1358,MergedCutProfiles.Batch033.profile1359,MergedCutProfiles.Batch032.profile1314,MergedCutProfiles.Batch034.profile1360,MergedCutProfiles.Batch034.profile1361,MergedCutProfiles.Batch033.profile1340,MergedCutProfiles.Batch034.profile1362,MergedCutProfiles.Batch034.profile1363,MergedCutProfiles.Batch034.profile1364,MergedCutProfiles.Batch034.profile1365,MergedCutProfiles.Batch034.profile1366]⟩
theorem profilesValid205 : retention205.ProfilesValid := by
  change ∀ j : Fin 16, (retention205.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch033.valid1353
  · exact MergedCutProfiles.Batch033.valid1354
  · exact MergedCutProfiles.Batch033.valid1355
  · exact MergedCutProfiles.Batch033.valid1356
  · exact MergedCutProfiles.Batch033.valid1357
  · exact MergedCutProfiles.Batch033.valid1358
  · exact MergedCutProfiles.Batch033.valid1359
  · exact MergedCutProfiles.Batch032.valid1314
  · exact MergedCutProfiles.Batch034.valid1360
  · exact MergedCutProfiles.Batch034.valid1361
  · exact MergedCutProfiles.Batch033.valid1340
  · exact MergedCutProfiles.Batch034.valid1362
  · exact MergedCutProfiles.Batch034.valid1363
  · exact MergedCutProfiles.Batch034.valid1364
  · exact MergedCutProfiles.Batch034.valid1365
  · exact MergedCutProfiles.Batch034.valid1366
theorem numericValid205 : retention205.NumericValid := by decide +kernel
def certificate205 : RatCutBinCertificate := ⟨⟨retention205,(24398007666006109/12500000000000000),(5353370290855499/200000000000000000),(4507486493507919757/500000000000000000),(789324760767518664023/1000000000000000000),(54531125185028029/25000000000000000)⟩,(498793911335631743/500000000000000000),(186694631319883023/500000000000000000),(16173086682061529/62500000000000000),(84697302445165499/500000000000000000)⟩
theorem valid205 : certificate205.Valid := by decide +kernel
theorem sound205 : certificate205.Sound := rat_cut_bin_certificate_sound certificate205 profilesValid205 numericValid205 valid205

def retention206 : RatCutRetentionCertificate := ⟨(3/125),(1/40),(1794849623417936225/29043069902553804151),(81109717616143699/62500000000000000),(9/4),(32080842825613257039/16000000000000000000),true,MergedCutProfiles.Batch034.profile1367,![MergedCutProfiles.Batch034.profile1367,MergedCutProfiles.Batch034.profile1368,MergedCutProfiles.Batch034.profile1369,MergedCutProfiles.Batch034.profile1370,MergedCutProfiles.Batch034.profile1371,MergedCutProfiles.Batch034.profile1372,MergedCutProfiles.Batch034.profile1373,MergedCutProfiles.Batch034.profile1374,MergedCutProfiles.Batch034.profile1375,MergedCutProfiles.Batch034.profile1376,MergedCutProfiles.Batch034.profile1377,MergedCutProfiles.Batch034.profile1378,MergedCutProfiles.Batch034.profile1379,MergedCutProfiles.Batch034.profile1380,MergedCutProfiles.Batch034.profile1381,MergedCutProfiles.Batch034.profile1382]⟩
theorem profilesValid206 : retention206.ProfilesValid := by
  change ∀ j : Fin 16, (retention206.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch034.valid1367
  · exact MergedCutProfiles.Batch034.valid1368
  · exact MergedCutProfiles.Batch034.valid1369
  · exact MergedCutProfiles.Batch034.valid1370
  · exact MergedCutProfiles.Batch034.valid1371
  · exact MergedCutProfiles.Batch034.valid1372
  · exact MergedCutProfiles.Batch034.valid1373
  · exact MergedCutProfiles.Batch034.valid1374
  · exact MergedCutProfiles.Batch034.valid1375
  · exact MergedCutProfiles.Batch034.valid1376
  · exact MergedCutProfiles.Batch034.valid1377
  · exact MergedCutProfiles.Batch034.valid1378
  · exact MergedCutProfiles.Batch034.valid1379
  · exact MergedCutProfiles.Batch034.valid1380
  · exact MergedCutProfiles.Batch034.valid1381
  · exact MergedCutProfiles.Batch034.valid1382
theorem numericValid206 : retention206.NumericValid := by decide +kernel
def certificate206 : RatCutBinCertificate := ⟨⟨retention206,(24398007666006109/12500000000000000),(5353370290855499/200000000000000000),(4507486493507919757/500000000000000000),(789324760767518664023/1000000000000000000),(996006530764310773/500000000000000000)⟩,(498793911335631743/500000000000000000),(76471892809032487/200000000000000000),(250040121584198339/1000000000000000000),(169398463394238713/1000000000000000000)⟩
theorem valid206 : certificate206.Valid := by decide +kernel
theorem sound206 : certificate206.Sound := rat_cut_bin_certificate_sound certificate206 profilesValid206 numericValid206 valid206

def retention207 : RatCutRetentionCertificate := ⟨(3/125),(1/40),(34959691704943740592/87129209707661412453),(215381954810152347/40000000000000000),(23/20),(137192569532223222801745584403310469573/114870375898747918400000000000000000000),false,MergedCutProfiles.Batch034.profile1383,(fun _ => MergedCutProfiles.Batch034.profile1383)⟩
theorem profilesValid207 : retention207.ProfilesValid := by
  exact MergedCutProfiles.Batch034.valid1383
theorem numericValid207 : retention207.NumericValid := by decide +kernel
def certificate207 : RatCutBinCertificate := ⟨⟨retention207,(24398007666006109/12500000000000000),(5353370290855499/200000000000000000),(4507486493507919757/500000000000000000),(789324760767518664023/1000000000000000000),(1187660416978298647/1000000000000000000)⟩,(498793911335631743/500000000000000000),(111459964406671111/250000000000000000),(194012412260804289/1000000000000000000),(171280246023413483/1000000000000000000)⟩
theorem valid207 : certificate207.Valid := by decide +kernel
theorem sound207 : certificate207.Sound := rat_cut_bin_certificate_sound certificate207 profilesValid207 numericValid207 valid207

def retention208 : RatCutRetentionCertificate := ⟨(3/125),(1/40),(43084042294204146338/87129209707661412453),(2184980731558983787/62500000000000000),1,(1405647008750315364031234664546196927/1398387668197749623680000000000000000),false,MergedCutProfiles.Batch034.profile1384,(fun _ => MergedCutProfiles.Batch034.profile1384)⟩
theorem profilesValid208 : retention208.ProfilesValid := by
  exact MergedCutProfiles.Batch034.valid1384
theorem numericValid208 : retention208.NumericValid := by decide +kernel
def certificate208 : RatCutBinCertificate := ⟨⟨retention208,(24398007666006109/12500000000000000),(5353370290855499/200000000000000000),(4507486493507919757/500000000000000000),(789324760767518664023/1000000000000000000),(999395899009630751/1000000000000000000)⟩,(498793911335631743/500000000000000000),(233710893103727777/500000000000000000),(88546461463085731/500000000000000000),(171645764483651293/1000000000000000000)⟩
theorem valid208 : certificate208.Valid := by decide +kernel
theorem sound208 : certificate208.Sound := rat_cut_bin_certificate_sound certificate208 profilesValid208 numericValid208 valid208

def retention209 : RatCutRetentionCertificate := ⟨(3/125),(1/40),(14504960905715395934/29043069902553804151),(21542021147102073169/500000000000000000),1,(1342040519355432883319536114693235769/1346376321693879573062500000000000000),false,MergedCutProfiles.Batch034.profile1385,(fun _ => MergedCutProfiles.Batch034.profile1385)⟩
theorem profilesValid209 : retention209.ProfilesValid := by
  exact MergedCutProfiles.Batch034.valid1385
theorem numericValid209 : retention209.NumericValid := by decide +kernel
def certificate209 : RatCutBinCertificate := ⟨⟨retention209,(24398007666006109/12500000000000000),(5353370290855499/200000000000000000),(4507486493507919757/500000000000000000),(789324760767518664023/1000000000000000000),(990984328748531933/1000000000000000000)⟩,(498793911335631743/500000000000000000),(117307166957384487/250000000000000000),(175722244575568773/1000000000000000000),(84903517832383279/500000000000000000)⟩
theorem valid209 : certificate209.Valid := by decide +kernel
theorem sound209 : certificate209.Sound := rat_cut_bin_certificate_sound certificate209 profilesValid209 numericValid209 valid209

def retention210 : RatCutRetentionCertificate := ⟨(3/125),(1/40),(1/2),(21757441358573093901/500000000000000000),1,(57770792464054277501759872500838056309/58019843622861583736000000000000000000),false,MergedCutProfiles.Batch034.profile1386,(fun _ => MergedCutProfiles.Batch034.profile1386)⟩
theorem profilesValid210 : retention210.ProfilesValid := by
  exact MergedCutProfiles.Batch034.valid1386
theorem numericValid210 : retention210.NumericValid := by decide +kernel
def certificate210 : RatCutBinCertificate := ⟨⟨retention210,(24398007666006109/12500000000000000),(5353370290855499/200000000000000000),(4507486493507919757/500000000000000000),(789324760767518664023/1000000000000000000),(494956080709914911/500000000000000000)⟩,(498793911335631743/500000000000000000),(93928946638816483/200000000000000000),(35081521782444287/200000000000000000),(16936143212119113/100000000000000000)⟩
theorem valid210 : certificate210.Valid := by decide +kernel
theorem sound210 : certificate210.Sound := rat_cut_bin_certificate_sound certificate210 profilesValid210 numericValid210 valid210

def retention211 : RatCutRetentionCertificate := ⟨(3/125),(1/40),(11892889559627106806/29043069902553804151),(3582377073644304293/1000000000000000000),(13/10),(1696271223863676631802346910596904978399/1432950829457721717200000000000000000000),false,MergedCutProfiles.Batch034.profile1387,(fun _ => MergedCutProfiles.Batch034.profile1387)⟩
theorem profilesValid211 : retention211.ProfilesValid := by
  exact MergedCutProfiles.Batch034.valid1387
theorem numericValid211 : retention211.NumericValid := by decide +kernel
def certificate211 : RatCutBinCertificate := ⟨⟨retention211,(29191158628506109/12500000000000000),(5353370290855499/200000000000000000),(4507486493507919757/500000000000000000),(789324760767518664023/1000000000000000000),(117474687693070973/100000000000000000)⟩,(498556949963261027/500000000000000000),(85852799287666799/250000000000000000),(144767369040105919/500000000000000000),(43687425606462469/200000000000000000)⟩
theorem valid211 : certificate211.Valid := by decide +kernel
theorem sound211 : certificate211.Sound := rat_cut_bin_certificate_sound certificate211 profilesValid211 numericValid211 valid211

def retention212 : RatCutRetentionCertificate := ⟨(3/125),(1/40),(14367906323621937656/29043069902553804151),(17839334339440660209/500000000000000000),1,(8963307424853961530445183655214504657/8919667169720330104500000000000000000),false,MergedCutProfiles.Batch034.profile1388,(fun _ => MergedCutProfiles.Batch034.profile1388)⟩
theorem profilesValid212 : retention212.ProfilesValid := by
  exact MergedCutProfiles.Batch034.valid1388
theorem numericValid212 : retention212.NumericValid := by decide +kernel
def certificate212 : RatCutBinCertificate := ⟨⟨retention212,(29191158628506109/12500000000000000),(5353370290855499/200000000000000000),(4507486493507919757/500000000000000000),(789324760767518664023/1000000000000000000),(997958735454370829/1000000000000000000)⟩,(498556949963261027/500000000000000000),(2526540032565229/6250000000000000),(229614044663894163/1000000000000000000),(111129563480238927/500000000000000000)⟩
theorem valid212 : certificate212.Valid := by decide +kernel
theorem sound212 : certificate212.Sound := rat_cut_bin_certificate_sound certificate212 profilesValid212 numericValid212 valid212

def retention213 : RatCutRetentionCertificate := ⟨(3/125),(1/40),(43534756160574471098/87129209707661412453),(5387964871358226621/125000000000000000),1,(1717822396911416150416257134457728663/1724148758834632518720000000000000000),false,MergedCutProfiles.Batch034.profile1389,(fun _ => MergedCutProfiles.Batch034.profile1389)⟩
theorem profilesValid213 : retention213.ProfilesValid := by
  exact MergedCutProfiles.Batch034.valid1389
theorem numericValid213 : retention213.NumericValid := by decide +kernel
def certificate213 : RatCutBinCertificate := ⟨⟨retention213,(29191158628506109/12500000000000000),(5353370290855499/200000000000000000),(4507486493507919757/500000000000000000),(789324760767518664023/1000000000000000000),(49469844093867971/50000000000000000)⟩,(498556949963261027/500000000000000000),(407744595465370151/1000000000000000000),(56615209683087461/250000000000000000),(218393407260954169/1000000000000000000)⟩
theorem valid213 : certificate213.Valid := by decide +kernel
theorem sound213 : certificate213.Sound := rat_cut_bin_certificate_sound certificate213 profilesValid213 numericValid213 valid213

def retention214 : RatCutRetentionCertificate := ⟨(3/125),(1/40),(1/2),(21767378080287235549/500000000000000000),1,(173391987985304096410011078252086221791/174139024642297884392000000000000000000),false,MergedCutProfiles.Batch034.profile1386,(fun _ => MergedCutProfiles.Batch034.profile1386)⟩
theorem profilesValid214 : retention214.ProfilesValid := by
  exact MergedCutProfiles.Batch034.valid1386
theorem numericValid214 : retention214.NumericValid := by decide +kernel
def certificate214 : RatCutBinCertificate := ⟨⟨retention214,(29191158628506109/12500000000000000),(5353370290855499/200000000000000000),(4507486493507919757/500000000000000000),(789324760767518664023/1000000000000000000),(247194065567149543/250000000000000000)⟩,(498556949963261027/500000000000000000),(408000522211357799/1000000000000000000),(226231331784497423/1000000000000000000),(10904338822813731/50000000000000000)⟩
theorem valid214 : certificate214.Valid := by decide +kernel
theorem sound214 : certificate214.Sound := rat_cut_bin_certificate_sound certificate214 profilesValid214 numericValid214 valid214

def retention215 : RatCutRetentionCertificate := ⟨(1/40),(13/500),(352374104773788123/40079938802876286037),(348885252251275369/500000000000000000),(19/5),(1448320769838059861093/640000000000000000000),true,MergedCutProfiles.Batch034.profile1390,![MergedCutProfiles.Batch034.profile1390,MergedCutProfiles.Batch034.profile1391,MergedCutProfiles.Batch034.profile1392,MergedCutProfiles.Batch034.profile1393,MergedCutProfiles.Batch034.profile1394,MergedCutProfiles.Batch034.profile1395,MergedCutProfiles.Batch034.profile1396,MergedCutProfiles.Batch034.profile1397,MergedCutProfiles.Batch034.profile1398,MergedCutProfiles.Batch034.profile1399,MergedCutProfiles.Batch035.profile1400,MergedCutProfiles.Batch035.profile1401,MergedCutProfiles.Batch035.profile1402,MergedCutProfiles.Batch035.profile1403,MergedCutProfiles.Batch035.profile1404,MergedCutProfiles.Batch035.profile1405]⟩
theorem profilesValid215 : retention215.ProfilesValid := by
  change ∀ j : Fin 16, (retention215.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch034.valid1390
  · exact MergedCutProfiles.Batch034.valid1391
  · exact MergedCutProfiles.Batch034.valid1392
  · exact MergedCutProfiles.Batch034.valid1393
  · exact MergedCutProfiles.Batch034.valid1394
  · exact MergedCutProfiles.Batch034.valid1395
  · exact MergedCutProfiles.Batch034.valid1396
  · exact MergedCutProfiles.Batch034.valid1397
  · exact MergedCutProfiles.Batch034.valid1398
  · exact MergedCutProfiles.Batch034.valid1399
  · exact MergedCutProfiles.Batch035.valid1400
  · exact MergedCutProfiles.Batch035.valid1401
  · exact MergedCutProfiles.Batch035.valid1402
  · exact MergedCutProfiles.Batch035.valid1403
  · exact MergedCutProfiles.Batch035.valid1404
  · exact MergedCutProfiles.Batch035.valid1405
theorem numericValid215 : retention215.NumericValid := by decide +kernel
def certificate215 : RatCutBinCertificate := ⟨⟨retention215,(24470022261850779/12500000000000000),(14531335098101001/500000000000000000),(1142303834011931957/125000000000000000),(73615407029209521159/100000000000000000),(2239343187676582981/1000000000000000000)⟩,(997411765385071471/1000000000000000000),(45427910721961003/100000000000000000),(187274675336977969/1000000000000000000),(90020819064381203/1000000000000000000)⟩
theorem valid215 : certificate215.Valid := by decide +kernel
theorem sound215 : certificate215.Sound := rat_cut_bin_certificate_sound certificate215 profilesValid215 numericValid215 valid215

def certificates : List RatCutBinCertificate := [certificate204,certificate205,certificate206,certificate207,certificate208,certificate209,certificate210,certificate211,certificate212,certificate213,certificate214,certificate215]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound204,List.forall_mem_cons.mpr ⟨sound205,List.forall_mem_cons.mpr ⟨sound206,List.forall_mem_cons.mpr ⟨sound207,List.forall_mem_cons.mpr ⟨sound208,List.forall_mem_cons.mpr ⟨sound209,List.forall_mem_cons.mpr ⟨sound210,List.forall_mem_cons.mpr ⟨sound211,List.forall_mem_cons.mpr ⟨sound212,List.forall_mem_cons.mpr ⟨sound213,List.forall_mem_cons.mpr ⟨sound214,List.forall_mem_cons.mpr ⟨sound215,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch017
