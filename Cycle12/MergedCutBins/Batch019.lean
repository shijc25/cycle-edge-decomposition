import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch037
import Cycle12.MergedCutProfiles.Batch038
import Cycle12.MergedCutProfiles.Batch039

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch019

def retention228 : RatCutRetentionCertificate := ⟨(13/500),(27/1000),(173705202571782221/14792906713384515856),(352374104545851217/500000000000000000),(15/4),(287054069711926918301/128000000000000000000),true,MergedCutProfiles.Batch037.profile1484,![MergedCutProfiles.Batch037.profile1484,MergedCutProfiles.Batch037.profile1485,MergedCutProfiles.Batch037.profile1486,MergedCutProfiles.Batch037.profile1487,MergedCutProfiles.Batch037.profile1488,MergedCutProfiles.Batch037.profile1489,MergedCutProfiles.Batch037.profile1490,MergedCutProfiles.Batch037.profile1491,MergedCutProfiles.Batch037.profile1492,MergedCutProfiles.Batch037.profile1493,MergedCutProfiles.Batch037.profile1494,MergedCutProfiles.Batch037.profile1495,MergedCutProfiles.Batch037.profile1496,MergedCutProfiles.Batch037.profile1497,MergedCutProfiles.Batch037.profile1498,MergedCutProfiles.Batch037.profile1499]⟩
theorem profilesValid228 : retention228.ProfilesValid := by
  change ∀ j : Fin 16, (retention228.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch037.valid1484
  · exact MergedCutProfiles.Batch037.valid1485
  · exact MergedCutProfiles.Batch037.valid1486
  · exact MergedCutProfiles.Batch037.valid1487
  · exact MergedCutProfiles.Batch037.valid1488
  · exact MergedCutProfiles.Batch037.valid1489
  · exact MergedCutProfiles.Batch037.valid1490
  · exact MergedCutProfiles.Batch037.valid1491
  · exact MergedCutProfiles.Batch037.valid1492
  · exact MergedCutProfiles.Batch037.valid1493
  · exact MergedCutProfiles.Batch037.valid1494
  · exact MergedCutProfiles.Batch037.valid1495
  · exact MergedCutProfiles.Batch037.valid1496
  · exact MergedCutProfiles.Batch037.valid1497
  · exact MergedCutProfiles.Batch037.valid1498
  · exact MergedCutProfiles.Batch037.valid1499
theorem numericValid228 : retention228.NumericValid := by decide +kernel
def certificate228 : RatCutBinCertificate := ⟨⟨retention228,(492840193330873023/250000000000000000),(31463473579235007/1000000000000000000),(28951570700090931/3125000000000000),(172162408772343592041/250000000000000000),(277187903814229509/125000000000000000)⟩,(997220316340344303/1000000000000000000),(7096073023545649/15625000000000000),(187377610893763103/1000000000000000000),(90249876354548777/1000000000000000000)⟩
theorem valid228 : certificate228.Valid := by decide +kernel
theorem sound228 : certificate228.Sound := rat_cut_bin_certificate_sound certificate228 profilesValid228 numericValid228 valid228

def retention229 : RatCutRetentionCertificate := ⟨(13/500),(27/1000),(13570727300000000/924556669586532241),(173705202571782221/200000000000000000),(31/10),(565838547839737505729/256000000000000000000),true,MergedCutProfiles.Batch037.profile1500,![MergedCutProfiles.Batch037.profile1500,MergedCutProfiles.Batch037.profile1501,MergedCutProfiles.Batch037.profile1502,MergedCutProfiles.Batch037.profile1488,MergedCutProfiles.Batch037.profile1503,MergedCutProfiles.Batch037.profile1504,MergedCutProfiles.Batch037.profile1505,MergedCutProfiles.Batch037.profile1493,MergedCutProfiles.Batch037.profile1481,MergedCutProfiles.Batch037.profile1506,MergedCutProfiles.Batch037.profile1507,MergedCutProfiles.Batch037.profile1498,MergedCutProfiles.Batch037.profile1508,MergedCutProfiles.Batch037.profile1509,MergedCutProfiles.Batch037.profile1510,MergedCutProfiles.Batch037.profile1511]⟩
theorem profilesValid229 : retention229.ProfilesValid := by
  change ∀ j : Fin 16, (retention229.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch037.valid1500
  · exact MergedCutProfiles.Batch037.valid1501
  · exact MergedCutProfiles.Batch037.valid1502
  · exact MergedCutProfiles.Batch037.valid1488
  · exact MergedCutProfiles.Batch037.valid1503
  · exact MergedCutProfiles.Batch037.valid1504
  · exact MergedCutProfiles.Batch037.valid1505
  · exact MergedCutProfiles.Batch037.valid1493
  · exact MergedCutProfiles.Batch037.valid1481
  · exact MergedCutProfiles.Batch037.valid1506
  · exact MergedCutProfiles.Batch037.valid1507
  · exact MergedCutProfiles.Batch037.valid1498
  · exact MergedCutProfiles.Batch037.valid1508
  · exact MergedCutProfiles.Batch037.valid1509
  · exact MergedCutProfiles.Batch037.valid1510
  · exact MergedCutProfiles.Batch037.valid1511
theorem numericValid229 : retention229.NumericValid := by decide +kernel
def certificate229 : RatCutBinCertificate := ⟨⟨retention229,(492840193330873023/250000000000000000),(31463473579235007/1000000000000000000),(28951570700090931/3125000000000000),(172162408772343592041/250000000000000000),(1094775985557031073/500000000000000000)⟩,(997220316340344303/1000000000000000000),(412698652417008137/1000000000000000000),(111023303965784777/500000000000000000),(483753216272383/3906250000000000)⟩
theorem valid229 : certificate229.Valid := by decide +kernel
theorem sound229 : certificate229.Sound := rat_cut_bin_certificate_sound certificate229 profilesValid229 numericValid229 valid229

def retention230 : RatCutRetentionCertificate := ⟨(13/500),(27/1000),(1319108531556304099/73964533566922579280),(135707273/125000000),(13/5),(34980176568674867413/16000000000000000000),true,MergedCutProfiles.Batch037.profile1512,![MergedCutProfiles.Batch037.profile1512,MergedCutProfiles.Batch037.profile1486,MergedCutProfiles.Batch037.profile1513,MergedCutProfiles.Batch037.profile1514,MergedCutProfiles.Batch037.profile1515,MergedCutProfiles.Batch037.profile1516,MergedCutProfiles.Batch037.profile1480,MergedCutProfiles.Batch037.profile1482,MergedCutProfiles.Batch037.profile1507,MergedCutProfiles.Batch037.profile1517,MergedCutProfiles.Batch037.profile1518,MergedCutProfiles.Batch037.profile1519,MergedCutProfiles.Batch038.profile1520,MergedCutProfiles.Batch038.profile1521,MergedCutProfiles.Batch038.profile1522,MergedCutProfiles.Batch038.profile1523]⟩
theorem profilesValid230 : retention230.ProfilesValid := by
  change ∀ j : Fin 16, (retention230.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch037.valid1512
  · exact MergedCutProfiles.Batch037.valid1486
  · exact MergedCutProfiles.Batch037.valid1513
  · exact MergedCutProfiles.Batch037.valid1514
  · exact MergedCutProfiles.Batch037.valid1515
  · exact MergedCutProfiles.Batch037.valid1516
  · exact MergedCutProfiles.Batch037.valid1480
  · exact MergedCutProfiles.Batch037.valid1482
  · exact MergedCutProfiles.Batch037.valid1507
  · exact MergedCutProfiles.Batch037.valid1517
  · exact MergedCutProfiles.Batch037.valid1518
  · exact MergedCutProfiles.Batch037.valid1519
  · exact MergedCutProfiles.Batch038.valid1520
  · exact MergedCutProfiles.Batch038.valid1521
  · exact MergedCutProfiles.Batch038.valid1522
  · exact MergedCutProfiles.Batch038.valid1523
theorem numericValid230 : retention230.NumericValid := by decide +kernel
def certificate230 : RatCutBinCertificate := ⟨⟨retention230,(492840193330873023/250000000000000000),(31463473579235007/1000000000000000000),(28951570700090931/3125000000000000),(172162408772343592041/250000000000000000),(1084426875136006303/500000000000000000)⟩,(997220316340344303/1000000000000000000),(93896769130827267/250000000000000000),(64152721610802861/250000000000000000),(82351185382523791/500000000000000000)⟩
theorem valid230 : certificate230.Valid := by decide +kernel
theorem sound230 : certificate230.Sound := rat_cut_bin_certificate_sound certificate230 profilesValid230 numericValid230 valid230

def retention231 : RatCutRetentionCertificate := ⟨(13/500),(27/1000),(2791577774905828527/36982266783461289640),(1319108531556304099/1000000000000000000),(9/4),(502770310356218912559/256000000000000000000),true,MergedCutProfiles.Batch038.profile1524,![MergedCutProfiles.Batch038.profile1524,MergedCutProfiles.Batch038.profile1525,MergedCutProfiles.Batch038.profile1526,MergedCutProfiles.Batch038.profile1527,MergedCutProfiles.Batch038.profile1528,MergedCutProfiles.Batch038.profile1529,MergedCutProfiles.Batch038.profile1530,MergedCutProfiles.Batch038.profile1531,MergedCutProfiles.Batch038.profile1532,MergedCutProfiles.Batch038.profile1533,MergedCutProfiles.Batch038.profile1534,MergedCutProfiles.Batch038.profile1535,MergedCutProfiles.Batch038.profile1536,MergedCutProfiles.Batch038.profile1537,MergedCutProfiles.Batch038.profile1538,MergedCutProfiles.Batch038.profile1539]⟩
theorem profilesValid231 : retention231.ProfilesValid := by
  change ∀ j : Fin 16, (retention231.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch038.valid1524
  · exact MergedCutProfiles.Batch038.valid1525
  · exact MergedCutProfiles.Batch038.valid1526
  · exact MergedCutProfiles.Batch038.valid1527
  · exact MergedCutProfiles.Batch038.valid1528
  · exact MergedCutProfiles.Batch038.valid1529
  · exact MergedCutProfiles.Batch038.valid1530
  · exact MergedCutProfiles.Batch038.valid1531
  · exact MergedCutProfiles.Batch038.valid1532
  · exact MergedCutProfiles.Batch038.valid1533
  · exact MergedCutProfiles.Batch038.valid1534
  · exact MergedCutProfiles.Batch038.valid1535
  · exact MergedCutProfiles.Batch038.valid1536
  · exact MergedCutProfiles.Batch038.valid1537
  · exact MergedCutProfiles.Batch038.valid1538
  · exact MergedCutProfiles.Batch038.valid1539
theorem numericValid231 : retention231.NumericValid := by decide +kernel
def certificate231 : RatCutBinCertificate := ⟨⟨retention231,(492840193330873023/250000000000000000),(31463473579235007/1000000000000000000),(28951570700090931/3125000000000000),(172162408772343592041/250000000000000000),(974441269947840471/500000000000000000)⟩,(997220316340344303/1000000000000000000),(77128074217882751/200000000000000000),(246900124067254443/1000000000000000000),(82510236847339101/500000000000000000)⟩
theorem valid231 : certificate231.Valid := by decide +kernel
theorem sound231 : certificate231.Sound := rat_cut_bin_certificate_sound certificate231 profilesValid231 numericValid231 valid231

def retention232 : RatCutRetentionCertificate := ⟨(13/500),(27/1000),(1515246449631812315/3698226678346128964),(2791577774905828527/500000000000000000),(11/10),(162837210728448165832356064233201987989/139578888745291426350000000000000000000),false,MergedCutProfiles.Batch038.profile1540,(fun _ => MergedCutProfiles.Batch038.profile1540)⟩
theorem profilesValid232 : retention232.ProfilesValid := by
  exact MergedCutProfiles.Batch038.valid1540
theorem numericValid232 : retention232.NumericValid := by decide +kernel
def certificate232 : RatCutBinCertificate := ⟨⟨retention232,(492840193330873023/250000000000000000),(31463473579235007/1000000000000000000),(28951570700090931/3125000000000000),(172162408772343592041/250000000000000000),(289816883487695581/250000000000000000)⟩,(997220316340344303/1000000000000000000),(455216075968050951/1000000000000000000),(186536339211826587/1000000000000000000),(33458414719308407/200000000000000000)⟩
theorem valid232 : certificate232.Valid := by decide +kernel
theorem sound232 : certificate232.Sound := rat_cut_bin_certificate_sound certificate232 profilesValid232 numericValid232 valid232

def retention233 : RatCutRetentionCertificate := ⟨(13/500),(27/1000),(9152913989639881039/18491133391730644820),(303049289926362463/10000000000000000),1,(1899879985072882812579691763416008301/1894058062039765393750000000000000000),false,MergedCutProfiles.Batch038.profile1541,(fun _ => MergedCutProfiles.Batch038.profile1541)⟩
theorem profilesValid233 : retention233.ProfilesValid := by
  exact MergedCutProfiles.Batch038.valid1541
theorem numericValid233 : retention233.NumericValid := by decide +kernel
def certificate233 : RatCutBinCertificate := ⟨⟨retention233,(492840193330873023/250000000000000000),(31463473579235007/1000000000000000000),(28951570700090931/3125000000000000),(172162408772343592041/250000000000000000),(49818938566060887/50000000000000000)⟩,(997220316340344303/1000000000000000000),(472938336968423167/1000000000000000000),(172929910541820791/1000000000000000000),(41586814970739079/250000000000000000)⟩
theorem valid233 : certificate233.Valid := by decide +kernel
theorem sound233 : certificate233.Sound := rat_cut_bin_certificate_sound certificate233 profilesValid233 numericValid233 valid233

def retention234 : RatCutRetentionCertificate := ⟨(13/500),(27/1000),(18488886259072559699/36982266783461289640),(9152913989639881039/250000000000000000),1,(145677031775689016079223043556871575183/146446623834238096624000000000000000000),false,MergedCutProfiles.Batch038.profile1542,(fun _ => MergedCutProfiles.Batch038.profile1542)⟩
theorem profilesValid234 : retention234.ProfilesValid := by
  exact MergedCutProfiles.Batch038.valid1542
theorem numericValid234 : retention234.NumericValid := by decide +kernel
def certificate234 : RatCutBinCertificate := ⟨⟨retention234,(492840193330873023/250000000000000000),(31463473579235007/1000000000000000000),(28951570700090931/3125000000000000),(172162408772343592041/250000000000000000),(988049887521846999/1000000000000000000)⟩,(997220316340344303/1000000000000000000),(118675187305930527/250000000000000000),(171613520718236947/1000000000000000000),(82320703812410369/500000000000000000)⟩
theorem valid234 : certificate234.Valid := by decide +kernel
theorem sound234 : certificate234.Sound := rat_cut_bin_certificate_sound certificate234 profilesValid234 numericValid234 valid234

def retention235 : RatCutRetentionCertificate := ⟨(13/500),(27/1000),(1/2),(18488886259072559699/500000000000000000),1,(9195379771175936957138686619221805701/9244443129536279849500000000000000000),false,MergedCutProfiles.Batch038.profile1543,(fun _ => MergedCutProfiles.Batch038.profile1543)⟩
theorem profilesValid235 : retention235.ProfilesValid := by
  exact MergedCutProfiles.Batch038.valid1543
theorem numericValid235 : retention235.NumericValid := by decide +kernel
def certificate235 : RatCutBinCertificate := ⟨⟨retention235,(492840193330873023/250000000000000000),(31463473579235007/1000000000000000000),(28951570700090931/3125000000000000),(172162408772343592041/250000000000000000),(987997655181515383/1000000000000000000)⟩,(997220316340344303/1000000000000000000),(237310008677021891/500000000000000000),(42918419548837291/250000000000000000),(82366782362155383/500000000000000000)⟩
theorem valid235 : certificate235.Valid := by decide +kernel
theorem sound235 : certificate235.Sound := rat_cut_bin_certificate_sound certificate235 profilesValid235 numericValid235 valid235

def retention236 : RatCutRetentionCertificate := ⟨(13/500),(27/1000),(30791366681700222901/73964533566922579280),(1830732875332963701/500000000000000000),(5/4),(13664700993188547130732346010422829211/11716690402130967686400000000000000000),false,MergedCutProfiles.Batch038.profile1544,(fun _ => MergedCutProfiles.Batch038.profile1544)⟩
theorem profilesValid236 : retention236.ProfilesValid := by
  exact MergedCutProfiles.Batch038.valid1544
theorem numericValid236 : retention236.NumericValid := by decide +kernel
def certificate236 : RatCutBinCertificate := ⟨⟨retention236,(587520242580873023/250000000000000000),(31463473579235007/1000000000000000000),(28951570700090931/3125000000000000),(172162408772343592041/250000000000000000),(578141438299388347/500000000000000000)⟩,(249171563853657477/250000000000000000),(344102104103615783/1000000000000000000),(288797107507518269/1000000000000000000),(221433011834305439/1000000000000000000)⟩
theorem valid236 : certificate236.Valid := by decide +kernel
theorem sound236 : certificate236.Sound := rat_cut_bin_certificate_sound certificate236 profilesValid236 numericValid236 valid236

def retention237 : RatCutRetentionCertificate := ⟨(13/500),(27/1000),(7366203105851639971/14792906713384515856),(30791366681700222901/1000000000000000000),1,(24568067395219400489233772503622944991/24633093345360178320800000000000000000),false,MergedCutProfiles.Batch038.profile1545,(fun _ => MergedCutProfiles.Batch038.profile1545)⟩
theorem profilesValid237 : retention237.ProfilesValid := by
  exact MergedCutProfiles.Batch038.valid1545
theorem numericValid237 : retention237.NumericValid := by decide +kernel
def certificate237 : RatCutBinCertificate := ⟨⟨retention237,(587520242580873023/250000000000000000),(31463473579235007/1000000000000000000),(28951570700090931/3125000000000000),(172162408772343592041/250000000000000000),(494689511456309523/500000000000000000)⟩,(249171563853657477/250000000000000000),(50268825389751679/125000000000000000),(115758820658197369/500000000000000000),(55295477668317059/250000000000000000)⟩
theorem valid237 : certificate237.Valid := by decide +kernel
theorem sound237 : certificate237.Sound := rat_cut_bin_certificate_sound certificate237 profilesValid237 numericValid237 valid237

def retention238 : RatCutRetentionCertificate := ⟨(13/500),(27/1000),(1/2),(7366203105851639971/200000000000000000),1,(4579318232626838090882075743997905317/4603876941157274981875000000000000000),false,MergedCutProfiles.Batch038.profile1543,(fun _ => MergedCutProfiles.Batch038.profile1543)⟩
theorem profilesValid238 : retention238.ProfilesValid := by
  exact MergedCutProfiles.Batch038.valid1543
theorem numericValid238 : retention238.NumericValid := by decide +kernel
def certificate238 : RatCutBinCertificate := ⟨⟨retention238,(587520242580873023/250000000000000000),(31463473579235007/1000000000000000000),(28951570700090931/3125000000000000),(172162408772343592041/250000000000000000),(986684451159749857/1000000000000000000)⟩,(249171563853657477/250000000000000000),(201624425270385473/500000000000000000),(230518755921774557/1000000000000000000),(110386090106506021/500000000000000000)⟩
theorem valid238 : certificate238.Valid := by decide +kernel
theorem sound238 : certificate238.Sound := rat_cut_bin_certificate_sound certificate238 profilesValid238 numericValid238 valid238

def retention239 : RatCutRetentionCertificate := ⟨(27/1000),(7/250),(713167550894988739/68433625112009156493),(141221297206928463/200000000000000000),(37/10),(35920196701625983449/16000000000000000000),true,MergedCutProfiles.Batch038.profile1546,![MergedCutProfiles.Batch038.profile1546,MergedCutProfiles.Batch038.profile1547,MergedCutProfiles.Batch038.profile1548,MergedCutProfiles.Batch038.profile1549,MergedCutProfiles.Batch038.profile1550,MergedCutProfiles.Batch038.profile1551,MergedCutProfiles.Batch038.profile1552,MergedCutProfiles.Batch038.profile1553,MergedCutProfiles.Batch038.profile1554,MergedCutProfiles.Batch038.profile1555,MergedCutProfiles.Batch038.profile1556,MergedCutProfiles.Batch038.profile1557,MergedCutProfiles.Batch038.profile1558,MergedCutProfiles.Batch038.profile1559,MergedCutProfiles.Batch039.profile1560,MergedCutProfiles.Batch039.profile1561]⟩
theorem profilesValid239 : retention239.ProfilesValid := by
  change ∀ j : Fin 16, (retention239.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch038.valid1546
  · exact MergedCutProfiles.Batch038.valid1547
  · exact MergedCutProfiles.Batch038.valid1548
  · exact MergedCutProfiles.Batch038.valid1549
  · exact MergedCutProfiles.Batch038.valid1550
  · exact MergedCutProfiles.Batch038.valid1551
  · exact MergedCutProfiles.Batch038.valid1552
  · exact MergedCutProfiles.Batch038.valid1553
  · exact MergedCutProfiles.Batch038.valid1554
  · exact MergedCutProfiles.Batch038.valid1555
  · exact MergedCutProfiles.Batch038.valid1556
  · exact MergedCutProfiles.Batch038.valid1557
  · exact MergedCutProfiles.Batch038.valid1558
  · exact MergedCutProfiles.Batch038.valid1559
  · exact MergedCutProfiles.Batch039.valid1560
  · exact MergedCutProfiles.Batch039.valid1561
theorem numericValid239 : retention239.NumericValid := by decide +kernel
def certificate239 : RatCutBinCertificate := ⟨⟨retention239,(1977022381507928213/1000000000000000000),(1358828718451041/40000000000000000),(1878652763054541511/200000000000000000),(646028248295473760117/1000000000000000000),(443711428424326901/200000000000000000)⟩,(99703572687332897/100000000000000000),(8991937536812107/20000000000000000),(23874166452077067/125000000000000000),(46410865494297143/500000000000000000)⟩
theorem valid239 : certificate239.Valid := by decide +kernel
theorem sound239 : certificate239.Sound := rat_cut_bin_certificate_sound certificate239 profilesValid239 numericValid239 valid239

def certificates : List RatCutBinCertificate := [certificate228,certificate229,certificate230,certificate231,certificate232,certificate233,certificate234,certificate235,certificate236,certificate237,certificate238,certificate239]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound228,List.forall_mem_cons.mpr ⟨sound229,List.forall_mem_cons.mpr ⟨sound230,List.forall_mem_cons.mpr ⟨sound231,List.forall_mem_cons.mpr ⟨sound232,List.forall_mem_cons.mpr ⟨sound233,List.forall_mem_cons.mpr ⟨sound234,List.forall_mem_cons.mpr ⟨sound235,List.forall_mem_cons.mpr ⟨sound236,List.forall_mem_cons.mpr ⟨sound237,List.forall_mem_cons.mpr ⟨sound238,List.forall_mem_cons.mpr ⟨sound239,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch019
