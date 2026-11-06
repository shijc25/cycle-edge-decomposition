import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch260
import Cycle12.MergedCutProfiles.Batch261

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch135

def retention1620 : RatCutRetentionCertificate := ⟨(51/800),(511/8000),(1/2),64,1,(10216570041964305586067861601130137919/10240000000000000000000000000000000000),false,MergedCutProfiles.Batch260.profile10403,(fun _ => MergedCutProfiles.Batch260.profile10403)⟩
theorem profilesValid1620 : retention1620.ProfilesValid := by
  exact MergedCutProfiles.Batch260.valid10403
theorem numericValid1620 : retention1620.NumericValid := by decide +kernel
def certificate1620 : RatCutBinCertificate := ⟨⟨retention1620,(2370502591943633393/1000000000000000000),(21182226506109577/100000000000000000),(8503990036874126001/500000000000000000),(5721494197070798261/31250000000000000),(96818846486270619/100000000000000000)⟩,(989752926237757021/1000000000000000000),(388164577557181391/1000000000000000000),(24450332654032583/100000000000000000),(57696049211022893/250000000000000000)⟩
theorem valid1620 : certificate1620.Valid := by decide +kernel
theorem sound1620 : certificate1620.Sound := rat_cut_bin_certificate_sound certificate1620 profilesValid1620 numericValid1620 valid1620

def retention1621 : RatCutRetentionCertificate := ⟨(51/800),(511/8000),(455980253377766924/977852110863584295),(3205360645708925957/1000000000000000000),(6/5),(7686806700688986760433700385300846159/7284910558429377175000000000000000000),false,MergedCutProfiles.Batch260.profile10404,(fun _ => MergedCutProfiles.Batch260.profile10404)⟩
theorem profilesValid1621 : retention1621.ProfilesValid := by
  exact MergedCutProfiles.Batch260.valid10404
theorem numericValid1621 : retention1621.NumericValid := by decide +kernel
def certificate1621 : RatCutBinCertificate := ⟨⟨retention1621,(2684738069943633393/1000000000000000000),(21182226506109577/100000000000000000),(8503990036874126001/500000000000000000),(5721494197070798261/31250000000000000),(507516217414056409/500000000000000000)⟩,(494195178397442541/500000000000000000),(193221335395736687/500000000000000000),(49227307092341163/200000000000000000),(168445016899054221/1000000000000000000)⟩
theorem valid1621 : certificate1621.Valid := by decide +kernel
theorem sound1621 : certificate1621.Sound := rat_cut_bin_certificate_sound certificate1621 profilesValid1621 numericValid1621 valid1621

def retention1622 : RatCutRetentionCertificate := ⟨(51/800),(511/8000),(5324354499603142129/10756373219499427245),(1253945696788859041/250000000000000000),(11/10),(125231006275068306990858505393630804199/125394569678885904100000000000000000000),false,MergedCutProfiles.Batch260.profile10405,(fun _ => MergedCutProfiles.Batch260.profile10405)⟩
theorem profilesValid1622 : retention1622.ProfilesValid := by
  exact MergedCutProfiles.Batch260.valid10405
theorem numericValid1622 : retention1622.NumericValid := by decide +kernel
def certificate1622 : RatCutBinCertificate := ⟨⟨retention1622,(2684738069943633393/1000000000000000000),(21182226506109577/100000000000000000),(8503990036874126001/500000000000000000),(5721494197070798261/31250000000000000),(961907749392167713/1000000000000000000)⟩,(494195178397442541/500000000000000000),(203892652545326269/500000000000000000),(226424320901065859/1000000000000000000),(168750536534009801/1000000000000000000)⟩
theorem valid1622 : certificate1622.Valid := by decide +kernel
theorem sound1622 : certificate1622.Sound := rat_cut_bin_certificate_sound certificate1622 profilesValid1622 numericValid1622 valid1622

def retention1623 : RatCutRetentionCertificate := ⟨(51/800),(511/8000),(5377598044599173551/10756373219499427245),(5324354499603142129/1000000000000000000),(11/10),(2111423963886896451144437141227698225599/2129741799841256851600000000000000000000),false,MergedCutProfiles.Batch260.profile10406,(fun _ => MergedCutProfiles.Batch260.profile10406)⟩
theorem profilesValid1623 : retention1623.ProfilesValid := by
  exact MergedCutProfiles.Batch260.valid10406
theorem numericValid1623 : retention1623.NumericValid := by decide +kernel
def certificate1623 : RatCutBinCertificate := ⟨⟨retention1623,(2684738069943633393/1000000000000000000),(21182226506109577/100000000000000000),(8503990036874126001/500000000000000000),(5721494197070798261/31250000000000000),(477305810308890781/500000000000000000)⟩,(494195178397442541/500000000000000000),(410902021914525157/1000000000000000000),(55910139495466079/250000000000000000),(83453335215657683/500000000000000000)⟩
theorem valid1623 : certificate1623.Valid := by decide +kernel
theorem sound1623 : certificate1623.Sound := rat_cut_bin_certificate_sound certificate1623 profilesValid1623 numericValid1623 valid1623

def retention1624 : RatCutRetentionCertificate := ⟨(51/800),(511/8000),(1/2),(5377598044599173551/1000000000000000000),(11/10),(2133029749772652484885666807333367833999/2151039217839669420400000000000000000000),false,MergedCutProfiles.Batch260.profile10403,(fun _ => MergedCutProfiles.Batch260.profile10403)⟩
theorem profilesValid1624 : retention1624.ProfilesValid := by
  exact MergedCutProfiles.Batch260.valid10403
theorem numericValid1624 : retention1624.NumericValid := by decide +kernel
def certificate1624 : RatCutBinCertificate := ⟨⟨retention1624,(2684738069943633393/1000000000000000000),(21182226506109577/100000000000000000),(8503990036874126001/500000000000000000),(5721494197070798261/31250000000000000),(190968041652030303/200000000000000000)⟩,(494195178397442541/500000000000000000),(410803652445349119/1000000000000000000),(223728056689618621/1000000000000000000),(10451371397475473/62500000000000000)⟩
theorem valid1624 : certificate1624.Valid := by decide +kernel
theorem sound1624 : certificate1624.Sound := rat_cut_bin_certificate_sound certificate1624 profilesValid1624 numericValid1624 valid1624

def retention1625 : RatCutRetentionCertificate := ⟨(511/8000),(8/125),(1350708572530328629/10705984450122921257),(907207652425697259/1000000000000000000),(5/2),(93538999185290140359/51200000000000000000),true,MergedCutProfiles.Batch260.profile10407,![MergedCutProfiles.Batch260.profile10407,MergedCutProfiles.Batch260.profile10408,MergedCutProfiles.Batch260.profile10409,MergedCutProfiles.Batch260.profile10410,MergedCutProfiles.Batch260.profile10411,MergedCutProfiles.Batch260.profile10412,MergedCutProfiles.Batch260.profile10413,MergedCutProfiles.Batch260.profile10414,MergedCutProfiles.Batch260.profile10415,MergedCutProfiles.Batch260.profile10416,MergedCutProfiles.Batch260.profile10417,MergedCutProfiles.Batch260.profile10418,MergedCutProfiles.Batch260.profile10419,MergedCutProfiles.Batch260.profile10420,MergedCutProfiles.Batch260.profile10421,MergedCutProfiles.Batch260.profile10422]⟩
theorem profilesValid1625 : retention1625.ProfilesValid := by
  change ∀ j : Fin 16, (retention1625.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch260.valid10407
  · exact MergedCutProfiles.Batch260.valid10408
  · exact MergedCutProfiles.Batch260.valid10409
  · exact MergedCutProfiles.Batch260.valid10410
  · exact MergedCutProfiles.Batch260.valid10411
  · exact MergedCutProfiles.Batch260.valid10412
  · exact MergedCutProfiles.Batch260.valid10413
  · exact MergedCutProfiles.Batch260.valid10414
  · exact MergedCutProfiles.Batch260.valid10415
  · exact MergedCutProfiles.Batch260.valid10416
  · exact MergedCutProfiles.Batch260.valid10417
  · exact MergedCutProfiles.Batch260.valid10418
  · exact MergedCutProfiles.Batch260.valid10419
  · exact MergedCutProfiles.Batch260.valid10420
  · exact MergedCutProfiles.Batch260.valid10421
  · exact MergedCutProfiles.Batch260.valid10422
theorem numericValid1625 : retention1625.NumericValid := by decide +kernel
def certificate1625 : RatCutBinCertificate := ⟨⟨retention1625,(73996785269951413/31250000000000000),(106411689904918233/500000000000000000),(852416440356973433/50000000000000000),(36532513181200568633/200000000000000000),(876498154069250147/500000000000000000)⟩,(494876572380097603/500000000000000000),(339443359095571057/1000000000000000000),(146898928477271817/500000000000000000),(77698537522858987/500000000000000000)⟩
theorem valid1625 : certificate1625.Valid := by decide +kernel
theorem sound1625 : certificate1625.Sound := rat_cut_bin_certificate_sound certificate1625 profilesValid1625 numericValid1625 valid1625

def retention1626 : RatCutRetentionCertificate := ⟨(511/8000),(8/125),(2877306081804078358/10705984450122921257),(1350708572530328629/1000000000000000000),(7/4),(375317806035923425537/256000000000000000000),true,MergedCutProfiles.Batch260.profile10423,![MergedCutProfiles.Batch260.profile10423,MergedCutProfiles.Batch260.profile10424,MergedCutProfiles.Batch260.profile10425,MergedCutProfiles.Batch260.profile10426,MergedCutProfiles.Batch260.profile10427,MergedCutProfiles.Batch260.profile10428,MergedCutProfiles.Batch260.profile10429,MergedCutProfiles.Batch260.profile10430,MergedCutProfiles.Batch260.profile10431,MergedCutProfiles.Batch260.profile10432,MergedCutProfiles.Batch260.profile10433,MergedCutProfiles.Batch260.profile10434,MergedCutProfiles.Batch260.profile10435,MergedCutProfiles.Batch260.profile10436,MergedCutProfiles.Batch260.profile10437,MergedCutProfiles.Batch260.profile10438]⟩
theorem profilesValid1626 : retention1626.ProfilesValid := by
  change ∀ j : Fin 16, (retention1626.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch260.valid10423
  · exact MergedCutProfiles.Batch260.valid10424
  · exact MergedCutProfiles.Batch260.valid10425
  · exact MergedCutProfiles.Batch260.valid10426
  · exact MergedCutProfiles.Batch260.valid10427
  · exact MergedCutProfiles.Batch260.valid10428
  · exact MergedCutProfiles.Batch260.valid10429
  · exact MergedCutProfiles.Batch260.valid10430
  · exact MergedCutProfiles.Batch260.valid10431
  · exact MergedCutProfiles.Batch260.valid10432
  · exact MergedCutProfiles.Batch260.valid10433
  · exact MergedCutProfiles.Batch260.valid10434
  · exact MergedCutProfiles.Batch260.valid10435
  · exact MergedCutProfiles.Batch260.valid10436
  · exact MergedCutProfiles.Batch260.valid10437
  · exact MergedCutProfiles.Batch260.valid10438
theorem numericValid1626 : retention1626.NumericValid := by decide +kernel
def certificate1626 : RatCutBinCertificate := ⟨⟨retention1626,(73996785269951413/31250000000000000),(106411689904918233/500000000000000000),(852416440356973433/50000000000000000),(36532513181200568633/200000000000000000),(353582541794369327/250000000000000000)⟩,(494876572380097603/500000000000000000),(369807101251897029/1000000000000000000),(262315207129192339/1000000000000000000),(156035536895980649/1000000000000000000)⟩
theorem valid1626 : certificate1626.Valid := by decide +kernel
theorem sound1626 : certificate1626.Sound := rat_cut_bin_certificate_sound certificate1626 profilesValid1626 numericValid1626 valid1626

def retention1627 : RatCutRetentionCertificate := ⟨(511/8000),(8/125),(4685256577544478130/10705984450122921257),(1438653040902039179/500000000000000000),(11/10),(695291486904765590927/640000000000000000000),true,MergedCutProfiles.Batch260.profile10439,![MergedCutProfiles.Batch260.profile10439,MergedCutProfiles.Batch261.profile10440,MergedCutProfiles.Batch261.profile10441,MergedCutProfiles.Batch261.profile10442,MergedCutProfiles.Batch261.profile10443,MergedCutProfiles.Batch261.profile10444,MergedCutProfiles.Batch261.profile10445,MergedCutProfiles.Batch261.profile10446,MergedCutProfiles.Batch261.profile10447,MergedCutProfiles.Batch261.profile10448,MergedCutProfiles.Batch261.profile10449,MergedCutProfiles.Batch261.profile10450,MergedCutProfiles.Batch261.profile10451,MergedCutProfiles.Batch261.profile10452,MergedCutProfiles.Batch261.profile10453,MergedCutProfiles.Batch261.profile10454]⟩
theorem profilesValid1627 : retention1627.ProfilesValid := by
  change ∀ j : Fin 16, (retention1627.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch260.valid10439
  · exact MergedCutProfiles.Batch261.valid10440
  · exact MergedCutProfiles.Batch261.valid10441
  · exact MergedCutProfiles.Batch261.valid10442
  · exact MergedCutProfiles.Batch261.valid10443
  · exact MergedCutProfiles.Batch261.valid10444
  · exact MergedCutProfiles.Batch261.valid10445
  · exact MergedCutProfiles.Batch261.valid10446
  · exact MergedCutProfiles.Batch261.valid10447
  · exact MergedCutProfiles.Batch261.valid10448
  · exact MergedCutProfiles.Batch261.valid10449
  · exact MergedCutProfiles.Batch261.valid10450
  · exact MergedCutProfiles.Batch261.valid10451
  · exact MergedCutProfiles.Batch261.valid10452
  · exact MergedCutProfiles.Batch261.valid10453
  · exact MergedCutProfiles.Batch261.valid10454
theorem numericValid1627 : retention1627.NumericValid := by decide +kernel
def certificate1627 : RatCutBinCertificate := ⟨⟨retention1627,(73996785269951413/31250000000000000),(106411689904918233/500000000000000000),(852416440356973433/50000000000000000),(36532513181200568633/200000000000000000),(32933290116580971/31250000000000000)⟩,(494876572380097603/500000000000000000),(211067208287811013/500000000000000000),(53450722074294539/250000000000000000),(155375807387461497/1000000000000000000)⟩
theorem valid1627 : certificate1627.Valid := by decide +kernel
theorem sound1627 : certificate1627.Sound := rat_cut_bin_certificate_sound certificate1627 profilesValid1627 numericValid1627 valid1627

def retention1628 : RatCutRetentionCertificate := ⟨(511/8000),(8/125),(5175438078784007354/10705984450122921257),(468525657754447813/100000000000000000),1,(25304933696515910269/25600000000000000000),true,MergedCutProfiles.Batch261.profile10455,![MergedCutProfiles.Batch261.profile10455,MergedCutProfiles.Batch261.profile10456,MergedCutProfiles.Batch261.profile10457,MergedCutProfiles.Batch261.profile10458,MergedCutProfiles.Batch260.profile10431,MergedCutProfiles.Batch261.profile10459,MergedCutProfiles.Batch261.profile10460,MergedCutProfiles.Batch261.profile10461,MergedCutProfiles.Batch261.profile10462,MergedCutProfiles.Batch261.profile10463,MergedCutProfiles.Batch261.profile10464,MergedCutProfiles.Batch261.profile10465,MergedCutProfiles.Batch261.profile10466,MergedCutProfiles.Batch261.profile10467,MergedCutProfiles.Batch261.profile10468,MergedCutProfiles.Batch261.profile10469]⟩
theorem profilesValid1628 : retention1628.ProfilesValid := by
  change ∀ j : Fin 16, (retention1628.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch261.valid10455
  · exact MergedCutProfiles.Batch261.valid10456
  · exact MergedCutProfiles.Batch261.valid10457
  · exact MergedCutProfiles.Batch261.valid10458
  · exact MergedCutProfiles.Batch260.valid10431
  · exact MergedCutProfiles.Batch261.valid10459
  · exact MergedCutProfiles.Batch261.valid10460
  · exact MergedCutProfiles.Batch261.valid10461
  · exact MergedCutProfiles.Batch261.valid10462
  · exact MergedCutProfiles.Batch261.valid10463
  · exact MergedCutProfiles.Batch261.valid10464
  · exact MergedCutProfiles.Batch261.valid10465
  · exact MergedCutProfiles.Batch261.valid10466
  · exact MergedCutProfiles.Batch261.valid10467
  · exact MergedCutProfiles.Batch261.valid10468
  · exact MergedCutProfiles.Batch261.valid10469
theorem numericValid1628 : retention1628.NumericValid := by decide +kernel
def certificate1628 : RatCutBinCertificate := ⟨⟨retention1628,(73996785269951413/31250000000000000),(106411689904918233/500000000000000000),(852416440356973433/50000000000000000),(36532513181200568633/200000000000000000),(191781379821137483/200000000000000000)⟩,(494876572380097603/500000000000000000),(218054809892131517/500000000000000000),(201979296374119527/1000000000000000000),(39734617816984189/250000000000000000)⟩
theorem valid1628 : certificate1628.Valid := by decide +kernel
theorem sound1628 : certificate1628.Sound := rat_cut_bin_certificate_sound certificate1628 profilesValid1628 numericValid1628 valid1628

def retention1629 : RatCutRetentionCertificate := ⟨(511/8000),(8/125),(5279464384167565903/10705984450122921257),(2587719039392003677/500000000000000000),(11/10),(519319495846384667800412964769255560991/517543807878400735400000000000000000000),false,MergedCutProfiles.Batch261.profile10470,(fun _ => MergedCutProfiles.Batch261.profile10470)⟩
theorem profilesValid1629 : retention1629.ProfilesValid := by
  exact MergedCutProfiles.Batch261.valid10470
theorem numericValid1629 : retention1629.NumericValid := by decide +kernel
def certificate1629 : RatCutBinCertificate := ⟨⟨retention1629,(73996785269951413/31250000000000000),(106411689904918233/500000000000000000),(852416440356973433/50000000000000000),(36532513181200568633/200000000000000000),(194181728240410897/200000000000000000)⟩,(494876572380097603/500000000000000000),(213287993511808939/500000000000000000),(52498927872361281/250000000000000000),(158665916290626601/1000000000000000000)⟩
theorem valid1629 : certificate1629.Valid := by decide +kernel
theorem sound1629 : certificate1629.Sound := rat_cut_bin_certificate_sound certificate1629 profilesValid1629 numericValid1629 valid1629

def retention1630 : RatCutRetentionCertificate := ⟨(511/8000),(8/125),(5332259028009241563/10705984450122921257),(5279464384167565903/1000000000000000000),(11/10),(2100619787177807350913299938558352439951/2111785753667026361200000000000000000000),false,MergedCutProfiles.Batch261.profile10471,(fun _ => MergedCutProfiles.Batch261.profile10471)⟩
theorem profilesValid1630 : retention1630.ProfilesValid := by
  exact MergedCutProfiles.Batch261.valid10471
theorem numericValid1630 : retention1630.NumericValid := by decide +kernel
def certificate1630 : RatCutBinCertificate := ⟨⟨retention1630,(73996785269951413/31250000000000000),(106411689904918233/500000000000000000),(852416440356973433/50000000000000000),(36532513181200568633/200000000000000000),(962190329346909243/1000000000000000000)⟩,(494876572380097603/500000000000000000),(42965386199894399/100000000000000000),(207384602539106249/1000000000000000000),(155885016611176383/1000000000000000000)⟩
theorem valid1630 : certificate1630.Valid := by decide +kernel
theorem sound1630 : certificate1630.Sound := rat_cut_bin_certificate_sound certificate1630 profilesValid1630 numericValid1630 valid1630

def retention1631 : RatCutRetentionCertificate := ⟨(511/8000),(8/125),(1/2),(5332259028009241563/1000000000000000000),(11/10),(704814521131359141226564091374049019477/710967870401232208400000000000000000000),false,MergedCutProfiles.Batch261.profile10472,(fun _ => MergedCutProfiles.Batch261.profile10472)⟩
theorem profilesValid1631 : retention1631.ProfilesValid := by
  exact MergedCutProfiles.Batch261.valid10472
theorem numericValid1631 : retention1631.NumericValid := by decide +kernel
def certificate1631 : RatCutBinCertificate := ⟨⟨retention1631,(73996785269951413/31250000000000000),(106411689904918233/500000000000000000),(852416440356973433/50000000000000000),(36532513181200568633/200000000000000000),(23970573886855993/25000000000000000)⟩,(494876572380097603/500000000000000000),(430773631332483877/1000000000000000000),(206440125608663393/1000000000000000000),(154904310397224139/1000000000000000000)⟩
theorem valid1631 : certificate1631.Valid := by decide +kernel
theorem sound1631 : certificate1631.Sound := rat_cut_bin_certificate_sound certificate1631 profilesValid1631 numericValid1631 valid1631

def certificates : List RatCutBinCertificate := [certificate1620,certificate1621,certificate1622,certificate1623,certificate1624,certificate1625,certificate1626,certificate1627,certificate1628,certificate1629,certificate1630,certificate1631]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1620,List.forall_mem_cons.mpr ⟨sound1621,List.forall_mem_cons.mpr ⟨sound1622,List.forall_mem_cons.mpr ⟨sound1623,List.forall_mem_cons.mpr ⟨sound1624,List.forall_mem_cons.mpr ⟨sound1625,List.forall_mem_cons.mpr ⟨sound1626,List.forall_mem_cons.mpr ⟨sound1627,List.forall_mem_cons.mpr ⟨sound1628,List.forall_mem_cons.mpr ⟨sound1629,List.forall_mem_cons.mpr ⟨sound1630,List.forall_mem_cons.mpr ⟨sound1631,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch135
