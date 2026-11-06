import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch038
import Cycle12.MergedCutProfiles.Batch039
import Cycle12.MergedCutProfiles.Batch040

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch020

def retention240 : RatCutRetentionCertificate := ⟨(27/1000),(7/250),(870199942416149983/68433625112009156493),(713167550894988739/1000000000000000000),(37/10),(2861367369091585047567/1280000000000000000000),true,MergedCutProfiles.Batch039.profile1562,![MergedCutProfiles.Batch039.profile1562,MergedCutProfiles.Batch039.profile1563,MergedCutProfiles.Batch039.profile1564,MergedCutProfiles.Batch039.profile1565,MergedCutProfiles.Batch039.profile1566,MergedCutProfiles.Batch039.profile1567,MergedCutProfiles.Batch039.profile1568,MergedCutProfiles.Batch039.profile1569,MergedCutProfiles.Batch038.profile1556,MergedCutProfiles.Batch039.profile1570,MergedCutProfiles.Batch039.profile1571,MergedCutProfiles.Batch039.profile1572,MergedCutProfiles.Batch039.profile1573,MergedCutProfiles.Batch039.profile1574,MergedCutProfiles.Batch039.profile1575,MergedCutProfiles.Batch039.profile1576]⟩
theorem profilesValid240 : retention240.ProfilesValid := by
  change ∀ j : Fin 16, (retention240.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch039.valid1562
  · exact MergedCutProfiles.Batch039.valid1563
  · exact MergedCutProfiles.Batch039.valid1564
  · exact MergedCutProfiles.Batch039.valid1565
  · exact MergedCutProfiles.Batch039.valid1566
  · exact MergedCutProfiles.Batch039.valid1567
  · exact MergedCutProfiles.Batch039.valid1568
  · exact MergedCutProfiles.Batch039.valid1569
  · exact MergedCutProfiles.Batch038.valid1556
  · exact MergedCutProfiles.Batch039.valid1570
  · exact MergedCutProfiles.Batch039.valid1571
  · exact MergedCutProfiles.Batch039.valid1572
  · exact MergedCutProfiles.Batch039.valid1573
  · exact MergedCutProfiles.Batch039.valid1574
  · exact MergedCutProfiles.Batch039.valid1575
  · exact MergedCutProfiles.Batch039.valid1576
theorem numericValid240 : retention240.NumericValid := by decide +kernel
def certificate240 : RatCutBinCertificate := ⟨⟨retention240,(1977022381507928213/1000000000000000000),(1358828718451041/40000000000000000),(1878652763054541511/200000000000000000),(646028248295473760117/1000000000000000000),(2208988110644641809/1000000000000000000)⟩,(99703572687332897/100000000000000000),(449133153267452307/1000000000000000000),(47841067244705721/250000000000000000),(18569363527338329/200000000000000000)⟩
theorem valid240 : certificate240.Valid := by decide +kernel
theorem sound240 : certificate240.Sound := rat_cut_bin_certificate_sound certificate240 profilesValid240 numericValid240 valid240

def retention241 : RatCutRetentionCertificate := ⟨(27/1000),(7/250),(357746618000000000/22811208370669718831),(870199942416149983/1000000000000000000),(31/10),(2825215733194575680027/1280000000000000000000),true,MergedCutProfiles.Batch039.profile1577,![MergedCutProfiles.Batch039.profile1577,MergedCutProfiles.Batch038.profile1548,MergedCutProfiles.Batch039.profile1578,MergedCutProfiles.Batch038.profile1551,MergedCutProfiles.Batch039.profile1579,MergedCutProfiles.Batch039.profile1580,MergedCutProfiles.Batch039.profile1581,MergedCutProfiles.Batch038.profile1557,MergedCutProfiles.Batch039.profile1582,MergedCutProfiles.Batch039.profile1560,MergedCutProfiles.Batch039.profile1583,MergedCutProfiles.Batch039.profile1584,MergedCutProfiles.Batch039.profile1585,MergedCutProfiles.Batch039.profile1586,MergedCutProfiles.Batch039.profile1587,MergedCutProfiles.Batch039.profile1588]⟩
theorem profilesValid241 : retention241.ProfilesValid := by
  change ∀ j : Fin 16, (retention241.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch039.valid1577
  · exact MergedCutProfiles.Batch038.valid1548
  · exact MergedCutProfiles.Batch039.valid1578
  · exact MergedCutProfiles.Batch038.valid1551
  · exact MergedCutProfiles.Batch039.valid1579
  · exact MergedCutProfiles.Batch039.valid1580
  · exact MergedCutProfiles.Batch039.valid1581
  · exact MergedCutProfiles.Batch038.valid1557
  · exact MergedCutProfiles.Batch039.valid1582
  · exact MergedCutProfiles.Batch039.valid1560
  · exact MergedCutProfiles.Batch039.valid1583
  · exact MergedCutProfiles.Batch039.valid1584
  · exact MergedCutProfiles.Batch039.valid1585
  · exact MergedCutProfiles.Batch039.valid1586
  · exact MergedCutProfiles.Batch039.valid1587
  · exact MergedCutProfiles.Batch039.valid1588
theorem numericValid241 : retention241.NumericValid := by decide +kernel
def certificate241 : RatCutBinCertificate := ⟨⟨retention241,(1977022381507928213/1000000000000000000),(1358828718451041/40000000000000000),(1878652763054541511/200000000000000000),(646028248295473760117/1000000000000000000),(437006935698805631/200000000000000000)⟩,(99703572687332897/100000000000000000),(410066241102129693/1000000000000000000),(56096181830324743/250000000000000000),(62481623439546759/500000000000000000)⟩
theorem valid241 : certificate241.Valid := by decide +kernel
theorem sound241 : certificate241.Sound := rat_cut_bin_certificate_sound certificate241 profilesValid241 numericValid241 valid241

def retention242 : RatCutRetentionCertificate := ⟨(27/1000),(7/250),(440550292950722191/22811208370669718831),(536619927/500000000),(13/5),(17404348831357897279/8000000000000000000),true,MergedCutProfiles.Batch039.profile1589,![MergedCutProfiles.Batch039.profile1589,MergedCutProfiles.Batch039.profile1564,MergedCutProfiles.Batch039.profile1590,MergedCutProfiles.Batch039.profile1591,MergedCutProfiles.Batch039.profile1592,MergedCutProfiles.Batch039.profile1593,MergedCutProfiles.Batch038.profile1558,MergedCutProfiles.Batch039.profile1594,MergedCutProfiles.Batch039.profile1595,MergedCutProfiles.Batch039.profile1596,MergedCutProfiles.Batch039.profile1597,MergedCutProfiles.Batch039.profile1598,MergedCutProfiles.Batch039.profile1588,MergedCutProfiles.Batch039.profile1599,MergedCutProfiles.Batch040.profile1600,MergedCutProfiles.Batch040.profile1601]⟩
theorem profilesValid242 : retention242.ProfilesValid := by
  change ∀ j : Fin 16, (retention242.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch039.valid1589
  · exact MergedCutProfiles.Batch039.valid1564
  · exact MergedCutProfiles.Batch039.valid1590
  · exact MergedCutProfiles.Batch039.valid1591
  · exact MergedCutProfiles.Batch039.valid1592
  · exact MergedCutProfiles.Batch039.valid1593
  · exact MergedCutProfiles.Batch038.valid1558
  · exact MergedCutProfiles.Batch039.valid1594
  · exact MergedCutProfiles.Batch039.valid1595
  · exact MergedCutProfiles.Batch039.valid1596
  · exact MergedCutProfiles.Batch039.valid1597
  · exact MergedCutProfiles.Batch039.valid1598
  · exact MergedCutProfiles.Batch039.valid1588
  · exact MergedCutProfiles.Batch039.valid1599
  · exact MergedCutProfiles.Batch040.valid1600
  · exact MergedCutProfiles.Batch040.valid1601
theorem numericValid242 : retention242.NumericValid := by decide +kernel
def certificate242 : RatCutBinCertificate := ⟨⟨retention242,(1977022381507928213/1000000000000000000),(1358828718451041/40000000000000000),(1878652763054541511/200000000000000000),(646028248295473760117/1000000000000000000),(269619190142896657/125000000000000000)⟩,(99703572687332897/100000000000000000),(94279190061370829/250000000000000000),(255116153594424971/1000000000000000000),(8129290331833933/50000000000000000)⟩
theorem valid242 : certificate242.Valid := by decide +kernel
theorem sound242 : certificate242.Sound := rat_cut_bin_certificate_sound certificate242 profilesValid242 numericValid242 valid242

def retention243 : RatCutRetentionCertificate := ⟨(27/1000),(7/250),(5593916090036271143/68433625112009156493),(1321650878852166573/1000000000000000000),(9/4),(498005968857259600113/256000000000000000000),true,MergedCutProfiles.Batch040.profile1602,![MergedCutProfiles.Batch040.profile1602,MergedCutProfiles.Batch040.profile1603,MergedCutProfiles.Batch040.profile1604,MergedCutProfiles.Batch040.profile1605,MergedCutProfiles.Batch040.profile1606,MergedCutProfiles.Batch040.profile1607,MergedCutProfiles.Batch040.profile1608,MergedCutProfiles.Batch040.profile1609,MergedCutProfiles.Batch040.profile1610,MergedCutProfiles.Batch040.profile1611,MergedCutProfiles.Batch040.profile1612,MergedCutProfiles.Batch040.profile1613,MergedCutProfiles.Batch040.profile1614,MergedCutProfiles.Batch040.profile1615,MergedCutProfiles.Batch040.profile1616,MergedCutProfiles.Batch040.profile1617]⟩
theorem profilesValid243 : retention243.ProfilesValid := by
  change ∀ j : Fin 16, (retention243.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch040.valid1602
  · exact MergedCutProfiles.Batch040.valid1603
  · exact MergedCutProfiles.Batch040.valid1604
  · exact MergedCutProfiles.Batch040.valid1605
  · exact MergedCutProfiles.Batch040.valid1606
  · exact MergedCutProfiles.Batch040.valid1607
  · exact MergedCutProfiles.Batch040.valid1608
  · exact MergedCutProfiles.Batch040.valid1609
  · exact MergedCutProfiles.Batch040.valid1610
  · exact MergedCutProfiles.Batch040.valid1611
  · exact MergedCutProfiles.Batch040.valid1612
  · exact MergedCutProfiles.Batch040.valid1613
  · exact MergedCutProfiles.Batch040.valid1614
  · exact MergedCutProfiles.Batch040.valid1615
  · exact MergedCutProfiles.Batch040.valid1616
  · exact MergedCutProfiles.Batch040.valid1617
theorem numericValid243 : retention243.NumericValid := by decide +kernel
def certificate243 : RatCutBinCertificate := ⟨⟨retention243,(1977022381507928213/1000000000000000000),(1358828718451041/40000000000000000),(1878652763054541511/200000000000000000),(646028248295473760117/1000000000000000000),(964624131450349997/500000000000000000)⟩,(99703572687332897/100000000000000000),(387143840505709643/1000000000000000000),(245470560490554993/1000000000000000000),(162818221890319921/1000000000000000000)⟩
theorem valid243 : certificate243.Valid := by decide +kernel
theorem sound243 : certificate243.Sound := rat_cut_bin_certificate_sound certificate243 profilesValid243 numericValid243 valid243

def retention244 : RatCutRetentionCertificate := ⟨(27/1000),(7/250),(28320432022477529000/68433625112009156493),(5593916090036271143/1000000000000000000),(11/10),(2592859063179973657294678716202400887711/2237566436014508457200000000000000000000),false,MergedCutProfiles.Batch040.profile1618,(fun _ => MergedCutProfiles.Batch040.profile1618)⟩
theorem profilesValid244 : retention244.ProfilesValid := by
  exact MergedCutProfiles.Batch040.valid1618
theorem numericValid244 : retention244.NumericValid := by decide +kernel
def certificate244 : RatCutBinCertificate := ⟨⟨retention244,(1977022381507928213/1000000000000000000),(1358828718451041/40000000000000000),(1878652763054541511/200000000000000000),(646028248295473760117/1000000000000000000),(1150920332281400029/1000000000000000000)⟩,(99703572687332897/100000000000000000),(22911293146584851/50000000000000000),(92088819106416527/500000000000000000),(82086874414367269/500000000000000000)⟩
theorem valid244 : certificate244.Valid := by decide +kernel
theorem sound244 : certificate244.Sound := rat_cut_bin_certificate_sound certificate244 profilesValid244 numericValid244 valid244

def retention245 : RatCutRetentionCertificate := ⟨(27/1000),(7/250),(11291804424680761693/22811208370669718831),(28320432022477529/1000000000000000),1,(28389571968814584946161853300056677631/28320432022477529000000000000000000000),false,MergedCutProfiles.Batch040.profile1619,(fun _ => MergedCutProfiles.Batch040.profile1619)⟩
theorem profilesValid245 : retention245.ProfilesValid := by
  exact MergedCutProfiles.Batch040.valid1619
theorem numericValid245 : retention245.NumericValid := by decide +kernel
def certificate245 : RatCutBinCertificate := ⟨⟨retention245,(1977022381507928213/1000000000000000000),(1358828718451041/40000000000000000),(1878652763054541511/200000000000000000),(646028248295473760117/1000000000000000000),(995291434666167863/1000000000000000000)⟩,(99703572687332897/100000000000000000),(475123699590918021/1000000000000000000),(6851943316730849/40000000000000000),(262730335326599/1600000000000000)⟩
theorem valid245 : certificate245.Valid := by decide +kernel
theorem sound245 : certificate245.Sound := rat_cut_bin_certificate_sound certificate245 profilesValid245 numericValid245 valid245

def retention246 : RatCutRetentionCertificate := ⟨(27/1000),(7/250),(11404722468927569310/22811208370669718831),(33875413274042285079/1000000000000000000),1,(280643686698354259260529019459805957/282295110617019042325000000000000000),false,MergedCutProfiles.Batch040.profile1620,(fun _ => MergedCutProfiles.Batch040.profile1620)⟩
theorem profilesValid246 : retention246.ProfilesValid := by
  exact MergedCutProfiles.Batch040.valid1620
theorem numericValid246 : retention246.NumericValid := by decide +kernel
def certificate246 : RatCutBinCertificate := ⟨⟨retention246,(1977022381507928213/1000000000000000000),(1358828718451041/40000000000000000),(1878652763054541511/200000000000000000),(646028248295473760117/1000000000000000000),(987000100579636033/1000000000000000000)⟩,(99703572687332897/100000000000000000),(19075458333322799/40000000000000000),(169990045978532469/1000000000000000000),(162539368505930761/1000000000000000000)⟩
theorem valid246 : certificate246.Valid := by decide +kernel
theorem sound246 : certificate246.Sound := rat_cut_bin_certificate_sound certificate246 profilesValid246 numericValid246 valid246

def retention247 : RatCutRetentionCertificate := ⟨(27/1000),(7/250),(1/2),(3421416740678270793/100000000000000000),1,(3779323612206586518472184656969597979/3801574156309189770000000000000000000),false,MergedCutProfiles.Batch040.profile1621,(fun _ => MergedCutProfiles.Batch040.profile1621)⟩
theorem profilesValid247 : retention247.ProfilesValid := by
  exact MergedCutProfiles.Batch040.valid1621
theorem numericValid247 : retention247.NumericValid := by decide +kernel
def certificate247 : RatCutBinCertificate := ⟨⟨retention247,(1977022381507928213/1000000000000000000),(1358828718451041/40000000000000000),(1878652763054541511/200000000000000000),(646028248295473760117/1000000000000000000),(986997110174511083/1000000000000000000)⟩,(99703572687332897/100000000000000000),(119193853096692243/250000000000000000),(42518071357222717/250000000000000000),(81331596327264009/500000000000000000)⟩
theorem valid247 : certificate247.Valid := by decide +kernel
theorem sound247 : certificate247.Sound := rat_cut_bin_certificate_sound certificate247 profilesValid247 numericValid247 valid247

def retention248 : RatCutRetentionCertificate := ⟨(27/1000),(7/250),(28410172770013441574/68433625112009156493),(3694811182409305561/1000000000000000000),(5/4),(55280201778293565475623281490017193491/47293583134839111180800000000000000000),false,MergedCutProfiles.Batch040.profile1622,(fun _ => MergedCutProfiles.Batch040.profile1622)⟩
theorem profilesValid248 : retention248.ProfilesValid := by
  exact MergedCutProfiles.Batch040.valid1622
theorem numericValid248 : retention248.NumericValid := by decide +kernel
def certificate248 : RatCutBinCertificate := ⟨⟨retention248,(2357980755507928213/1000000000000000000),(1358828718451041/40000000000000000),(1878652763054541511/200000000000000000),(646028248295473760117/1000000000000000000),(1158213536664228197/1000000000000000000)⟩,(199292893317795951/200000000000000000),(341125098992447263/1000000000000000000),(72996335801383333/250000000000000000),(112237969525267857/500000000000000000)⟩
theorem valid248 : certificate248.Valid := by decide +kernel
theorem sound248 : certificate248.Sound := rat_cut_bin_certificate_sound certificate248 profilesValid248 numericValid248 valid248

def retention249 : RatCutRetentionCertificate := ⟨(27/1000),(7/250),(11327585480891200398/22811208370669718831),(14205086385006720787/500000000000000000),1,(113570394053437625386318849065090264279/113640691080053766296000000000000000000),false,MergedCutProfiles.Batch040.profile1623,(fun _ => MergedCutProfiles.Batch040.profile1623)⟩
theorem profilesValid249 : retention249.ProfilesValid := by
  exact MergedCutProfiles.Batch040.valid1623
theorem numericValid249 : retention249.NumericValid := by decide +kernel
def certificate249 : RatCutBinCertificate := ⟨⟨retention249,(2357980755507928213/1000000000000000000),(1358828718451041/40000000000000000),(1878652763054541511/200000000000000000),(646028248295473760117/1000000000000000000),(495426880857278067/500000000000000000)⟩,(199292893317795951/200000000000000000),(398742703126352917/1000000000000000000),(234636338485883789/1000000000000000000),(55962140721989719/250000000000000000)⟩
theorem valid249 : certificate249.Valid := by decide +kernel
theorem sound249 : certificate249.Sound := rat_cut_bin_certificate_sound certificate249 profilesValid249 numericValid249 valid249

def retention250 : RatCutRetentionCertificate := ⟨(27/1000),(7/250),(1/2),(16991378221336800597/500000000000000000),1,(150142933760767555412935733173204979/151034473078549338640000000000000000),false,MergedCutProfiles.Batch040.profile1621,(fun _ => MergedCutProfiles.Batch040.profile1621)⟩
theorem profilesValid250 : retention250.ProfilesValid := by
  exact MergedCutProfiles.Batch040.valid1621
theorem numericValid250 : retention250.NumericValid := by decide +kernel
def certificate250 : RatCutBinCertificate := ⟨⟨retention250,(2357980755507928213/1000000000000000000),(1358828718451041/40000000000000000),(1878652763054541511/200000000000000000),(646028248295473760117/1000000000000000000),(246392367076965419/250000000000000000)⟩,(199292893317795951/200000000000000000),(100220156988863191/250000000000000000),(116338227962923351/500000000000000000),(222057432502204059/1000000000000000000)⟩
theorem valid250 : certificate250.Valid := by decide +kernel
theorem sound250 : certificate250.Sound := rat_cut_bin_certificate_sound certificate250 profilesValid250 numericValid250 valid250

def retention251 : RatCutRetentionCertificate := ⟨(7/250),(29/1000),(718007998690644917/63476256200139309633),(710899008604598927/1000000000000000000),(37/10),(2872023952216197361931/1280000000000000000000),true,MergedCutProfiles.Batch040.profile1624,![MergedCutProfiles.Batch040.profile1624,MergedCutProfiles.Batch040.profile1625,MergedCutProfiles.Batch040.profile1626,MergedCutProfiles.Batch040.profile1627,MergedCutProfiles.Batch040.profile1628,MergedCutProfiles.Batch040.profile1629,MergedCutProfiles.Batch040.profile1630,MergedCutProfiles.Batch040.profile1631,MergedCutProfiles.Batch040.profile1632,MergedCutProfiles.Batch040.profile1633,MergedCutProfiles.Batch040.profile1634,MergedCutProfiles.Batch040.profile1635,MergedCutProfiles.Batch040.profile1636,MergedCutProfiles.Batch040.profile1637,MergedCutProfiles.Batch040.profile1638,MergedCutProfiles.Batch040.profile1639]⟩
theorem profilesValid251 : retention251.ProfilesValid := by
  change ∀ j : Fin 16, (retention251.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch040.valid1624
  · exact MergedCutProfiles.Batch040.valid1625
  · exact MergedCutProfiles.Batch040.valid1626
  · exact MergedCutProfiles.Batch040.valid1627
  · exact MergedCutProfiles.Batch040.valid1628
  · exact MergedCutProfiles.Batch040.valid1629
  · exact MergedCutProfiles.Batch040.valid1630
  · exact MergedCutProfiles.Batch040.valid1631
  · exact MergedCutProfiles.Batch040.valid1632
  · exact MergedCutProfiles.Batch040.valid1633
  · exact MergedCutProfiles.Batch040.valid1634
  · exact MergedCutProfiles.Batch040.valid1635
  · exact MergedCutProfiles.Batch040.valid1636
  · exact MergedCutProfiles.Batch040.valid1637
  · exact MergedCutProfiles.Batch040.valid1638
  · exact MergedCutProfiles.Batch040.valid1639
theorem numericValid251 : retention251.NumericValid := by decide +kernel
def certificate251 : RatCutBinCertificate := ⟨⟨retention251,(991191016586418053/500000000000000000),(36585906920747501/1000000000000000000),(4762395989857947939/500000000000000000),(121527652363862859971/200000000000000000),(2215594139603861139/1000000000000000000)⟩,(996848037382240881/1000000000000000000),(447360785122269087/1000000000000000000),(192786420635379579/1000000000000000000),(93688689550088989/1000000000000000000)⟩
theorem valid251 : certificate251.Valid := by decide +kernel
theorem sound251 : certificate251.Sound := rat_cut_bin_certificate_sound certificate251 profilesValid251 numericValid251 valid251

def certificates : List RatCutBinCertificate := [certificate240,certificate241,certificate242,certificate243,certificate244,certificate245,certificate246,certificate247,certificate248,certificate249,certificate250,certificate251]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound240,List.forall_mem_cons.mpr ⟨sound241,List.forall_mem_cons.mpr ⟨sound242,List.forall_mem_cons.mpr ⟨sound243,List.forall_mem_cons.mpr ⟨sound244,List.forall_mem_cons.mpr ⟨sound245,List.forall_mem_cons.mpr ⟨sound246,List.forall_mem_cons.mpr ⟨sound247,List.forall_mem_cons.mpr ⟨sound248,List.forall_mem_cons.mpr ⟨sound249,List.forall_mem_cons.mpr ⟨sound250,List.forall_mem_cons.mpr ⟨sound251,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch020
