import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch288
import Cycle12.MergedCutProfiles.Batch289
import Cycle12.MergedCutProfiles.Batch290

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch151

def retention1812 : RatCutRetentionCertificate := ⟨(263/4000),(527/8000),(826933997532623160/1664337852357428483),(4912479193263107881/1000000000000000000),(11/10),(1953912410582800015091708775434634856159/1964991677305243152400000000000000000000),false,MergedCutProfiles.Batch288.profile11545,(fun _ => MergedCutProfiles.Batch288.profile11545)⟩
theorem profilesValid1812 : retention1812.ProfilesValid := by
  exact MergedCutProfiles.Batch288.valid11545
theorem numericValid1812 : retention1812.NumericValid := by decide +kernel
def certificate1812 : RatCutBinCertificate := ⟨⟨retention1812,(33906138117166049/12500000000000000),(57064330308281523/250000000000000000),(8835637598779032713/500000000000000000),(176606313810354852443/1000000000000000000),(191162382338626351/200000000000000000)⟩,(988087120478718677/1000000000000000000),(199243916828130353/500000000000000000),(14679421629235937/62500000000000000),(173524379875919721/1000000000000000000)⟩
theorem valid1812 : certificate1812.Valid := by decide +kernel
theorem sound1812 : certificate1812.Sound := rat_cut_bin_certificate_sound certificate1812 profilesValid1812 numericValid1812 valid1812

def retention1813 : RatCutRetentionCertificate := ⟨(263/4000),(527/8000),(1/2),(62020049814946737/12500000000000000),(11/10),(38327221618265198344892057354400463/38762531134341710625000000000000000),false,MergedCutProfiles.Batch288.profile11542,(fun _ => MergedCutProfiles.Batch288.profile11542)⟩
theorem profilesValid1813 : retention1813.ProfilesValid := by
  exact MergedCutProfiles.Batch288.valid11542
theorem numericValid1813 : retention1813.NumericValid := by decide +kernel
def certificate1813 : RatCutBinCertificate := ⟨⟨retention1813,(33906138117166049/12500000000000000),(57064330308281523/250000000000000000),(8835637598779032713/500000000000000000),(176606313810354852443/1000000000000000000),(47511008410553141/50000000000000000)⟩,(988087120478718677/1000000000000000000),(40083280782232811/100000000000000000),(116360084429828397/500000000000000000),(42825882598726069/250000000000000000)⟩
theorem valid1813 : certificate1813.Valid := by decide +kernel
theorem sound1813 : certificate1813.Sound := rat_cut_bin_certificate_sound certificate1813 profilesValid1813 numericValid1813 valid1813

def retention1814 : RatCutRetentionCertificate := ⟨(527/8000),(33/500),(654649774497752654/4970158454520361661),(906041704285818243/1000000000000000000),(49/20),(579140343686796271429/320000000000000000000),true,MergedCutProfiles.Batch288.profile11546,![MergedCutProfiles.Batch288.profile11546,MergedCutProfiles.Batch288.profile11547,MergedCutProfiles.Batch288.profile11548,MergedCutProfiles.Batch288.profile11549,MergedCutProfiles.Batch288.profile11550,MergedCutProfiles.Batch288.profile11551,MergedCutProfiles.Batch288.profile11552,MergedCutProfiles.Batch288.profile11553,MergedCutProfiles.Batch288.profile11554,MergedCutProfiles.Batch288.profile11555,MergedCutProfiles.Batch288.profile11556,MergedCutProfiles.Batch288.profile11557,MergedCutProfiles.Batch288.profile11558,MergedCutProfiles.Batch288.profile11559,MergedCutProfiles.Batch289.profile11560,MergedCutProfiles.Batch289.profile11561]⟩
theorem profilesValid1814 : retention1814.ProfilesValid := by
  change ∀ j : Fin 16, (retention1814.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch288.valid11546
  · exact MergedCutProfiles.Batch288.valid11547
  · exact MergedCutProfiles.Batch288.valid11548
  · exact MergedCutProfiles.Batch288.valid11549
  · exact MergedCutProfiles.Batch288.valid11550
  · exact MergedCutProfiles.Batch288.valid11551
  · exact MergedCutProfiles.Batch288.valid11552
  · exact MergedCutProfiles.Batch288.valid11553
  · exact MergedCutProfiles.Batch288.valid11554
  · exact MergedCutProfiles.Batch288.valid11555
  · exact MergedCutProfiles.Batch288.valid11556
  · exact MergedCutProfiles.Batch288.valid11557
  · exact MergedCutProfiles.Batch288.valid11558
  · exact MergedCutProfiles.Batch288.valid11559
  · exact MergedCutProfiles.Batch289.valid11560
  · exact MergedCutProfiles.Batch289.valid11561
theorem numericValid1814 : retention1814.NumericValid := by decide +kernel
def certificate1814 : RatCutBinCertificate := ⟨⟨retention1814,(601004780592031847/250000000000000000),(229314578619222081/1000000000000000000),(2214252168013179003/125000000000000000),(176223244068692845303/1000000000000000000),(1733522607634653973/1000000000000000000)⟩,(494718659837167121/500000000000000000),(166474292617178459/500000000000000000),(150438052813517011/500000000000000000),(39835891655374023/250000000000000000)⟩
theorem valid1814 : certificate1814.Valid := by decide +kernel
theorem sound1814 : certificate1814.Sound := rat_cut_bin_certificate_sound certificate1814 profilesValid1814 numericValid1814 valid1814

def retention1815 : RatCutRetentionCertificate := ⟨(527/8000),(33/500),(2627454373180777011/9940316909040723322),(327324887248876327/250000000000000000),(9/5),(473115169270684143963/320000000000000000000),true,MergedCutProfiles.Batch289.profile11562,![MergedCutProfiles.Batch289.profile11562,MergedCutProfiles.Batch289.profile11563,MergedCutProfiles.Batch288.profile11551,MergedCutProfiles.Batch289.profile11564,MergedCutProfiles.Batch289.profile11565,MergedCutProfiles.Batch289.profile11566,MergedCutProfiles.Batch289.profile11567,MergedCutProfiles.Batch289.profile11568,MergedCutProfiles.Batch289.profile11569,MergedCutProfiles.Batch289.profile11570,MergedCutProfiles.Batch289.profile11571,MergedCutProfiles.Batch289.profile11572,MergedCutProfiles.Batch289.profile11573,MergedCutProfiles.Batch289.profile11574,MergedCutProfiles.Batch289.profile11575,MergedCutProfiles.Batch289.profile11576]⟩
theorem profilesValid1815 : retention1815.ProfilesValid := by
  change ∀ j : Fin 16, (retention1815.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch289.valid11562
  · exact MergedCutProfiles.Batch289.valid11563
  · exact MergedCutProfiles.Batch288.valid11551
  · exact MergedCutProfiles.Batch289.valid11564
  · exact MergedCutProfiles.Batch289.valid11565
  · exact MergedCutProfiles.Batch289.valid11566
  · exact MergedCutProfiles.Batch289.valid11567
  · exact MergedCutProfiles.Batch289.valid11568
  · exact MergedCutProfiles.Batch289.valid11569
  · exact MergedCutProfiles.Batch289.valid11570
  · exact MergedCutProfiles.Batch289.valid11571
  · exact MergedCutProfiles.Batch289.valid11572
  · exact MergedCutProfiles.Batch289.valid11573
  · exact MergedCutProfiles.Batch289.valid11574
  · exact MergedCutProfiles.Batch289.valid11575
  · exact MergedCutProfiles.Batch289.valid11576
theorem numericValid1815 : retention1815.NumericValid := by decide +kernel
def certificate1815 : RatCutBinCertificate := ⟨⟨retention1815,(601004780592031847/250000000000000000),(229314578619222081/1000000000000000000),(2214252168013179003/125000000000000000),(176223244068692845303/1000000000000000000),(1422436306098938731/1000000000000000000)⟩,(494718659837167121/500000000000000000),(22440741629416047/62500000000000000),(273170972358771123/1000000000000000000),(159599125637293077/1000000000000000000)⟩
theorem valid1815 : certificate1815.Valid := by decide +kernel
theorem sound1815 : certificate1815.Sound := rat_cut_bin_certificate_sound certificate1815 profilesValid1815 numericValid1815 valid1815

def retention1816 : RatCutRetentionCertificate := ⟨(527/8000),(33/500),(4278410962946510967/9940316909040723322),(2627454373180777011/1000000000000000000),(23/20),(1415332945117335390387/1280000000000000000000),true,MergedCutProfiles.Batch289.profile11577,![MergedCutProfiles.Batch289.profile11577,MergedCutProfiles.Batch289.profile11578,MergedCutProfiles.Batch289.profile11579,MergedCutProfiles.Batch289.profile11580,MergedCutProfiles.Batch289.profile11581,MergedCutProfiles.Batch289.profile11582,MergedCutProfiles.Batch289.profile11583,MergedCutProfiles.Batch289.profile11584,MergedCutProfiles.Batch289.profile11585,MergedCutProfiles.Batch289.profile11586,MergedCutProfiles.Batch289.profile11587,MergedCutProfiles.Batch289.profile11588,MergedCutProfiles.Batch289.profile11589,MergedCutProfiles.Batch289.profile11590,MergedCutProfiles.Batch289.profile11591,MergedCutProfiles.Batch289.profile11592]⟩
theorem profilesValid1816 : retention1816.ProfilesValid := by
  change ∀ j : Fin 16, (retention1816.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch289.valid11577
  · exact MergedCutProfiles.Batch289.valid11578
  · exact MergedCutProfiles.Batch289.valid11579
  · exact MergedCutProfiles.Batch289.valid11580
  · exact MergedCutProfiles.Batch289.valid11581
  · exact MergedCutProfiles.Batch289.valid11582
  · exact MergedCutProfiles.Batch289.valid11583
  · exact MergedCutProfiles.Batch289.valid11584
  · exact MergedCutProfiles.Batch289.valid11585
  · exact MergedCutProfiles.Batch289.valid11586
  · exact MergedCutProfiles.Batch289.valid11587
  · exact MergedCutProfiles.Batch289.valid11588
  · exact MergedCutProfiles.Batch289.valid11589
  · exact MergedCutProfiles.Batch289.valid11590
  · exact MergedCutProfiles.Batch289.valid11591
  · exact MergedCutProfiles.Batch289.valid11592
theorem numericValid1816 : retention1816.NumericValid := by decide +kernel
def certificate1816 : RatCutBinCertificate := ⟨⟨retention1816,(601004780592031847/250000000000000000),(229314578619222081/1000000000000000000),(2214252168013179003/125000000000000000),(176223244068692845303/1000000000000000000),(106992438493011049/100000000000000000)⟩,(494718659837167121/500000000000000000),(407348234135008263/1000000000000000000),(2835207498642897/12500000000000000),(159355955916027141/1000000000000000000)⟩
theorem valid1816 : certificate1816.Valid := by decide +kernel
theorem sound1816 : certificate1816.Sound := rat_cut_bin_certificate_sound certificate1816 profilesValid1816 numericValid1816 valid1816

def retention1817 : RatCutRetentionCertificate := ⟨(527/8000),(33/500),(2410510281119575907/4970158454520361661),(4278410962946510967/1000000000000000000),1,(251661122286179782887/256000000000000000000),true,MergedCutProfiles.Batch289.profile11593,![MergedCutProfiles.Batch289.profile11593,MergedCutProfiles.Batch289.profile11594,MergedCutProfiles.Batch289.profile11595,MergedCutProfiles.Batch289.profile11596,MergedCutProfiles.Batch289.profile11597,MergedCutProfiles.Batch289.profile11571,MergedCutProfiles.Batch289.profile11598,MergedCutProfiles.Batch289.profile11599,MergedCutProfiles.Batch290.profile11600,MergedCutProfiles.Batch290.profile11601,MergedCutProfiles.Batch290.profile11602,MergedCutProfiles.Batch290.profile11603,MergedCutProfiles.Batch290.profile11604,MergedCutProfiles.Batch290.profile11605,MergedCutProfiles.Batch290.profile11606,MergedCutProfiles.Batch290.profile11607]⟩
theorem profilesValid1817 : retention1817.ProfilesValid := by
  change ∀ j : Fin 16, (retention1817.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch289.valid11593
  · exact MergedCutProfiles.Batch289.valid11594
  · exact MergedCutProfiles.Batch289.valid11595
  · exact MergedCutProfiles.Batch289.valid11596
  · exact MergedCutProfiles.Batch289.valid11597
  · exact MergedCutProfiles.Batch289.valid11571
  · exact MergedCutProfiles.Batch289.valid11598
  · exact MergedCutProfiles.Batch289.valid11599
  · exact MergedCutProfiles.Batch290.valid11600
  · exact MergedCutProfiles.Batch290.valid11601
  · exact MergedCutProfiles.Batch290.valid11602
  · exact MergedCutProfiles.Batch290.valid11603
  · exact MergedCutProfiles.Batch290.valid11604
  · exact MergedCutProfiles.Batch290.valid11605
  · exact MergedCutProfiles.Batch290.valid11606
  · exact MergedCutProfiles.Batch290.valid11607
theorem numericValid1817 : retention1817.NumericValid := by decide +kernel
def certificate1817 : RatCutBinCertificate := ⟨⟨retention1817,(601004780592031847/250000000000000000),(229314578619222081/1000000000000000000),(2214252168013179003/125000000000000000),(176223244068692845303/1000000000000000000),(951920867026538827/1000000000000000000)⟩,(494718659837167121/500000000000000000),(427687657216926461/1000000000000000000),(41810015059392123/200000000000000000),(160845474207022819/1000000000000000000)⟩
theorem valid1817 : certificate1817.Valid := by decide +kernel
theorem sound1817 : certificate1817.Sound := rat_cut_bin_certificate_sound certificate1817 profilesValid1817 numericValid1817 valid1817

def retention1818 : RatCutRetentionCertificate := ⟨(527/8000),(33/500),(4917923075540158767/9940316909040723322),(2410510281119575907/500000000000000000),(11/10),(480949870058094839574063525604290962311/482102056223915181400000000000000000000),false,MergedCutProfiles.Batch290.profile11608,(fun _ => MergedCutProfiles.Batch290.profile11608)⟩
theorem profilesValid1818 : retention1818.ProfilesValid := by
  exact MergedCutProfiles.Batch290.valid11608
theorem numericValid1818 : retention1818.NumericValid := by decide +kernel
def certificate1818 : RatCutBinCertificate := ⟨⟨retention1818,(601004780592031847/250000000000000000),(229314578619222081/1000000000000000000),(2214252168013179003/125000000000000000),(176223244068692845303/1000000000000000000),(481684329540788807/500000000000000000)⟩,(494718659837167121/500000000000000000),(83453568189620081/200000000000000000),(109014012769015907/500000000000000000),(161966719653214073/1000000000000000000)⟩
theorem valid1818 : certificate1818.Valid := by decide +kernel
theorem sound1818 : certificate1818.Sound := rat_cut_bin_certificate_sound certificate1818 profilesValid1818 numericValid1818 valid1818

def retention1819 : RatCutRetentionCertificate := ⟨(527/8000),(33/500),(4967102306295560355/9940316909040723322),(4917923075540158767/1000000000000000000),(11/10),(1945559565967815663226416449760171966551/1967169230216063506800000000000000000000),false,MergedCutProfiles.Batch290.profile11609,(fun _ => MergedCutProfiles.Batch290.profile11609)⟩
theorem profilesValid1819 : retention1819.ProfilesValid := by
  exact MergedCutProfiles.Batch290.valid11609
theorem numericValid1819 : retention1819.NumericValid := by decide +kernel
def certificate1819 : RatCutBinCertificate := ⟨⟨retention1819,(601004780592031847/250000000000000000),(229314578619222081/1000000000000000000),(2214252168013179003/125000000000000000),(176223244068692845303/1000000000000000000),(190954717715948373/200000000000000000)⟩,(494718659837167121/500000000000000000),(420187445807024649/1000000000000000000),(107743235691370541/500000000000000000),(19911957755006143/125000000000000000)⟩
theorem valid1819 : certificate1819.Valid := by decide +kernel
theorem sound1819 : certificate1819.Sound := rat_cut_bin_certificate_sound certificate1819 profilesValid1819 numericValid1819 valid1819

def retention1820 : RatCutRetentionCertificate := ⟨(527/8000),(33/500),(1/2),(993420461259112071/200000000000000000),(11/10),(26194851681838783104275463530388549333/26491212300242988560000000000000000000),false,MergedCutProfiles.Batch290.profile11610,(fun _ => MergedCutProfiles.Batch290.profile11610)⟩
theorem profilesValid1820 : retention1820.ProfilesValid := by
  exact MergedCutProfiles.Batch290.valid11610
theorem numericValid1820 : retention1820.NumericValid := by decide +kernel
def certificate1820 : RatCutBinCertificate := ⟨⟨retention1820,(601004780592031847/250000000000000000),(229314578619222081/1000000000000000000),(2214252168013179003/125000000000000000),(176223244068692845303/1000000000000000000),(95457169848490203/100000000000000000)⟩,(494718659837167121/500000000000000000),(419864066962957969/1000000000000000000),(53941743891056141/250000000000000000),(159694049288635063/1000000000000000000)⟩
theorem valid1820 : certificate1820.Valid := by decide +kernel
theorem sound1820 : certificate1820.Sound := rat_cut_bin_certificate_sound certificate1820 profilesValid1820 numericValid1820 valid1820

def retention1821 : RatCutRetentionCertificate := ⟨(527/8000),(33/500),(1/2),64,1,(15963618519455286490294148889200821479/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch290.profile11610,(fun _ => MergedCutProfiles.Batch290.profile11610)⟩
theorem profilesValid1821 : retention1821.ProfilesValid := by
  exact MergedCutProfiles.Batch290.valid11610
theorem numericValid1821 : retention1821.NumericValid := by decide +kernel
def certificate1821 : RatCutBinCertificate := ⟨⟨retention1821,(601004780592031847/250000000000000000),(229314578619222081/1000000000000000000),(2214252168013179003/125000000000000000),(176223244068692845303/1000000000000000000),(966604598188771071/1000000000000000000)⟩,(494718659837167121/500000000000000000),(377085424057371311/1000000000000000000),(6378667787845603/25000000000000000),(2403642576091563/10000000000000000)⟩
theorem valid1821 : certificate1821.Valid := by decide +kernel
theorem sound1821 : certificate1821.Sound := rat_cut_bin_certificate_sound certificate1821 profilesValid1821 numericValid1821 valid1821

def retention1822 : RatCutRetentionCertificate := ⟨(527/8000),(33/500),(2302563474236422064/4970158454520361661),(735732253344838369/250000000000000000),(5/4),(12546711911824912481257320479044467311/11771716053517413904000000000000000000),false,MergedCutProfiles.Batch290.profile11611,(fun _ => MergedCutProfiles.Batch290.profile11611)⟩
theorem profilesValid1822 : retention1822.ProfilesValid := by
  exact MergedCutProfiles.Batch290.valid11611
theorem numericValid1822 : retention1822.NumericValid := by decide +kernel
def certificate1822 : RatCutBinCertificate := ⟨⟨retention1822,(678545036092031847/250000000000000000),(229314578619222081/1000000000000000000),(2214252168013179003/125000000000000000),(176223244068692845303/1000000000000000000),(204379957341205211/200000000000000000)⟩,(197613948362196651/200000000000000000),(37146781471193271/100000000000000000),(65166762904711573/250000000000000000),(86001919293403111/500000000000000000)⟩
theorem valid1822 : certificate1822.Valid := by decide +kernel
theorem sound1822 : certificate1822.Sound := rat_cut_bin_certificate_sound certificate1822 profilesValid1822 numericValid1822 valid1822

def retention1823 : RatCutRetentionCertificate := ⟨(527/8000),(33/500),(2444217525939808534/4970158454520361661),(143910217139776379/31250000000000000),(11/10),(1801136519077018690001124126392865839/1798877714247204737500000000000000000),false,MergedCutProfiles.Batch290.profile11612,(fun _ => MergedCutProfiles.Batch290.profile11612)⟩
theorem profilesValid1823 : retention1823.ProfilesValid := by
  exact MergedCutProfiles.Batch290.valid11612
theorem numericValid1823 : retention1823.NumericValid := by decide +kernel
def certificate1823 : RatCutBinCertificate := ⟨⟨retention1823,(678545036092031847/250000000000000000),(229314578619222081/1000000000000000000),(2214252168013179003/125000000000000000),(176223244068692845303/1000000000000000000),(96259606143476133/100000000000000000)⟩,(197613948362196651/200000000000000000),(197176622588957437/500000000000000000),(238696228699374091/1000000000000000000),(87889011877594557/500000000000000000)⟩
theorem valid1823 : certificate1823.Valid := by decide +kernel
theorem sound1823 : certificate1823.Sound := rat_cut_bin_certificate_sound certificate1823 profilesValid1823 numericValid1823 valid1823

def certificates : List RatCutBinCertificate := [certificate1812,certificate1813,certificate1814,certificate1815,certificate1816,certificate1817,certificate1818,certificate1819,certificate1820,certificate1821,certificate1822,certificate1823]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1812,List.forall_mem_cons.mpr ⟨sound1813,List.forall_mem_cons.mpr ⟨sound1814,List.forall_mem_cons.mpr ⟨sound1815,List.forall_mem_cons.mpr ⟨sound1816,List.forall_mem_cons.mpr ⟨sound1817,List.forall_mem_cons.mpr ⟨sound1818,List.forall_mem_cons.mpr ⟨sound1819,List.forall_mem_cons.mpr ⟨sound1820,List.forall_mem_cons.mpr ⟨sound1821,List.forall_mem_cons.mpr ⟨sound1822,List.forall_mem_cons.mpr ⟨sound1823,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch151
