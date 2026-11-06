import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch142
import Cycle12.MergedCutProfiles.Batch143
import Cycle12.MergedCutProfiles.Batch144

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch070

def retention840 : RatCutRetentionCertificate := ⟨(97/2000),(39/800),(4324803380362535572/20212032053131816613),(1404918496865362181/1000000000000000000),(39/20),(2049521292300539432661/1280000000000000000000),true,MergedCutProfiles.Batch142.profile5694,![MergedCutProfiles.Batch142.profile5694,MergedCutProfiles.Batch142.profile5695,MergedCutProfiles.Batch142.profile5696,MergedCutProfiles.Batch142.profile5697,MergedCutProfiles.Batch142.profile5698,MergedCutProfiles.Batch142.profile5699,MergedCutProfiles.Batch142.profile5700,MergedCutProfiles.Batch142.profile5701,MergedCutProfiles.Batch142.profile5702,MergedCutProfiles.Batch142.profile5703,MergedCutProfiles.Batch142.profile5704,MergedCutProfiles.Batch142.profile5705,MergedCutProfiles.Batch142.profile5706,MergedCutProfiles.Batch142.profile5707,MergedCutProfiles.Batch142.profile5708,MergedCutProfiles.Batch142.profile5709]⟩
theorem profilesValid840 : retention840.ProfilesValid := by
  change ∀ j : Fin 16, (retention840.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch142.valid5694
  · exact MergedCutProfiles.Batch142.valid5695
  · exact MergedCutProfiles.Batch142.valid5696
  · exact MergedCutProfiles.Batch142.valid5697
  · exact MergedCutProfiles.Batch142.valid5698
  · exact MergedCutProfiles.Batch142.valid5699
  · exact MergedCutProfiles.Batch142.valid5700
  · exact MergedCutProfiles.Batch142.valid5701
  · exact MergedCutProfiles.Batch142.valid5702
  · exact MergedCutProfiles.Batch142.valid5703
  · exact MergedCutProfiles.Batch142.valid5704
  · exact MergedCutProfiles.Batch142.valid5705
  · exact MergedCutProfiles.Batch142.valid5706
  · exact MergedCutProfiles.Batch142.valid5707
  · exact MergedCutProfiles.Batch142.valid5708
  · exact MergedCutProfiles.Batch142.valid5709
theorem numericValid840 : retention840.NumericValid := by decide +kernel
def certificate840 : RatCutBinCertificate := ⟨⟨retention840,(430671974922658799/200000000000000000),(5654114764730837/50000000000000000),(12992805386102834049/1000000000000000000),(131491975698769558831/500000000000000000),(1564636515987970243/1000000000000000000)⟩,(992720273333164311/1000000000000000000),(101276866738027567/250000000000000000),(228835101652681/1000000000000000),(35203621074662909/250000000000000000)⟩
theorem valid840 : certificate840.Valid := by decide +kernel
theorem sound840 : certificate840.Sound := rat_cut_bin_certificate_sound certificate840 profilesValid840 numericValid840 valid840

def retention841 : RatCutRetentionCertificate := ⟨(97/2000),(39/800),(8853302024908467499/20212032053131816613),(1081200845090633893/250000000000000000),(11/10),(351858409064269109209/320000000000000000000),true,MergedCutProfiles.Batch142.profile5710,![MergedCutProfiles.Batch142.profile5710,MergedCutProfiles.Batch142.profile5711,MergedCutProfiles.Batch142.profile5712,MergedCutProfiles.Batch142.profile5713,MergedCutProfiles.Batch142.profile5714,MergedCutProfiles.Batch142.profile5715,MergedCutProfiles.Batch142.profile5716,MergedCutProfiles.Batch142.profile5717,MergedCutProfiles.Batch142.profile5718,MergedCutProfiles.Batch142.profile5719,MergedCutProfiles.Batch143.profile5720,MergedCutProfiles.Batch143.profile5721,MergedCutProfiles.Batch143.profile5722,MergedCutProfiles.Batch143.profile5723,MergedCutProfiles.Batch143.profile5724,MergedCutProfiles.Batch143.profile5725]⟩
theorem profilesValid841 : retention841.ProfilesValid := by
  change ∀ j : Fin 16, (retention841.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch142.valid5710
  · exact MergedCutProfiles.Batch142.valid5711
  · exact MergedCutProfiles.Batch142.valid5712
  · exact MergedCutProfiles.Batch142.valid5713
  · exact MergedCutProfiles.Batch142.valid5714
  · exact MergedCutProfiles.Batch142.valid5715
  · exact MergedCutProfiles.Batch142.valid5716
  · exact MergedCutProfiles.Batch142.valid5717
  · exact MergedCutProfiles.Batch142.valid5718
  · exact MergedCutProfiles.Batch142.valid5719
  · exact MergedCutProfiles.Batch143.valid5720
  · exact MergedCutProfiles.Batch143.valid5721
  · exact MergedCutProfiles.Batch143.valid5722
  · exact MergedCutProfiles.Batch143.valid5723
  · exact MergedCutProfiles.Batch143.valid5724
  · exact MergedCutProfiles.Batch143.valid5725
theorem numericValid841 : retention841.NumericValid := by decide +kernel
def certificate841 : RatCutBinCertificate := ⟨⟨retention841,(430671974922658799/200000000000000000),(5654114764730837/50000000000000000),(12992805386102834049/1000000000000000000),(131491975698769558831/500000000000000000),(107893982738762357/100000000000000000)⟩,(992720273333164311/1000000000000000000),(2348958072398703/5000000000000000),(21912077855202323/125000000000000000),(141406933787161063/1000000000000000000)⟩
theorem valid841 : certificate841.Valid := by decide +kernel
theorem sound841 : certificate841.Sound := rat_cut_bin_certificate_sound certificate841 profilesValid841 numericValid841 valid841

def retention842 : RatCutRetentionCertificate := ⟨(97/2000),(39/800),(9976122320984912437/20212032053131816613),(8853302024908467499/1000000000000000000),(21/20),(14238919830483324161767305628425536933679/14165283239853547998400000000000000000000),false,MergedCutProfiles.Batch143.profile5726,(fun _ => MergedCutProfiles.Batch143.profile5726)⟩
theorem profilesValid842 : retention842.ProfilesValid := by
  exact MergedCutProfiles.Batch143.valid5726
theorem numericValid842 : retention842.NumericValid := by decide +kernel
def certificate842 : RatCutBinCertificate := ⟨⟨retention842,(430671974922658799/200000000000000000),(5654114764730837/50000000000000000),(12992805386102834049/1000000000000000000),(131491975698769558831/500000000000000000),(985518720351958969/1000000000000000000)⟩,(992720273333164311/1000000000000000000),(241308537853610793/500000000000000000),(165780971333476469/1000000000000000000),(140243246930836361/1000000000000000000)⟩
theorem valid842 : certificate842.Valid := by decide +kernel
theorem sound842 : certificate842.Sound := rat_cut_bin_certificate_sound certificate842 profilesValid842 numericValid842 valid842

def retention843 : RatCutRetentionCertificate := ⟨(97/2000),(39/800),(10075883544194761562/20212032053131816613),(9976122320984912437/1000000000000000000),(21/20),(15931853276260579537497169519474317947351/15961795713575859899200000000000000000000),false,MergedCutProfiles.Batch143.profile5727,(fun _ => MergedCutProfiles.Batch143.profile5727)⟩
theorem profilesValid843 : retention843.ProfilesValid := by
  exact MergedCutProfiles.Batch143.valid5727
theorem numericValid843 : retention843.NumericValid := by decide +kernel
def certificate843 : RatCutBinCertificate := ⟨⟨retention843,(430671974922658799/200000000000000000),(5654114764730837/50000000000000000),(12992805386102834049/1000000000000000000),(131491975698769558831/500000000000000000),(489222278337186501/500000000000000000)⟩,(992720273333164311/1000000000000000000),(482673537588714729/1000000000000000000),(2589685008512881/15625000000000000),(70371456748167123/500000000000000000)⟩
theorem valid843 : certificate843.Valid := by decide +kernel
theorem sound843 : certificate843.Sound := rat_cut_bin_certificate_sound certificate843 profilesValid843 numericValid843 valid843

def retention844 : RatCutRetentionCertificate := ⟨(97/2000),(39/800),(1/2),(5037941772097380781/500000000000000000),(21/20),(4011811139741599831716237809921645884479/4030353417677904624800000000000000000000),false,MergedCutProfiles.Batch143.profile5728,(fun _ => MergedCutProfiles.Batch143.profile5728)⟩
theorem profilesValid844 : retention844.ProfilesValid := by
  exact MergedCutProfiles.Batch143.valid5728
theorem numericValid844 : retention844.NumericValid := by decide +kernel
def certificate844 : RatCutBinCertificate := ⟨⟨retention844,(430671974922658799/200000000000000000),(5654114764730837/50000000000000000),(12992805386102834049/1000000000000000000),(131491975698769558831/500000000000000000),(975719788114230309/1000000000000000000)⟩,(992720273333164311/1000000000000000000),(241876346485548977/500000000000000000),(82477488364038733/500000000000000000),(139831399256363859/1000000000000000000)⟩
theorem valid844 : certificate844.Valid := by decide +kernel
theorem sound844 : certificate844.Sound := rat_cut_bin_certificate_sound certificate844 profilesValid844 numericValid844 valid844

def retention845 : RatCutRetentionCertificate := ⟨(97/2000),(39/800),(9045688692517446250/20212032053131816613),(3694179525647318741/1000000000000000000),(6/5),(36880821320139882472808068119826931269/33583450233157443100000000000000000000),false,MergedCutProfiles.Batch143.profile5729,(fun _ => MergedCutProfiles.Batch143.profile5729)⟩
theorem profilesValid845 : retention845.ProfilesValid := by
  exact MergedCutProfiles.Batch143.valid5729
theorem numericValid845 : retention845.NumericValid := by decide +kernel
def certificate845 : RatCutBinCertificate := ⟨⟨retention845,(505212859322658799/200000000000000000),(5654114764730837/50000000000000000),(12992805386102834049/1000000000000000000),(131491975698769558831/500000000000000000),(1071799262239460579/1000000000000000000)⟩,(991458941172001509/1000000000000000000),(190424004258138161/500000000000000000),(62874028334019517/250000000000000000),(92607008922398473/500000000000000000)⟩
theorem valid845 : certificate845.Valid := by decide +kernel
theorem sound845 : certificate845.Sound := rat_cut_bin_certificate_sound certificate845 profilesValid845 numericValid845 valid845

def retention846 : RatCutRetentionCertificate := ⟨(97/2000),(39/800),(9992067869336721068/20212032053131816613),(7236550954013957/800000000000000),(21/20),(145333483887650954333174114659030729671/144731019080279140000000000000000000000),false,MergedCutProfiles.Batch143.profile5730,(fun _ => MergedCutProfiles.Batch143.profile5730)⟩
theorem profilesValid846 : retention846.ProfilesValid := by
  exact MergedCutProfiles.Batch143.valid5730
theorem numericValid846 : retention846.NumericValid := by decide +kernel
def certificate846 : RatCutBinCertificate := ⟨⟨retention846,(505212859322658799/200000000000000000),(5654114764730837/50000000000000000),(12992805386102834049/1000000000000000000),(131491975698769558831/500000000000000000),(196215369111821167/200000000000000000)⟩,(991458941172001509/1000000000000000000),(104016473429379503/250000000000000000),(219080262517453151/1000000000000000000),(184698651062919923/1000000000000000000)⟩
theorem valid846 : certificate846.Valid := by decide +kernel
theorem sound846 : certificate846.Sound := rat_cut_bin_certificate_sound certificate846 profilesValid846 numericValid846 valid846

def retention847 : RatCutRetentionCertificate := ⟨(97/2000),(39/800),(593646385178240487/1188943061948930389),(2498016967334180267/250000000000000000),(21/20),(7779748201873314481957673951190286347/7806303022919313334375000000000000000),false,MergedCutProfiles.Batch143.profile5731,(fun _ => MergedCutProfiles.Batch143.profile5731)⟩
theorem profilesValid847 : retention847.ProfilesValid := by
  exact MergedCutProfiles.Batch143.valid5731
theorem numericValid847 : retention847.NumericValid := by decide +kernel
def certificate847 : RatCutBinCertificate := ⟨⟨retention847,(505212859322658799/200000000000000000),(5654114764730837/50000000000000000),(12992805386102834049/1000000000000000000),(131491975698769558831/500000000000000000),(973512577570519491/1000000000000000000)⟩,(991458941172001509/1000000000000000000),(419298757877161609/1000000000000000000),(21625793227041119/100000000000000000),(91291443856206689/500000000000000000)⟩
theorem valid847 : certificate847.Valid := by decide +kernel
theorem sound847 : certificate847.Sound := rat_cut_bin_certificate_sound certificate847 profilesValid847 numericValid847 valid847

def retention848 : RatCutRetentionCertificate := ⟨(97/2000),(39/800),(1/2),(10091988548030088279/1000000000000000000),(21/20),(16073372811556475728866043675168690423679/16147181676848141246400000000000000000000),false,MergedCutProfiles.Batch143.profile5728,(fun _ => MergedCutProfiles.Batch143.profile5728)⟩
theorem profilesValid848 : retention848.ProfilesValid := by
  exact MergedCutProfiles.Batch143.valid5728
theorem numericValid848 : retention848.NumericValid := by decide +kernel
def certificate848 : RatCutBinCertificate := ⟨⟨retention848,(505212859322658799/200000000000000000),(5654114764730837/50000000000000000),(12992805386102834049/1000000000000000000),(131491975698769558831/500000000000000000),(486171648128666521/500000000000000000)⟩,(991458941172001509/1000000000000000000),(13118843163607169/31250000000000000),(215819990293073063/1000000000000000000),(182158926514236617/1000000000000000000)⟩
theorem valid848 : certificate848.Valid := by decide +kernel
theorem sound848 : certificate848.Sound := rat_cut_bin_certificate_sound certificate848 profilesValid848 numericValid848 valid848

def retention849 : RatCutRetentionCertificate := ⟨(39/800),(49/1000),(213099373801036157/4994473862089329628),(26373684876365861/31250000000000000),(29/10),(41523874284698768779/20000000000000000000),true,MergedCutProfiles.Batch143.profile5732,![MergedCutProfiles.Batch143.profile5732,MergedCutProfiles.Batch143.profile5733,MergedCutProfiles.Batch143.profile5734,MergedCutProfiles.Batch143.profile5735,MergedCutProfiles.Batch143.profile5736,MergedCutProfiles.Batch143.profile5737,MergedCutProfiles.Batch143.profile5738,MergedCutProfiles.Batch143.profile5739,MergedCutProfiles.Batch143.profile5740,MergedCutProfiles.Batch143.profile5741,MergedCutProfiles.Batch143.profile5742,MergedCutProfiles.Batch143.profile5743,MergedCutProfiles.Batch143.profile5744,MergedCutProfiles.Batch143.profile5745,MergedCutProfiles.Batch143.profile5746,MergedCutProfiles.Batch143.profile5747]⟩
theorem profilesValid849 : retention849.ProfilesValid := by
  change ∀ j : Fin 16, (retention849.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch143.valid5732
  · exact MergedCutProfiles.Batch143.valid5733
  · exact MergedCutProfiles.Batch143.valid5734
  · exact MergedCutProfiles.Batch143.valid5735
  · exact MergedCutProfiles.Batch143.valid5736
  · exact MergedCutProfiles.Batch143.valid5737
  · exact MergedCutProfiles.Batch143.valid5738
  · exact MergedCutProfiles.Batch143.valid5739
  · exact MergedCutProfiles.Batch143.valid5740
  · exact MergedCutProfiles.Batch143.valid5741
  · exact MergedCutProfiles.Batch143.valid5742
  · exact MergedCutProfiles.Batch143.valid5743
  · exact MergedCutProfiles.Batch143.valid5744
  · exact MergedCutProfiles.Batch143.valid5745
  · exact MergedCutProfiles.Batch143.valid5746
  · exact MergedCutProfiles.Batch143.valid5747
theorem numericValid849 : retention849.NumericValid := by decide +kernel
def certificate849 : RatCutBinCertificate := ⟨⟨retention849,(2148772030523085131/1000000000000000000),(114392751307786871/1000000000000000000),(815404404890926431/62500000000000000),(130505885730980550373/500000000000000000),(101077302704273487/50000000000000000)⟩,(248172873573857223/250000000000000000),(373581479338245109/1000000000000000000),(258580093816392539/1000000000000000000),(139078627511827257/1000000000000000000)⟩
theorem valid849 : certificate849.Valid := by decide +kernel
theorem sound849 : certificate849.Sound := rat_cut_bin_certificate_sound certificate849 profilesValid849 numericValid849 valid849

def retention850 : RatCutRetentionCertificate := ⟨(39/800),(49/1000),(461512171771193631/9988947724178659256),(213099373801036157/250000000000000000),(29/10),(662342048698311331717/320000000000000000000),true,MergedCutProfiles.Batch143.profile5748,![MergedCutProfiles.Batch143.profile5748,MergedCutProfiles.Batch143.profile5749,MergedCutProfiles.Batch143.profile5750,MergedCutProfiles.Batch143.profile5751,MergedCutProfiles.Batch143.profile5752,MergedCutProfiles.Batch143.profile5753,MergedCutProfiles.Batch143.profile5754,MergedCutProfiles.Batch143.profile5755,MergedCutProfiles.Batch143.profile5756,MergedCutProfiles.Batch143.profile5757,MergedCutProfiles.Batch143.profile5758,MergedCutProfiles.Batch143.profile5744,MergedCutProfiles.Batch143.profile5759,MergedCutProfiles.Batch144.profile5760,MergedCutProfiles.Batch144.profile5761,MergedCutProfiles.Batch144.profile5762]⟩
theorem profilesValid850 : retention850.ProfilesValid := by
  change ∀ j : Fin 16, (retention850.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch143.valid5748
  · exact MergedCutProfiles.Batch143.valid5749
  · exact MergedCutProfiles.Batch143.valid5750
  · exact MergedCutProfiles.Batch143.valid5751
  · exact MergedCutProfiles.Batch143.valid5752
  · exact MergedCutProfiles.Batch143.valid5753
  · exact MergedCutProfiles.Batch143.valid5754
  · exact MergedCutProfiles.Batch143.valid5755
  · exact MergedCutProfiles.Batch143.valid5756
  · exact MergedCutProfiles.Batch143.valid5757
  · exact MergedCutProfiles.Batch143.valid5758
  · exact MergedCutProfiles.Batch143.valid5744
  · exact MergedCutProfiles.Batch143.valid5759
  · exact MergedCutProfiles.Batch144.valid5760
  · exact MergedCutProfiles.Batch144.valid5761
  · exact MergedCutProfiles.Batch144.valid5762
theorem numericValid850 : retention850.NumericValid := by decide +kernel
def certificate850 : RatCutBinCertificate := ⟨⟨retention850,(2148772030523085131/1000000000000000000),(114392751307786871/1000000000000000000),(815404404890926431/62500000000000000),(130505885730980550373/500000000000000000),(1007585669451684779/500000000000000000)⟩,(248172873573857223/250000000000000000),(186623058304362557/500000000000000000),(258910419926560701/1000000000000000000),(139220423538967687/1000000000000000000)⟩
theorem valid850 : certificate850.Valid := by decide +kernel
theorem sound850 : certificate850.Sound := rat_cut_bin_certificate_sound certificate850 profilesValid850 numericValid850 valid850

def retention851 : RatCutRetentionCertificate := ⟨(39/800),(49/1000),(375751289041180575/4994473862089329628),(461512171771193631/500000000000000000),(27/10),(316069162947189110723/160000000000000000000),true,MergedCutProfiles.Batch144.profile5763,![MergedCutProfiles.Batch144.profile5763,MergedCutProfiles.Batch144.profile5764,MergedCutProfiles.Batch144.profile5765,MergedCutProfiles.Batch144.profile5766,MergedCutProfiles.Batch144.profile5767,MergedCutProfiles.Batch144.profile5768,MergedCutProfiles.Batch144.profile5769,MergedCutProfiles.Batch144.profile5770,MergedCutProfiles.Batch144.profile5771,MergedCutProfiles.Batch144.profile5772,MergedCutProfiles.Batch144.profile5773,MergedCutProfiles.Batch144.profile5774,MergedCutProfiles.Batch144.profile5775,MergedCutProfiles.Batch144.profile5776,MergedCutProfiles.Batch144.profile5777,MergedCutProfiles.Batch144.profile5778]⟩
theorem profilesValid851 : retention851.ProfilesValid := by
  change ∀ j : Fin 16, (retention851.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch144.valid5763
  · exact MergedCutProfiles.Batch144.valid5764
  · exact MergedCutProfiles.Batch144.valid5765
  · exact MergedCutProfiles.Batch144.valid5766
  · exact MergedCutProfiles.Batch144.valid5767
  · exact MergedCutProfiles.Batch144.valid5768
  · exact MergedCutProfiles.Batch144.valid5769
  · exact MergedCutProfiles.Batch144.valid5770
  · exact MergedCutProfiles.Batch144.valid5771
  · exact MergedCutProfiles.Batch144.valid5772
  · exact MergedCutProfiles.Batch144.valid5773
  · exact MergedCutProfiles.Batch144.valid5774
  · exact MergedCutProfiles.Batch144.valid5775
  · exact MergedCutProfiles.Batch144.valid5776
  · exact MergedCutProfiles.Batch144.valid5777
  · exact MergedCutProfiles.Batch144.valid5778
theorem numericValid851 : retention851.NumericValid := by decide +kernel
def certificate851 : RatCutBinCertificate := ⟨⟨retention851,(2148772030523085131/1000000000000000000),(114392751307786871/1000000000000000000),(815404404890926431/62500000000000000),(130505885730980550373/500000000000000000),(1924553575758108677/1000000000000000000)⟩,(248172873573857223/250000000000000000),(378665211691500523/1000000000000000000),(253609395990854941/1000000000000000000),(222965534628549/1600000000000000)⟩
theorem valid851 : certificate851.Valid := by decide +kernel
theorem sound851 : certificate851.Sound := rat_cut_bin_certificate_sound certificate851 profilesValid851 numericValid851 valid851

def certificates : List RatCutBinCertificate := [certificate840,certificate841,certificate842,certificate843,certificate844,certificate845,certificate846,certificate847,certificate848,certificate849,certificate850,certificate851]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound840,List.forall_mem_cons.mpr ⟨sound841,List.forall_mem_cons.mpr ⟨sound842,List.forall_mem_cons.mpr ⟨sound843,List.forall_mem_cons.mpr ⟨sound844,List.forall_mem_cons.mpr ⟨sound845,List.forall_mem_cons.mpr ⟨sound846,List.forall_mem_cons.mpr ⟨sound847,List.forall_mem_cons.mpr ⟨sound848,List.forall_mem_cons.mpr ⟨sound849,List.forall_mem_cons.mpr ⟨sound850,List.forall_mem_cons.mpr ⟨sound851,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch070
