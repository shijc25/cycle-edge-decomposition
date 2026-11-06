import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch290
import Cycle12.MergedCutProfiles.Batch291
import Cycle12.MergedCutProfiles.Batch292

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch152

def retention1824 : RatCutRetentionCertificate := ⟨(527/8000),(33/500),(4937319402398413239/9940316909040723322),(1222108762969904267/250000000000000000),(11/10),(121534906205313168968972023648712039431/122210876296990426700000000000000000000),false,MergedCutProfiles.Batch290.profile11613,(fun _ => MergedCutProfiles.Batch290.profile11613)⟩
theorem profilesValid1824 : retention1824.ProfilesValid := by
  exact MergedCutProfiles.Batch290.valid11613
theorem numericValid1824 : retention1824.NumericValid := by decide +kernel
def certificate1824 : RatCutBinCertificate := ⟨⟨retention1824,(678545036092031847/250000000000000000),(229314578619222081/1000000000000000000),(2214252168013179003/125000000000000000),(176223244068692845303/1000000000000000000),(955809784511451081/1000000000000000000)⟩,(197613948362196651/200000000000000000),(397153164545502527/1000000000000000000),(236100925921926869/1000000000000000000),(174309656940517647/1000000000000000000)⟩
theorem valid1824 : certificate1824.Valid := by decide +kernel
theorem sound1824 : certificate1824.Sound := rat_cut_bin_certificate_sound certificate1824 profilesValid1824 numericValid1824 valid1824

def retention1825 : RatCutRetentionCertificate := ⟨(527/8000),(33/500),(1/2),(4937319402398413239/1000000000000000000),(11/10),(650793152844583199426589116745693164853/658309253653121765200000000000000000000),false,MergedCutProfiles.Batch290.profile11610,(fun _ => MergedCutProfiles.Batch290.profile11610)⟩
theorem profilesValid1825 : retention1825.ProfilesValid := by
  exact MergedCutProfiles.Batch290.valid11610
theorem numericValid1825 : retention1825.NumericValid := by decide +kernel
def certificate1825 : RatCutBinCertificate := ⟨⟨retention1825,(678545036092031847/250000000000000000),(229314578619222081/1000000000000000000),(2214252168013179003/125000000000000000),(176223244068692845303/1000000000000000000),(237480943842137619/250000000000000000)⟩,(197613948362196651/200000000000000000),(399614043216256691/1000000000000000000),(233836182165005169/1000000000000000000),(171958690999579417/1000000000000000000)⟩
theorem valid1825 : certificate1825.Valid := by decide +kernel
theorem sound1825 : certificate1825.Sound := rat_cut_bin_certificate_sound certificate1825 profilesValid1825 numericValid1825 valid1825

def retention1826 : RatCutRetentionCertificate := ⟨(33/500),(529/8000),(1248536208631024568/9894880052446134049),(899074762492129467/1000000000000000000),(49/20),(583031549959455141461/320000000000000000000),true,MergedCutProfiles.Batch290.profile11614,![MergedCutProfiles.Batch290.profile11614,MergedCutProfiles.Batch290.profile11615,MergedCutProfiles.Batch290.profile11616,MergedCutProfiles.Batch290.profile11617,MergedCutProfiles.Batch290.profile11618,MergedCutProfiles.Batch290.profile11619,MergedCutProfiles.Batch290.profile11620,MergedCutProfiles.Batch290.profile11621,MergedCutProfiles.Batch290.profile11622,MergedCutProfiles.Batch290.profile11623,MergedCutProfiles.Batch290.profile11624,MergedCutProfiles.Batch290.profile11625,MergedCutProfiles.Batch290.profile11626,MergedCutProfiles.Batch290.profile11627,MergedCutProfiles.Batch290.profile11628,MergedCutProfiles.Batch290.profile11629]⟩
theorem profilesValid1826 : retention1826.ProfilesValid := by
  change ∀ j : Fin 16, (retention1826.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch290.valid11614
  · exact MergedCutProfiles.Batch290.valid11615
  · exact MergedCutProfiles.Batch290.valid11616
  · exact MergedCutProfiles.Batch290.valid11617
  · exact MergedCutProfiles.Batch290.valid11618
  · exact MergedCutProfiles.Batch290.valid11619
  · exact MergedCutProfiles.Batch290.valid11620
  · exact MergedCutProfiles.Batch290.valid11621
  · exact MergedCutProfiles.Batch290.valid11622
  · exact MergedCutProfiles.Batch290.valid11623
  · exact MergedCutProfiles.Batch290.valid11624
  · exact MergedCutProfiles.Batch290.valid11625
  · exact MergedCutProfiles.Batch290.valid11626
  · exact MergedCutProfiles.Batch290.valid11627
  · exact MergedCutProfiles.Batch290.valid11628
  · exact MergedCutProfiles.Batch290.valid11629
theorem numericValid1826 : retention1826.NumericValid := by decide +kernel
def certificate1826 : RatCutBinCertificate := ⟨⟨retention1826,(2407474416072634489/1000000000000000000),(230375442520233127/1000000000000000000),(3551383010985760831/200000000000000000),(175842661536513036111/1000000000000000000),(872702148339308019/500000000000000000)⟩,(247353367756148559/250000000000000000),(332312318107534817/1000000000000000000),(60315258534517193/200000000000000000),(160234779083425253/1000000000000000000)⟩
theorem valid1826 : certificate1826.Valid := by decide +kernel
theorem sound1826 : certificate1826.Sound := rat_cut_bin_certificate_sound certificate1826 profilesValid1826 numericValid1826 valid1826

def retention1827 : RatCutRetentionCertificate := ⟨(33/500),(529/8000),(2456148149785311692/9894880052446134049),(156067026078878071/125000000000000000),(37/20),(242200576746444752383/160000000000000000000),true,MergedCutProfiles.Batch290.profile11630,![MergedCutProfiles.Batch290.profile11630,MergedCutProfiles.Batch290.profile11631,MergedCutProfiles.Batch290.profile11632,MergedCutProfiles.Batch290.profile11633,MergedCutProfiles.Batch290.profile11634,MergedCutProfiles.Batch290.profile11635,MergedCutProfiles.Batch290.profile11636,MergedCutProfiles.Batch290.profile11637,MergedCutProfiles.Batch290.profile11638,MergedCutProfiles.Batch290.profile11639,MergedCutProfiles.Batch291.profile11640,MergedCutProfiles.Batch291.profile11641,MergedCutProfiles.Batch291.profile11642,MergedCutProfiles.Batch291.profile11643,MergedCutProfiles.Batch291.profile11644,MergedCutProfiles.Batch291.profile11645]⟩
theorem profilesValid1827 : retention1827.ProfilesValid := by
  change ∀ j : Fin 16, (retention1827.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch290.valid11630
  · exact MergedCutProfiles.Batch290.valid11631
  · exact MergedCutProfiles.Batch290.valid11632
  · exact MergedCutProfiles.Batch290.valid11633
  · exact MergedCutProfiles.Batch290.valid11634
  · exact MergedCutProfiles.Batch290.valid11635
  · exact MergedCutProfiles.Batch290.valid11636
  · exact MergedCutProfiles.Batch290.valid11637
  · exact MergedCutProfiles.Batch290.valid11638
  · exact MergedCutProfiles.Batch290.valid11639
  · exact MergedCutProfiles.Batch291.valid11640
  · exact MergedCutProfiles.Batch291.valid11641
  · exact MergedCutProfiles.Batch291.valid11642
  · exact MergedCutProfiles.Batch291.valid11643
  · exact MergedCutProfiles.Batch291.valid11644
  · exact MergedCutProfiles.Batch291.valid11645
theorem numericValid1827 : retention1827.NumericValid := by decide +kernel
def certificate1827 : RatCutBinCertificate := ⟨⟨retention1827,(2407474416072634489/1000000000000000000),(230375442520233127/1000000000000000000),(3551383010985760831/200000000000000000),(175842661536513036111/1000000000000000000),(727968782613407327/500000000000000000)⟩,(247353367756148559/250000000000000000),(356001234554148791/1000000000000000000),(276308285898397653/1000000000000000000),(32021808207785783/200000000000000000)⟩
theorem valid1827 : certificate1827.Valid := by decide +kernel
theorem sound1827 : certificate1827.Sound := rat_cut_bin_certificate_sound certificate1827 profilesValid1827 numericValid1827 valid1827

def retention1828 : RatCutRetentionCertificate := ⟨(33/500),(529/8000),(4120652540366524853/9894880052446134049),(614037037446327923/250000000000000000),(6/5),(364211460129705789483/320000000000000000000),true,MergedCutProfiles.Batch291.profile11646,![MergedCutProfiles.Batch291.profile11646,MergedCutProfiles.Batch291.profile11647,MergedCutProfiles.Batch291.profile11648,MergedCutProfiles.Batch291.profile11649,MergedCutProfiles.Batch291.profile11650,MergedCutProfiles.Batch291.profile11651,MergedCutProfiles.Batch291.profile11652,MergedCutProfiles.Batch291.profile11653,MergedCutProfiles.Batch291.profile11654,MergedCutProfiles.Batch291.profile11655,MergedCutProfiles.Batch291.profile11656,MergedCutProfiles.Batch291.profile11657,MergedCutProfiles.Batch291.profile11658,MergedCutProfiles.Batch291.profile11659,MergedCutProfiles.Batch291.profile11660,MergedCutProfiles.Batch291.profile11661]⟩
theorem profilesValid1828 : retention1828.ProfilesValid := by
  change ∀ j : Fin 16, (retention1828.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch291.valid11646
  · exact MergedCutProfiles.Batch291.valid11647
  · exact MergedCutProfiles.Batch291.valid11648
  · exact MergedCutProfiles.Batch291.valid11649
  · exact MergedCutProfiles.Batch291.valid11650
  · exact MergedCutProfiles.Batch291.valid11651
  · exact MergedCutProfiles.Batch291.valid11652
  · exact MergedCutProfiles.Batch291.valid11653
  · exact MergedCutProfiles.Batch291.valid11654
  · exact MergedCutProfiles.Batch291.valid11655
  · exact MergedCutProfiles.Batch291.valid11656
  · exact MergedCutProfiles.Batch291.valid11657
  · exact MergedCutProfiles.Batch291.valid11658
  · exact MergedCutProfiles.Batch291.valid11659
  · exact MergedCutProfiles.Batch291.valid11660
  · exact MergedCutProfiles.Batch291.valid11661
theorem numericValid1828 : retention1828.NumericValid := by decide +kernel
def certificate1828 : RatCutBinCertificate := ⟨⟨retention1828,(2407474416072634489/1000000000000000000),(230375442520233127/1000000000000000000),(3551383010985760831/200000000000000000),(175842661536513036111/1000000000000000000),(2751657789870577/2500000000000000)⟩,(247353367756148559/250000000000000000),(399998952466987489/1000000000000000000),(1459270768032781/6250000000000000),(161304326193428657/1000000000000000000)⟩
theorem valid1828 : certificate1828.Valid := by decide +kernel
theorem sound1828 : certificate1828.Sound := rat_cut_bin_certificate_sound certificate1828 profilesValid1828 numericValid1828 valid1828

def retention1829 : RatCutRetentionCertificate := ⟨(33/500),(529/8000),(4783949675232055088/9894880052446134049),(4120652540366524853/1000000000000000000),1,(252160598888477353973/256000000000000000000),true,MergedCutProfiles.Batch291.profile11662,![MergedCutProfiles.Batch291.profile11662,MergedCutProfiles.Batch291.profile11663,MergedCutProfiles.Batch291.profile11664,MergedCutProfiles.Batch291.profile11665,MergedCutProfiles.Batch291.profile11666,MergedCutProfiles.Batch291.profile11667,MergedCutProfiles.Batch291.profile11668,MergedCutProfiles.Batch291.profile11669,MergedCutProfiles.Batch291.profile11670,MergedCutProfiles.Batch291.profile11671,MergedCutProfiles.Batch291.profile11672,MergedCutProfiles.Batch291.profile11673,MergedCutProfiles.Batch291.profile11674,MergedCutProfiles.Batch291.profile11675,MergedCutProfiles.Batch291.profile11676,MergedCutProfiles.Batch291.profile11677]⟩
theorem profilesValid1829 : retention1829.ProfilesValid := by
  change ∀ j : Fin 16, (retention1829.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch291.valid11662
  · exact MergedCutProfiles.Batch291.valid11663
  · exact MergedCutProfiles.Batch291.valid11664
  · exact MergedCutProfiles.Batch291.valid11665
  · exact MergedCutProfiles.Batch291.valid11666
  · exact MergedCutProfiles.Batch291.valid11667
  · exact MergedCutProfiles.Batch291.valid11668
  · exact MergedCutProfiles.Batch291.valid11669
  · exact MergedCutProfiles.Batch291.valid11670
  · exact MergedCutProfiles.Batch291.valid11671
  · exact MergedCutProfiles.Batch291.valid11672
  · exact MergedCutProfiles.Batch291.valid11673
  · exact MergedCutProfiles.Batch291.valid11674
  · exact MergedCutProfiles.Batch291.valid11675
  · exact MergedCutProfiles.Batch291.valid11676
  · exact MergedCutProfiles.Batch291.valid11677
theorem numericValid1829 : retention1829.NumericValid := by decide +kernel
def certificate1829 : RatCutBinCertificate := ⟨⟨retention1829,(2407474416072634489/1000000000000000000),(230375442520233127/1000000000000000000),(3551383010985760831/200000000000000000),(175842661536513036111/1000000000000000000),(2980494411663869/3125000000000000)⟩,(247353367756148559/250000000000000000),(427432628696543139/1000000000000000000),(209266758299570303/1000000000000000000),(16013752179574563/100000000000000000)⟩
theorem valid1829 : certificate1829.Valid := by decide +kernel
theorem sound1829 : certificate1829.Sound := rat_cut_bin_certificate_sound certificate1829 profilesValid1829 numericValid1829 valid1829

def retention1830 : RatCutRetentionCertificate := ⟨(33/500),(529/8000),(4880107063704219396/9894880052446134049),(298996854702003443/62500000000000000),(11/10),(478504327977855861915322520501024437039/478394967523205508800000000000000000000),false,MergedCutProfiles.Batch291.profile11678,(fun _ => MergedCutProfiles.Batch291.profile11678)⟩
theorem profilesValid1830 : retention1830.ProfilesValid := by
  exact MergedCutProfiles.Batch291.valid11678
theorem numericValid1830 : retention1830.NumericValid := by decide +kernel
def certificate1830 : RatCutBinCertificate := ⟨⟨retention1830,(2407474416072634489/1000000000000000000),(230375442520233127/1000000000000000000),(3551383010985760831/200000000000000000),(175842661536513036111/1000000000000000000),(482931214088400219/500000000000000000)⟩,(247353367756148559/250000000000000000),(415171253017271369/1000000000000000000),(219865722795317979/1000000000000000000),(163508962127067877/1000000000000000000)⟩
theorem valid1830 : certificate1830.Valid := by decide +kernel
theorem sound1830 : certificate1830.Sound := rat_cut_bin_certificate_sound certificate1830 profilesValid1830 numericValid1830 valid1830

def retention1831 : RatCutRetentionCertificate := ⟨(33/500),(529/8000),(4928908134341261590/9894880052446134049),(1220026765926054849/250000000000000000),(11/10),(483953268519335112475717929585521162231/488010706370421939600000000000000000000),false,MergedCutProfiles.Batch291.profile11679,(fun _ => MergedCutProfiles.Batch291.profile11679)⟩
theorem profilesValid1831 : retention1831.ProfilesValid := by
  exact MergedCutProfiles.Batch291.valid11679
theorem numericValid1831 : retention1831.NumericValid := by decide +kernel
def certificate1831 : RatCutBinCertificate := ⟨⟨retention1831,(2407474416072634489/1000000000000000000),(230375442520233127/1000000000000000000),(3551383010985760831/200000000000000000),(175842661536513036111/1000000000000000000),(957319758628786613/1000000000000000000)⟩,(247353367756148559/250000000000000000),(418023300397764987/1000000000000000000),(54342108861092167/250000000000000000),(80438840899133033/500000000000000000)⟩
theorem valid1831 : certificate1831.Valid := by decide +kernel
theorem sound1831 : certificate1831.Sound := rat_cut_bin_certificate_sound certificate1831 profilesValid1831 numericValid1831 valid1831

def retention1832 : RatCutRetentionCertificate := ⟨(33/500),(529/8000),(1/2),(492890813434126159/100000000000000000),(11/10),(2436156900029114232868604088350227813/2464454067170630795000000000000000000),false,MergedCutProfiles.Batch292.profile11680,(fun _ => MergedCutProfiles.Batch292.profile11680)⟩
theorem profilesValid1832 : retention1832.ProfilesValid := by
  exact MergedCutProfiles.Batch292.valid11680
theorem numericValid1832 : retention1832.NumericValid := by decide +kernel
def certificate1832 : RatCutBinCertificate := ⟨⟨retention1832,(2407474416072634489/1000000000000000000),(230375442520233127/1000000000000000000),(3551383010985760831/200000000000000000),(175842661536513036111/1000000000000000000),(477075978544159879/500000000000000000)⟩,(247353367756148559/250000000000000000),(418989699975014119/1000000000000000000),(54131665839615097/250000000000000000),(40005001988749363/250000000000000000)⟩
theorem valid1832 : certificate1832.Valid := by decide +kernel
theorem sound1832 : certificate1832.Sound := rat_cut_bin_certificate_sound certificate1832 profilesValid1832 numericValid1832 valid1832

def retention1833 : RatCutRetentionCertificate := ⟨(33/500),(529/8000),(1/2),64,1,(255418116223072916334057395546269834911/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch292.profile11680,(fun _ => MergedCutProfiles.Batch292.profile11680)⟩
theorem profilesValid1833 : retention1833.ProfilesValid := by
  exact MergedCutProfiles.Batch292.valid11680
theorem numericValid1833 : retention1833.NumericValid := by decide +kernel
def certificate1833 : RatCutBinCertificate := ⟨⟨retention1833,(2407474416072634489/1000000000000000000),(230375442520233127/1000000000000000000),(3551383010985760831/200000000000000000),(175842661536513036111/1000000000000000000),(966492180054084693/1000000000000000000)⟩,(247353367756148559/250000000000000000),(187618940549381337/500000000000000000),(10278119003003419/40000000000000000),(1512701399566923/6250000000000000)⟩
theorem valid1833 : certificate1833.Valid := by decide +kernel
theorem sound1833 : certificate1833.Sound := rat_cut_bin_certificate_sound certificate1833 profilesValid1833 numericValid1833 valid1833

def retention1834 : RatCutRetentionCertificate := ⟨(33/500),(529/8000),(4582616980866565535/9894880052446134049),(2928543907930585127/1000000000000000000),(5/4),(199770864497143915562805643230571778231/187426810107557448128000000000000000000),false,MergedCutProfiles.Batch292.profile11681,(fun _ => MergedCutProfiles.Batch292.profile11681)⟩
theorem profilesValid1834 : retention1834.ProfilesValid := by
  exact MergedCutProfiles.Batch292.valid11681
theorem numericValid1834 : retention1834.NumericValid := by decide +kernel
def certificate1834 : RatCutBinCertificate := ⟨⟨retention1834,(2716049804072634489/1000000000000000000),(230375442520233127/1000000000000000000),(3551383010985760831/200000000000000000),(175842661536513036111/1000000000000000000),(63862368359971517/62500000000000000)⟩,(494025866919223573/500000000000000000),(370257477741836441/1000000000000000000),(26186750138091041/100000000000000000),(17262264557647493/100000000000000000)⟩
theorem valid1834 : certificate1834.Valid := by decide +kernel
theorem sound1834 : certificate1834.Sound := rat_cut_bin_certificate_sound certificate1834 profilesValid1834 numericValid1834 valid1834

def retention1835 : RatCutRetentionCertificate := ⟨(33/500),(529/8000),(4864540267676176585/9894880052446134049),(916523396173313107/200000000000000000),(11/10),(73419519097438326561502506763125487831/73321871693865048560000000000000000000),false,MergedCutProfiles.Batch292.profile11682,(fun _ => MergedCutProfiles.Batch292.profile11682)⟩
theorem profilesValid1835 : retention1835.ProfilesValid := by
  exact MergedCutProfiles.Batch292.valid11682
theorem numericValid1835 : retention1835.NumericValid := by decide +kernel
def certificate1835 : RatCutBinCertificate := ⟨⟨retention1835,(2716049804072634489/1000000000000000000),(230375442520233127/1000000000000000000),(3551383010985760831/200000000000000000),(175842661536513036111/1000000000000000000),(481280161522722629/500000000000000000)⟩,(494025866919223573/500000000000000000),(98260935405153783/250000000000000000),(239916845199186659/1000000000000000000),(176538836656836431/1000000000000000000)⟩
theorem valid1835 : certificate1835.Valid := by decide +kernel
theorem sound1835 : certificate1835.Sound := rat_cut_bin_certificate_sound certificate1835 profilesValid1835 numericValid1835 valid1835

def certificates : List RatCutBinCertificate := [certificate1824,certificate1825,certificate1826,certificate1827,certificate1828,certificate1829,certificate1830,certificate1831,certificate1832,certificate1833,certificate1834,certificate1835]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1824,List.forall_mem_cons.mpr ⟨sound1825,List.forall_mem_cons.mpr ⟨sound1826,List.forall_mem_cons.mpr ⟨sound1827,List.forall_mem_cons.mpr ⟨sound1828,List.forall_mem_cons.mpr ⟨sound1829,List.forall_mem_cons.mpr ⟨sound1830,List.forall_mem_cons.mpr ⟨sound1831,List.forall_mem_cons.mpr ⟨sound1832,List.forall_mem_cons.mpr ⟨sound1833,List.forall_mem_cons.mpr ⟨sound1834,List.forall_mem_cons.mpr ⟨sound1835,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch152
