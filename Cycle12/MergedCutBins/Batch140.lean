import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch269
import Cycle12.MergedCutProfiles.Batch270
import Cycle12.MergedCutProfiles.Batch271

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch140

def retention1680 : RatCutRetentionCertificate := ⟨(103/1600),(129/2000),(1/2),(326376903555056823/62500000000000000),(11/10),(517310507468029990026366148977744845639/522203045688090916800000000000000000000),false,MergedCutProfiles.Batch269.profile10779,(fun _ => MergedCutProfiles.Batch269.profile10779)⟩
theorem profilesValid1680 : retention1680.ProfilesValid := by
  exact MergedCutProfiles.Batch269.valid10779
theorem numericValid1680 : retention1680.NumericValid := by decide +kernel
def certificate1680 : RatCutBinCertificate := ⟨⟨retention1680,(2383687632836081263/1000000000000000000),(216862197802423917/1000000000000000000),(430279376602469239/25000000000000000),(180989126143570984943/1000000000000000000),(19151719031612329/20000000000000000)⟩,(989641521272290877/1000000000000000000),(106848732813968157/250000000000000000),(52324700135174881/250000000000000000),(156423615887322699/1000000000000000000)⟩
theorem valid1680 : certificate1680.Valid := by decide +kernel
theorem sound1680 : certificate1680.Sound := rat_cut_bin_certificate_sound certificate1680 profilesValid1680 numericValid1680 valid1680

def retention1681 : RatCutRetentionCertificate := ⟨(103/1600),(129/2000),(1/2),64,1,(255415305052722385427829278962241032591/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch269.profile10779,(fun _ => MergedCutProfiles.Batch269.profile10779)⟩
theorem profilesValid1681 : retention1681.ProfilesValid := by
  exact MergedCutProfiles.Batch269.valid10779
theorem numericValid1681 : retention1681.NumericValid := by decide +kernel
def certificate1681 : RatCutBinCertificate := ⟨⟨retention1681,(2383687632836081263/1000000000000000000),(216862197802423917/1000000000000000000),(430279376602469239/25000000000000000),(180989126143570984943/1000000000000000000),(967680816094291229/1000000000000000000)⟩,(989641521272290877/1000000000000000000),(192002152213986691/500000000000000000),(248462422825182631/1000000000000000000),(58593311776478437/250000000000000000)⟩
theorem valid1681 : certificate1681.Valid := by decide +kernel
theorem sound1681 : certificate1681.Sound := rat_cut_bin_certificate_sound certificate1681 profilesValid1681 numericValid1681 valid1681

def retention1682 : RatCutRetentionCertificate := ⟨(103/1600),(129/2000),(4893322624811560587/10507506044520356836),(195443867312375697/62500000000000000),(6/5),(2290761230432519830467203884205071679/2171598525693063300000000000000000000),false,MergedCutProfiles.Batch269.profile10780,(fun _ => MergedCutProfiles.Batch269.profile10780)⟩
theorem profilesValid1682 : retention1682.ProfilesValid := by
  exact MergedCutProfiles.Batch269.valid10780
theorem numericValid1682 : retention1682.NumericValid := by decide +kernel
def certificate1682 : RatCutBinCertificate := ⟨⟨retention1682,(2692967892836081263/1000000000000000000),(216862197802423917/1000000000000000000),(430279376602469239/25000000000000000),(180989126143570984943/1000000000000000000),(253535582284551283/250000000000000000)⟩,(197658638911460143/200000000000000000),(380511087087019/1000000000000000),(125910743687327119/500000000000000000),(21426621381341571/125000000000000000)⟩
theorem valid1682 : certificate1682.Valid := by decide +kernel
theorem sound1682 : certificate1682.Sound := rat_cut_bin_certificate_sound certificate1682 profilesValid1682 numericValid1682 valid1682

def retention1683 : RatCutRetentionCertificate := ⟨(103/1600),(129/2000),(5194360569629248415/10507506044520356836),(4893322624811560587/1000000000000000000),(11/10),(1955292123684914243546857744691573931671/1957329049924624234800000000000000000000),false,MergedCutProfiles.Batch269.profile10781,(fun _ => MergedCutProfiles.Batch269.profile10781)⟩
theorem profilesValid1683 : retention1683.ProfilesValid := by
  exact MergedCutProfiles.Batch269.valid10781
theorem numericValid1683 : retention1683.NumericValid := by decide +kernel
def certificate1683 : RatCutBinCertificate := ⟨⟨retention1683,(2692967892836081263/1000000000000000000),(216862197802423917/1000000000000000000),(430279376602469239/25000000000000000),(180989126143570984943/1000000000000000000),(120203281314619419/125000000000000000)⟩,(197658638911460143/200000000000000000),(200645729000165133/500000000000000000),(46460229258740477/200000000000000000),(172472507111136691/1000000000000000000)⟩
theorem valid1683 : certificate1683.Valid := by decide +kernel
theorem sound1683 : certificate1683.Sound := rat_cut_bin_certificate_sound certificate1683 profilesValid1683 numericValid1683 valid1683

def retention1684 : RatCutRetentionCertificate := ⟨(103/1600),(129/2000),(1311576043831385225/2626876511130089209),(1038872113925849683/200000000000000000),(11/10),(82428148232230894597754792197446962599/83109769114067974640000000000000000000),false,MergedCutProfiles.Batch269.profile10782,(fun _ => MergedCutProfiles.Batch269.profile10782)⟩
theorem profilesValid1684 : retention1684.ProfilesValid := by
  exact MergedCutProfiles.Batch269.valid10782
theorem numericValid1684 : retention1684.NumericValid := by decide +kernel
def certificate1684 : RatCutBinCertificate := ⟨⟨retention1684,(2692967892836081263/1000000000000000000),(216862197802423917/1000000000000000000),(430279376602469239/25000000000000000),(180989126143570984943/1000000000000000000),(190893189014582593/200000000000000000)⟩,(197658638911460143/200000000000000000),(404301905283651591/1000000000000000000),(229563782351813073/1000000000000000000),(85364941170408137/500000000000000000)⟩
theorem valid1684 : certificate1684.Valid := by decide +kernel
theorem sound1684 : certificate1684.Sound := rat_cut_bin_certificate_sound certificate1684 profilesValid1684 numericValid1684 valid1684

def retention1685 : RatCutRetentionCertificate := ⟨(103/1600),(129/2000),(1/2),(52463041753255409/10000000000000000),(11/10),(20791995556853617868348178154755481831/20985216701302163600000000000000000000),false,MergedCutProfiles.Batch269.profile10779,(fun _ => MergedCutProfiles.Batch269.profile10779)⟩
theorem profilesValid1685 : retention1685.ProfilesValid := by
  exact MergedCutProfiles.Batch269.valid10779
theorem numericValid1685 : retention1685.NumericValid := by decide +kernel
def certificate1685 : RatCutBinCertificate := ⟨⟨retention1685,(2692967892836081263/1000000000000000000),(216862197802423917/1000000000000000000),(430279376602469239/25000000000000000),(180989126143570984943/1000000000000000000),(953459987126273667/1000000000000000000)⟩,(197658638911460143/200000000000000000),(404728468243768379/1000000000000000000),(229177729941260617/1000000000000000000),(85255324710948837/500000000000000000)⟩
theorem valid1685 : certificate1685.Valid := by decide +kernel
theorem sound1685 : certificate1685.Sound := rat_cut_bin_certificate_sound certificate1685 profilesValid1685 numericValid1685 valid1685

def retention1686 : RatCutRetentionCertificate := ⟨(129/2000),(517/8000),(1171632465758576917/10458643434815170388),(886733123218877859/1000000000000000000),(51/20),(596916439741892143913/320000000000000000000),true,MergedCutProfiles.Batch269.profile10783,![MergedCutProfiles.Batch269.profile10783,MergedCutProfiles.Batch269.profile10784,MergedCutProfiles.Batch269.profile10785,MergedCutProfiles.Batch269.profile10786,MergedCutProfiles.Batch269.profile10787,MergedCutProfiles.Batch269.profile10788,MergedCutProfiles.Batch269.profile10789,MergedCutProfiles.Batch269.profile10790,MergedCutProfiles.Batch269.profile10791,MergedCutProfiles.Batch269.profile10792,MergedCutProfiles.Batch269.profile10793,MergedCutProfiles.Batch269.profile10794,MergedCutProfiles.Batch269.profile10795,MergedCutProfiles.Batch269.profile10796,MergedCutProfiles.Batch269.profile10797,MergedCutProfiles.Batch269.profile10798]⟩
theorem profilesValid1686 : retention1686.ProfilesValid := by
  change ∀ j : Fin 16, (retention1686.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch269.valid10783
  · exact MergedCutProfiles.Batch269.valid10784
  · exact MergedCutProfiles.Batch269.valid10785
  · exact MergedCutProfiles.Batch269.valid10786
  · exact MergedCutProfiles.Batch269.valid10787
  · exact MergedCutProfiles.Batch269.valid10788
  · exact MergedCutProfiles.Batch269.valid10789
  · exact MergedCutProfiles.Batch269.valid10790
  · exact MergedCutProfiles.Batch269.valid10791
  · exact MergedCutProfiles.Batch269.valid10792
  · exact MergedCutProfiles.Batch269.valid10793
  · exact MergedCutProfiles.Batch269.valid10794
  · exact MergedCutProfiles.Batch269.valid10795
  · exact MergedCutProfiles.Batch269.valid10796
  · exact MergedCutProfiles.Batch269.valid10797
  · exact MergedCutProfiles.Batch269.valid10798
theorem numericValid1686 : retention1686.NumericValid := by decide +kernel
def certificate1686 : RatCutBinCertificate := ⟨⟨retention1686,(2381925784795996019/1000000000000000000),(217880547218111863/1000000000000000000),(4313063204272180767/250000000000000000),(4514438988136114743/25000000000000000),(1788614873299781791/1000000000000000000)⟩,(123704851174483891/125000000000000000),(336859812069174151/1000000000000000000),(296598517073303807/1000000000000000000),(39194787764027769/250000000000000000)⟩
theorem valid1686 : certificate1686.Valid := by decide +kernel
theorem sound1686 : certificate1686.Sound := rat_cut_bin_certificate_sound certificate1686 profilesValid1686 numericValid1686 valid1686

def retention1687 : RatCutRetentionCertificate := ⟨(129/2000),(517/8000),(564861631060568115/2614660858703792597),(1171632465758576917/1000000000000000000),2,(407743715351378125589/256000000000000000000),true,MergedCutProfiles.Batch269.profile10799,![MergedCutProfiles.Batch269.profile10799,MergedCutProfiles.Batch270.profile10800,MergedCutProfiles.Batch270.profile10801,MergedCutProfiles.Batch270.profile10802,MergedCutProfiles.Batch270.profile10803,MergedCutProfiles.Batch270.profile10804,MergedCutProfiles.Batch270.profile10805,MergedCutProfiles.Batch270.profile10806,MergedCutProfiles.Batch270.profile10807,MergedCutProfiles.Batch270.profile10808,MergedCutProfiles.Batch270.profile10809,MergedCutProfiles.Batch270.profile10810,MergedCutProfiles.Batch270.profile10811,MergedCutProfiles.Batch270.profile10812,MergedCutProfiles.Batch270.profile10813,MergedCutProfiles.Batch270.profile10814]⟩
theorem profilesValid1687 : retention1687.ProfilesValid := by
  change ∀ j : Fin 16, (retention1687.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch269.valid10799
  · exact MergedCutProfiles.Batch270.valid10800
  · exact MergedCutProfiles.Batch270.valid10801
  · exact MergedCutProfiles.Batch270.valid10802
  · exact MergedCutProfiles.Batch270.valid10803
  · exact MergedCutProfiles.Batch270.valid10804
  · exact MergedCutProfiles.Batch270.valid10805
  · exact MergedCutProfiles.Batch270.valid10806
  · exact MergedCutProfiles.Batch270.valid10807
  · exact MergedCutProfiles.Batch270.valid10808
  · exact MergedCutProfiles.Batch270.valid10809
  · exact MergedCutProfiles.Batch270.valid10810
  · exact MergedCutProfiles.Batch270.valid10811
  · exact MergedCutProfiles.Batch270.valid10812
  · exact MergedCutProfiles.Batch270.valid10813
  · exact MergedCutProfiles.Batch270.valid10814
theorem numericValid1687 : retention1687.NumericValid := by decide +kernel
def certificate1687 : RatCutBinCertificate := ⟨⟨retention1687,(2381925784795996019/1000000000000000000),(217880547218111863/1000000000000000000),(4313063204272180767/250000000000000000),(4514438988136114743/25000000000000000),(306510943601561191/200000000000000000)⟩,(123704851174483891/125000000000000000),(178050810365101943/500000000000000000),(138102316558643499/500000000000000000),(157496020412724261/1000000000000000000)⟩
theorem valid1687 : certificate1687.Valid := by decide +kernel
theorem sound1687 : certificate1687.Sound := rat_cut_bin_certificate_sound certificate1687 profilesValid1687 numericValid1687 valid1687

def retention1688 : RatCutRetentionCertificate := ⟨(129/2000),(517/8000),(4145776331584775609/10458643434815170388),(112972326212113623/50000000000000000),(5/4),(604540953891972051/512000000000000000),true,MergedCutProfiles.Batch270.profile10815,![MergedCutProfiles.Batch270.profile10815,MergedCutProfiles.Batch270.profile10816,MergedCutProfiles.Batch270.profile10817,MergedCutProfiles.Batch270.profile10818,MergedCutProfiles.Batch270.profile10819,MergedCutProfiles.Batch270.profile10809,MergedCutProfiles.Batch270.profile10820,MergedCutProfiles.Batch270.profile10821,MergedCutProfiles.Batch270.profile10822,MergedCutProfiles.Batch270.profile10823,MergedCutProfiles.Batch270.profile10824,MergedCutProfiles.Batch270.profile10825,MergedCutProfiles.Batch270.profile10826,MergedCutProfiles.Batch270.profile10827,MergedCutProfiles.Batch270.profile10828,MergedCutProfiles.Batch270.profile10829]⟩
theorem profilesValid1688 : retention1688.ProfilesValid := by
  change ∀ j : Fin 16, (retention1688.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch270.valid10815
  · exact MergedCutProfiles.Batch270.valid10816
  · exact MergedCutProfiles.Batch270.valid10817
  · exact MergedCutProfiles.Batch270.valid10818
  · exact MergedCutProfiles.Batch270.valid10819
  · exact MergedCutProfiles.Batch270.valid10809
  · exact MergedCutProfiles.Batch270.valid10820
  · exact MergedCutProfiles.Batch270.valid10821
  · exact MergedCutProfiles.Batch270.valid10822
  · exact MergedCutProfiles.Batch270.valid10823
  · exact MergedCutProfiles.Batch270.valid10824
  · exact MergedCutProfiles.Batch270.valid10825
  · exact MergedCutProfiles.Batch270.valid10826
  · exact MergedCutProfiles.Batch270.valid10827
  · exact MergedCutProfiles.Batch270.valid10828
  · exact MergedCutProfiles.Batch270.valid10829
theorem numericValid1688 : retention1688.NumericValid := by decide +kernel
def certificate1688 : RatCutBinCertificate := ⟨⟨retention1688,(2381925784795996019/1000000000000000000),(217880547218111863/1000000000000000000),(4313063204272180767/250000000000000000),(4514438988136114743/25000000000000000),(285781498001591113/250000000000000000)⟩,(123704851174483891/125000000000000000),(403000209835385351/1000000000000000000),(115372319591501429/500000000000000000),(157464188527697379/1000000000000000000)⟩
theorem valid1688 : certificate1688.Valid := by decide +kernel
theorem sound1688 : certificate1688.Sound := rat_cut_bin_certificate_sound certificate1688 profilesValid1688 numericValid1688 valid1688

def retention1689 : RatCutRetentionCertificate := ⟨(129/2000),(517/8000),(5008549492724517541/10458643434815170388),(4145776331584775609/1000000000000000000),1,(254477106517486462649/256000000000000000000),true,MergedCutProfiles.Batch270.profile10830,![MergedCutProfiles.Batch270.profile10830,MergedCutProfiles.Batch270.profile10831,MergedCutProfiles.Batch270.profile10832,MergedCutProfiles.Batch270.profile10833,MergedCutProfiles.Batch270.profile10834,MergedCutProfiles.Batch270.profile10835,MergedCutProfiles.Batch270.profile10836,MergedCutProfiles.Batch270.profile10837,MergedCutProfiles.Batch270.profile10838,MergedCutProfiles.Batch270.profile10839,MergedCutProfiles.Batch271.profile10840,MergedCutProfiles.Batch271.profile10841,MergedCutProfiles.Batch271.profile10842,MergedCutProfiles.Batch271.profile10843,MergedCutProfiles.Batch271.profile10844,MergedCutProfiles.Batch271.profile10845]⟩
theorem profilesValid1689 : retention1689.ProfilesValid := by
  change ∀ j : Fin 16, (retention1689.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch270.valid10830
  · exact MergedCutProfiles.Batch270.valid10831
  · exact MergedCutProfiles.Batch270.valid10832
  · exact MergedCutProfiles.Batch270.valid10833
  · exact MergedCutProfiles.Batch270.valid10834
  · exact MergedCutProfiles.Batch270.valid10835
  · exact MergedCutProfiles.Batch270.valid10836
  · exact MergedCutProfiles.Batch270.valid10837
  · exact MergedCutProfiles.Batch270.valid10838
  · exact MergedCutProfiles.Batch270.valid10839
  · exact MergedCutProfiles.Batch271.valid10840
  · exact MergedCutProfiles.Batch271.valid10841
  · exact MergedCutProfiles.Batch271.valid10842
  · exact MergedCutProfiles.Batch271.valid10843
  · exact MergedCutProfiles.Batch271.valid10844
  · exact MergedCutProfiles.Batch271.valid10845
theorem numericValid1689 : retention1689.NumericValid := by decide +kernel
def certificate1689 : RatCutBinCertificate := ⟨⟨retention1689,(2381925784795996019/1000000000000000000),(217880547218111863/1000000000000000000),(4313063204272180767/250000000000000000),(4514438988136114743/25000000000000000),(240990211701724079/250000000000000000)⟩,(123704851174483891/125000000000000000),(217328865342128851/500000000000000000),(20318656219854537/100000000000000000),(157058205088294773/1000000000000000000)⟩
theorem valid1689 : certificate1689.Valid := by decide +kernel
theorem sound1689 : certificate1689.Sound := rat_cut_bin_certificate_sound certificate1689 profilesValid1689 numericValid1689 valid1689

def retention1690 : RatCutRetentionCertificate := ⟨(129/2000),(517/8000),(5160313550903563149/10458643434815170388),(5008549492724517541/1000000000000000000),(11/10),(2006783845903050204545051588221850224639/2003419797089807016400000000000000000000),false,MergedCutProfiles.Batch271.profile10846,(fun _ => MergedCutProfiles.Batch271.profile10846)⟩
theorem profilesValid1690 : retention1690.ProfilesValid := by
  exact MergedCutProfiles.Batch271.valid10846
theorem numericValid1690 : retention1690.NumericValid := by decide +kernel
def certificate1690 : RatCutBinCertificate := ⟨⟨retention1690,(2381925784795996019/1000000000000000000),(217880547218111863/1000000000000000000),(4313063204272180767/250000000000000000),(4514438988136114743/25000000000000000),(15134096113230559/15625000000000000)⟩,(123704851174483891/125000000000000000),(211851739092406467/500000000000000000),(212452625243930823/1000000000000000000),(31890315734763091/200000000000000000)⟩
theorem valid1690 : certificate1690.Valid := by decide +kernel
theorem sound1690 : certificate1690.Sound := rat_cut_bin_certificate_sound certificate1690 profilesValid1690 numericValid1690 valid1690

def retention1691 : RatCutRetentionCertificate := ⟨(129/2000),(517/8000),(5211916686412598781/10458643434815170388),(5160313550903563149/1000000000000000000),(11/10),(2050479071472556361414464051638080203919/2064125420361425259600000000000000000000),false,MergedCutProfiles.Batch271.profile10847,(fun _ => MergedCutProfiles.Batch271.profile10847)⟩
theorem profilesValid1691 : retention1691.ProfilesValid := by
  exact MergedCutProfiles.Batch271.valid10847
theorem numericValid1691 : retention1691.NumericValid := by decide +kernel
def certificate1691 : RatCutBinCertificate := ⟨⟨retention1691,(2381925784795996019/1000000000000000000),(217880547218111863/1000000000000000000),(4313063204272180767/250000000000000000),(4514438988136114743/25000000000000000),(480146004869046489/500000000000000000)⟩,(123704851174483891/125000000000000000),(213047737370510983/500000000000000000),(52601338184865867/250000000000000000),(157385490065159403/1000000000000000000)⟩
theorem valid1691 : certificate1691.Valid := by decide +kernel
theorem sound1691 : certificate1691.Sound := rat_cut_bin_certificate_sound certificate1691 profilesValid1691 numericValid1691 valid1691

def certificates : List RatCutBinCertificate := [certificate1680,certificate1681,certificate1682,certificate1683,certificate1684,certificate1685,certificate1686,certificate1687,certificate1688,certificate1689,certificate1690,certificate1691]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1680,List.forall_mem_cons.mpr ⟨sound1681,List.forall_mem_cons.mpr ⟨sound1682,List.forall_mem_cons.mpr ⟨sound1683,List.forall_mem_cons.mpr ⟨sound1684,List.forall_mem_cons.mpr ⟨sound1685,List.forall_mem_cons.mpr ⟨sound1686,List.forall_mem_cons.mpr ⟨sound1687,List.forall_mem_cons.mpr ⟨sound1688,List.forall_mem_cons.mpr ⟨sound1689,List.forall_mem_cons.mpr ⟨sound1690,List.forall_mem_cons.mpr ⟨sound1691,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch140
