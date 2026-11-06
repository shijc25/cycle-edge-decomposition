import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch244
import Cycle12.MergedCutProfiles.Batch245

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch126

def retention1512 : RatCutRetentionCertificate := ⟨(249/4000),(499/8000),(1381311951084449/2771030040705171),(5619614660401981129/1000000000000000000),(21/20),(802163790264105380129686960034883834309/817398496058469982400000000000000000000),false,MergedCutProfiles.Batch244.profile9769,(fun _ => MergedCutProfiles.Batch244.profile9769)⟩
theorem profilesValid1512 : retention1512.ProfilesValid := by
  exact MergedCutProfiles.Batch244.valid9769
theorem numericValid1512 : retention1512.NumericValid := by decide +kernel
def certificate1512 : RatCutBinCertificate := ⟨⟨retention1512,(1332090844598504437/500000000000000000),(40014422526402453/200000000000000000),(3306965155773552057/200000000000000000),(367997090825037559/1953125000000000),(947507318404560121/1000000000000000000)⟩,(988642204017253493/1000000000000000000),(418490431808734459/1000000000000000000),(216961267031096021/1000000000000000000),(83863069558543969/500000000000000000)⟩
theorem valid1512 : certificate1512.Valid := by decide +kernel
theorem sound1512 : certificate1512.Sound := rat_cut_bin_certificate_sound certificate1512 profilesValid1512 numericValid1512 valid1512

def retention1513 : RatCutRetentionCertificate := ⟨(249/4000),(499/8000),(1/2),(5675810807006000941/1000000000000000000),(21/20),(8889907541808068399260854204886468244519/9081297291209601505600000000000000000000),false,MergedCutProfiles.Batch244.profile9766,(fun _ => MergedCutProfiles.Batch244.profile9766)⟩
theorem profilesValid1513 : retention1513.ProfilesValid := by
  exact MergedCutProfiles.Batch244.valid9766
theorem numericValid1513 : retention1513.NumericValid := by decide +kernel
def certificate1513 : RatCutBinCertificate := ⟨⟨retention1513,(1332090844598504437/500000000000000000),(40014422526402453/200000000000000000),(3306965155773552057/200000000000000000),(367997090825037559/1953125000000000),(945070263475494149/1000000000000000000)⟩,(988642204017253493/1000000000000000000),(104892398519356843/250000000000000000),(216022622836710661/1000000000000000000),(41711937717968127/250000000000000000)⟩
theorem valid1513 : certificate1513.Valid := by decide +kernel
theorem sound1513 : certificate1513.Sound := rat_cut_bin_certificate_sound certificate1513 profilesValid1513 numericValid1513 valid1513

def retention1514 : RatCutRetentionCertificate := ⟨(499/8000),(1/16),(1290749874291714133/11331850113481391492),(223301309621467113/250000000000000000),(51/20),(148745575996800112411/80000000000000000000),true,MergedCutProfiles.Batch244.profile9770,![MergedCutProfiles.Batch244.profile9770,MergedCutProfiles.Batch244.profile9771,MergedCutProfiles.Batch244.profile9772,MergedCutProfiles.Batch244.profile9773,MergedCutProfiles.Batch244.profile9774,MergedCutProfiles.Batch244.profile9775,MergedCutProfiles.Batch244.profile9776,MergedCutProfiles.Batch244.profile9777,MergedCutProfiles.Batch244.profile9778,MergedCutProfiles.Batch244.profile9779,MergedCutProfiles.Batch244.profile9780,MergedCutProfiles.Batch244.profile9781,MergedCutProfiles.Batch244.profile9782,MergedCutProfiles.Batch244.profile9783,MergedCutProfiles.Batch244.profile9784,MergedCutProfiles.Batch244.profile9785]⟩
theorem profilesValid1514 : retention1514.ProfilesValid := by
  change ∀ j : Fin 16, (retention1514.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch244.valid9770
  · exact MergedCutProfiles.Batch244.valid9771
  · exact MergedCutProfiles.Batch244.valid9772
  · exact MergedCutProfiles.Batch244.valid9773
  · exact MergedCutProfiles.Batch244.valid9774
  · exact MergedCutProfiles.Batch244.valid9775
  · exact MergedCutProfiles.Batch244.valid9776
  · exact MergedCutProfiles.Batch244.valid9777
  · exact MergedCutProfiles.Batch244.valid9778
  · exact MergedCutProfiles.Batch244.valid9779
  · exact MergedCutProfiles.Batch244.valid9780
  · exact MergedCutProfiles.Batch244.valid9781
  · exact MergedCutProfiles.Batch244.valid9782
  · exact MergedCutProfiles.Batch244.valid9783
  · exact MergedCutProfiles.Batch244.valid9784
  · exact MergedCutProfiles.Batch244.valid9785
theorem numericValid1514 : retention1514.NumericValid := by decide +kernel
def certificate1514 : RatCutBinCertificate := ⟨⟨retention1514,(2343205138188501917/1000000000000000000),(50258241146397749/250000000000000000),(3314698326419687903/200000000000000000),(93977194418985317703/500000000000000000),(3573616145928561/2000000000000000)⟩,(990001296168243611/1000000000000000000),(43210825971630279/125000000000000000),(143555337212586189/500000000000000000),(151983074940605459/1000000000000000000)⟩
theorem valid1514 : certificate1514.Valid := by decide +kernel
theorem sound1514 : certificate1514.Sound := rat_cut_bin_certificate_sound certificate1514 profilesValid1514 numericValid1514 valid1514

def retention1515 : RatCutRetentionCertificate := ⟨(499/8000),(1/16),(2804847454106476565/11331850113481391492),(1290749874291714133/1000000000000000000),(37/20),(1941747593118166524109/1280000000000000000000),true,MergedCutProfiles.Batch244.profile9786,![MergedCutProfiles.Batch244.profile9786,MergedCutProfiles.Batch244.profile9787,MergedCutProfiles.Batch244.profile9788,MergedCutProfiles.Batch244.profile9789,MergedCutProfiles.Batch244.profile9790,MergedCutProfiles.Batch244.profile9782,MergedCutProfiles.Batch244.profile9791,MergedCutProfiles.Batch244.profile9792,MergedCutProfiles.Batch244.profile9793,MergedCutProfiles.Batch244.profile9794,MergedCutProfiles.Batch244.profile9795,MergedCutProfiles.Batch244.profile9796,MergedCutProfiles.Batch244.profile9797,MergedCutProfiles.Batch244.profile9798,MergedCutProfiles.Batch244.profile9799,MergedCutProfiles.Batch245.profile9800]⟩
theorem profilesValid1515 : retention1515.ProfilesValid := by
  change ∀ j : Fin 16, (retention1515.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch244.valid9786
  · exact MergedCutProfiles.Batch244.valid9787
  · exact MergedCutProfiles.Batch244.valid9788
  · exact MergedCutProfiles.Batch244.valid9789
  · exact MergedCutProfiles.Batch244.valid9790
  · exact MergedCutProfiles.Batch244.valid9782
  · exact MergedCutProfiles.Batch244.valid9791
  · exact MergedCutProfiles.Batch244.valid9792
  · exact MergedCutProfiles.Batch244.valid9793
  · exact MergedCutProfiles.Batch244.valid9794
  · exact MergedCutProfiles.Batch244.valid9795
  · exact MergedCutProfiles.Batch244.valid9796
  · exact MergedCutProfiles.Batch244.valid9797
  · exact MergedCutProfiles.Batch244.valid9798
  · exact MergedCutProfiles.Batch244.valid9799
  · exact MergedCutProfiles.Batch245.valid9800
theorem numericValid1515 : retention1515.NumericValid := by decide +kernel
def certificate1515 : RatCutBinCertificate := ⟨⟨retention1515,(2343205138188501917/1000000000000000000),(50258241146397749/250000000000000000),(3314698326419687903/200000000000000000),(93977194418985317703/500000000000000000),(1464384972312087133/1000000000000000000)⟩,(990001296168243611/1000000000000000000),(93169703753319967/250000000000000000),(25946988705269307/100000000000000000),(30480299893886653/200000000000000000)⟩
theorem valid1515 : certificate1515.Valid := by decide +kernel
theorem sound1515 : certificate1515.Sound := rat_cut_bin_certificate_sound certificate1515 profilesValid1515 numericValid1515 valid1515

def retention1516 : RatCutRetentionCertificate := ⟨(499/8000),(1/16),(4848247749263962729/11331850113481391492),(560969490821295313/200000000000000000),(23/20),(284907450602658531041/256000000000000000000),true,MergedCutProfiles.Batch245.profile9801,![MergedCutProfiles.Batch245.profile9801,MergedCutProfiles.Batch245.profile9802,MergedCutProfiles.Batch245.profile9803,MergedCutProfiles.Batch244.profile9784,MergedCutProfiles.Batch245.profile9804,MergedCutProfiles.Batch245.profile9805,MergedCutProfiles.Batch245.profile9806,MergedCutProfiles.Batch245.profile9807,MergedCutProfiles.Batch245.profile9808,MergedCutProfiles.Batch245.profile9809,MergedCutProfiles.Batch245.profile9810,MergedCutProfiles.Batch245.profile9811,MergedCutProfiles.Batch245.profile9812,MergedCutProfiles.Batch245.profile9813,MergedCutProfiles.Batch245.profile9814,MergedCutProfiles.Batch245.profile9815]⟩
theorem profilesValid1516 : retention1516.ProfilesValid := by
  change ∀ j : Fin 16, (retention1516.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch245.valid9801
  · exact MergedCutProfiles.Batch245.valid9802
  · exact MergedCutProfiles.Batch245.valid9803
  · exact MergedCutProfiles.Batch244.valid9784
  · exact MergedCutProfiles.Batch245.valid9804
  · exact MergedCutProfiles.Batch245.valid9805
  · exact MergedCutProfiles.Batch245.valid9806
  · exact MergedCutProfiles.Batch245.valid9807
  · exact MergedCutProfiles.Batch245.valid9808
  · exact MergedCutProfiles.Batch245.valid9809
  · exact MergedCutProfiles.Batch245.valid9810
  · exact MergedCutProfiles.Batch245.valid9811
  · exact MergedCutProfiles.Batch245.valid9812
  · exact MergedCutProfiles.Batch245.valid9813
  · exact MergedCutProfiles.Batch245.valid9814
  · exact MergedCutProfiles.Batch245.valid9815
theorem numericValid1516 : retention1516.NumericValid := by decide +kernel
def certificate1516 : RatCutBinCertificate := ⟨⟨retention1516,(2343205138188501917/1000000000000000000),(50258241146397749/250000000000000000),(3314698326419687903/200000000000000000),(93977194418985317703/500000000000000000),(5401114588026143/5000000000000000)⟩,(990001296168243611/1000000000000000000),(424453068591465101/1000000000000000000),(211809613638380553/1000000000000000000),(152309924610509991/1000000000000000000)⟩
theorem valid1516 : certificate1516.Valid := by decide +kernel
theorem sound1516 : certificate1516.Sound := rat_cut_bin_certificate_sound certificate1516 profilesValid1516 numericValid1516 valid1516

def retention1517 : RatCutRetentionCertificate := ⟨(499/8000),(1/16),(1365781729037904797/2832962528370347873),(4848247749263962729/1000000000000000000),1,(253537545832665519529/256000000000000000000),true,MergedCutProfiles.Batch245.profile9816,![MergedCutProfiles.Batch245.profile9816,MergedCutProfiles.Batch245.profile9817,MergedCutProfiles.Batch245.profile9818,MergedCutProfiles.Batch245.profile9819,MergedCutProfiles.Batch245.profile9820,MergedCutProfiles.Batch245.profile9821,MergedCutProfiles.Batch245.profile9822,MergedCutProfiles.Batch245.profile9823,MergedCutProfiles.Batch245.profile9824,MergedCutProfiles.Batch245.profile9825,MergedCutProfiles.Batch245.profile9826,MergedCutProfiles.Batch245.profile9827,MergedCutProfiles.Batch245.profile9828,MergedCutProfiles.Batch245.profile9829,MergedCutProfiles.Batch245.profile9830,MergedCutProfiles.Batch245.profile9831]⟩
theorem profilesValid1517 : retention1517.ProfilesValid := by
  change ∀ j : Fin 16, (retention1517.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch245.valid9816
  · exact MergedCutProfiles.Batch245.valid9817
  · exact MergedCutProfiles.Batch245.valid9818
  · exact MergedCutProfiles.Batch245.valid9819
  · exact MergedCutProfiles.Batch245.valid9820
  · exact MergedCutProfiles.Batch245.valid9821
  · exact MergedCutProfiles.Batch245.valid9822
  · exact MergedCutProfiles.Batch245.valid9823
  · exact MergedCutProfiles.Batch245.valid9824
  · exact MergedCutProfiles.Batch245.valid9825
  · exact MergedCutProfiles.Batch245.valid9826
  · exact MergedCutProfiles.Batch245.valid9827
  · exact MergedCutProfiles.Batch245.valid9828
  · exact MergedCutProfiles.Batch245.valid9829
  · exact MergedCutProfiles.Batch245.valid9830
  · exact MergedCutProfiles.Batch245.valid9831
theorem numericValid1517 : retention1517.NumericValid := by decide +kernel
def certificate1517 : RatCutBinCertificate := ⟨⟨retention1517,(2343205138188501917/1000000000000000000),(50258241146397749/250000000000000000),(3314698326419687903/200000000000000000),(93977194418985317703/500000000000000000),(961952182978528651/1000000000000000000)⟩,(990001296168243611/1000000000000000000),(444053412191923653/1000000000000000000),(195459059578628107/1000000000000000000),(155152006354991731/1000000000000000000)⟩
theorem valid1517 : certificate1517.Valid := by decide +kernel
theorem sound1517 : certificate1517.Sound := rat_cut_bin_certificate_sound certificate1517 profilesValid1517 numericValid1517 valid1517

def retention1518 : RatCutRetentionCertificate := ⟨(499/8000),(1/16),(2814332562418964701/5665925056740695746),(1365781729037904797/250000000000000000),(11/10),(136366304006427539928420365444668341031/136578172903790479700000000000000000000),false,MergedCutProfiles.Batch245.profile9832,(fun _ => MergedCutProfiles.Batch245.profile9832)⟩
theorem profilesValid1518 : retention1518.ProfilesValid := by
  exact MergedCutProfiles.Batch245.valid9832
theorem numericValid1518 : retention1518.NumericValid := by decide +kernel
def certificate1518 : RatCutBinCertificate := ⟨⟨retention1518,(2343205138188501917/1000000000000000000),(50258241146397749/250000000000000000),(3314698326419687903/200000000000000000),(93977194418985317703/500000000000000000),(24179458177690287/25000000000000000)⟩,(990001296168243611/1000000000000000000),(54580872494601693/125000000000000000),(201533700148020373/1000000000000000000),(152893290192774707/1000000000000000000)⟩
theorem valid1518 : certificate1518.Valid := by decide +kernel
theorem sound1518 : certificate1518.Sound := rat_cut_bin_certificate_sound certificate1518 profilesValid1518 numericValid1518 valid1518

def retention1519 : RatCutRetentionCertificate := ⟨(499/8000),(1/16),(1/2),(2814332562418964701/500000000000000000),(11/10),(558966820689886526123662313387171341279/562866512483792940200000000000000000000),false,MergedCutProfiles.Batch245.profile9833,(fun _ => MergedCutProfiles.Batch245.profile9833)⟩
theorem profilesValid1519 : retention1519.ProfilesValid := by
  exact MergedCutProfiles.Batch245.valid9833
theorem numericValid1519 : retention1519.NumericValid := by decide +kernel
def certificate1519 : RatCutBinCertificate := ⟨⟨retention1519,(2343205138188501917/1000000000000000000),(50258241146397749/250000000000000000),(3314698326419687903/200000000000000000),(93977194418985317703/500000000000000000),(96180148435104701/100000000000000000)⟩,(990001296168243611/1000000000000000000),(218960213934524199/500000000000000000),(100240177514708787/500000000000000000),(15192711317275283/100000000000000000)⟩
theorem valid1519 : certificate1519.Valid := by decide +kernel
theorem sound1519 : certificate1519.Sound := rat_cut_bin_certificate_sound certificate1519 profilesValid1519 numericValid1519 valid1519

def retention1520 : RatCutRetentionCertificate := ⟨(499/8000),(1/16),(1/2),64,1,(63852996127278868732392469561083246319/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch245.profile9833,(fun _ => MergedCutProfiles.Batch245.profile9833)⟩
theorem profilesValid1520 : retention1520.ProfilesValid := by
  exact MergedCutProfiles.Batch245.valid9833
theorem numericValid1520 : retention1520.NumericValid := by decide +kernel
def certificate1520 : RatCutBinCertificate := ⟨⟨retention1520,(2343205138188501917/1000000000000000000),(50258241146397749/250000000000000000),(3314698326419687903/200000000000000000),(93977194418985317703/500000000000000000),(4846400022145271/5000000000000000)⟩,(990001296168243611/1000000000000000000),(79933800844582899/200000000000000000),(233785774887573687/1000000000000000000),(110484651866728813/500000000000000000)⟩
theorem valid1520 : certificate1520.Valid := by decide +kernel
theorem sound1520 : certificate1520.Sound := rat_cut_bin_certificate_sound certificate1520 profilesValid1520 numericValid1520 valid1520

def retention1521 : RatCutRetentionCertificate := ⟨(499/8000),(1/16),(5287978870260534287/11331850113481391492),(337930889062405409/100000000000000000),(6/5),(14292565912475331244882529516446226879/13517235562496216360000000000000000000),false,MergedCutProfiles.Batch245.profile9834,(fun _ => MergedCutProfiles.Batch245.profile9834)⟩
theorem profilesValid1521 : retention1521.ProfilesValid := by
  exact MergedCutProfiles.Batch245.valid9834
theorem numericValid1521 : retention1521.NumericValid := by decide +kernel
def certificate1521 : RatCutBinCertificate := ⟨⟨retention1521,(2666259796188501917/1000000000000000000),(50258241146397749/250000000000000000),(3314698326419687903/200000000000000000),(93977194418985317703/500000000000000000),(509269503581224779/500000000000000000)⟩,(988618866104151203/1000000000000000000),(390905080745668559/1000000000000000000),(241919719673570339/1000000000000000000),(83822085365545249/500000000000000000)⟩
theorem valid1521 : certificate1521.Valid := by decide +kernel
theorem sound1521 : certificate1521.Sound := rat_cut_bin_certificate_sound certificate1521 profilesValid1521 numericValid1521 valid1521

def retention1522 : RatCutRetentionCertificate := ⟨(499/8000),(1/16),(1403324031683467050/2832962528370347873),(5287978870260534287/1000000000000000000),(11/10),(2115069584441572535318810689903870710311/2115191548104213714800000000000000000000),false,MergedCutProfiles.Batch245.profile9835,(fun _ => MergedCutProfiles.Batch245.profile9835)⟩
theorem profilesValid1522 : retention1522.ProfilesValid := by
  exact MergedCutProfiles.Batch245.valid9835
theorem numericValid1522 : retention1522.NumericValid := by decide +kernel
def certificate1522 : RatCutBinCertificate := ⟨⟨retention1522,(2666259796188501917/1000000000000000000),(50258241146397749/250000000000000000),(3314698326419687903/200000000000000000),(93977194418985317703/500000000000000000),(482180255290634233/500000000000000000)⟩,(988618866104151203/1000000000000000000),(412866421290378429/1000000000000000000),(44379632994605649/200000000000000000),(16697142578953729/100000000000000000)⟩
theorem valid1522 : certificate1522.Valid := by decide +kernel
theorem sound1522 : certificate1522.Sound := rat_cut_bin_certificate_sound certificate1522 profilesValid1522 numericValid1522 valid1522

def retention1523 : RatCutRetentionCertificate := ⟨(499/8000),(1/16),(1/2),(28066480633669341/5000000000000000),(11/10),(5573936528206472648329985097385846199/5613296126733868200000000000000000000),false,MergedCutProfiles.Batch245.profile9833,(fun _ => MergedCutProfiles.Batch245.profile9833)⟩
theorem profilesValid1523 : retention1523.ProfilesValid := by
  exact MergedCutProfiles.Batch245.valid9833
theorem numericValid1523 : retention1523.NumericValid := by decide +kernel
def certificate1523 : RatCutBinCertificate := ⟨⟨retention1523,(2666259796188501917/1000000000000000000),(50258241146397749/250000000000000000),(3314698326419687903/200000000000000000),(93977194418985317703/500000000000000000),(239351674766990169/250000000000000000)⟩,(988618866104151203/1000000000000000000),(83173028395362827/200000000000000000),(219256347363934199/1000000000000000000),(8260137162088591/50000000000000000)⟩
theorem valid1523 : certificate1523.Valid := by decide +kernel
theorem sound1523 : certificate1523.Sound := rat_cut_bin_certificate_sound certificate1523 profilesValid1523 numericValid1523 valid1523

def certificates : List RatCutBinCertificate := [certificate1512,certificate1513,certificate1514,certificate1515,certificate1516,certificate1517,certificate1518,certificate1519,certificate1520,certificate1521,certificate1522,certificate1523]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1512,List.forall_mem_cons.mpr ⟨sound1513,List.forall_mem_cons.mpr ⟨sound1514,List.forall_mem_cons.mpr ⟨sound1515,List.forall_mem_cons.mpr ⟨sound1516,List.forall_mem_cons.mpr ⟨sound1517,List.forall_mem_cons.mpr ⟨sound1518,List.forall_mem_cons.mpr ⟨sound1519,List.forall_mem_cons.mpr ⟨sound1520,List.forall_mem_cons.mpr ⟨sound1521,List.forall_mem_cons.mpr ⟨sound1522,List.forall_mem_cons.mpr ⟨sound1523,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch126
