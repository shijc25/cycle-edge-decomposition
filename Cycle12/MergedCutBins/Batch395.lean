import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch669
import Cycle12.MergedCutProfiles.Batch670

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch395

def retention4740 : RatCutRetentionCertificate := ⟨(31/800),(311/8000),(587050624248854984/3356130979488257458691),(17983856492281853/31250000000000000),4,(8895116643314737201/4000000000000000000),true,MergedCutProfiles.Batch669.profile26760,![MergedCutProfiles.Batch669.profile26760,MergedCutProfiles.Batch669.profile26761,MergedCutProfiles.Batch669.profile26762,MergedCutProfiles.Batch669.profile26763,MergedCutProfiles.Batch669.profile26764,MergedCutProfiles.Batch669.profile26765,MergedCutProfiles.Batch669.profile26766,MergedCutProfiles.Batch669.profile26767,MergedCutProfiles.Batch669.profile26768,MergedCutProfiles.Batch669.profile26769,MergedCutProfiles.Batch669.profile26770,MergedCutProfiles.Batch669.profile26771,MergedCutProfiles.Batch669.profile26772,MergedCutProfiles.Batch669.profile26773,MergedCutProfiles.Batch669.profile26774,MergedCutProfiles.Batch669.profile26775]⟩
theorem profilesValid4740 : retention4740.ProfilesValid := by
  change ∀ j : Fin 16, (retention4740.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch669.valid26760
  · exact MergedCutProfiles.Batch669.valid26761
  · exact MergedCutProfiles.Batch669.valid26762
  · exact MergedCutProfiles.Batch669.valid26763
  · exact MergedCutProfiles.Batch669.valid26764
  · exact MergedCutProfiles.Batch669.valid26765
  · exact MergedCutProfiles.Batch669.valid26766
  · exact MergedCutProfiles.Batch669.valid26767
  · exact MergedCutProfiles.Batch669.valid26768
  · exact MergedCutProfiles.Batch669.valid26769
  · exact MergedCutProfiles.Batch669.valid26770
  · exact MergedCutProfiles.Batch669.valid26771
  · exact MergedCutProfiles.Batch669.valid26772
  · exact MergedCutProfiles.Batch669.valid26773
  · exact MergedCutProfiles.Batch669.valid26774
  · exact MergedCutProfiles.Batch669.valid26775
theorem numericValid4740 : retention4740.NumericValid := by decide +kernel
def certificate4740 : RatCutBinCertificate := ⟨⟨retention4740,(188063001914930577/100000000000000000),(6856308347981701/100000000000000000),(11138194659233295489/1000000000000000000),(18703095331422374979123/500000000000000000),(217747295067040249/100000000000000000)⟩,(999953146943627557/1000000000000000000),(89650175719715141/125000000000000000),(22200933703949307/500000000000000000),(19547046481018131/1000000000000000000)⟩
theorem valid4740 : certificate4740.Valid := by decide +kernel
theorem sound4740 : certificate4740.Sound := rat_cut_bin_certificate_sound certificate4740 profilesValid4740 numericValid4740 valid4740

def retention4741 : RatCutRetentionCertificate := ⟨(31/800),(311/8000),(164018756000000000/479447282784036779813),(73381328031106873/125000000000000000),4,(71887917127724087161/32000000000000000000),true,MergedCutProfiles.Batch669.profile26761,![MergedCutProfiles.Batch669.profile26761,MergedCutProfiles.Batch669.profile26763,MergedCutProfiles.Batch669.profile26765,MergedCutProfiles.Batch669.profile26776,MergedCutProfiles.Batch669.profile26769,MergedCutProfiles.Batch669.profile26771,MergedCutProfiles.Batch669.profile26773,MergedCutProfiles.Batch669.profile26774,MergedCutProfiles.Batch669.profile26777,MergedCutProfiles.Batch669.profile26778,MergedCutProfiles.Batch669.profile26779,MergedCutProfiles.Batch669.profile26780,MergedCutProfiles.Batch669.profile26781,MergedCutProfiles.Batch669.profile26782,MergedCutProfiles.Batch669.profile26783,MergedCutProfiles.Batch669.profile26784]⟩
theorem profilesValid4741 : retention4741.ProfilesValid := by
  change ∀ j : Fin 16, (retention4741.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch669.valid26761
  · exact MergedCutProfiles.Batch669.valid26763
  · exact MergedCutProfiles.Batch669.valid26765
  · exact MergedCutProfiles.Batch669.valid26776
  · exact MergedCutProfiles.Batch669.valid26769
  · exact MergedCutProfiles.Batch669.valid26771
  · exact MergedCutProfiles.Batch669.valid26773
  · exact MergedCutProfiles.Batch669.valid26774
  · exact MergedCutProfiles.Batch669.valid26777
  · exact MergedCutProfiles.Batch669.valid26778
  · exact MergedCutProfiles.Batch669.valid26779
  · exact MergedCutProfiles.Batch669.valid26780
  · exact MergedCutProfiles.Batch669.valid26781
  · exact MergedCutProfiles.Batch669.valid26782
  · exact MergedCutProfiles.Batch669.valid26783
  · exact MergedCutProfiles.Batch669.valid26784
theorem numericValid4741 : retention4741.NumericValid := by decide +kernel
def certificate4741 : RatCutBinCertificate := ⟨⟨retention4741,(188063001914930577/100000000000000000),(6856308347981701/100000000000000000),(11138194659233295489/1000000000000000000),(18703095331422374979123/500000000000000000),(2200191200809613719/1000000000000000000)⟩,(999953146943627557/1000000000000000000),(28014005752987507/40000000000000000),(12550684816206539/250000000000000000),(11185950118135639/500000000000000000)⟩
theorem valid4741 : certificate4741.Valid := by decide +kernel
theorem sound4741 : certificate4741.Sound := rat_cut_bin_certificate_sound certificate4741 profilesValid4741 numericValid4741 valid4741

def retention4742 : RatCutRetentionCertificate := ⟨(31/800),(311/8000),(3062129843340579441/3356130979488257458691),(287032823/250000000),(11/4),(995329793058286121252820154290293341/417502288000000000000000000000000000),true,MergedCutProfiles.Batch669.profile26764,![MergedCutProfiles.Batch669.profile26764,MergedCutProfiles.Batch669.profile26769,MergedCutProfiles.Batch669.profile26774,MergedCutProfiles.Batch669.profile26785,MergedCutProfiles.Batch669.profile26781,MergedCutProfiles.Batch669.profile26784,MergedCutProfiles.Batch669.profile26786,MergedCutProfiles.Batch669.profile26787,MergedCutProfiles.Batch669.profile26788,MergedCutProfiles.Batch669.profile26789,MergedCutProfiles.Batch669.profile26790,MergedCutProfiles.Batch669.profile26791,MergedCutProfiles.Batch669.profile26792,MergedCutProfiles.Batch669.profile26793,MergedCutProfiles.Batch669.profile26794,MergedCutProfiles.Batch669.profile26795]⟩
theorem profilesValid4742 : retention4742.ProfilesValid := by
  change ∀ j : Fin 16, (retention4742.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch669.valid26764
  · exact MergedCutProfiles.Batch669.valid26769
  · exact MergedCutProfiles.Batch669.valid26774
  · exact MergedCutProfiles.Batch669.valid26785
  · exact MergedCutProfiles.Batch669.valid26781
  · exact MergedCutProfiles.Batch669.valid26784
  · exact MergedCutProfiles.Batch669.valid26786
  · exact MergedCutProfiles.Batch669.valid26787
  · exact MergedCutProfiles.Batch669.valid26788
  · exact MergedCutProfiles.Batch669.valid26789
  · exact MergedCutProfiles.Batch669.valid26790
  · exact MergedCutProfiles.Batch669.valid26791
  · exact MergedCutProfiles.Batch669.valid26792
  · exact MergedCutProfiles.Batch669.valid26793
  · exact MergedCutProfiles.Batch669.valid26794
  · exact MergedCutProfiles.Batch669.valid26795
theorem numericValid4742 : retention4742.NumericValid := by decide +kernel
def certificate4742 : RatCutBinCertificate := ⟨⟨retention4742,(188063001914930577/100000000000000000),(6856308347981701/100000000000000000),(11138194659233295489/1000000000000000000),(18703095331422374979123/500000000000000000),(147010929928947363/62500000000000000)⟩,(999953146943627557/1000000000000000000),(110070666013838249/250000000000000000),(198536203873161279/1000000000000000000),(33402658654587511/250000000000000000)⟩
theorem valid4742 : certificate4742.Valid := by decide +kernel
theorem sound4742 : certificate4742.Sound := rat_cut_bin_certificate_sound certificate4742 profilesValid4742 numericValid4742 valid4742

def retention4743 : RatCutRetentionCertificate := ⟨(31/800),(311/8000),(64000000000000000000/3356130979488257458691),(3062129843340579441/1000000000000000000),(3/2),(107857363311394081424209575096273433919/48994077493449271056000000000000000000),true,MergedCutProfiles.Batch669.profile26796,![MergedCutProfiles.Batch669.profile26796,MergedCutProfiles.Batch669.profile26797,MergedCutProfiles.Batch669.profile26798,MergedCutProfiles.Batch669.profile26799,MergedCutProfiles.Batch670.profile26800,MergedCutProfiles.Batch670.profile26801,MergedCutProfiles.Batch670.profile26802,MergedCutProfiles.Batch670.profile26803,MergedCutProfiles.Batch670.profile26804,MergedCutProfiles.Batch670.profile26805,MergedCutProfiles.Batch670.profile26806,MergedCutProfiles.Batch670.profile26807,MergedCutProfiles.Batch670.profile26808,MergedCutProfiles.Batch670.profile26809,MergedCutProfiles.Batch670.profile26810,MergedCutProfiles.Batch670.profile26811]⟩
theorem profilesValid4743 : retention4743.ProfilesValid := by
  change ∀ j : Fin 16, (retention4743.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch669.valid26796
  · exact MergedCutProfiles.Batch669.valid26797
  · exact MergedCutProfiles.Batch669.valid26798
  · exact MergedCutProfiles.Batch669.valid26799
  · exact MergedCutProfiles.Batch670.valid26800
  · exact MergedCutProfiles.Batch670.valid26801
  · exact MergedCutProfiles.Batch670.valid26802
  · exact MergedCutProfiles.Batch670.valid26803
  · exact MergedCutProfiles.Batch670.valid26804
  · exact MergedCutProfiles.Batch670.valid26805
  · exact MergedCutProfiles.Batch670.valid26806
  · exact MergedCutProfiles.Batch670.valid26807
  · exact MergedCutProfiles.Batch670.valid26808
  · exact MergedCutProfiles.Batch670.valid26809
  · exact MergedCutProfiles.Batch670.valid26810
  · exact MergedCutProfiles.Batch670.valid26811
theorem numericValid4743 : retention4743.NumericValid := by decide +kernel
def certificate4743 : RatCutBinCertificate := ⟨⟨retention4743,(188063001914930577/100000000000000000),(6856308347981701/100000000000000000),(11138194659233295489/1000000000000000000),(18703095331422374979123/500000000000000000),(136504496251722851/62500000000000000)⟩,(999953146943627557/1000000000000000000),(40358924547619897/125000000000000000),(312109724108083853/1000000000000000000),(69008792217251323/200000000000000000)⟩
theorem valid4743 : certificate4743.Valid := by decide +kernel
theorem sound4743 : certificate4743.Sound := rat_cut_bin_certificate_sound certificate4743 profilesValid4743 numericValid4743 valid4743

def retention4744 : RatCutRetentionCertificate := ⟨(31/800),(311/8000),(1/2),64,1,(10215323140453216190340153356783243319/10240000000000000000000000000000000000),false,MergedCutProfiles.Batch670.profile26812,(fun _ => MergedCutProfiles.Batch670.profile26812)⟩
theorem profilesValid4744 : retention4744.ProfilesValid := by
  exact MergedCutProfiles.Batch670.valid26812
theorem numericValid4744 : retention4744.NumericValid := by decide +kernel
def certificate4744 : RatCutBinCertificate := ⟨⟨retention4744,(188063001914930577/100000000000000000),(6856308347981701/100000000000000000),(11138194659233295489/1000000000000000000),(18703095331422374979123/500000000000000000),(986013606781686979/1000000000000000000)⟩,(999953146943627557/1000000000000000000),(6547021938154981/12500000000000000),(137511878274004273/1000000000000000000),(133525022465506127/1000000000000000000)⟩
theorem valid4744 : certificate4744.Valid := by decide +kernel
theorem sound4744 : certificate4744.Sound := rat_cut_bin_certificate_sound certificate4744 profilesValid4744 numericValid4744 valid4744

def retention4745 : RatCutRetentionCertificate := ⟨(31/800),(311/8000),(64000000000000000000/3356130979488257458691),(7486341369963121837/250000000000000000),1,(262757487369782811766977910278440517007/119781461919409949392000000000000000000),false,MergedCutProfiles.Batch670.profile26813,(fun _ => MergedCutProfiles.Batch670.profile26813)⟩
theorem profilesValid4745 : retention4745.ProfilesValid := by
  exact MergedCutProfiles.Batch670.valid26813
theorem numericValid4745 : retention4745.NumericValid := by decide +kernel
def certificate4745 : RatCutBinCertificate := ⟨⟨retention4745,(175364495514930577/100000000000000000),(6856308347981701/100000000000000000),(11138194659233295489/1000000000000000000),(18703095331422374979123/500000000000000000),(27285572660200117/12500000000000000)⟩,(249989077648698353/250000000000000000),(1324441820896603/62500000000000000),(217597993075112869/250000000000000000),(885383962818327369/500000000000000000)⟩
theorem valid4745 : certificate4745.Valid := by decide +kernel
theorem sound4745 : certificate4745.Sound := rat_cut_bin_certificate_sound certificate4745 profilesValid4745 numericValid4745 valid4745

def retention4746 : RatCutRetentionCertificate := ⟨(31/800),(311/8000),(1/2),64,1,(10215323140453216190340153356783243319/10240000000000000000000000000000000000),false,MergedCutProfiles.Batch670.profile26812,(fun _ => MergedCutProfiles.Batch670.profile26812)⟩
theorem profilesValid4746 : retention4746.ProfilesValid := by
  exact MergedCutProfiles.Batch670.valid26812
theorem numericValid4746 : retention4746.NumericValid := by decide +kernel
def certificate4746 : RatCutBinCertificate := ⟨⟨retention4746,(175364495514930577/100000000000000000),(6856308347981701/100000000000000000),(11138194659233295489/1000000000000000000),(18703095331422374979123/500000000000000000),(986795285326499869/1000000000000000000)⟩,(249989077648698353/250000000000000000),(4687581833520417/100000000000000000),(398400730508917739/500000000000000000),(774306446857837923/1000000000000000000)⟩
theorem valid4746 : certificate4746.Valid := by decide +kernel
theorem sound4746 : certificate4746.Sound := rat_cut_bin_certificate_sound certificate4746 profilesValid4746 numericValid4746 valid4746

def retention4747 : RatCutRetentionCertificate := ⟨(31/800),(311/8000),(695840410693017146/3356130979488257458691),(3444754508381273/5000000000000000),4,(412051885817018371620489606104342031/172237725419063650000000000000000000),false,MergedCutProfiles.Batch670.profile26814,(fun _ => MergedCutProfiles.Batch670.profile26814)⟩
theorem profilesValid4747 : retention4747.ProfilesValid := by
  exact MergedCutProfiles.Batch670.valid26814
theorem numericValid4747 : retention4747.NumericValid := by decide +kernel
def certificate4747 : RatCutBinCertificate := ⟨⟨retention4747,(183996467914930577/100000000000000000),(6856308347981701/100000000000000000),(11138194659233295489/1000000000000000000),(18703095331422374979123/500000000000000000),(2347039068348953/1000000000000000)⟩,(249988540015636137/250000000000000000),(106392505974468673/125000000000000000),(11674394772664639/1000000000000000000),(5647284878838041/1000000000000000000)⟩
theorem valid4747 : certificate4747.Valid := by decide +kernel
theorem sound4747 : certificate4747.Sound := rat_cut_bin_certificate_sound certificate4747 profilesValid4747 numericValid4747 valid4747

def retention4748 : RatCutRetentionCertificate := ⟨(31/800),(311/8000),(133983963256769540/479447282784036779813),(347920205346508573/500000000000000000),4,(1666850123436104734238635946262666039/695840410693017146000000000000000000),false,MergedCutProfiles.Batch670.profile26815,(fun _ => MergedCutProfiles.Batch670.profile26815)⟩
theorem profilesValid4748 : retention4748.ProfilesValid := by
  exact MergedCutProfiles.Batch670.valid26815
theorem numericValid4748 : retention4748.NumericValid := by decide +kernel
def certificate4748 : RatCutBinCertificate := ⟨⟨retention4748,(183996467914930577/100000000000000000),(6856308347981701/100000000000000000),(11138194659233295489/1000000000000000000),(18703095331422374979123/500000000000000000),(587535988513068111/250000000000000000)⟩,(249988540015636137/250000000000000000),(423906431718749893/500000000000000000),(3054294324702609/250000000000000000),(740825372886177/125000000000000000)⟩
theorem valid4748 : certificate4748.Valid := by decide +kernel
theorem sound4748 : certificate4748.Sound := rat_cut_bin_certificate_sound certificate4748 profilesValid4748 numericValid4748 valid4748

def retention4749 : RatCutRetentionCertificate := ⟨(31/800),(311/8000),(8289564565677668503/3356130979488257458691),(46894387139869339/50000000000000000),(69/20),(2235289428425362218523968116092005219/937887742797386780000000000000000000),false,MergedCutProfiles.Batch670.profile26816,(fun _ => MergedCutProfiles.Batch670.profile26816)⟩
theorem profilesValid4749 : retention4749.ProfilesValid := by
  exact MergedCutProfiles.Batch670.valid26816
theorem numericValid4749 : retention4749.NumericValid := by decide +kernel
def certificate4749 : RatCutBinCertificate := ⟨⟨retention4749,(183996467914930577/100000000000000000),(6856308347981701/100000000000000000),(11138194659233295489/1000000000000000000),(18703095331422374979123/500000000000000000),(2344247515716055017/1000000000000000000)⟩,(249988540015636137/250000000000000000),(39647782137918363/50000000000000000),(5772041907626387/250000000000000000),(2592962472441921/200000000000000000)⟩
theorem valid4749 : certificate4749.Valid := by decide +kernel
theorem sound4749 : certificate4749.Sound := rat_cut_bin_certificate_sound certificate4749 profilesValid4749 numericValid4749 valid4749

def retention4750 : RatCutRetentionCertificate := ⟨(31/800),(311/8000),(1/40),(8289564565677668503/1000000000000000000),(6/5),(38655338910753850637697159975034751553/17637371416335464900000000000000000000),false,MergedCutProfiles.Batch670.profile26817,(fun _ => MergedCutProfiles.Batch670.profile26817)⟩
theorem profilesValid4750 : retention4750.ProfilesValid := by
  exact MergedCutProfiles.Batch670.valid26817
theorem numericValid4750 : retention4750.NumericValid := by decide +kernel
def certificate4750 : RatCutBinCertificate := ⟨⟨retention4750,(183996467914930577/100000000000000000),(6856308347981701/100000000000000000),(11138194659233295489/1000000000000000000),(18703095331422374979123/500000000000000000),(1089040431377822111/500000000000000000)⟩,(249988540015636137/250000000000000000),(174266851053532777/250000000000000000),(25689837105333983/500000000000000000),(9857909361454531/125000000000000000)⟩
theorem valid4750 : certificate4750.Valid := by decide +kernel
theorem sound4750 : certificate4750.Sound := rat_cut_bin_certificate_sound certificate4750 profilesValid4750 numericValid4750 valid4750

def retention4751 : RatCutRetentionCertificate := ⟨(311/8000),(39/1000),(587298437928122940/3332425821775927600291),(287863169261897333/500000000000000000),4,(71180884454449254101/32000000000000000000),true,MergedCutProfiles.Batch670.profile26818,![MergedCutProfiles.Batch670.profile26818,MergedCutProfiles.Batch670.profile26819,MergedCutProfiles.Batch670.profile26820,MergedCutProfiles.Batch670.profile26821,MergedCutProfiles.Batch670.profile26822,MergedCutProfiles.Batch670.profile26823,MergedCutProfiles.Batch670.profile26824,MergedCutProfiles.Batch670.profile26825,MergedCutProfiles.Batch670.profile26826,MergedCutProfiles.Batch670.profile26827,MergedCutProfiles.Batch670.profile26828,MergedCutProfiles.Batch670.profile26829,MergedCutProfiles.Batch670.profile26830,MergedCutProfiles.Batch670.profile26831,MergedCutProfiles.Batch670.profile26832,MergedCutProfiles.Batch670.profile26833]⟩
theorem profilesValid4751 : retention4751.ProfilesValid := by
  change ∀ j : Fin 16, (retention4751.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch670.valid26818
  · exact MergedCutProfiles.Batch670.valid26819
  · exact MergedCutProfiles.Batch670.valid26820
  · exact MergedCutProfiles.Batch670.valid26821
  · exact MergedCutProfiles.Batch670.valid26822
  · exact MergedCutProfiles.Batch670.valid26823
  · exact MergedCutProfiles.Batch670.valid26824
  · exact MergedCutProfiles.Batch670.valid26825
  · exact MergedCutProfiles.Batch670.valid26826
  · exact MergedCutProfiles.Batch670.valid26827
  · exact MergedCutProfiles.Batch670.valid26828
  · exact MergedCutProfiles.Batch670.valid26829
  · exact MergedCutProfiles.Batch670.valid26830
  · exact MergedCutProfiles.Batch670.valid26831
  · exact MergedCutProfiles.Batch670.valid26832
  · exact MergedCutProfiles.Batch670.valid26833
theorem numericValid4751 : retention4751.NumericValid := by decide +kernel
def certificate4751 : RatCutBinCertificate := ⟨⟨retention4751,(235126540587285351/125000000000000000),(69043717129131353/1000000000000000000),(2231872470360797053/200000000000000000),(4651573464116167766979/125000000000000000),(2177850808226656309/1000000000000000000)⟩,(999952917802806253/1000000000000000000),(358545772046924049/500000000000000000),(11109598420858523/250000000000000000),(19567445699159603/1000000000000000000)⟩
theorem valid4751 : certificate4751.Valid := by decide +kernel
theorem sound4751 : certificate4751.Sound := rat_cut_bin_certificate_sound certificate4751 profilesValid4751 numericValid4751 valid4751

def certificates : List RatCutBinCertificate := [certificate4740,certificate4741,certificate4742,certificate4743,certificate4744,certificate4745,certificate4746,certificate4747,certificate4748,certificate4749,certificate4750,certificate4751]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4740,List.forall_mem_cons.mpr ⟨sound4741,List.forall_mem_cons.mpr ⟨sound4742,List.forall_mem_cons.mpr ⟨sound4743,List.forall_mem_cons.mpr ⟨sound4744,List.forall_mem_cons.mpr ⟨sound4745,List.forall_mem_cons.mpr ⟨sound4746,List.forall_mem_cons.mpr ⟨sound4747,List.forall_mem_cons.mpr ⟨sound4748,List.forall_mem_cons.mpr ⟨sound4749,List.forall_mem_cons.mpr ⟨sound4750,List.forall_mem_cons.mpr ⟨sound4751,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch395
