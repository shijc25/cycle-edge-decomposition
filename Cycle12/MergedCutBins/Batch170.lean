import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch021
import Cycle12.MergedCutProfiles.Batch022
import Cycle12.MergedCutProfiles.Batch023
import Cycle12.MergedCutProfiles.Batch318
import Cycle12.MergedCutProfiles.Batch319
import Cycle12.MergedCutProfiles.Batch320

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch170

def retention2040 : RatCutRetentionCertificate := ⟨(17/1000),(9/500),(610977512500000000/173833819108730224839),(156552411019054643/250000000000000000),4,(36279456672042679573/16000000000000000000),true,MergedCutProfiles.Batch318.profile12731,![MergedCutProfiles.Batch318.profile12731,MergedCutProfiles.Batch021.profile861,MergedCutProfiles.Batch318.profile12744,MergedCutProfiles.Batch021.profile862,MergedCutProfiles.Batch318.profile12745,MergedCutProfiles.Batch318.profile12746,MergedCutProfiles.Batch318.profile12747,MergedCutProfiles.Batch021.profile864,MergedCutProfiles.Batch318.profile12748,MergedCutProfiles.Batch021.profile865,MergedCutProfiles.Batch318.profile12749,MergedCutProfiles.Batch021.profile852,MergedCutProfiles.Batch318.profile12750,MergedCutProfiles.Batch318.profile12751,MergedCutProfiles.Batch318.profile12752,MergedCutProfiles.Batch318.profile12753]⟩
theorem profilesValid2040 : retention2040.ProfilesValid := by
  change ∀ j : Fin 16, (retention2040.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch318.valid12731
  · exact MergedCutProfiles.Batch021.valid861
  · exact MergedCutProfiles.Batch318.valid12744
  · exact MergedCutProfiles.Batch021.valid862
  · exact MergedCutProfiles.Batch318.valid12745
  · exact MergedCutProfiles.Batch318.valid12746
  · exact MergedCutProfiles.Batch318.valid12747
  · exact MergedCutProfiles.Batch021.valid864
  · exact MergedCutProfiles.Batch318.valid12748
  · exact MergedCutProfiles.Batch021.valid865
  · exact MergedCutProfiles.Batch318.valid12749
  · exact MergedCutProfiles.Batch021.valid852
  · exact MergedCutProfiles.Batch318.valid12750
  · exact MergedCutProfiles.Batch318.valid12751
  · exact MergedCutProfiles.Batch318.valid12752
  · exact MergedCutProfiles.Batch318.valid12753
theorem numericValid2040 : retention2040.NumericValid := by decide +kernel
def certificate2040 : RatCutBinCertificate := ⟨⟨retention2040,(1885819660274741523/1000000000000000000),(13522397103991873/1000000000000000000),(8218226185730691081/1000000000000000000),(179417633552813698357/62500000000000000),(2255054190738219553/1000000000000000000)⟩,(7807429426585233/7812500000000000),(525081127361802151/1000000000000000000),(68330138686814143/500000000000000000),(15710373115722439/250000000000000000)⟩
theorem valid2040 : certificate2040.Valid := by decide +kernel
theorem sound2040 : certificate2040.Sound := rat_cut_bin_certificate_sound certificate2040 profilesValid2040 numericValid2040 valid2040

def retention2041 : RatCutRetentionCertificate := ⟨(17/1000),(9/500),(1402009731649328653/347667638217460449678),(48878201/40000000),(49/20),(2784533453592698768230836061780323919/1221955025000000000000000000000000000),true,MergedCutProfiles.Batch318.profile12754,![MergedCutProfiles.Batch318.profile12754,MergedCutProfiles.Batch318.profile12755,MergedCutProfiles.Batch021.profile848,MergedCutProfiles.Batch318.profile12737,MergedCutProfiles.Batch318.profile12739,MergedCutProfiles.Batch021.profile849,MergedCutProfiles.Batch318.profile12743,MergedCutProfiles.Batch318.profile12748,MergedCutProfiles.Batch021.profile851,MergedCutProfiles.Batch318.profile12756,MergedCutProfiles.Batch021.profile842,MergedCutProfiles.Batch021.profile843,MergedCutProfiles.Batch318.profile12752,MergedCutProfiles.Batch318.profile12753,MergedCutProfiles.Batch318.profile12757,MergedCutProfiles.Batch318.profile12758]⟩
theorem profilesValid2041 : retention2041.ProfilesValid := by
  change ∀ j : Fin 16, (retention2041.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch318.valid12754
  · exact MergedCutProfiles.Batch318.valid12755
  · exact MergedCutProfiles.Batch021.valid848
  · exact MergedCutProfiles.Batch318.valid12737
  · exact MergedCutProfiles.Batch318.valid12739
  · exact MergedCutProfiles.Batch021.valid849
  · exact MergedCutProfiles.Batch318.valid12743
  · exact MergedCutProfiles.Batch318.valid12748
  · exact MergedCutProfiles.Batch021.valid851
  · exact MergedCutProfiles.Batch318.valid12756
  · exact MergedCutProfiles.Batch021.valid842
  · exact MergedCutProfiles.Batch021.valid843
  · exact MergedCutProfiles.Batch318.valid12752
  · exact MergedCutProfiles.Batch318.valid12753
  · exact MergedCutProfiles.Batch318.valid12757
  · exact MergedCutProfiles.Batch318.valid12758
theorem numericValid2041 : retention2041.NumericValid := by decide +kernel
def certificate2041 : RatCutBinCertificate := ⟨⟨retention2041,(1885819660274741523/1000000000000000000),(13522397103991873/1000000000000000000),(8218226185730691081/1000000000000000000),(179417633552813698357/62500000000000000),(454230111780475957/200000000000000000)⟩,(7807429426585233/7812500000000000),(36008880904625161/100000000000000000),(272110471165405633/1000000000000000000),(1503632664650319/7812500000000000)⟩
theorem valid2041 : certificate2041.Valid := by decide +kernel
theorem sound2041 : certificate2041.Sound := rat_cut_bin_certificate_sound certificate2041 profilesValid2041 numericValid2041 valid2041

def retention2042 : RatCutRetentionCertificate := ⟨(17/1000),(9/500),(12147562410247947745/347667638217460449678),(1402009731649328653/1000000000000000000),(9/4),(540478999946518994913/256000000000000000000),true,MergedCutProfiles.Batch021.profile865,![MergedCutProfiles.Batch021.profile865,MergedCutProfiles.Batch021.profile868,MergedCutProfiles.Batch021.profile872,MergedCutProfiles.Batch318.profile12759,MergedCutProfiles.Batch022.profile885,MergedCutProfiles.Batch319.profile12760,MergedCutProfiles.Batch319.profile12761,MergedCutProfiles.Batch319.profile12762,MergedCutProfiles.Batch319.profile12763,MergedCutProfiles.Batch319.profile12764,MergedCutProfiles.Batch319.profile12765,MergedCutProfiles.Batch319.profile12766,MergedCutProfiles.Batch319.profile12767,MergedCutProfiles.Batch319.profile12768,MergedCutProfiles.Batch319.profile12769,MergedCutProfiles.Batch319.profile12770]⟩
theorem profilesValid2042 : retention2042.ProfilesValid := by
  change ∀ j : Fin 16, (retention2042.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch021.valid865
  · exact MergedCutProfiles.Batch021.valid868
  · exact MergedCutProfiles.Batch021.valid872
  · exact MergedCutProfiles.Batch318.valid12759
  · exact MergedCutProfiles.Batch022.valid885
  · exact MergedCutProfiles.Batch319.valid12760
  · exact MergedCutProfiles.Batch319.valid12761
  · exact MergedCutProfiles.Batch319.valid12762
  · exact MergedCutProfiles.Batch319.valid12763
  · exact MergedCutProfiles.Batch319.valid12764
  · exact MergedCutProfiles.Batch319.valid12765
  · exact MergedCutProfiles.Batch319.valid12766
  · exact MergedCutProfiles.Batch319.valid12767
  · exact MergedCutProfiles.Batch319.valid12768
  · exact MergedCutProfiles.Batch319.valid12769
  · exact MergedCutProfiles.Batch319.valid12770
theorem numericValid2042 : retention2042.NumericValid := by decide +kernel
def certificate2042 : RatCutBinCertificate := ⟨⟨retention2042,(1885819660274741523/1000000000000000000),(13522397103991873/1000000000000000000),(8218226185730691081/1000000000000000000),(179417633552813698357/62500000000000000),(13151652686930571/6250000000000000)⟩,(7807429426585233/7812500000000000),(365149831607000031/1000000000000000000),(66744277826877013/250000000000000000),(96223041730067807/500000000000000000)⟩
theorem valid2042 : certificate2042.Valid := by decide +kernel
theorem sound2042 : certificate2042.Sound := rat_cut_bin_certificate_sound certificate2042 profilesValid2042 numericValid2042 valid2042

def retention2043 : RatCutRetentionCertificate := ⟨(17/1000),(9/500),(32000000000000000000/173833819108730224839),(2429512482049589549/200000000000000000),(21/20),(1284171629816161466209800972763253695439/777443994255868655680000000000000000000),false,MergedCutProfiles.Batch319.profile12771,(fun _ => MergedCutProfiles.Batch319.profile12771)⟩
theorem profilesValid2043 : retention2043.ProfilesValid := by
  exact MergedCutProfiles.Batch319.valid12771
theorem numericValid2043 : retention2043.NumericValid := by decide +kernel
def certificate2043 : RatCutBinCertificate := ⟨⟨retention2043,(1885819660274741523/1000000000000000000),(13522397103991873/1000000000000000000),(8218226185730691081/1000000000000000000),(179417633552813698357/62500000000000000),(1648528568382363879/1000000000000000000)⟩,(7807429426585233/7812500000000000),(57207845135432887/200000000000000000),(177956604963916157/500000000000000000),(248607028240905241/500000000000000000)⟩
theorem valid2043 : certificate2043.Valid := by decide +kernel
theorem sound2043 : certificate2043.Sound := rat_cut_bin_certificate_sound certificate2043 profilesValid2043 numericValid2043 valid2043

def retention2044 : RatCutRetentionCertificate := ⟨(17/1000),(9/500),(1/2),64,1,(63842651577774958124598119296594031199/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch022.profile888,(fun _ => MergedCutProfiles.Batch022.profile888)⟩
theorem profilesValid2044 : retention2044.ProfilesValid := by
  exact MergedCutProfiles.Batch022.valid888
theorem numericValid2044 : retention2044.NumericValid := by decide +kernel
def certificate2044 : RatCutBinCertificate := ⟨⟨retention2044,(1885819660274741523/1000000000000000000),(13522397103991873/1000000000000000000),(8218226185730691081/1000000000000000000),(179417633552813698357/62500000000000000),(994438473693557263/1000000000000000000)⟩,(7807429426585233/7812500000000000),(442628171288841959/1000000000000000000),(7864734349028497/40000000000000000),(19240725292256589/100000000000000000)⟩
theorem valid2044 : certificate2044.Valid := by decide +kernel
theorem sound2044 : certificate2044.Sound := rat_cut_bin_certificate_sound certificate2044 profilesValid2044 numericValid2044 valid2044

def retention2045 : RatCutRetentionCertificate := ⟨(17/1000),(9/500),(32000000000000000000/173833819108730224839),(502818751961226307/100000000000000000),(11/10),(8079847389295156708017697488257783989/5028187519612263070000000000000000000),false,MergedCutProfiles.Batch319.profile12771,(fun _ => MergedCutProfiles.Batch319.profile12771)⟩
theorem profilesValid2045 : retention2045.ProfilesValid := by
  exact MergedCutProfiles.Batch319.valid12771
theorem numericValid2045 : retention2045.NumericValid := by decide +kernel
def certificate2045 : RatCutBinCertificate := ⟨⟨retention2045,(2173954020274741523/1000000000000000000),(13522397103991873/1000000000000000000),(8218226185730691081/1000000000000000000),(179417633552813698357/62500000000000000),(1602975746676064011/1000000000000000000)⟩,(99925179989646641/100000000000000000),(151979470982635357/1000000000000000000),(560733223127009899/1000000000000000000),(646217660696295837/1000000000000000000)⟩
theorem valid2045 : certificate2045.Valid := by decide +kernel
theorem sound2045 : certificate2045.Sound := rat_cut_bin_certificate_sound certificate2045 profilesValid2045 numericValid2045 valid2045

def retention2046 : RatCutRetentionCertificate := ⟨(17/1000),(9/500),(1/2),64,1,(63842651577774958124598119296594031199/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch022.profile888,(fun _ => MergedCutProfiles.Batch022.profile888)⟩
theorem profilesValid2046 : retention2046.ProfilesValid := by
  exact MergedCutProfiles.Batch022.valid888
theorem numericValid2046 : retention2046.NumericValid := by decide +kernel
def certificate2046 : RatCutBinCertificate := ⟨⟨retention2046,(2173954020274741523/1000000000000000000),(13522397103991873/1000000000000000000),(8218226185730691081/1000000000000000000),(179417633552813698357/62500000000000000),(496982186452086281/500000000000000000)⟩,(99925179989646641/100000000000000000),(9803949220675349/40000000000000000),(410173201144495263/1000000000000000000),(80232000338131591/200000000000000000)⟩
theorem valid2046 : certificate2046.Valid := by decide +kernel
theorem sound2046 : certificate2046.Sound := rat_cut_bin_certificate_sound certificate2046 profilesValid2046 numericValid2046 valid2046

def retention2047 : RatCutRetentionCertificate := ⟨(9/500),(19/1000),(637831145365702033/310561428747902365480),(619072625733355623/1000000000000000000),4,(145344902372673320143/64000000000000000000),true,MergedCutProfiles.Batch319.profile12772,![MergedCutProfiles.Batch319.profile12772,MergedCutProfiles.Batch319.profile12773,MergedCutProfiles.Batch319.profile12774,MergedCutProfiles.Batch022.profile890,MergedCutProfiles.Batch319.profile12775,MergedCutProfiles.Batch319.profile12776,MergedCutProfiles.Batch319.profile12777,MergedCutProfiles.Batch319.profile12778,MergedCutProfiles.Batch319.profile12779,MergedCutProfiles.Batch319.profile12780,MergedCutProfiles.Batch319.profile12781,MergedCutProfiles.Batch319.profile12782,MergedCutProfiles.Batch319.profile12783,MergedCutProfiles.Batch319.profile12784,MergedCutProfiles.Batch023.profile923,MergedCutProfiles.Batch319.profile12785]⟩
theorem profilesValid2047 : retention2047.ProfilesValid := by
  change ∀ j : Fin 16, (retention2047.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch319.valid12772
  · exact MergedCutProfiles.Batch319.valid12773
  · exact MergedCutProfiles.Batch319.valid12774
  · exact MergedCutProfiles.Batch022.valid890
  · exact MergedCutProfiles.Batch319.valid12775
  · exact MergedCutProfiles.Batch319.valid12776
  · exact MergedCutProfiles.Batch319.valid12777
  · exact MergedCutProfiles.Batch319.valid12778
  · exact MergedCutProfiles.Batch319.valid12779
  · exact MergedCutProfiles.Batch319.valid12780
  · exact MergedCutProfiles.Batch319.valid12781
  · exact MergedCutProfiles.Batch319.valid12782
  · exact MergedCutProfiles.Batch319.valid12783
  · exact MergedCutProfiles.Batch319.valid12784
  · exact MergedCutProfiles.Batch023.valid923
  · exact MergedCutProfiles.Batch319.valid12785
theorem numericValid2047 : retention2047.NumericValid := by decide +kernel
def certificate2047 : RatCutBinCertificate := ⟨⟨retention2047,(1892704313882366181/1000000000000000000),(15120529320228081/1000000000000000000),(8325279707217303457/1000000000000000000),(2597771268675315586621/1000000000000000000),(564315951700770073/250000000000000000)⟩,(999281257413213797/1000000000000000000),(526787272191579119/1000000000000000000),(67781972376725327/500000000000000000),(15562515765829493/250000000000000000)⟩
theorem valid2047 : certificate2047.Valid := by decide +kernel
theorem sound2047 : certificate2047.Sound := rat_cut_bin_certificate_sound certificate2047 profilesValid2047 numericValid2047 valid2047

def retention2048 : RatCutRetentionCertificate := ⟨(9/500),(19/1000),(30881923700000000/7764035718697559137),(637831145365702033/1000000000000000000),4,(582977579072856229161/256000000000000000000),true,MergedCutProfiles.Batch319.profile12773,![MergedCutProfiles.Batch319.profile12773,MergedCutProfiles.Batch319.profile12786,MergedCutProfiles.Batch319.profile12787,MergedCutProfiles.Batch319.profile12788,MergedCutProfiles.Batch319.profile12789,MergedCutProfiles.Batch319.profile12790,MergedCutProfiles.Batch319.profile12791,MergedCutProfiles.Batch022.profile909,MergedCutProfiles.Batch319.profile12792,MergedCutProfiles.Batch319.profile12793,MergedCutProfiles.Batch319.profile12794,MergedCutProfiles.Batch319.profile12795,MergedCutProfiles.Batch022.profile912,MergedCutProfiles.Batch319.profile12796,MergedCutProfiles.Batch319.profile12797,MergedCutProfiles.Batch022.profile913]⟩
theorem profilesValid2048 : retention2048.ProfilesValid := by
  change ∀ j : Fin 16, (retention2048.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch319.valid12773
  · exact MergedCutProfiles.Batch319.valid12786
  · exact MergedCutProfiles.Batch319.valid12787
  · exact MergedCutProfiles.Batch319.valid12788
  · exact MergedCutProfiles.Batch319.valid12789
  · exact MergedCutProfiles.Batch319.valid12790
  · exact MergedCutProfiles.Batch319.valid12791
  · exact MergedCutProfiles.Batch022.valid909
  · exact MergedCutProfiles.Batch319.valid12792
  · exact MergedCutProfiles.Batch319.valid12793
  · exact MergedCutProfiles.Batch319.valid12794
  · exact MergedCutProfiles.Batch319.valid12795
  · exact MergedCutProfiles.Batch022.valid912
  · exact MergedCutProfiles.Batch319.valid12796
  · exact MergedCutProfiles.Batch319.valid12797
  · exact MergedCutProfiles.Batch022.valid913
theorem numericValid2048 : retention2048.NumericValid := by decide +kernel
def certificate2048 : RatCutBinCertificate := ⟨⟨retention2048,(1892704313882366181/1000000000000000000),(15120529320228081/1000000000000000000),(8325279707217303457/1000000000000000000),(2597771268675315586621/1000000000000000000),(2263505876433939627/1000000000000000000)⟩,(999281257413213797/1000000000000000000),(257767937970280563/500000000000000000),(142896633912958367/1000000000000000000),(8265855531274089/125000000000000000)⟩
theorem valid2048 : certificate2048.Valid := by decide +kernel
theorem sound2048 : certificate2048.Sound := rat_cut_bin_certificate_sound certificate2048 profilesValid2048 numericValid2048 valid2048

def retention2049 : RatCutRetentionCertificate := ⟨(9/500),(19/1000),(553117569171325171/77640357186975591370),(308819237/250000000),(49/20),(1128808714529601587/500000000000000000),true,MergedCutProfiles.Batch319.profile12798,![MergedCutProfiles.Batch319.profile12798,MergedCutProfiles.Batch319.profile12777,MergedCutProfiles.Batch022.profile893,MergedCutProfiles.Batch319.profile12784,MergedCutProfiles.Batch319.profile12792,MergedCutProfiles.Batch319.profile12799,MergedCutProfiles.Batch022.profile900,MergedCutProfiles.Batch320.profile12800,MergedCutProfiles.Batch022.profile913,MergedCutProfiles.Batch022.profile914,MergedCutProfiles.Batch320.profile12801,MergedCutProfiles.Batch320.profile12802,MergedCutProfiles.Batch023.profile929,MergedCutProfiles.Batch023.profile930,MergedCutProfiles.Batch023.profile931,MergedCutProfiles.Batch320.profile12803]⟩
theorem profilesValid2049 : retention2049.ProfilesValid := by
  change ∀ j : Fin 16, (retention2049.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch319.valid12798
  · exact MergedCutProfiles.Batch319.valid12777
  · exact MergedCutProfiles.Batch022.valid893
  · exact MergedCutProfiles.Batch319.valid12784
  · exact MergedCutProfiles.Batch319.valid12792
  · exact MergedCutProfiles.Batch319.valid12799
  · exact MergedCutProfiles.Batch022.valid900
  · exact MergedCutProfiles.Batch320.valid12800
  · exact MergedCutProfiles.Batch022.valid913
  · exact MergedCutProfiles.Batch022.valid914
  · exact MergedCutProfiles.Batch320.valid12801
  · exact MergedCutProfiles.Batch320.valid12802
  · exact MergedCutProfiles.Batch023.valid929
  · exact MergedCutProfiles.Batch023.valid930
  · exact MergedCutProfiles.Batch023.valid931
  · exact MergedCutProfiles.Batch320.valid12803
theorem numericValid2049 : retention2049.NumericValid := by decide +kernel
def certificate2049 : RatCutBinCertificate := ⟨⟨retention2049,(1892704313882366181/1000000000000000000),(15120529320228081/1000000000000000000),(8325279707217303457/1000000000000000000),(2597771268675315586621/1000000000000000000),(562298844584031253/250000000000000000)⟩,(999281257413213797/1000000000000000000),(22588627538836593/62500000000000000),(270755401585382191/1000000000000000000),(47639255973727381/250000000000000000)⟩
theorem valid2049 : certificate2049.Valid := by decide +kernel
theorem sound2049 : certificate2049.Sound := rat_cut_bin_certificate_sound certificate2049 profilesValid2049 numericValid2049 valid2049

def retention2050 : RatCutRetentionCertificate := ⟨(9/500),(19/1000),(28354063156353636959/155280714373951182740),(553117569171325171/250000000000000000),(17/10),(371074760498990861355848663596368924919/221247027668530068400000000000000000000),false,MergedCutProfiles.Batch320.profile12804,(fun _ => MergedCutProfiles.Batch320.profile12804)⟩
theorem profilesValid2050 : retention2050.ProfilesValid := by
  exact MergedCutProfiles.Batch320.valid12804
theorem numericValid2050 : retention2050.NumericValid := by decide +kernel
def certificate2050 : RatCutBinCertificate := ⟨⟨retention2050,(1892704313882366181/1000000000000000000),(15120529320228081/1000000000000000000),(8325279707217303457/1000000000000000000),(2597771268675315586621/1000000000000000000),(1671352720923865303/1000000000000000000)⟩,(999281257413213797/1000000000000000000),(386494714965332089/1000000000000000000),(246087059956631439/1000000000000000000),(47912600411557141/250000000000000000)⟩
theorem valid2050 : certificate2050.Valid := by decide +kernel
theorem sound2050 : certificate2050.Sound := rat_cut_bin_certificate_sound certificate2050 profilesValid2050 numericValid2050 valid2050

def retention2051 : RatCutRetentionCertificate := ⟨(9/500),(19/1000),(1600000000000000000/7764035718697559137),(28354063156353636959/500000000000000000),1,(91388008221535729200965814420766606843/56708126312707273918000000000000000000),false,MergedCutProfiles.Batch320.profile12805,(fun _ => MergedCutProfiles.Batch320.profile12805)⟩
theorem profilesValid2051 : retention2051.ProfilesValid := by
  exact MergedCutProfiles.Batch320.valid12805
theorem numericValid2051 : retention2051.NumericValid := by decide +kernel
def certificate2051 : RatCutBinCertificate := ⟨⟨retention2051,(1892704313882366181/1000000000000000000),(15120529320228081/1000000000000000000),(8325279707217303457/1000000000000000000),(2597771268675315586621/1000000000000000000),(321622583056459451/200000000000000000)⟩,(999281257413213797/1000000000000000000),(55118455195459311/200000000000000000),(369171513122704071/1000000000000000000),(72109976385717969/125000000000000000)⟩
theorem valid2051 : certificate2051.Valid := by decide +kernel
theorem sound2051 : certificate2051.Sound := rat_cut_bin_certificate_sound certificate2051 profilesValid2051 numericValid2051 valid2051

def certificates : List RatCutBinCertificate := [certificate2040,certificate2041,certificate2042,certificate2043,certificate2044,certificate2045,certificate2046,certificate2047,certificate2048,certificate2049,certificate2050,certificate2051]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2040,List.forall_mem_cons.mpr ⟨sound2041,List.forall_mem_cons.mpr ⟨sound2042,List.forall_mem_cons.mpr ⟨sound2043,List.forall_mem_cons.mpr ⟨sound2044,List.forall_mem_cons.mpr ⟨sound2045,List.forall_mem_cons.mpr ⟨sound2046,List.forall_mem_cons.mpr ⟨sound2047,List.forall_mem_cons.mpr ⟨sound2048,List.forall_mem_cons.mpr ⟨sound2049,List.forall_mem_cons.mpr ⟨sound2050,List.forall_mem_cons.mpr ⟨sound2051,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch170
