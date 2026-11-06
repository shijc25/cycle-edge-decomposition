import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch020
import Cycle12.MergedCutProfiles.Batch021
import Cycle12.MergedCutProfiles.Batch022
import Cycle12.MergedCutProfiles.Batch318
import Cycle12.MergedCutProfiles.Batch453
import Cycle12.MergedCutProfiles.Batch454
import Cycle12.MergedCutProfiles.Batch578
import Cycle12.MergedCutProfiles.Batch579
import Cycle12.MergedCutProfiles.Batch648

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch371

def retention4452 : RatCutRetentionCertificate := ⟨(17/1000),(9/500),(1273291123000000000/17383381910873022483903),(33250569390657453/50000000000000000),4,(6034903855502819937/2560000000000000000),true,MergedCutProfiles.Batch648.profile25936,![MergedCutProfiles.Batch648.profile25936,MergedCutProfiles.Batch578.profile23155,MergedCutProfiles.Batch648.profile25938,MergedCutProfiles.Batch648.profile25939,MergedCutProfiles.Batch578.profile23156,MergedCutProfiles.Batch648.profile25940,MergedCutProfiles.Batch578.profile23157,MergedCutProfiles.Batch648.profile25941,MergedCutProfiles.Batch453.profile18148,MergedCutProfiles.Batch453.profile18148,MergedCutProfiles.Batch578.profile23158,MergedCutProfiles.Batch578.profile23159,MergedCutProfiles.Batch578.profile23159,MergedCutProfiles.Batch579.profile23165,MergedCutProfiles.Batch579.profile23165,MergedCutProfiles.Batch579.profile23160]⟩
theorem profilesValid4452 : retention4452.ProfilesValid := by
  change ∀ j : Fin 16, (retention4452.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch648.valid25936
  · exact MergedCutProfiles.Batch578.valid23155
  · exact MergedCutProfiles.Batch648.valid25938
  · exact MergedCutProfiles.Batch648.valid25939
  · exact MergedCutProfiles.Batch578.valid23156
  · exact MergedCutProfiles.Batch648.valid25940
  · exact MergedCutProfiles.Batch578.valid23157
  · exact MergedCutProfiles.Batch648.valid25941
  · exact MergedCutProfiles.Batch453.valid18148
  · exact MergedCutProfiles.Batch453.valid18148
  · exact MergedCutProfiles.Batch578.valid23158
  · exact MergedCutProfiles.Batch578.valid23159
  · exact MergedCutProfiles.Batch578.valid23159
  · exact MergedCutProfiles.Batch579.valid23165
  · exact MergedCutProfiles.Batch579.valid23165
  · exact MergedCutProfiles.Batch579.valid23160
theorem numericValid4452 : retention4452.NumericValid := by decide +kernel
def certificate4452 : RatCutBinCertificate := ⟨⟨retention4452,(1878427048205494831/1000000000000000000),(13522397103991873/1000000000000000000),(4109117189075387729/500000000000000000),(71767124962822745430191/500000000000000000),(1172510579097153707/500000000000000000)⟩,(999987070330746971/1000000000000000000),(239149449649371263/500000000000000000),(168946261122695329/1000000000000000000),(81157583763342367/1000000000000000000)⟩
theorem valid4452 : certificate4452.Valid := by decide +kernel
theorem sound4452 : certificate4452.Sound := rat_cut_bin_certificate_sound certificate4452 profilesValid4452 numericValid4452 valid4452

def retention4453 : RatCutRetentionCertificate := ⟨(17/1000),(9/500),(7922297629563828412/17383381910873022483903),(1273291123/1000000000),(5/2),(37746668458378371349/16000000000000000000),true,MergedCutProfiles.Batch648.profile25940,![MergedCutProfiles.Batch648.profile25940,MergedCutProfiles.Batch578.profile23159,MergedCutProfiles.Batch453.profile18149,MergedCutProfiles.Batch318.profile12730,MergedCutProfiles.Batch579.profile23163,MergedCutProfiles.Batch453.profile18151,MergedCutProfiles.Batch454.profile18170,MergedCutProfiles.Batch318.profile12731,MergedCutProfiles.Batch318.profile12754,MergedCutProfiles.Batch648.profile25942,MergedCutProfiles.Batch579.profile23166,MergedCutProfiles.Batch318.profile12732,MergedCutProfiles.Batch021.profile847,MergedCutProfiles.Batch453.profile18154,MergedCutProfiles.Batch021.profile861,MergedCutProfiles.Batch318.profile12733]⟩
theorem profilesValid4453 : retention4453.ProfilesValid := by
  change ∀ j : Fin 16, (retention4453.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch648.valid25940
  · exact MergedCutProfiles.Batch578.valid23159
  · exact MergedCutProfiles.Batch453.valid18149
  · exact MergedCutProfiles.Batch318.valid12730
  · exact MergedCutProfiles.Batch579.valid23163
  · exact MergedCutProfiles.Batch453.valid18151
  · exact MergedCutProfiles.Batch454.valid18170
  · exact MergedCutProfiles.Batch318.valid12731
  · exact MergedCutProfiles.Batch318.valid12754
  · exact MergedCutProfiles.Batch648.valid25942
  · exact MergedCutProfiles.Batch579.valid23166
  · exact MergedCutProfiles.Batch318.valid12732
  · exact MergedCutProfiles.Batch021.valid847
  · exact MergedCutProfiles.Batch453.valid18154
  · exact MergedCutProfiles.Batch021.valid861
  · exact MergedCutProfiles.Batch318.valid12733
theorem numericValid4453 : retention4453.NumericValid := by decide +kernel
def certificate4453 : RatCutBinCertificate := ⟨⟨retention4453,(1878427048205494831/1000000000000000000),(13522397103991873/1000000000000000000),(4109117189075387729/500000000000000000),(71767124962822745430191/500000000000000000),(117571990173385029/50000000000000000)⟩,(999987070330746971/1000000000000000000),(66053542062136841/200000000000000000),(303834542904903419/1000000000000000000),(220594346485334463/1000000000000000000)⟩
theorem valid4453 : certificate4453.Valid := by decide +kernel
theorem sound4453 : certificate4453.Sound := rat_cut_bin_certificate_sound certificate4453 profilesValid4453 numericValid4453 valid4453

def retention4454 : RatCutRetentionCertificate := ⟨(17/1000),(9/500),(64000000000000000000/17383381910873022483903),(1980574407390957103/250000000000000000),(11/10),(1796683801820942913093698969968467915199/792229762956382841200000000000000000000),true,MergedCutProfiles.Batch020.profile831,![MergedCutProfiles.Batch020.profile831,MergedCutProfiles.Batch318.profile12733,MergedCutProfiles.Batch020.profile833,MergedCutProfiles.Batch020.profile834,MergedCutProfiles.Batch020.profile835,MergedCutProfiles.Batch020.profile836,MergedCutProfiles.Batch020.profile837,MergedCutProfiles.Batch579.profile23167,MergedCutProfiles.Batch020.profile839,MergedCutProfiles.Batch021.profile840,MergedCutProfiles.Batch021.profile841,MergedCutProfiles.Batch021.profile842,MergedCutProfiles.Batch021.profile843,MergedCutProfiles.Batch021.profile844,MergedCutProfiles.Batch021.profile845,MergedCutProfiles.Batch021.profile846]⟩
theorem profilesValid4454 : retention4454.ProfilesValid := by
  change ∀ j : Fin 16, (retention4454.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch020.valid831
  · exact MergedCutProfiles.Batch318.valid12733
  · exact MergedCutProfiles.Batch020.valid833
  · exact MergedCutProfiles.Batch020.valid834
  · exact MergedCutProfiles.Batch020.valid835
  · exact MergedCutProfiles.Batch020.valid836
  · exact MergedCutProfiles.Batch020.valid837
  · exact MergedCutProfiles.Batch579.valid23167
  · exact MergedCutProfiles.Batch020.valid839
  · exact MergedCutProfiles.Batch021.valid840
  · exact MergedCutProfiles.Batch021.valid841
  · exact MergedCutProfiles.Batch021.valid842
  · exact MergedCutProfiles.Batch021.valid843
  · exact MergedCutProfiles.Batch021.valid844
  · exact MergedCutProfiles.Batch021.valid845
  · exact MergedCutProfiles.Batch021.valid846
theorem numericValid4454 : retention4454.NumericValid := by decide +kernel
def certificate4454 : RatCutBinCertificate := ⟨⟨retention4454,(1878427048205494831/1000000000000000000),(13522397103991873/1000000000000000000),(4109117189075387729/500000000000000000),(71767124962822745430191/500000000000000000),(11322411807035851/5000000000000000)⟩,(999987070330746971/1000000000000000000),(40630360892423/200000000000000),(23639489283954243/50000000000000000),(3936494701071879/5000000000000000)⟩
theorem valid4454 : certificate4454.Valid := by decide +kernel
theorem sound4454 : certificate4454.Sound := rat_cut_bin_certificate_sound certificate4454 profilesValid4454 numericValid4454 valid4454

def retention4455 : RatCutRetentionCertificate := ⟨(17/1000),(9/500),(1/2),64,1,(63842651577774958124598119296594031199/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch022.profile888,(fun _ => MergedCutProfiles.Batch022.profile888)⟩
theorem profilesValid4455 : retention4455.ProfilesValid := by
  exact MergedCutProfiles.Batch022.valid888
theorem numericValid4455 : retention4455.NumericValid := by decide +kernel
def certificate4455 : RatCutBinCertificate := ⟨⟨retention4455,(1878427048205494831/1000000000000000000),(13522397103991873/1000000000000000000),(4109117189075387729/500000000000000000),(71767124962822745430191/500000000000000000),(99445064091727939/100000000000000000)⟩,(999987070330746971/1000000000000000000),(204592551171878343/500000000000000000),(225171126869057921/1000000000000000000),(110246287017339071/500000000000000000)⟩
theorem valid4455 : certificate4455.Valid := by decide +kernel
theorem sound4455 : certificate4455.Sound := rat_cut_bin_certificate_sound certificate4455 profilesValid4455 numericValid4455 valid4455

def retention4456 : RatCutRetentionCertificate := ⟨(17/1000),(9/500),(64000000000000000000/17383381910873022483903),(8698746124664660087/500000000000000000),1,(123004087112231175692450163805186391/54367163279154125543750000000000000),false,MergedCutProfiles.Batch648.profile25943,(fun _ => MergedCutProfiles.Batch648.profile25943)⟩
theorem profilesValid4456 : retention4456.ProfilesValid := by
  exact MergedCutProfiles.Batch648.valid25943
theorem numericValid4456 : retention4456.NumericValid := by decide +kernel
def certificate4456 : RatCutBinCertificate := ⟨⟨retention4456,(1668527959205494831/1000000000000000000),(13522397103991873/1000000000000000000),(4109117189075387729/500000000000000000),(71767124962822745430191/500000000000000000),(564931196759536179/250000000000000000)⟩,(499994257558659681/500000000000000000),(30046904233332987/1000000000000000000),(844123199572513621/1000000000000000000),(844094101151970367/500000000000000000)⟩
theorem valid4456 : certificate4456.Valid := by decide +kernel
theorem sound4456 : certificate4456.Sound := rat_cut_bin_certificate_sound certificate4456 profilesValid4456 numericValid4456 valid4456

def retention4457 : RatCutRetentionCertificate := ⟨(17/1000),(9/500),(1/2),64,1,(63842651577774958124598119296594031199/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch022.profile888,(fun _ => MergedCutProfiles.Batch022.profile888)⟩
theorem profilesValid4457 : retention4457.ProfilesValid := by
  exact MergedCutProfiles.Batch022.valid888
theorem numericValid4457 : retention4457.NumericValid := by decide +kernel
def certificate4457 : RatCutBinCertificate := ⟨⟨retention4457,(1668527959205494831/1000000000000000000),(13522397103991873/1000000000000000000),(4109117189075387729/500000000000000000),(71767124962822745430191/500000000000000000),(994796011797057211/1000000000000000000)⟩,(499994257558659681/500000000000000000),(68252921669005797/1000000000000000000),(741126546420651009/1000000000000000000),(72597682798090383/100000000000000000)⟩
theorem valid4457 : certificate4457.Valid := by decide +kernel
theorem sound4457 : certificate4457.Sound := rat_cut_bin_certificate_sound certificate4457 profilesValid4457 numericValid4457 valid4457

def retention4458 : RatCutRetentionCertificate := ⟨(17/1000),(9/500),(680906335135604696/17383381910873022483903),(168541172063268489/250000000000000000),4,(1277422888963678166773735336929610867/539331750602459164800000000000000000),false,MergedCutProfiles.Batch648.profile25944,(fun _ => MergedCutProfiles.Batch648.profile25944)⟩
theorem profilesValid4458 : retention4458.ProfilesValid := by
  exact MergedCutProfiles.Batch648.valid25944
theorem numericValid4458 : retention4458.NumericValid := by decide +kernel
def certificate4458 : RatCutBinCertificate := ⟨⟨retention4458,(1765031117205494831/1000000000000000000),(13522397103991873/1000000000000000000),(4109117189075387729/500000000000000000),(71767124962822745430191/500000000000000000),(2356912167149740439/1000000000000000000)⟩,(124998481357821969/125000000000000000),(397282578703843701/500000000000000000),(22716411919481851/1000000000000000000),(5492376904993593/500000000000000000)⟩
theorem valid4458 : certificate4458.Valid := by decide +kernel
theorem sound4458 : certificate4458.Sound := rat_cut_bin_certificate_sound certificate4458 profilesValid4458 numericValid4458 valid4458

def retention4459 : RatCutRetentionCertificate := ⟨(17/1000),(9/500),(589953800586613809/5794460636957674161301),(85113291891950587/125000000000000000),4,(403533296434464620670178249776479607/170226583783901174000000000000000000),false,MergedCutProfiles.Batch648.profile25945,(fun _ => MergedCutProfiles.Batch648.profile25945)⟩
theorem profilesValid4459 : retention4459.ProfilesValid := by
  exact MergedCutProfiles.Batch648.valid25945
theorem numericValid4459 : retention4459.NumericValid := by decide +kernel
def certificate4459 : RatCutBinCertificate := ⟨⟨retention4459,(1765031117205494831/1000000000000000000),(13522397103991873/1000000000000000000),(4109117189075387729/500000000000000000),(71767124962822745430191/500000000000000000),(2358948847310271877/1000000000000000000)⟩,(124998481357821969/125000000000000000),(197861101433810087/250000000000000000),(2344019747191903/100000000000000000),(90903789923187/8000000000000000)⟩
theorem valid4459 : certificate4459.Valid := by decide +kernel
theorem sound4459 : certificate4459.Sound := rat_cut_bin_certificate_sound certificate4459 profilesValid4459 numericValid4459 valid4459

def retention4460 : RatCutRetentionCertificate := ⟨(17/1000),(9/500),(64000000000000000000/17383381910873022483903),(1769861401759841427/1000000000000000000),(11/5),(103296231345206991072579052992027726719/44246535043996035675000000000000000000),false,MergedCutProfiles.Batch648.profile25943,(fun _ => MergedCutProfiles.Batch648.profile25943)⟩
theorem profilesValid4460 : retention4460.ProfilesValid := by
  exact MergedCutProfiles.Batch648.valid25943
theorem numericValid4460 : retention4460.NumericValid := by decide +kernel
def certificate4460 : RatCutBinCertificate := ⟨⟨retention4460,(1765031117205494831/1000000000000000000),(13522397103991873/1000000000000000000),(4109117189075387729/500000000000000000),(71767124962822745430191/500000000000000000),(2328171660183871733/1000000000000000000)⟩,(124998481357821969/125000000000000000),(650122819054190689/1000000000000000000),(559505661584577/8000000000000000),(58195067470819421/1000000000000000000)⟩
theorem valid4460 : certificate4460.Valid := by decide +kernel
theorem sound4460 : certificate4460.Sound := rat_cut_bin_certificate_sound certificate4460 profilesValid4460 numericValid4460 valid4460

def retention4461 : RatCutRetentionCertificate := ⟨(17/1000),(9/500),(1/40),64,1,(138254140364058033254301379555765782631/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch648.profile25946,(fun _ => MergedCutProfiles.Batch648.profile25946)⟩
theorem profilesValid4461 : retention4461.ProfilesValid := by
  exact MergedCutProfiles.Batch648.valid25946
theorem numericValid4461 : retention4461.NumericValid := by decide +kernel
def certificate4461 : RatCutBinCertificate := ⟨⟨retention4461,(1765031117205494831/1000000000000000000),(13522397103991873/1000000000000000000),(4109117189075387729/500000000000000000),(71767124962822745430191/500000000000000000),(2157316736444639091/1000000000000000000)⟩,(124998481357821969/125000000000000000),(602018941179914663/1000000000000000000),(92476690920363577/1000000000000000000),(192993624607628467/1000000000000000000)⟩
theorem valid4461 : certificate4461.Valid := by decide +kernel
theorem sound4461 : certificate4461.Sound := rat_cut_bin_certificate_sound certificate4461 profilesValid4461 numericValid4461 valid4461

def retention4462 : RatCutRetentionCertificate := ⟨(9/500),(19/1000),(328599115861054481/7764035718697559137017),(306490328124407327/500000000000000000),4,(5613098458676492627880383020152570007/2451922624995258616000000000000000000),true,MergedCutProfiles.Batch648.profile25947,![MergedCutProfiles.Batch648.profile25947,MergedCutProfiles.Batch648.profile25948,MergedCutProfiles.Batch648.profile25949,MergedCutProfiles.Batch579.profile23177,MergedCutProfiles.Batch648.profile25950,MergedCutProfiles.Batch648.profile25951,MergedCutProfiles.Batch648.profile25951,MergedCutProfiles.Batch579.profile23178,MergedCutProfiles.Batch579.profile23178,MergedCutProfiles.Batch579.profile23189,MergedCutProfiles.Batch579.profile23179,MergedCutProfiles.Batch579.profile23179,MergedCutProfiles.Batch648.profile25952,MergedCutProfiles.Batch648.profile25952,MergedCutProfiles.Batch648.profile25952,MergedCutProfiles.Batch579.profile23180]⟩
theorem profilesValid4462 : retention4462.ProfilesValid := by
  change ∀ j : Fin 16, (retention4462.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch648.valid25947
  · exact MergedCutProfiles.Batch648.valid25948
  · exact MergedCutProfiles.Batch648.valid25949
  · exact MergedCutProfiles.Batch579.valid23177
  · exact MergedCutProfiles.Batch648.valid25950
  · exact MergedCutProfiles.Batch648.valid25951
  · exact MergedCutProfiles.Batch648.valid25951
  · exact MergedCutProfiles.Batch579.valid23178
  · exact MergedCutProfiles.Batch579.valid23178
  · exact MergedCutProfiles.Batch579.valid23189
  · exact MergedCutProfiles.Batch579.valid23179
  · exact MergedCutProfiles.Batch579.valid23179
  · exact MergedCutProfiles.Batch648.valid25952
  · exact MergedCutProfiles.Batch648.valid25952
  · exact MergedCutProfiles.Batch648.valid25952
  · exact MergedCutProfiles.Batch579.valid23180
theorem numericValid4462 : retention4462.NumericValid := by decide +kernel
def certificate4462 : RatCutBinCertificate := ⟨⟨retention4462,(469889899374411831/250000000000000000),(15120529320228081/1000000000000000000),(8325289973709849721/1000000000000000000),(6494436180428026453419/50000000000000000),(2275609357518020553/1000000000000000000)⟩,(249996431284106979/250000000000000000),(259147131143610111/500000000000000000),(4408638705143949/31250000000000000),(32571374628175823/500000000000000000)⟩
theorem valid4462 : certificate4462.Valid := by decide +kernel
theorem sound4462 : certificate4462.Sound := rat_cut_bin_certificate_sound certificate4462 profilesValid4462 numericValid4462 valid4462

def retention4463 : RatCutRetentionCertificate := ⟨(9/500),(19/1000),(640989058000000000/7764035718697559137017),(328599115861054481/500000000000000000),4,(6175442117886293449421982297668520063/2628792926888435848000000000000000000),true,MergedCutProfiles.Batch648.profile25948,![MergedCutProfiles.Batch648.profile25948,MergedCutProfiles.Batch579.profile23177,MergedCutProfiles.Batch648.profile25951,MergedCutProfiles.Batch579.profile23178,MergedCutProfiles.Batch579.profile23189,MergedCutProfiles.Batch579.profile23179,MergedCutProfiles.Batch648.profile25952,MergedCutProfiles.Batch579.profile23180,MergedCutProfiles.Batch579.profile23180,MergedCutProfiles.Batch454.profile18188,MergedCutProfiles.Batch579.profile23181,MergedCutProfiles.Batch579.profile23182,MergedCutProfiles.Batch579.profile23182,MergedCutProfiles.Batch579.profile23190,MergedCutProfiles.Batch579.profile23183,MergedCutProfiles.Batch579.profile23183]⟩
theorem profilesValid4463 : retention4463.ProfilesValid := by
  change ∀ j : Fin 16, (retention4463.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch648.valid25948
  · exact MergedCutProfiles.Batch579.valid23177
  · exact MergedCutProfiles.Batch648.valid25951
  · exact MergedCutProfiles.Batch579.valid23178
  · exact MergedCutProfiles.Batch579.valid23189
  · exact MergedCutProfiles.Batch579.valid23179
  · exact MergedCutProfiles.Batch648.valid25952
  · exact MergedCutProfiles.Batch579.valid23180
  · exact MergedCutProfiles.Batch579.valid23180
  · exact MergedCutProfiles.Batch454.valid18188
  · exact MergedCutProfiles.Batch579.valid23181
  · exact MergedCutProfiles.Batch579.valid23182
  · exact MergedCutProfiles.Batch579.valid23182
  · exact MergedCutProfiles.Batch579.valid23190
  · exact MergedCutProfiles.Batch579.valid23183
  · exact MergedCutProfiles.Batch579.valid23183
theorem numericValid4463 : retention4463.NumericValid := by decide +kernel
def certificate4463 : RatCutBinCertificate := ⟨⟨retention4463,(469889899374411831/250000000000000000),(15120529320228081/1000000000000000000),(8325289973709849721/1000000000000000000),(6494436180428026453419/50000000000000000),(2335500277029461647/1000000000000000000)⟩,(249996431284106979/250000000000000000),(482525172340370871/1000000000000000000),(41461983577032433/250000000000000000),(19808577166337707/250000000000000000)⟩
theorem valid4463 : certificate4463.Valid := by decide +kernel
theorem sound4463 : certificate4463.Sound := rat_cut_bin_certificate_sound certificate4463 profilesValid4463 numericValid4463 valid4463

def certificates : List RatCutBinCertificate := [certificate4452,certificate4453,certificate4454,certificate4455,certificate4456,certificate4457,certificate4458,certificate4459,certificate4460,certificate4461,certificate4462,certificate4463]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4452,List.forall_mem_cons.mpr ⟨sound4453,List.forall_mem_cons.mpr ⟨sound4454,List.forall_mem_cons.mpr ⟨sound4455,List.forall_mem_cons.mpr ⟨sound4456,List.forall_mem_cons.mpr ⟨sound4457,List.forall_mem_cons.mpr ⟨sound4458,List.forall_mem_cons.mpr ⟨sound4459,List.forall_mem_cons.mpr ⟨sound4460,List.forall_mem_cons.mpr ⟨sound4461,List.forall_mem_cons.mpr ⟨sound4462,List.forall_mem_cons.mpr ⟨sound4463,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch371
