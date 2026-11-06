import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch120
import Cycle12.MergedCutProfiles.Batch121
import Cycle12.MergedCutProfiles.Batch122

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch060

def retention720 : RatCutRetentionCertificate := ⟨(23/500),(37/800),(1/2),(11357976606964700183/1000000000000000000),(21/20),(18125454068798488960223359671128030842151/18172762571143520292800000000000000000000),false,MergedCutProfiles.Batch120.profile4834,(fun _ => MergedCutProfiles.Batch120.profile4834)⟩
theorem profilesValid720 : retention720.ProfilesValid := by
  exact MergedCutProfiles.Batch120.valid4834
theorem numericValid720 : retention720.NumericValid := by decide +kernel
def certificate720 : RatCutBinCertificate := ⟨⟨retention720,(1063479516989765619/500000000000000000),(100499784855757983/1000000000000000000),(311855683291598777/25000000000000000),(284495464265982334187/1000000000000000000),(195880671041059613/200000000000000000)⟩,(496630485685780807/500000000000000000),(486296257665608391/1000000000000000000),(163114570080268999/1000000000000000000),(35029360024594763/250000000000000000)⟩
theorem valid720 : certificate720.Valid := by decide +kernel
theorem sound720 : certificate720.Sound := rat_cut_bin_certificate_sound certificate720 profilesValid720 numericValid720 valid720

def retention721 : RatCutRetentionCertificate := ⟨(23/500),(37/800),(3385246208280476980/7591609031483492281),(1858757643112766289/500000000000000000),(6/5),(25594433031006251620542211348511484581/23234470538909578612500000000000000000),false,MergedCutProfiles.Batch120.profile4835,(fun _ => MergedCutProfiles.Batch120.profile4835)⟩
theorem profilesValid721 : retention721.ProfilesValid := by
  exact MergedCutProfiles.Batch120.valid4835
theorem numericValid721 : retention721.NumericValid := by decide +kernel
def certificate721 : RatCutBinCertificate := ⟨⟨retention721,(1251592764989765619/500000000000000000),(100499784855757983/1000000000000000000),(311855683291598777/25000000000000000),(284495464265982334187/1000000000000000000),(538684555228999993/500000000000000000)⟩,(124008487274858597/125000000000000000),(47283023491377321/125000000000000000),(253999013580593207/1000000000000000000),(94096919554645519/500000000000000000)⟩
theorem valid721 : certificate721.Valid := by decide +kernel
theorem sound721 : certificate721.Sound := rat_cut_bin_certificate_sound certificate721 profilesValid721 numericValid721 valid721

def retention722 : RatCutRetentionCertificate := ⟨(23/500),(37/800),(11218253584893004763/22774827094450476843),(507786931242071547/50000000000000000),(21/20),(41031543763541185016119722568817429279/40622954499365723760000000000000000000),false,MergedCutProfiles.Batch120.profile4836,(fun _ => MergedCutProfiles.Batch120.profile4836)⟩
theorem profilesValid722 : retention722.ProfilesValid := by
  exact MergedCutProfiles.Batch120.valid4836
theorem numericValid722 : retention722.NumericValid := by decide +kernel
def certificate722 : RatCutBinCertificate := ⟨⟨retention722,(1251592764989765619/500000000000000000),(100499784855757983/1000000000000000000),(311855683291598777/25000000000000000),(284495464265982334187/1000000000000000000),(988881879876304013/1000000000000000000)⟩,(124008487274858597/125000000000000000),(206056031545615851/500000000000000000),(111283080986279583/500000000000000000),(191008917787397227/1000000000000000000)⟩
theorem valid722 : certificate722.Valid := by decide +kernel
theorem sound722 : certificate722.Sound := rat_cut_bin_certificate_sound certificate722 profilesValid722 numericValid722 valid722

def retention723 : RatCutRetentionCertificate := ⟨(23/500),(37/800),(11330436120741934811/22774827094450476843),(11218253584893004763/1000000000000000000),(21/20),(17987308109032156789270676084553701193071/17949205735828807620800000000000000000000),false,MergedCutProfiles.Batch120.profile4837,(fun _ => MergedCutProfiles.Batch120.profile4837)⟩
theorem profilesValid723 : retention723.ProfilesValid := by
  exact MergedCutProfiles.Batch120.valid4837
theorem numericValid723 : retention723.NumericValid := by decide +kernel
def certificate723 : RatCutBinCertificate := ⟨⟨retention723,(1251592764989765619/500000000000000000),(100499784855757983/1000000000000000000),(311855683291598777/25000000000000000),(284495464265982334187/1000000000000000000),(490473323406673653/500000000000000000)⟩,(124008487274858597/125000000000000000),(207722893489284379/500000000000000000),(54906121930617751/250000000000000000),(18853759651707989/100000000000000000)⟩
theorem valid723 : certificate723.Valid := by decide +kernel
theorem sound723 : certificate723.Sound := rat_cut_bin_certificate_sound certificate723 profilesValid723 numericValid723 valid723

def retention724 : RatCutRetentionCertificate := ⟨(23/500),(37/800),(1/2),(11330436120741934811/1000000000000000000),(21/20),(18080843159375992846950724863109846541759/18128697793187095697600000000000000000000),false,MergedCutProfiles.Batch120.profile4834,(fun _ => MergedCutProfiles.Batch120.profile4834)⟩
theorem profilesValid724 : retention724.ProfilesValid := by
  exact MergedCutProfiles.Batch120.valid4834
theorem numericValid724 : retention724.NumericValid := by decide +kernel
def certificate724 : RatCutBinCertificate := ⟨⟨retention724,(1251592764989765619/500000000000000000),(100499784855757983/1000000000000000000),(311855683291598777/25000000000000000),(284495464265982334187/1000000000000000000),(976184147170807921/1000000000000000000)⟩,(124008487274858597/125000000000000000),(417472618102301121/1000000000000000000),(217849100043908131/1000000000000000000),(93153710338252419/500000000000000000)⟩
theorem valid724 : certificate724.Valid := by decide +kernel
theorem sound724 : certificate724.Sound := rat_cut_bin_certificate_sound certificate724 profilesValid724 numericValid724 valid724

def retention725 : RatCutRetentionCertificate := ⟨(37/800),(93/2000),(834998681457723008/22499097179828279839),(82673136777992377/100000000000000000),3,(16816532547265383981/8000000000000000000),true,MergedCutProfiles.Batch120.profile4838,![MergedCutProfiles.Batch120.profile4838,MergedCutProfiles.Batch120.profile4839,MergedCutProfiles.Batch121.profile4840,MergedCutProfiles.Batch121.profile4841,MergedCutProfiles.Batch121.profile4842,MergedCutProfiles.Batch121.profile4843,MergedCutProfiles.Batch121.profile4844,MergedCutProfiles.Batch121.profile4845,MergedCutProfiles.Batch121.profile4846,MergedCutProfiles.Batch121.profile4847,MergedCutProfiles.Batch121.profile4848,MergedCutProfiles.Batch121.profile4849,MergedCutProfiles.Batch121.profile4850,MergedCutProfiles.Batch121.profile4851,MergedCutProfiles.Batch121.profile4852,MergedCutProfiles.Batch121.profile4853]⟩
theorem profilesValid725 : retention725.ProfilesValid := by
  change ∀ j : Fin 16, (retention725.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch120.valid4838
  · exact MergedCutProfiles.Batch120.valid4839
  · exact MergedCutProfiles.Batch121.valid4840
  · exact MergedCutProfiles.Batch121.valid4841
  · exact MergedCutProfiles.Batch121.valid4842
  · exact MergedCutProfiles.Batch121.valid4843
  · exact MergedCutProfiles.Batch121.valid4844
  · exact MergedCutProfiles.Batch121.valid4845
  · exact MergedCutProfiles.Batch121.valid4846
  · exact MergedCutProfiles.Batch121.valid4847
  · exact MergedCutProfiles.Batch121.valid4848
  · exact MergedCutProfiles.Batch121.valid4849
  · exact MergedCutProfiles.Batch121.valid4850
  · exact MergedCutProfiles.Batch121.valid4851
  · exact MergedCutProfiles.Batch121.valid4852
  · exact MergedCutProfiles.Batch121.valid4853
theorem numericValid725 : retention725.NumericValid := by decide +kernel
def certificate725 : RatCutBinCertificate := ⟨⟨retention725,(2129070161864492131/1000000000000000000),(50858016999050421/500000000000000000),(1565580850186765421/125000000000000000),(35273467744402477229/125000000000000000),(82007470837683931/40000000000000000)⟩,(993208118316980171/1000000000000000000),(47777871857208933/125000000000000000),(250171356637937653/1000000000000000000),(6647932225695809/50000000000000000)⟩
theorem valid725 : certificate725.Valid := by decide +kernel
theorem sound725 : certificate725.Sound := rat_cut_bin_certificate_sound certificate725 profilesValid725 numericValid725 valid725

def retention726 : RatCutRetentionCertificate := ⟨(37/800),(93/2000),(868374306000000000/22499097179828279839),(6523427198888461/7812500000000000),3,(8404061383993318727/4000000000000000000),true,MergedCutProfiles.Batch121.profile4854,![MergedCutProfiles.Batch121.profile4854,MergedCutProfiles.Batch121.profile4855,MergedCutProfiles.Batch121.profile4856,MergedCutProfiles.Batch121.profile4857,MergedCutProfiles.Batch121.profile4858,MergedCutProfiles.Batch121.profile4859,MergedCutProfiles.Batch121.profile4860,MergedCutProfiles.Batch121.profile4861,MergedCutProfiles.Batch121.profile4862,MergedCutProfiles.Batch121.profile4863,MergedCutProfiles.Batch121.profile4864,MergedCutProfiles.Batch121.profile4865,MergedCutProfiles.Batch121.profile4866,MergedCutProfiles.Batch121.profile4867,MergedCutProfiles.Batch121.profile4868,MergedCutProfiles.Batch121.profile4869]⟩
theorem profilesValid726 : retention726.ProfilesValid := by
  change ∀ j : Fin 16, (retention726.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch121.valid4854
  · exact MergedCutProfiles.Batch121.valid4855
  · exact MergedCutProfiles.Batch121.valid4856
  · exact MergedCutProfiles.Batch121.valid4857
  · exact MergedCutProfiles.Batch121.valid4858
  · exact MergedCutProfiles.Batch121.valid4859
  · exact MergedCutProfiles.Batch121.valid4860
  · exact MergedCutProfiles.Batch121.valid4861
  · exact MergedCutProfiles.Batch121.valid4862
  · exact MergedCutProfiles.Batch121.valid4863
  · exact MergedCutProfiles.Batch121.valid4864
  · exact MergedCutProfiles.Batch121.valid4865
  · exact MergedCutProfiles.Batch121.valid4866
  · exact MergedCutProfiles.Batch121.valid4867
  · exact MergedCutProfiles.Batch121.valid4868
  · exact MergedCutProfiles.Batch121.valid4869
theorem numericValid726 : retention726.NumericValid := by decide +kernel
def certificate726 : RatCutBinCertificate := ⟨⟨retention726,(2129070161864492131/1000000000000000000),(50858016999050421/500000000000000000),(1565580850186765421/125000000000000000),(35273467744402477229/125000000000000000),(2049135623173588267/1000000000000000000)⟩,(993208118316980171/1000000000000000000),(380813766621177397/1000000000000000000),(125764584024640293/500000000000000000),(133914113505777971/1000000000000000000)⟩
theorem valid726 : certificate726.Valid := by decide +kernel
theorem sound726 : certificate726.Sound := rat_cut_bin_certificate_sound certificate726 profilesValid726 numericValid726 valid726

def retention727 : RatCutRetentionCertificate := ⟨(37/800),(93/2000),(895231605353564944/22499097179828279839),(434187153/500000000),(29/10),(33506326230275423949/16000000000000000000),true,MergedCutProfiles.Batch121.profile4870,![MergedCutProfiles.Batch121.profile4870,MergedCutProfiles.Batch121.profile4871,MergedCutProfiles.Batch121.profile4872,MergedCutProfiles.Batch121.profile4873,MergedCutProfiles.Batch121.profile4874,MergedCutProfiles.Batch121.profile4875,MergedCutProfiles.Batch121.profile4876,MergedCutProfiles.Batch121.profile4877,MergedCutProfiles.Batch121.profile4878,MergedCutProfiles.Batch121.profile4879,MergedCutProfiles.Batch122.profile4880,MergedCutProfiles.Batch122.profile4881,MergedCutProfiles.Batch122.profile4882,MergedCutProfiles.Batch121.profile4852,MergedCutProfiles.Batch122.profile4883,MergedCutProfiles.Batch122.profile4884]⟩
theorem profilesValid727 : retention727.ProfilesValid := by
  change ∀ j : Fin 16, (retention727.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch121.valid4870
  · exact MergedCutProfiles.Batch121.valid4871
  · exact MergedCutProfiles.Batch121.valid4872
  · exact MergedCutProfiles.Batch121.valid4873
  · exact MergedCutProfiles.Batch121.valid4874
  · exact MergedCutProfiles.Batch121.valid4875
  · exact MergedCutProfiles.Batch121.valid4876
  · exact MergedCutProfiles.Batch121.valid4877
  · exact MergedCutProfiles.Batch121.valid4878
  · exact MergedCutProfiles.Batch121.valid4879
  · exact MergedCutProfiles.Batch122.valid4880
  · exact MergedCutProfiles.Batch122.valid4881
  · exact MergedCutProfiles.Batch122.valid4882
  · exact MergedCutProfiles.Batch121.valid4852
  · exact MergedCutProfiles.Batch122.valid4883
  · exact MergedCutProfiles.Batch122.valid4884
theorem numericValid727 : retention727.NumericValid := by decide +kernel
def certificate727 : RatCutBinCertificate := ⟨⟨retention727,(2129070161864492131/1000000000000000000),(50858016999050421/500000000000000000),(1565580850186765421/125000000000000000),(35273467744402477229/125000000000000000),(127749689296138247/62500000000000000)⟩,(993208118316980171/1000000000000000000),(375586164961450127/1000000000000000000),(256611779030631711/1000000000000000000),(35046071033922313/250000000000000000)⟩
theorem valid727 : certificate727.Valid := by decide +kernel
theorem sound727 : certificate727.Sound := rat_cut_bin_certificate_sound certificate727 profilesValid727 numericValid727 valid727

def retention728 : RatCutRetentionCertificate := ⟨(37/800),(93/2000),(1148073653656053058/22499097179828279839),(55951975334597809/62500000000000000),(14/5),(164155345853019943543/80000000000000000000),true,MergedCutProfiles.Batch122.profile4885,![MergedCutProfiles.Batch122.profile4885,MergedCutProfiles.Batch122.profile4886,MergedCutProfiles.Batch122.profile4887,MergedCutProfiles.Batch122.profile4888,MergedCutProfiles.Batch122.profile4889,MergedCutProfiles.Batch122.profile4890,MergedCutProfiles.Batch122.profile4891,MergedCutProfiles.Batch121.profile4848,MergedCutProfiles.Batch122.profile4892,MergedCutProfiles.Batch122.profile4893,MergedCutProfiles.Batch122.profile4894,MergedCutProfiles.Batch122.profile4895,MergedCutProfiles.Batch122.profile4896,MergedCutProfiles.Batch122.profile4897,MergedCutProfiles.Batch122.profile4898,MergedCutProfiles.Batch122.profile4899]⟩
theorem profilesValid728 : retention728.ProfilesValid := by
  change ∀ j : Fin 16, (retention728.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch122.valid4885
  · exact MergedCutProfiles.Batch122.valid4886
  · exact MergedCutProfiles.Batch122.valid4887
  · exact MergedCutProfiles.Batch122.valid4888
  · exact MergedCutProfiles.Batch122.valid4889
  · exact MergedCutProfiles.Batch122.valid4890
  · exact MergedCutProfiles.Batch122.valid4891
  · exact MergedCutProfiles.Batch121.valid4848
  · exact MergedCutProfiles.Batch122.valid4892
  · exact MergedCutProfiles.Batch122.valid4893
  · exact MergedCutProfiles.Batch122.valid4894
  · exact MergedCutProfiles.Batch122.valid4895
  · exact MergedCutProfiles.Batch122.valid4896
  · exact MergedCutProfiles.Batch122.valid4897
  · exact MergedCutProfiles.Batch122.valid4898
  · exact MergedCutProfiles.Batch122.valid4899
theorem numericValid728 : retention728.NumericValid := by decide +kernel
def certificate728 : RatCutBinCertificate := ⟨⟨retention728,(2129070161864492131/1000000000000000000),(50858016999050421/500000000000000000),(1565580850186765421/125000000000000000),(35273467744402477229/125000000000000000),(80140830124753827/40000000000000000)⟩,(993208118316980171/1000000000000000000),(75687473457365673/200000000000000000),(126915353906319549/500000000000000000),(8760182748936971/62500000000000000)⟩
theorem valid728 : certificate728.Valid := by decide +kernel
theorem sound728 : certificate728.Sound := rat_cut_bin_certificate_sound certificate728 profilesValid728 numericValid728 valid728

def retention729 : RatCutRetentionCertificate := ⟨(37/800),(93/2000),(3074579698617219610/22499097179828279839),(574036826828026529/500000000000000000),(23/10),(1148109259957584680261/640000000000000000000),true,MergedCutProfiles.Batch122.profile4900,![MergedCutProfiles.Batch122.profile4900,MergedCutProfiles.Batch122.profile4901,MergedCutProfiles.Batch121.profile4848,MergedCutProfiles.Batch122.profile4902,MergedCutProfiles.Batch122.profile4903,MergedCutProfiles.Batch122.profile4904,MergedCutProfiles.Batch122.profile4905,MergedCutProfiles.Batch122.profile4906,MergedCutProfiles.Batch122.profile4907,MergedCutProfiles.Batch122.profile4908,MergedCutProfiles.Batch122.profile4909,MergedCutProfiles.Batch122.profile4910,MergedCutProfiles.Batch122.profile4911,MergedCutProfiles.Batch122.profile4912,MergedCutProfiles.Batch122.profile4913,MergedCutProfiles.Batch122.profile4914]⟩
theorem profilesValid729 : retention729.ProfilesValid := by
  change ∀ j : Fin 16, (retention729.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch122.valid4900
  · exact MergedCutProfiles.Batch122.valid4901
  · exact MergedCutProfiles.Batch121.valid4848
  · exact MergedCutProfiles.Batch122.valid4902
  · exact MergedCutProfiles.Batch122.valid4903
  · exact MergedCutProfiles.Batch122.valid4904
  · exact MergedCutProfiles.Batch122.valid4905
  · exact MergedCutProfiles.Batch122.valid4906
  · exact MergedCutProfiles.Batch122.valid4907
  · exact MergedCutProfiles.Batch122.valid4908
  · exact MergedCutProfiles.Batch122.valid4909
  · exact MergedCutProfiles.Batch122.valid4910
  · exact MergedCutProfiles.Batch122.valid4911
  · exact MergedCutProfiles.Batch122.valid4912
  · exact MergedCutProfiles.Batch122.valid4913
  · exact MergedCutProfiles.Batch122.valid4914
theorem numericValid729 : retention729.NumericValid := by decide +kernel
def certificate729 : RatCutBinCertificate := ⟨⟨retention729,(2129070161864492131/1000000000000000000),(50858016999050421/500000000000000000),(1565580850186765421/125000000000000000),(35273467744402477229/125000000000000000),(877073279162748737/500000000000000000)⟩,(993208118316980171/1000000000000000000),(4921464527069993/12500000000000000),(239288591687743821/1000000000000000000),(140476619001403211/1000000000000000000)⟩
theorem valid729 : certificate729.Valid := by decide +kernel
theorem sound729 : certificate729.Sound := rat_cut_bin_certificate_sound certificate729 profilesValid729 numericValid729 valid729

def retention730 : RatCutRetentionCertificate := ⟨(37/800),(93/2000),(8740373716887713907/22499097179828279839),(307457969861721961/100000000000000000),(5/4),(59595246897314554150482596564601929359/49193275177875513760000000000000000000),false,MergedCutProfiles.Batch122.profile4915,(fun _ => MergedCutProfiles.Batch122.profile4915)⟩
theorem profilesValid730 : retention730.ProfilesValid := by
  exact MergedCutProfiles.Batch122.valid4915
theorem numericValid730 : retention730.NumericValid := by decide +kernel
def certificate730 : RatCutBinCertificate := ⟨⟨retention730,(2129070161864492131/1000000000000000000),(50858016999050421/500000000000000000),(1565580850186765421/125000000000000000),(35273467744402477229/125000000000000000),(118983562302735937/100000000000000000)⟩,(993208118316980171/1000000000000000000),(227229177297654311/500000000000000000),(23391659768239199/125000000000000000),(28336180109457017/200000000000000000)⟩
theorem valid730 : certificate730.Valid := by decide +kernel
theorem sound730 : certificate730.Sound := rat_cut_bin_certificate_sound certificate730 profilesValid730 numericValid730 valid730

def retention731 : RatCutRetentionCertificate := ⟨(37/800),(93/2000),(10988074603415845874/22499097179828279839),(8740373716887713907/1000000000000000000),(21/20),(4731291671982300867555015434450053827237/4661532649006780750400000000000000000000),false,MergedCutProfiles.Batch122.profile4916,(fun _ => MergedCutProfiles.Batch122.profile4916)⟩
theorem profilesValid731 : retention731.ProfilesValid := by
  exact MergedCutProfiles.Batch122.valid4916
theorem numericValid731 : retention731.NumericValid := by decide +kernel
def certificate731 : RatCutBinCertificate := ⟨⟨retention731,(2129070161864492131/1000000000000000000),(50858016999050421/500000000000000000),(1565580850186765421/125000000000000000),(35273467744402477229/125000000000000000),(498404410975917449/500000000000000000)⟩,(993208118316980171/1000000000000000000),(484366691561717497/1000000000000000000),(32901898741542667/200000000000000000),(5620762605490417/40000000000000000)⟩
theorem valid731 : certificate731.Valid := by decide +kernel
theorem sound731 : certificate731.Sound := rat_cut_bin_certificate_sound certificate731 profilesValid731 numericValid731 valid731

def certificates : List RatCutBinCertificate := [certificate720,certificate721,certificate722,certificate723,certificate724,certificate725,certificate726,certificate727,certificate728,certificate729,certificate730,certificate731]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound720,List.forall_mem_cons.mpr ⟨sound721,List.forall_mem_cons.mpr ⟨sound722,List.forall_mem_cons.mpr ⟨sound723,List.forall_mem_cons.mpr ⟨sound724,List.forall_mem_cons.mpr ⟨sound725,List.forall_mem_cons.mpr ⟨sound726,List.forall_mem_cons.mpr ⟨sound727,List.forall_mem_cons.mpr ⟨sound728,List.forall_mem_cons.mpr ⟨sound729,List.forall_mem_cons.mpr ⟨sound730,List.forall_mem_cons.mpr ⟨sound731,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch060
