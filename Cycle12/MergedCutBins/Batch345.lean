import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch514
import Cycle12.MergedCutProfiles.Batch515
import Cycle12.MergedCutProfiles.Batch516
import Cycle12.MergedCutProfiles.Batch621
import Cycle12.MergedCutProfiles.Batch622
import Cycle12.MergedCutProfiles.Batch623

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch345

def retention4140 : RatCutRetentionCertificate := ⟨(57/1000),(23/400),(62500000000000000/269612376137375753),(21964479993516306387/500000000000000000),1,(54842224198939645996562844087980240539/35143167989626090219200000000000000000),false,MergedCutProfiles.Batch621.profile24879,(fun _ => MergedCutProfiles.Batch621.profile24879)⟩
theorem profilesValid4140 : retention4140.ProfilesValid := by
  exact MergedCutProfiles.Batch621.valid24879
theorem numericValid4140 : retention4140.NumericValid := by decide +kernel
def certificate4140 : RatCutBinCertificate := ⟨⟨retention4140,(2029116924191451017/1000000000000000000),(165065648943161283/1000000000000000000),(15031599453156358853/1000000000000000000),(4162450143084543733863/1000000000000000000),(76912752264016839/50000000000000000)⟩,(9995913293345847/10000000000000000),(32224496300001607/100000000000000000),(78204575325336843/250000000000000000),(232360808911545353/500000000000000000)⟩
theorem valid4140 : certificate4140.Valid := by decide +kernel
theorem sound4140 : certificate4140.Sound := rat_cut_bin_certificate_sound certificate4140 profilesValid4140 numericValid4140 valid4140

def retention4141 : RatCutRetentionCertificate := ⟨(57/1000),(23/400),(1/2),64,1,(63850940339993400478273430624811024279/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch514.profile20586,(fun _ => MergedCutProfiles.Batch514.profile20586)⟩
theorem profilesValid4141 : retention4141.ProfilesValid := by
  exact MergedCutProfiles.Batch514.valid20586
theorem numericValid4141 : retention4141.NumericValid := by decide +kernel
def certificate4141 : RatCutBinCertificate := ⟨⟨retention4141,(2029116924191451017/1000000000000000000),(165065648943161283/1000000000000000000),(15031599453156358853/1000000000000000000),(4162450143084543733863/1000000000000000000),(195077740525102539/200000000000000000)⟩,(9995913293345847/10000000000000000),(504534402936163557/1000000000000000000),(150303856946772403/1000000000000000000),(72172134055953041/500000000000000000)⟩
theorem valid4141 : certificate4141.Valid := by decide +kernel
theorem sound4141 : certificate4141.Sound := rat_cut_bin_certificate_sound certificate4141 profilesValid4141 numericValid4141 valid4141

def retention4142 : RatCutRetentionCertificate := ⟨(57/1000),(23/400),(62500000000000000/269612376137375753),(12527302198200351329/500000000000000000),1,(31065847552902515493169435169493264843/20043683517120562126400000000000000000),false,MergedCutProfiles.Batch621.profile24879,(fun _ => MergedCutProfiles.Batch621.profile24879)⟩
theorem profilesValid4142 : retention4142.ProfilesValid := by
  exact MergedCutProfiles.Batch621.valid24879
theorem numericValid4142 : retention4142.NumericValid := by decide +kernel
def certificate4142 : RatCutBinCertificate := ⟨⟨retention4142,(1898201623191451017/1000000000000000000),(165065648943161283/1000000000000000000),(15031599453156358853/1000000000000000000),(4162450143084543733863/1000000000000000000),(1529062461344076017/1000000000000000000)⟩,(999617698041518103/1000000000000000000),(4292439296023047/125000000000000000),(831738635622175699/1000000000000000000),(299539525312609017/250000000000000000)⟩
theorem valid4142 : certificate4142.Valid := by decide +kernel
theorem sound4142 : certificate4142.Sound := rat_cut_bin_certificate_sound certificate4142 profilesValid4142 numericValid4142 valid4142

def retention4143 : RatCutRetentionCertificate := ⟨(57/1000),(23/400),(1/2),64,1,(63850940339993400478273430624811024279/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch514.profile20586,(fun _ => MergedCutProfiles.Batch514.profile20586)⟩
theorem profilesValid4143 : retention4143.ProfilesValid := by
  exact MergedCutProfiles.Batch514.valid20586
theorem numericValid4143 : retention4143.NumericValid := by decide +kernel
def certificate4143 : RatCutBinCertificate := ⟨⟨retention4143,(1898201623191451017/1000000000000000000),(165065648943161283/1000000000000000000),(15031599453156358853/1000000000000000000),(4162450143084543733863/1000000000000000000),(976826316272238657/1000000000000000000)⟩,(999617698041518103/1000000000000000000),(6719114427828161/125000000000000000),(389188028766639887/500000000000000000),(748618170415831621/1000000000000000000)⟩
theorem valid4143 : certificate4143.Valid := by decide +kernel
theorem sound4143 : certificate4143.Sound := rat_cut_bin_certificate_sound certificate4143 profilesValid4143 numericValid4143 valid4143

def retention4144 : RatCutRetentionCertificate := ⟨(23/400),(29/500),(735322457984638063/270527273922842851485),(22526053143828977/31250000000000000),(39/10),(745046809267447609/312500000000000000),true,MergedCutProfiles.Batch622.profile24880,![MergedCutProfiles.Batch622.profile24880,MergedCutProfiles.Batch622.profile24881,MergedCutProfiles.Batch622.profile24882,MergedCutProfiles.Batch622.profile24883,MergedCutProfiles.Batch622.profile24884,MergedCutProfiles.Batch515.profile20622,MergedCutProfiles.Batch515.profile20638,MergedCutProfiles.Batch622.profile24885,MergedCutProfiles.Batch622.profile24886,MergedCutProfiles.Batch622.profile24887,MergedCutProfiles.Batch622.profile24888,MergedCutProfiles.Batch515.profile20623,MergedCutProfiles.Batch622.profile24889,MergedCutProfiles.Batch515.profile20639,MergedCutProfiles.Batch622.profile24890,MergedCutProfiles.Batch622.profile24891]⟩
theorem profilesValid4144 : retention4144.ProfilesValid := by
  change ∀ j : Fin 16, (retention4144.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch622.valid24880
  · exact MergedCutProfiles.Batch622.valid24881
  · exact MergedCutProfiles.Batch622.valid24882
  · exact MergedCutProfiles.Batch622.valid24883
  · exact MergedCutProfiles.Batch622.valid24884
  · exact MergedCutProfiles.Batch515.valid20622
  · exact MergedCutProfiles.Batch515.valid20638
  · exact MergedCutProfiles.Batch622.valid24885
  · exact MergedCutProfiles.Batch622.valid24886
  · exact MergedCutProfiles.Batch622.valid24887
  · exact MergedCutProfiles.Batch622.valid24888
  · exact MergedCutProfiles.Batch515.valid20623
  · exact MergedCutProfiles.Batch622.valid24889
  · exact MergedCutProfiles.Batch515.valid20639
  · exact MergedCutProfiles.Batch622.valid24890
  · exact MergedCutProfiles.Batch622.valid24891
theorem numericValid4144 : retention4144.NumericValid := by decide +kernel
def certificate4144 : RatCutBinCertificate := ⟨⟨retention4144,(2036572706962492951/1000000000000000000),(168442616661570077/1000000000000000000),(7583137641424036037/500000000000000000),(12860221213138014157/3125000000000000),(57398362348939023/25000000000000000)⟩,(19991735446759591/20000000000000000),(254033986912812189/500000000000000000),(9243676459778521/62500000000000000),(71956603470434569/1000000000000000000)⟩
theorem valid4144 : certificate4144.Valid := by decide +kernel
theorem sound4144 : certificate4144.Sound := rat_cut_bin_certificate_sound certificate4144 profilesValid4144 numericValid4144 valid4144

def retention4145 : RatCutRetentionCertificate := ⟨(23/400),(29/500),(219206454400000000/54105454784568570297),(735322457984638063/1000000000000000000),(19/5),(3025676946606982823091/1280000000000000000000),true,MergedCutProfiles.Batch622.profile24892,![MergedCutProfiles.Batch622.profile24892,MergedCutProfiles.Batch622.profile24882,MergedCutProfiles.Batch622.profile24893,MergedCutProfiles.Batch515.profile20622,MergedCutProfiles.Batch622.profile24894,MergedCutProfiles.Batch622.profile24895,MergedCutProfiles.Batch622.profile24896,MergedCutProfiles.Batch515.profile20623,MergedCutProfiles.Batch622.profile24897,MergedCutProfiles.Batch622.profile24890,MergedCutProfiles.Batch622.profile24898,MergedCutProfiles.Batch515.profile20624,MergedCutProfiles.Batch622.profile24899,MergedCutProfiles.Batch516.profile20640,MergedCutProfiles.Batch622.profile24900,MergedCutProfiles.Batch515.profile20625]⟩
theorem profilesValid4145 : retention4145.ProfilesValid := by
  change ∀ j : Fin 16, (retention4145.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch622.valid24892
  · exact MergedCutProfiles.Batch622.valid24882
  · exact MergedCutProfiles.Batch622.valid24893
  · exact MergedCutProfiles.Batch515.valid20622
  · exact MergedCutProfiles.Batch622.valid24894
  · exact MergedCutProfiles.Batch622.valid24895
  · exact MergedCutProfiles.Batch622.valid24896
  · exact MergedCutProfiles.Batch515.valid20623
  · exact MergedCutProfiles.Batch622.valid24897
  · exact MergedCutProfiles.Batch622.valid24890
  · exact MergedCutProfiles.Batch622.valid24898
  · exact MergedCutProfiles.Batch515.valid20624
  · exact MergedCutProfiles.Batch622.valid24899
  · exact MergedCutProfiles.Batch516.valid20640
  · exact MergedCutProfiles.Batch622.valid24900
  · exact MergedCutProfiles.Batch515.valid20625
theorem numericValid4145 : retention4145.NumericValid := by decide +kernel
def certificate4145 : RatCutBinCertificate := ⟨⟨retention4145,(2036572706962492951/1000000000000000000),(168442616661570077/1000000000000000000),(7583137641424036037/500000000000000000),(12860221213138014157/3125000000000000),(2277856741871940203/1000000000000000000)⟩,(19991735446759591/20000000000000000),(20246579461261089/40000000000000000),(74595659148295511/500000000000000000),(3679878233548961/50000000000000000)⟩
theorem valid4145 : certificate4145.Valid := by decide +kernel
theorem sound4145 : certificate4145.Sound := rat_cut_bin_certificate_sound certificate4145 profilesValid4145 numericValid4145 valid4145

def retention4146 : RatCutRetentionCertificate := ⟨(23/400),(29/500),(419479517509049767/90175757974280950495),(68502017/62500000),(11/4),(9375791035172830197/4000000000000000000),true,MergedCutProfiles.Batch622.profile24901,![MergedCutProfiles.Batch622.profile24901,MergedCutProfiles.Batch622.profile24902,MergedCutProfiles.Batch622.profile24903,MergedCutProfiles.Batch622.profile24904,MergedCutProfiles.Batch622.profile24905,MergedCutProfiles.Batch622.profile24906,MergedCutProfiles.Batch515.profile20623,MergedCutProfiles.Batch622.profile24907,MergedCutProfiles.Batch622.profile24908,MergedCutProfiles.Batch515.profile20608,MergedCutProfiles.Batch514.profile20593,MergedCutProfiles.Batch622.profile24909,MergedCutProfiles.Batch622.profile24910,MergedCutProfiles.Batch515.profile20625,MergedCutProfiles.Batch622.profile24911,MergedCutProfiles.Batch622.profile24912]⟩
theorem profilesValid4146 : retention4146.ProfilesValid := by
  change ∀ j : Fin 16, (retention4146.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch622.valid24901
  · exact MergedCutProfiles.Batch622.valid24902
  · exact MergedCutProfiles.Batch622.valid24903
  · exact MergedCutProfiles.Batch622.valid24904
  · exact MergedCutProfiles.Batch622.valid24905
  · exact MergedCutProfiles.Batch622.valid24906
  · exact MergedCutProfiles.Batch515.valid20623
  · exact MergedCutProfiles.Batch622.valid24907
  · exact MergedCutProfiles.Batch622.valid24908
  · exact MergedCutProfiles.Batch515.valid20608
  · exact MergedCutProfiles.Batch514.valid20593
  · exact MergedCutProfiles.Batch622.valid24909
  · exact MergedCutProfiles.Batch622.valid24910
  · exact MergedCutProfiles.Batch515.valid20625
  · exact MergedCutProfiles.Batch622.valid24911
  · exact MergedCutProfiles.Batch622.valid24912
theorem numericValid4146 : retention4146.NumericValid := by decide +kernel
def certificate4146 : RatCutBinCertificate := ⟨⟨retention4146,(2036572706962492951/1000000000000000000),(168442616661570077/1000000000000000000),(7583137641424036037/500000000000000000),(12860221213138014157/3125000000000000),(2281744726619493399/1000000000000000000)⟩,(19991735446759591/20000000000000000),(8165612685161757/20000000000000000),(45196064032755161/200000000000000000),(14695590836982177/100000000000000000)⟩
theorem valid4146 : certificate4146.Valid := by decide +kernel
theorem sound4146 : certificate4146.Sound := rat_cut_bin_certificate_sound certificate4146 profilesValid4146 numericValid4146 valid4146

def retention4147 : RatCutRetentionCertificate := ⟨(23/400),(29/500),(9580590246801124864/270527273922842851485),(1258438552527149301/1000000000000000000),(49/20),(2760228483498715168221/1280000000000000000000),true,MergedCutProfiles.Batch622.profile24889,![MergedCutProfiles.Batch622.profile24889,MergedCutProfiles.Batch622.profile24913,MergedCutProfiles.Batch622.profile24914,MergedCutProfiles.Batch622.profile24915,MergedCutProfiles.Batch515.profile20632,MergedCutProfiles.Batch622.profile24916,MergedCutProfiles.Batch515.profile20621,MergedCutProfiles.Batch516.profile20649,MergedCutProfiles.Batch622.profile24917,MergedCutProfiles.Batch622.profile24918,MergedCutProfiles.Batch622.profile24919,MergedCutProfiles.Batch623.profile24920,MergedCutProfiles.Batch623.profile24921,MergedCutProfiles.Batch623.profile24922,MergedCutProfiles.Batch516.profile20658,MergedCutProfiles.Batch623.profile24923]⟩
theorem profilesValid4147 : retention4147.ProfilesValid := by
  change ∀ j : Fin 16, (retention4147.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch622.valid24889
  · exact MergedCutProfiles.Batch622.valid24913
  · exact MergedCutProfiles.Batch622.valid24914
  · exact MergedCutProfiles.Batch622.valid24915
  · exact MergedCutProfiles.Batch515.valid20632
  · exact MergedCutProfiles.Batch622.valid24916
  · exact MergedCutProfiles.Batch515.valid20621
  · exact MergedCutProfiles.Batch516.valid20649
  · exact MergedCutProfiles.Batch622.valid24917
  · exact MergedCutProfiles.Batch622.valid24918
  · exact MergedCutProfiles.Batch622.valid24919
  · exact MergedCutProfiles.Batch623.valid24920
  · exact MergedCutProfiles.Batch623.valid24921
  · exact MergedCutProfiles.Batch623.valid24922
  · exact MergedCutProfiles.Batch516.valid20658
  · exact MergedCutProfiles.Batch623.valid24923
theorem numericValid4147 : retention4147.NumericValid := by decide +kernel
def certificate4147 : RatCutBinCertificate := ⟨⟨retention4147,(2036572706962492951/1000000000000000000),(168442616661570077/1000000000000000000),(7583137641424036037/500000000000000000),(12860221213138014157/3125000000000000),(2101011272750381541/1000000000000000000)⟩,(19991735446759591/20000000000000000),(207840788110260491/500000000000000000),(10970872135272923/50000000000000000),(29428901618119401/200000000000000000)⟩
theorem valid4147 : certificate4147.Valid := by decide +kernel
theorem sound4147 : certificate4147.Sound := rat_cut_bin_certificate_sound certificate4147 profilesValid4147 numericValid4147 valid4147

def retention4148 : RatCutRetentionCertificate := ⟨(23/400),(29/500),(12800000000000000000/54105454784568570297),(18712090325783447/1953125000000000),(21/20),(1468603584360898828538632204854566879639/958059024680112486400000000000000000000),false,MergedCutProfiles.Batch623.profile24924,(fun _ => MergedCutProfiles.Batch623.profile24924)⟩
theorem profilesValid4148 : retention4148.ProfilesValid := by
  exact MergedCutProfiles.Batch623.valid24924
theorem numericValid4148 : retention4148.NumericValid := by decide +kernel
def certificate4148 : RatCutBinCertificate := ⟨⟨retention4148,(2036572706962492951/1000000000000000000),(168442616661570077/1000000000000000000),(7583137641424036037/500000000000000000),(12860221213138014157/3125000000000000),(754572329821400791/500000000000000000)⟩,(19991735446759591/20000000000000000),(352472255817730607/1000000000000000000),(279970120444942597/1000000000000000000),(87984026487703879/250000000000000000)⟩
theorem valid4148 : certificate4148.Valid := by decide +kernel
theorem sound4148 : certificate4148.Sound := rat_cut_bin_certificate_sound certificate4148 profilesValid4148 numericValid4148 valid4148

def retention4149 : RatCutRetentionCertificate := ⟨(23/400),(29/500),(1/2),64,1,(15962780019151752954074012989410801519/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch516.profile20670,(fun _ => MergedCutProfiles.Batch516.profile20670)⟩
theorem profilesValid4149 : retention4149.ProfilesValid := by
  exact MergedCutProfiles.Batch516.valid20670
theorem numericValid4149 : retention4149.NumericValid := by decide +kernel
def certificate4149 : RatCutBinCertificate := ⟨⟨retention4149,(2036572706962492951/1000000000000000000),(168442616661570077/1000000000000000000),(7583137641424036037/500000000000000000),(12860221213138014157/3125000000000000),(975054759468367279/1000000000000000000)⟩,(19991735446759591/20000000000000000),(500517687586425511/1000000000000000000),(153067794174183777/1000000000000000000),(1469483628697917/10000000000000000)⟩
theorem valid4149 : certificate4149.Valid := by decide +kernel
theorem sound4149 : certificate4149.Sound := rat_cut_bin_certificate_sound certificate4149 profilesValid4149 numericValid4149 valid4149

def retention4150 : RatCutRetentionCertificate := ⟨(23/400),(29/500),(12800000000000000000/54105454784568570297),(12479702866627355967/500000000000000000),1,(153660173199416598885273353042862511223/99837622933018847736000000000000000000),false,MergedCutProfiles.Batch623.profile24924,(fun _ => MergedCutProfiles.Batch623.profile24924)⟩
theorem profilesValid4150 : retention4150.ProfilesValid := by
  exact MergedCutProfiles.Batch623.valid24924
theorem numericValid4150 : retention4150.NumericValid := by decide +kernel
def certificate4150 : RatCutBinCertificate := ⟨⟨retention4150,(1901151993962492951/1000000000000000000),(168442616661570077/1000000000000000000),(7583137641424036037/500000000000000000),(12860221213138014157/3125000000000000),(1517985902655829523/1000000000000000000)⟩,(499807125882778867/500000000000000000),(34462641677849617/1000000000000000000),(3247604146737367/3906250000000000),(594603714006960217/500000000000000000)⟩
theorem valid4150 : certificate4150.Valid := by decide +kernel
theorem sound4150 : certificate4150.Sound := rat_cut_bin_certificate_sound certificate4150 profilesValid4150 numericValid4150 valid4150

def retention4151 : RatCutRetentionCertificate := ⟨(23/400),(29/500),(1/2),64,1,(15962780019151752954074012989410801519/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch516.profile20670,(fun _ => MergedCutProfiles.Batch516.profile20670)⟩
theorem profilesValid4151 : retention4151.ProfilesValid := by
  exact MergedCutProfiles.Batch516.valid20670
theorem numericValid4151 : retention4151.NumericValid := by decide +kernel
def certificate4151 : RatCutBinCertificate := ⟨⟨retention4151,(1901151993962492951/1000000000000000000),(168442616661570077/1000000000000000000),(7583137641424036037/500000000000000000),(12860221213138014157/3125000000000000),(976558796116191641/1000000000000000000)⟩,(499807125882778867/500000000000000000),(13392384678554119/250000000000000000),(389430418995444723/500000000000000000),(37443986153459643/50000000000000000)⟩
theorem valid4151 : certificate4151.Valid := by decide +kernel
theorem sound4151 : certificate4151.Sound := rat_cut_bin_certificate_sound certificate4151 profilesValid4151 numericValid4151 valid4151

def certificates : List RatCutBinCertificate := [certificate4140,certificate4141,certificate4142,certificate4143,certificate4144,certificate4145,certificate4146,certificate4147,certificate4148,certificate4149,certificate4150,certificate4151]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4140,List.forall_mem_cons.mpr ⟨sound4141,List.forall_mem_cons.mpr ⟨sound4142,List.forall_mem_cons.mpr ⟨sound4143,List.forall_mem_cons.mpr ⟨sound4144,List.forall_mem_cons.mpr ⟨sound4145,List.forall_mem_cons.mpr ⟨sound4146,List.forall_mem_cons.mpr ⟨sound4147,List.forall_mem_cons.mpr ⟨sound4148,List.forall_mem_cons.mpr ⟨sound4149,List.forall_mem_cons.mpr ⟨sound4150,List.forall_mem_cons.mpr ⟨sound4151,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch345
