import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch374
import Cycle12.MergedCutProfiles.Batch375
import Cycle12.MergedCutProfiles.Batch610
import Cycle12.MergedCutProfiles.Batch695
import Cycle12.MergedCutProfiles.Batch696

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch414

def retention4968 : RatCutRetentionCertificate := ⟨(6/125),(49/1000),(1/40),(1866070599996858423/40000000000000000),(21/20),(2213204879735666307/1000000000000000000),false,MergedCutProfiles.Batch695.profile27817,(fun _ => MergedCutProfiles.Batch695.profile27817)⟩
theorem profilesValid4968 : retention4968.ProfilesValid := by
  exact MergedCutProfiles.Batch695.valid27817
theorem numericValid4968 : retention4968.NumericValid := by decide +kernel
def certificate4968 : RatCutBinCertificate := ⟨⟨retention4968,(471259808556307713/250000000000000000),(114392751307786871/1000000000000000000),(2577762339130688791/200000000000000000),(5179120136195503627223/200000000000000000),(1097818985220990599/500000000000000000)⟩,(999935155387811347/1000000000000000000),(346056650276193003/500000000000000000),(53185123708703067/1000000000000000000),(106654299050527933/1000000000000000000)⟩
theorem valid4968 : certificate4968.Valid := by decide +kernel
theorem sound4968 : certificate4968.Sound := rat_cut_bin_certificate_sound certificate4968 profilesValid4968 numericValid4968 valid4968

def retention4969 : RatCutRetentionCertificate := ⟨(49/1000),(1/20),(305609076934304646/953877650712359839975),(599174741563189189/1000000000000000000),4,(1365422201992813239501354068070143883/599174741563189189000000000000000000),true,MergedCutProfiles.Batch695.profile27818,![MergedCutProfiles.Batch695.profile27818,MergedCutProfiles.Batch695.profile27819,MergedCutProfiles.Batch695.profile27820,MergedCutProfiles.Batch695.profile27821,MergedCutProfiles.Batch695.profile27822,MergedCutProfiles.Batch695.profile27823,MergedCutProfiles.Batch695.profile27824,MergedCutProfiles.Batch695.profile27825,MergedCutProfiles.Batch610.profile24418,MergedCutProfiles.Batch610.profile24432,MergedCutProfiles.Batch695.profile27826,MergedCutProfiles.Batch695.profile27827,MergedCutProfiles.Batch695.profile27828,MergedCutProfiles.Batch695.profile27829,MergedCutProfiles.Batch695.profile27830,MergedCutProfiles.Batch610.profile24405]⟩
theorem profilesValid4969 : retention4969.ProfilesValid := by
  change ∀ j : Fin 16, (retention4969.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch695.valid27818
  · exact MergedCutProfiles.Batch695.valid27819
  · exact MergedCutProfiles.Batch695.valid27820
  · exact MergedCutProfiles.Batch695.valid27821
  · exact MergedCutProfiles.Batch695.valid27822
  · exact MergedCutProfiles.Batch695.valid27823
  · exact MergedCutProfiles.Batch695.valid27824
  · exact MergedCutProfiles.Batch695.valid27825
  · exact MergedCutProfiles.Batch610.valid24418
  · exact MergedCutProfiles.Batch610.valid24432
  · exact MergedCutProfiles.Batch695.valid27826
  · exact MergedCutProfiles.Batch695.valid27827
  · exact MergedCutProfiles.Batch695.valid27828
  · exact MergedCutProfiles.Batch695.valid27829
  · exact MergedCutProfiles.Batch695.valid27830
  · exact MergedCutProfiles.Batch610.valid24405
theorem numericValid4969 : retention4969.NumericValid := by decide +kernel
def certificate4969 : RatCutBinCertificate := ⟨⟨retention4969,(1918214503239611651/1000000000000000000),(59865971199444307/500000000000000000),(13103032017811620311/1000000000000000000),(12570243598073477431933/500000000000000000),(1104362712567894819/500000000000000000)⟩,(999932427741464209/1000000000000000000),(350006026103530027/500000000000000000),(50323240619888097/1000000000000000000),(22582435234350687/1000000000000000000)⟩
theorem valid4969 : certificate4969.Valid := by decide +kernel
theorem sound4969 : certificate4969.Sound := rat_cut_bin_certificate_sound certificate4969 profilesValid4969 numericValid4969 valid4969

def retention4970 : RatCutRetentionCertificate := ⟨(49/1000),(1/20),(598833800000000/1031219081851199827),(152804538467152323/250000000000000000),4,(4593889167458432057/2000000000000000000),true,MergedCutProfiles.Batch695.profile27819,![MergedCutProfiles.Batch695.profile27819,MergedCutProfiles.Batch695.profile27831,MergedCutProfiles.Batch610.profile24403,MergedCutProfiles.Batch695.profile27824,MergedCutProfiles.Batch610.profile24418,MergedCutProfiles.Batch695.profile27826,MergedCutProfiles.Batch695.profile27832,MergedCutProfiles.Batch695.profile27829,MergedCutProfiles.Batch695.profile27833,MergedCutProfiles.Batch695.profile27834,MergedCutProfiles.Batch610.profile24433,MergedCutProfiles.Batch610.profile24406,MergedCutProfiles.Batch695.profile27835,MergedCutProfiles.Batch695.profile27836,MergedCutProfiles.Batch610.profile24407,MergedCutProfiles.Batch610.profile24434]⟩
theorem profilesValid4970 : retention4970.ProfilesValid := by
  change ∀ j : Fin 16, (retention4970.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch695.valid27819
  · exact MergedCutProfiles.Batch695.valid27831
  · exact MergedCutProfiles.Batch610.valid24403
  · exact MergedCutProfiles.Batch695.valid27824
  · exact MergedCutProfiles.Batch610.valid24418
  · exact MergedCutProfiles.Batch695.valid27826
  · exact MergedCutProfiles.Batch695.valid27832
  · exact MergedCutProfiles.Batch695.valid27829
  · exact MergedCutProfiles.Batch695.valid27833
  · exact MergedCutProfiles.Batch695.valid27834
  · exact MergedCutProfiles.Batch610.valid24433
  · exact MergedCutProfiles.Batch610.valid24406
  · exact MergedCutProfiles.Batch695.valid27835
  · exact MergedCutProfiles.Batch695.valid27836
  · exact MergedCutProfiles.Batch610.valid24407
  · exact MergedCutProfiles.Batch610.valid24434
theorem numericValid4970 : retention4970.NumericValid := by decide +kernel
def certificate4970 : RatCutBinCertificate := ⟨⟨retention4970,(1918214503239611651/1000000000000000000),(59865971199444307/500000000000000000),(13103032017811620311/1000000000000000000),(12570243598073477431933/500000000000000000),(1113415978869348263/500000000000000000)⟩,(999932427741464209/1000000000000000000),(21415055404462993/31250000000000000),(55732991065023091/1000000000000000000),(5054058153697001/200000000000000000)⟩
theorem valid4970 : certificate4970.Valid := by decide +kernel
theorem sound4970 : certificate4970.Sound := rat_cut_bin_certificate_sound certificate4970 profilesValid4970 numericValid4970 valid4970

def retention4971 : RatCutRetentionCertificate := ⟨(49/1000),(1/20),(2461436148697625397/1907755301424719679950),(110784253/100000000),(57/20),(2655228606631053965674739531359797039/1107842530000000000000000000000000000),true,MergedCutProfiles.Batch695.profile27821,![MergedCutProfiles.Batch695.profile27821,MergedCutProfiles.Batch695.profile27837,MergedCutProfiles.Batch695.profile27827,MergedCutProfiles.Batch610.profile24405,MergedCutProfiles.Batch695.profile27838,MergedCutProfiles.Batch695.profile27839,MergedCutProfiles.Batch696.profile27840,MergedCutProfiles.Batch696.profile27841,MergedCutProfiles.Batch610.profile24409,MergedCutProfiles.Batch696.profile27842,MergedCutProfiles.Batch696.profile27843,MergedCutProfiles.Batch610.profile24411,MergedCutProfiles.Batch610.profile24412,MergedCutProfiles.Batch696.profile27844,MergedCutProfiles.Batch696.profile27845,MergedCutProfiles.Batch696.profile27846]⟩
theorem profilesValid4971 : retention4971.ProfilesValid := by
  change ∀ j : Fin 16, (retention4971.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch695.valid27821
  · exact MergedCutProfiles.Batch695.valid27837
  · exact MergedCutProfiles.Batch695.valid27827
  · exact MergedCutProfiles.Batch610.valid24405
  · exact MergedCutProfiles.Batch695.valid27838
  · exact MergedCutProfiles.Batch695.valid27839
  · exact MergedCutProfiles.Batch696.valid27840
  · exact MergedCutProfiles.Batch696.valid27841
  · exact MergedCutProfiles.Batch610.valid24409
  · exact MergedCutProfiles.Batch696.valid27842
  · exact MergedCutProfiles.Batch696.valid27843
  · exact MergedCutProfiles.Batch610.valid24411
  · exact MergedCutProfiles.Batch610.valid24412
  · exact MergedCutProfiles.Batch696.valid27844
  · exact MergedCutProfiles.Batch696.valid27845
  · exact MergedCutProfiles.Batch696.valid27846
theorem numericValid4971 : retention4971.NumericValid := by decide +kernel
def certificate4971 : RatCutBinCertificate := ⟨⟨retention4971,(1918214503239611651/1000000000000000000),(59865971199444307/500000000000000000),(13103032017811620311/1000000000000000000),(12570243598073477431933/500000000000000000),(2346801115157006693/1000000000000000000)⟩,(999932427741464209/1000000000000000000),(229487505079584801/500000000000000000),(91796813091334527/500000000000000000),(119897029490761407/1000000000000000000)⟩
theorem valid4971 : certificate4971.Valid := by decide +kernel
theorem sound4971 : certificate4971.Sound := rat_cut_bin_certificate_sound certificate4971 profilesValid4971 numericValid4971 valid4971

def retention4972 : RatCutRetentionCertificate := ⟨(49/1000),(1/20),(1280000000000000000/38155106028494393599),(2461436148697625397/1000000000000000000),(17/10),(2753028685171607291217/1280000000000000000000),true,MergedCutProfiles.Batch696.profile27847,![MergedCutProfiles.Batch696.profile27847,MergedCutProfiles.Batch696.profile27848,MergedCutProfiles.Batch696.profile27849,MergedCutProfiles.Batch696.profile27850,MergedCutProfiles.Batch696.profile27851,MergedCutProfiles.Batch696.profile27852,MergedCutProfiles.Batch374.profile14984,MergedCutProfiles.Batch696.profile27853,MergedCutProfiles.Batch696.profile27854,MergedCutProfiles.Batch374.profile14977,MergedCutProfiles.Batch374.profile14965,MergedCutProfiles.Batch696.profile27855,MergedCutProfiles.Batch696.profile27856,MergedCutProfiles.Batch696.profile27857,MergedCutProfiles.Batch696.profile27858,MergedCutProfiles.Batch696.profile27859]⟩
theorem profilesValid4972 : retention4972.ProfilesValid := by
  change ∀ j : Fin 16, (retention4972.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch696.valid27847
  · exact MergedCutProfiles.Batch696.valid27848
  · exact MergedCutProfiles.Batch696.valid27849
  · exact MergedCutProfiles.Batch696.valid27850
  · exact MergedCutProfiles.Batch696.valid27851
  · exact MergedCutProfiles.Batch696.valid27852
  · exact MergedCutProfiles.Batch374.valid14984
  · exact MergedCutProfiles.Batch696.valid27853
  · exact MergedCutProfiles.Batch696.valid27854
  · exact MergedCutProfiles.Batch374.valid14977
  · exact MergedCutProfiles.Batch374.valid14965
  · exact MergedCutProfiles.Batch696.valid27855
  · exact MergedCutProfiles.Batch696.valid27856
  · exact MergedCutProfiles.Batch696.valid27857
  · exact MergedCutProfiles.Batch696.valid27858
  · exact MergedCutProfiles.Batch696.valid27859
theorem numericValid4972 : retention4972.NumericValid := by decide +kernel
def certificate4972 : RatCutBinCertificate := ⟨⟨retention4972,(1918214503239611651/1000000000000000000),(59865971199444307/500000000000000000),(13103032017811620311/1000000000000000000),(12570243598073477431933/500000000000000000),(1060502909187485443/500000000000000000)⟩,(999932427741464209/1000000000000000000),(364597243010097011/1000000000000000000),(133767086519603293/500000000000000000),(32138062519266529/125000000000000000)⟩
theorem valid4972 : certificate4972.Valid := by decide +kernel
theorem sound4972 : certificate4972.Sound := rat_cut_bin_certificate_sound certificate4972 profilesValid4972 numericValid4972 valid4972

def retention4973 : RatCutRetentionCertificate := ⟨(49/1000),(1/20),(1/2),64,1,(15962085016107493154417226112293942951/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch375.profile15016,(fun _ => MergedCutProfiles.Batch375.profile15016)⟩
theorem profilesValid4973 : retention4973.ProfilesValid := by
  exact MergedCutProfiles.Batch375.valid15016
theorem numericValid4973 : retention4973.NumericValid := by decide +kernel
def certificate4973 : RatCutBinCertificate := ⟨⟨retention4973,(1918214503239611651/1000000000000000000),(59865971199444307/500000000000000000),(13103032017811620311/1000000000000000000),(12570243598073477431933/500000000000000000),(490051094924416069/500000000000000000)⟩,(999932427741464209/1000000000000000000),(545069642264295841/1000000000000000000),(124159355286979353/1000000000000000000),(119845228389658431/1000000000000000000)⟩
theorem valid4973 : certificate4973.Valid := by decide +kernel
theorem sound4973 : certificate4973.Sound := rat_cut_bin_certificate_sound certificate4973 profilesValid4973 numericValid4973 valid4973

def retention4974 : RatCutRetentionCertificate := ⟨(49/1000),(1/20),(1280000000000000000/38155106028494393599),(2284929539080199469/62500000000000000),1,(6946690334565834816070396200043374187/3249677566691839244800000000000000000),false,MergedCutProfiles.Batch696.profile27860,(fun _ => MergedCutProfiles.Batch696.profile27860)⟩
theorem profilesValid4974 : retention4974.ProfilesValid := by
  exact MergedCutProfiles.Batch696.valid27860
theorem numericValid4974 : retention4974.NumericValid := by decide +kernel
def certificate4974 : RatCutBinCertificate := ⟨⟨retention4974,(1741627666239611651/1000000000000000000),(59865971199444307/500000000000000000),(13103032017811620311/1000000000000000000),(12570243598073477431933/500000000000000000),(132608795952006649/62500000000000000)⟩,(999938648352320947/1000000000000000000),(18481303431925501/1000000000000000000),(439315152401843399/500000000000000000),(176185754259991463/100000000000000000)⟩
theorem valid4974 : certificate4974.Valid := by decide +kernel
theorem sound4974 : certificate4974.Sound := rat_cut_bin_certificate_sound certificate4974 profilesValid4974 numericValid4974 valid4974

def retention4975 : RatCutRetentionCertificate := ⟨(49/1000),(1/20),(1/2),64,1,(15962085016107493154417226112293942951/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch375.profile15016,(fun _ => MergedCutProfiles.Batch375.profile15016)⟩
theorem profilesValid4975 : retention4975.ProfilesValid := by
  exact MergedCutProfiles.Batch375.valid15016
theorem numericValid4975 : retention4975.NumericValid := by decide +kernel
def certificate4975 : RatCutBinCertificate := ⟨⟨retention4975,(1741627666239611651/1000000000000000000),(59865971199444307/500000000000000000),(13103032017811620311/1000000000000000000),(12570243598073477431933/500000000000000000),(196343158490340487/200000000000000000)⟩,(999938648352320947/1000000000000000000),(2496428614651119/62500000000000000),(163180189082089987/200000000000000000),(98604124905602273/125000000000000000)⟩
theorem valid4975 : certificate4975.Valid := by decide +kernel
theorem sound4975 : certificate4975.Sound := rat_cut_bin_certificate_sound certificate4975 profilesValid4975 numericValid4975 valid4975

def retention4976 : RatCutRetentionCertificate := ⟨(49/1000),(1/20),(71834091544352512/190775530142471967995),(711228629152005069/1000000000000000000),4,(1719268118584912106108768656476678419/711228629152005069000000000000000000),false,MergedCutProfiles.Batch696.profile27861,(fun _ => MergedCutProfiles.Batch696.profile27861)⟩
theorem profilesValid4976 : retention4976.ProfilesValid := by
  exact MergedCutProfiles.Batch696.valid27861
theorem numericValid4976 : retention4976.NumericValid := by decide +kernel
def certificate4976 : RatCutBinCertificate := ⟨⟨retention4976,(1893292060239611651/1000000000000000000),(59865971199444307/500000000000000000),(13103032017811620311/1000000000000000000),(12570243598073477431933/500000000000000000),(2348119638616482317/1000000000000000000)⟩,(499966652841521559/500000000000000000),(839807649777208797/1000000000000000000),(106068076061801/7812500000000000),(6606162657972001/1000000000000000000)⟩
theorem valid4976 : certificate4976.Valid := by decide +kernel
theorem sound4976 : certificate4976.Sound := rat_cut_bin_certificate_sound certificate4976 profilesValid4976 numericValid4976 valid4976

def retention4977 : RatCutRetentionCertificate := ⟨(49/1000),(1/20),(438256215155646993/953877650712359839975),(280601920095127/390625000000000),4,(6952317302416180469787176092805593119/2873363661774100480000000000000000000),false,MergedCutProfiles.Batch696.profile27862,(fun _ => MergedCutProfiles.Batch696.profile27862)⟩
theorem profilesValid4977 : retention4977.ProfilesValid := by
  exact MergedCutProfiles.Batch696.valid27862
theorem numericValid4977 : retention4977.NumericValid := by decide +kernel
def certificate4977 : RatCutBinCertificate := ⟨⟨retention4977,(1893292060239611651/1000000000000000000),(59865971199444307/500000000000000000),(13103032017811620311/1000000000000000000),(12570243598073477431933/500000000000000000),(235037278419460673/100000000000000000)⟩,(499966652841521559/500000000000000000),(418522749212928031/500000000000000000),(703174206917269/50000000000000000),(6860085685522769/1000000000000000000)⟩
theorem valid4977 : certificate4977.Valid := by decide +kernel
theorem sound4977 : certificate4977.Sound := rat_cut_bin_certificate_sound certificate4977 profilesValid4977 numericValid4977 valid4977

def retention4978 : RatCutRetentionCertificate := ⟨(49/1000),(1/20),(382227033001833648/190775530142471967995),(438256215155646993/500000000000000000),(73/20),(281476517014477261054266679744434476013/116868324041505864800000000000000000000),false,MergedCutProfiles.Batch696.profile27863,(fun _ => MergedCutProfiles.Batch696.profile27863)⟩
theorem profilesValid4978 : retention4978.ProfilesValid := by
  exact MergedCutProfiles.Batch696.valid27863
theorem numericValid4978 : retention4978.NumericValid := by decide +kernel
def certificate4978 : RatCutBinCertificate := ⟨⟨retention4978,(1893292060239611651/1000000000000000000),(59865971199444307/500000000000000000),(13103032017811620311/1000000000000000000),(12570243598073477431933/500000000000000000),(2345346290457700011/1000000000000000000)⟩,(499966652841521559/500000000000000000),(20086177165300259/25000000000000000),(4144675932098483/200000000000000000),(2217600835624313/200000000000000000)⟩
theorem valid4978 : certificate4978.Valid := by decide +kernel
theorem sound4978 : certificate4978.Sound := rat_cut_bin_certificate_sound certificate4978 profilesValid4978 numericValid4978 valid4978

def retention4979 : RatCutRetentionCertificate := ⟨(49/1000),(1/20),(4508396431655943592/190775530142471967995),(23889189562614603/6250000000000000),(31/20),(33965624781581541250571076564285042791/15289081320073345920000000000000000000),false,MergedCutProfiles.Batch696.profile27864,(fun _ => MergedCutProfiles.Batch696.profile27864)⟩
theorem profilesValid4979 : retention4979.ProfilesValid := by
  exact MergedCutProfiles.Batch696.valid27864
theorem numericValid4979 : retention4979.NumericValid := by decide +kernel
def certificate4979 : RatCutBinCertificate := ⟨⟨retention4979,(1893292060239611651/1000000000000000000),(59865971199444307/500000000000000000),(13103032017811620311/1000000000000000000),(12570243598073477431933/500000000000000000),(2194745246144295899/1000000000000000000)⟩,(499966652841521559/500000000000000000),(363101229790844629/500000000000000000),(41466177823929277/1000000000000000000),(47385257286498893/1000000000000000000)⟩
theorem valid4979 : certificate4979.Valid := by decide +kernel
theorem sound4979 : certificate4979.Sound := rat_cut_bin_certificate_sound certificate4979 profilesValid4979 numericValid4979 valid4979

def certificates : List RatCutBinCertificate := [certificate4968,certificate4969,certificate4970,certificate4971,certificate4972,certificate4973,certificate4974,certificate4975,certificate4976,certificate4977,certificate4978,certificate4979]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4968,List.forall_mem_cons.mpr ⟨sound4969,List.forall_mem_cons.mpr ⟨sound4970,List.forall_mem_cons.mpr ⟨sound4971,List.forall_mem_cons.mpr ⟨sound4972,List.forall_mem_cons.mpr ⟨sound4973,List.forall_mem_cons.mpr ⟨sound4974,List.forall_mem_cons.mpr ⟨sound4975,List.forall_mem_cons.mpr ⟨sound4976,List.forall_mem_cons.mpr ⟨sound4977,List.forall_mem_cons.mpr ⟨sound4978,List.forall_mem_cons.mpr ⟨sound4979,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch414
