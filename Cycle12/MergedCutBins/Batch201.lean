import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch373
import Cycle12.MergedCutProfiles.Batch374
import Cycle12.MergedCutProfiles.Batch375
import Cycle12.MergedCutProfiles.Batch376

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch201

def retention2412 : RatCutRetentionCertificate := ⟨(49/1000),(1/20),(13318120815016637602/38155106028494393599),(2993897191497295767/1000000000000000000),(13/10),(1660737878920666006443/1280000000000000000000),true,MergedCutProfiles.Batch373.profile14949,![MergedCutProfiles.Batch373.profile14949,MergedCutProfiles.Batch374.profile14998,MergedCutProfiles.Batch374.profile14999,MergedCutProfiles.Batch375.profile15000,MergedCutProfiles.Batch375.profile15001,MergedCutProfiles.Batch375.profile15002,MergedCutProfiles.Batch375.profile15003,MergedCutProfiles.Batch375.profile15004,MergedCutProfiles.Batch375.profile15005,MergedCutProfiles.Batch375.profile15006,MergedCutProfiles.Batch375.profile15007,MergedCutProfiles.Batch375.profile15008,MergedCutProfiles.Batch375.profile15009,MergedCutProfiles.Batch375.profile15010,MergedCutProfiles.Batch375.profile15011,MergedCutProfiles.Batch375.profile15012]⟩
theorem profilesValid2412 : retention2412.ProfilesValid := by
  change ∀ j : Fin 16, (retention2412.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch373.valid14949
  · exact MergedCutProfiles.Batch374.valid14998
  · exact MergedCutProfiles.Batch374.valid14999
  · exact MergedCutProfiles.Batch375.valid15000
  · exact MergedCutProfiles.Batch375.valid15001
  · exact MergedCutProfiles.Batch375.valid15002
  · exact MergedCutProfiles.Batch375.valid15003
  · exact MergedCutProfiles.Batch375.valid15004
  · exact MergedCutProfiles.Batch375.valid15005
  · exact MergedCutProfiles.Batch375.valid15006
  · exact MergedCutProfiles.Batch375.valid15007
  · exact MergedCutProfiles.Batch375.valid15008
  · exact MergedCutProfiles.Batch375.valid15009
  · exact MergedCutProfiles.Batch375.valid15010
  · exact MergedCutProfiles.Batch375.valid15011
  · exact MergedCutProfiles.Batch375.valid15012
theorem numericValid2412 : retention2412.NumericValid := by decide +kernel
def certificate2412 : RatCutBinCertificate := ⟨⟨retention2412,(428977783796116503/200000000000000000),(59865971199444307/500000000000000000),(13102353185538516663/1000000000000000000),(100556738944896641207/200000000000000000),(1271969353829626383/1000000000000000000)⟩,(996220105590945219/1000000000000000000),(51282440611296863/125000000000000000),(224212478486276311/1000000000000000000),(174564315345084959/1000000000000000000)⟩
theorem valid2412 : certificate2412.Valid := by decide +kernel
theorem sound2412 : certificate2412.Sound := rat_cut_bin_certificate_sound certificate2412 profilesValid2412 numericValid2412 valid2412

def retention2413 : RatCutRetentionCertificate := ⟨(49/1000),(1/20),(18494742330859684070/38155106028494393599),(6659060407508318801/500000000000000000),(21/20),(5485393300842275197385066926257373279119/5327248326006655040800000000000000000000),false,MergedCutProfiles.Batch375.profile15013,(fun _ => MergedCutProfiles.Batch375.profile15013)⟩
theorem profilesValid2413 : retention2413.ProfilesValid := by
  exact MergedCutProfiles.Batch375.valid15013
theorem numericValid2413 : retention2413.NumericValid := by decide +kernel
def certificate2413 : RatCutBinCertificate := ⟨⟨retention2413,(428977783796116503/200000000000000000),(59865971199444307/500000000000000000),(13102353185538516663/1000000000000000000),(100556738944896641207/200000000000000000),(1009105253984254801/1000000000000000000)⟩,(996220105590945219/1000000000000000000),(439778608786291637/1000000000000000000),(7957999285150851/40000000000000000),(89101592932015503/500000000000000000)⟩
theorem valid2413 : certificate2413.Valid := by decide +kernel
theorem sound2413 : certificate2413.Sound := rat_cut_bin_certificate_sound certificate2413 profilesValid2413 numericValid2413 valid2413

def retention2414 : RatCutRetentionCertificate := ⟨(49/1000),(1/20),(18866486651709963721/38155106028494393599),(1849474233085968407/100000000000000000),1,(73888408761076761633462773883583752831/73978969323438736280000000000000000000),false,MergedCutProfiles.Batch375.profile15014,(fun _ => MergedCutProfiles.Batch375.profile15014)⟩
theorem profilesValid2414 : retention2414.ProfilesValid := by
  exact MergedCutProfiles.Batch375.valid15014
theorem numericValid2414 : retention2414.NumericValid := by decide +kernel
def certificate2414 : RatCutBinCertificate := ⟨⟨retention2414,(428977783796116503/200000000000000000),(59865971199444307/500000000000000000),(13102353185538516663/1000000000000000000),(100556738944896641207/200000000000000000),(979175181392525467/1000000000000000000)⟩,(996220105590945219/1000000000000000000),(44675097953807449/100000000000000000),(193277351794556279/1000000000000000000),(44759147031596517/250000000000000000)⟩
theorem valid2414 : certificate2414.Valid := by decide +kernel
theorem sound2414 : certificate2414.Sound := rat_cut_bin_certificate_sound certificate2414 profilesValid2414 numericValid2414 valid2414

def retention2415 : RatCutRetentionCertificate := ⟨(49/1000),(1/20),(19055151518227063359/38155106028494393599),(18866486651709963721/1000000000000000000),1,(583329061046070915841860267245634081/589577707865936366281250000000000000),false,MergedCutProfiles.Batch375.profile15015,(fun _ => MergedCutProfiles.Batch375.profile15015)⟩
theorem profilesValid2415 : retention2415.ProfilesValid := by
  exact MergedCutProfiles.Batch375.valid15015
theorem numericValid2415 : retention2415.NumericValid := by decide +kernel
def certificate2415 : RatCutBinCertificate := ⟨⟨retention2415,(428977783796116503/200000000000000000),(59865971199444307/500000000000000000),(13102353185538516663/1000000000000000000),(100556738944896641207/200000000000000000),(969800812954701809/1000000000000000000)⟩,(996220105590945219/1000000000000000000),(28171139765042327/62500000000000000),(95041191151485253/500000000000000000),(34929424142372517/200000000000000000)⟩
theorem valid2415 : certificate2415.Valid := by decide +kernel
theorem sound2415 : certificate2415.Sound := rat_cut_bin_certificate_sound certificate2415 profilesValid2415 numericValid2415 valid2415

def retention2416 : RatCutRetentionCertificate := ⟨(49/1000),(1/20),(1/2),(19055151518227063359/1000000000000000000),1,(784745281663038746636713715848076619/793964646592794306625000000000000000),false,MergedCutProfiles.Batch375.profile15016,(fun _ => MergedCutProfiles.Batch375.profile15016)⟩
theorem profilesValid2416 : retention2416.ProfilesValid := by
  exact MergedCutProfiles.Batch375.valid15016
theorem numericValid2416 : retention2416.NumericValid := by decide +kernel
def certificate2416 : RatCutBinCertificate := ⟨⟨retention2416,(428977783796116503/200000000000000000),(59865971199444307/500000000000000000),(13102353185538516663/1000000000000000000),(100556738944896641207/200000000000000000),(19375750404580591/20000000000000000)⟩,(996220105590945219/1000000000000000000),(112761595806324431/250000000000000000),(37967387542786787/200000000000000000),(21791594022183721/125000000000000000)⟩
theorem valid2416 : certificate2416.Valid := by decide +kernel
theorem sound2416 : certificate2416.Sound := rat_cut_bin_certificate_sound certificate2416 profilesValid2416 numericValid2416 valid2416

def retention2417 : RatCutRetentionCertificate := ⟨(49/1000),(1/20),(16862789444787871397/38155106028494393599),(5477901008702628699/1000000000000000000),(21/20),(1057771693107367355118089952203333542191/973849068213800657600000000000000000000),false,MergedCutProfiles.Batch375.profile15017,(fun _ => MergedCutProfiles.Batch375.profile15017)⟩
theorem profilesValid2417 : retention2417.ProfilesValid := by
  exact MergedCutProfiles.Batch375.valid15017
theorem numericValid2417 : retention2417.NumericValid := by decide +kernel
def certificate2417 : RatCutBinCertificate := ⟨⟨retention2417,(484629637396116503/200000000000000000),(59865971199444307/500000000000000000),(13102353185538516663/1000000000000000000),(100556738944896641207/200000000000000000),(212584974709619347/200000000000000000)⟩,(995729464422327871/1000000000000000000),(225897801031615953/1000000000000000000),(218942069313391513/500000000000000000),(375200525427315321/1000000000000000000)⟩
theorem valid2417 : certificate2417.Valid := by decide +kernel
theorem sound2417 : certificate2417.Sound := rat_cut_bin_certificate_sound certificate2417 profilesValid2417 numericValid2417 valid2417

def retention2418 : RatCutRetentionCertificate := ⟨(49/1000),(1/20),(18813280420031835791/38155106028494393599),(16862789444787871397/1000000000000000000),1,(67461133907618190857295629527968266067/67451157779151485588000000000000000000),false,MergedCutProfiles.Batch375.profile15018,(fun _ => MergedCutProfiles.Batch375.profile15018)⟩
theorem profilesValid2418 : retention2418.ProfilesValid := by
  exact MergedCutProfiles.Batch375.valid15018
theorem numericValid2418 : retention2418.NumericValid := by decide +kernel
def certificate2418 : RatCutBinCertificate := ⟨⟨retention2418,(484629637396116503/200000000000000000),(59865971199444307/500000000000000000),(13102353185538516663/1000000000000000000),(100556738944896641207/200000000000000000),(244501093154921137/250000000000000000)⟩,(995729464422327871/1000000000000000000),(24551259515656147/100000000000000000),(409592624107955107/1000000000000000000),(47119982574250297/125000000000000000)⟩
theorem valid2418 : certificate2418.Valid := by decide +kernel
theorem sound2418 : certificate2418.Sound := rat_cut_bin_certificate_sound certificate2418 profilesValid2418 numericValid2418 valid2418

def retention2419 : RatCutRetentionCertificate := ⟨(49/1000),(1/20),(19001413224232154149/38155106028494393599),(18813280420031835791/1000000000000000000),1,(466621367885910344235257659582784119/470332010500795894775000000000000000),false,MergedCutProfiles.Batch375.profile15019,(fun _ => MergedCutProfiles.Batch375.profile15019)⟩
theorem profilesValid2419 : retention2419.ProfilesValid := by
  exact MergedCutProfiles.Batch375.valid15019
theorem numericValid2419 : retention2419.NumericValid := by decide +kernel
def certificate2419 : RatCutBinCertificate := ⟨⟨retention2419,(484629637396116503/200000000000000000),(59865971199444307/500000000000000000),(13102353185538516663/1000000000000000000),(100556738944896641207/200000000000000000),(242491773089893581/250000000000000000)⟩,(995729464422327871/1000000000000000000),(247546946167233453/1000000000000000000),(5084359664087547/12500000000000000),(46693076911131171/125000000000000000)⟩
theorem valid2419 : certificate2419.Valid := by decide +kernel
theorem sound2419 : certificate2419.Sound := rat_cut_bin_certificate_sound certificate2419 profilesValid2419 numericValid2419 valid2419

def retention2420 : RatCutRetentionCertificate := ⟨(49/1000),(1/20),(1/2),(19001413224232154149/1000000000000000000),1,(9169953731901138233658305938829937/9278033800894606518066406250000000),false,MergedCutProfiles.Batch375.profile15016,(fun _ => MergedCutProfiles.Batch375.profile15016)⟩
theorem profilesValid2420 : retention2420.ProfilesValid := by
  exact MergedCutProfiles.Batch375.valid15016
theorem numericValid2420 : retention2420.NumericValid := by decide +kernel
def certificate2420 : RatCutBinCertificate := ⟨⟨retention2420,(484629637396116503/200000000000000000),(59865971199444307/500000000000000000),(13102353185538516663/1000000000000000000),(100556738944896641207/200000000000000000),(966207479004357461/1000000000000000000)⟩,(995729464422327871/1000000000000000000),(248510176969185549/1000000000000000000),(40540801562958469/100000000000000000),(92780146964650199/250000000000000000)⟩
theorem valid2420 : certificate2420.Valid := by decide +kernel
theorem sound2420 : certificate2420.Sound := rat_cut_bin_certificate_sound certificate2420 profilesValid2420 numericValid2420 valid2420

def retention2421 : RatCutRetentionCertificate := ⟨(1/20),(51/1000),(105508628653923272/4557924207760763037),(417855955065042661/500000000000000000),(31/10),(87238160295595715507/40000000000000000000),true,MergedCutProfiles.Batch375.profile15020,![MergedCutProfiles.Batch375.profile15020,MergedCutProfiles.Batch375.profile15021,MergedCutProfiles.Batch375.profile15022,MergedCutProfiles.Batch375.profile15023,MergedCutProfiles.Batch375.profile15024,MergedCutProfiles.Batch375.profile15025,MergedCutProfiles.Batch375.profile15026,MergedCutProfiles.Batch375.profile15027,MergedCutProfiles.Batch375.profile15028,MergedCutProfiles.Batch375.profile15029,MergedCutProfiles.Batch375.profile15030,MergedCutProfiles.Batch375.profile15031,MergedCutProfiles.Batch375.profile15032,MergedCutProfiles.Batch375.profile15033,MergedCutProfiles.Batch375.profile15034,MergedCutProfiles.Batch375.profile15035]⟩
theorem profilesValid2421 : retention2421.ProfilesValid := by
  change ∀ j : Fin 16, (retention2421.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch375.valid15020
  · exact MergedCutProfiles.Batch375.valid15021
  · exact MergedCutProfiles.Batch375.valid15022
  · exact MergedCutProfiles.Batch375.valid15023
  · exact MergedCutProfiles.Batch375.valid15024
  · exact MergedCutProfiles.Batch375.valid15025
  · exact MergedCutProfiles.Batch375.valid15026
  · exact MergedCutProfiles.Batch375.valid15027
  · exact MergedCutProfiles.Batch375.valid15028
  · exact MergedCutProfiles.Batch375.valid15029
  · exact MergedCutProfiles.Batch375.valid15030
  · exact MergedCutProfiles.Batch375.valid15031
  · exact MergedCutProfiles.Batch375.valid15032
  · exact MergedCutProfiles.Batch375.valid15033
  · exact MergedCutProfiles.Batch375.valid15034
  · exact MergedCutProfiles.Batch375.valid15035
theorem numericValid2421 : retention2421.NumericValid := by decide +kernel
def certificate2421 : RatCutBinCertificate := ⟨⟨retention2421,(431113381787465781/200000000000000000),(31307344283847009/250000000000000000),(13322007802705716331/1000000000000000000),(244282304990708490629/500000000000000000),(1059066658497655487/500000000000000000)⟩,(249028534861385659/250000000000000000),(22753371504680611/62500000000000000),(268082685506732447/1000000000000000000),(28855980111329269/200000000000000000)⟩
theorem valid2421 : certificate2421.Valid := by decide +kernel
theorem sound2421 : certificate2421.Sound := rat_cut_bin_certificate_sound certificate2421 profilesValid2421 numericValid2421 valid2421

def retention2422 : RatCutRetentionCertificate := ⟨(1/20),(51/1000),(941701098313979371/36463393662086104296),(13188578581740409/15625000000000000),(31/10),(173911126303286963939/80000000000000000000),true,MergedCutProfiles.Batch375.profile15036,![MergedCutProfiles.Batch375.profile15036,MergedCutProfiles.Batch375.profile15037,MergedCutProfiles.Batch375.profile15038,MergedCutProfiles.Batch375.profile15039,MergedCutProfiles.Batch376.profile15040,MergedCutProfiles.Batch376.profile15041,MergedCutProfiles.Batch376.profile15042,MergedCutProfiles.Batch376.profile15043,MergedCutProfiles.Batch375.profile15029,MergedCutProfiles.Batch376.profile15044,MergedCutProfiles.Batch376.profile15045,MergedCutProfiles.Batch376.profile15046,MergedCutProfiles.Batch376.profile15047,MergedCutProfiles.Batch376.profile15048,MergedCutProfiles.Batch376.profile15049,MergedCutProfiles.Batch376.profile15050]⟩
theorem profilesValid2422 : retention2422.ProfilesValid := by
  change ∀ j : Fin 16, (retention2422.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch375.valid15036
  · exact MergedCutProfiles.Batch375.valid15037
  · exact MergedCutProfiles.Batch375.valid15038
  · exact MergedCutProfiles.Batch375.valid15039
  · exact MergedCutProfiles.Batch376.valid15040
  · exact MergedCutProfiles.Batch376.valid15041
  · exact MergedCutProfiles.Batch376.valid15042
  · exact MergedCutProfiles.Batch376.valid15043
  · exact MergedCutProfiles.Batch375.valid15029
  · exact MergedCutProfiles.Batch376.valid15044
  · exact MergedCutProfiles.Batch376.valid15045
  · exact MergedCutProfiles.Batch376.valid15046
  · exact MergedCutProfiles.Batch376.valid15047
  · exact MergedCutProfiles.Batch376.valid15048
  · exact MergedCutProfiles.Batch376.valid15049
  · exact MergedCutProfiles.Batch376.valid15050
theorem numericValid2422 : retention2422.NumericValid := by decide +kernel
def certificate2422 : RatCutBinCertificate := ⟨⟨retention2422,(431113381787465781/200000000000000000),(31307344283847009/250000000000000000),(13322007802705716331/1000000000000000000),(244282304990708490629/500000000000000000),(131941778120560471/62500000000000000)⟩,(249028534861385659/250000000000000000),(363613503157363223/1000000000000000000),(67131986818745293/250000000000000000),(5777449051606389/40000000000000000)⟩
theorem valid2422 : certificate2422.Valid := by decide +kernel
theorem sound2422 : certificate2422.Sound := rat_cut_bin_certificate_sound certificate2422 profilesValid2422 numericValid2422 valid2422

def retention2423 : RatCutRetentionCertificate := ⟨(1/20),(51/1000),(124137595750000000/4557924207760763037),(941701098313979371/1000000000000000000),(14/5),(2760255288571283997647/1280000000000000000000),true,MergedCutProfiles.Batch376.profile15051,![MergedCutProfiles.Batch376.profile15051,MergedCutProfiles.Batch376.profile15052,MergedCutProfiles.Batch376.profile15053,MergedCutProfiles.Batch376.profile15054,MergedCutProfiles.Batch376.profile15055,MergedCutProfiles.Batch375.profile15026,MergedCutProfiles.Batch376.profile15056,MergedCutProfiles.Batch376.profile15057,MergedCutProfiles.Batch376.profile15058,MergedCutProfiles.Batch376.profile15059,MergedCutProfiles.Batch375.profile15032,MergedCutProfiles.Batch376.profile15060,MergedCutProfiles.Batch376.profile15061,MergedCutProfiles.Batch376.profile15062,MergedCutProfiles.Batch376.profile15063,MergedCutProfiles.Batch376.profile15064]⟩
theorem profilesValid2423 : retention2423.ProfilesValid := by
  change ∀ j : Fin 16, (retention2423.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch376.valid15051
  · exact MergedCutProfiles.Batch376.valid15052
  · exact MergedCutProfiles.Batch376.valid15053
  · exact MergedCutProfiles.Batch376.valid15054
  · exact MergedCutProfiles.Batch376.valid15055
  · exact MergedCutProfiles.Batch375.valid15026
  · exact MergedCutProfiles.Batch376.valid15056
  · exact MergedCutProfiles.Batch376.valid15057
  · exact MergedCutProfiles.Batch376.valid15058
  · exact MergedCutProfiles.Batch376.valid15059
  · exact MergedCutProfiles.Batch375.valid15032
  · exact MergedCutProfiles.Batch376.valid15060
  · exact MergedCutProfiles.Batch376.valid15061
  · exact MergedCutProfiles.Batch376.valid15062
  · exact MergedCutProfiles.Batch376.valid15063
  · exact MergedCutProfiles.Batch376.valid15064
theorem numericValid2423 : retention2423.NumericValid := by decide +kernel
def certificate2423 : RatCutBinCertificate := ⟨⟨retention2423,(431113381787465781/200000000000000000),(31307344283847009/250000000000000000),(13322007802705716331/1000000000000000000),(244282304990708490629/500000000000000000),(2099708273500783037/1000000000000000000)⟩,(249028534861385659/250000000000000000),(87072536337620613/250000000000000000),(56871076566803339/200000000000000000),(165262709972892569/1000000000000000000)⟩
theorem valid2423 : certificate2423.Valid := by decide +kernel
theorem sound2423 : certificate2423.Sound := rat_cut_bin_certificate_sound certificate2423 profilesValid2423 numericValid2423 valid2423

def certificates : List RatCutBinCertificate := [certificate2412,certificate2413,certificate2414,certificate2415,certificate2416,certificate2417,certificate2418,certificate2419,certificate2420,certificate2421,certificate2422,certificate2423]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2412,List.forall_mem_cons.mpr ⟨sound2413,List.forall_mem_cons.mpr ⟨sound2414,List.forall_mem_cons.mpr ⟨sound2415,List.forall_mem_cons.mpr ⟨sound2416,List.forall_mem_cons.mpr ⟨sound2417,List.forall_mem_cons.mpr ⟨sound2418,List.forall_mem_cons.mpr ⟨sound2419,List.forall_mem_cons.mpr ⟨sound2420,List.forall_mem_cons.mpr ⟨sound2421,List.forall_mem_cons.mpr ⟨sound2422,List.forall_mem_cons.mpr ⟨sound2423,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch201
