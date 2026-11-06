import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch032
import Cycle12.MergedCutProfiles.Batch033
import Cycle12.MergedCutProfiles.Batch034
import Cycle12.MergedCutProfiles.Batch035
import Cycle12.MergedCutProfiles.Batch036
import Cycle12.MergedCutProfiles.Batch325
import Cycle12.MergedCutProfiles.Batch326
import Cycle12.MergedCutProfiles.Batch327

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch175

def retention2100 : RatCutRetentionCertificate := ⟨(3/125),(1/40),(1013779347764838937/174258419415322824906),(330441337549969361/500000000000000000),4,(292864078774874257401/128000000000000000000),true,MergedCutProfiles.Batch325.profile13035,![MergedCutProfiles.Batch325.profile13035,MergedCutProfiles.Batch325.profile13036,MergedCutProfiles.Batch325.profile13037,MergedCutProfiles.Batch325.profile13038,MergedCutProfiles.Batch325.profile13039,MergedCutProfiles.Batch326.profile13040,MergedCutProfiles.Batch326.profile13041,MergedCutProfiles.Batch326.profile13042,MergedCutProfiles.Batch325.profile13033,MergedCutProfiles.Batch326.profile13043,MergedCutProfiles.Batch032.profile1307,MergedCutProfiles.Batch326.profile13044,MergedCutProfiles.Batch033.profile1335,MergedCutProfiles.Batch326.profile13045,MergedCutProfiles.Batch032.profile1310,MergedCutProfiles.Batch326.profile13046]⟩
theorem profilesValid2100 : retention2100.ProfilesValid := by
  change ∀ j : Fin 16, (retention2100.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch325.valid13035
  · exact MergedCutProfiles.Batch325.valid13036
  · exact MergedCutProfiles.Batch325.valid13037
  · exact MergedCutProfiles.Batch325.valid13038
  · exact MergedCutProfiles.Batch325.valid13039
  · exact MergedCutProfiles.Batch326.valid13040
  · exact MergedCutProfiles.Batch326.valid13041
  · exact MergedCutProfiles.Batch326.valid13042
  · exact MergedCutProfiles.Batch325.valid13033
  · exact MergedCutProfiles.Batch326.valid13043
  · exact MergedCutProfiles.Batch032.valid1307
  · exact MergedCutProfiles.Batch326.valid13044
  · exact MergedCutProfiles.Batch033.valid1335
  · exact MergedCutProfiles.Batch326.valid13045
  · exact MergedCutProfiles.Batch032.valid1310
  · exact MergedCutProfiles.Batch326.valid13046
theorem numericValid2100 : retention2100.NumericValid := by decide +kernel
def certificate2100 : RatCutBinCertificate := ⟨⟨retention2100,(48332530941006109/25000000000000000),(5353370290855499/200000000000000000),(4507535409253092731/500000000000000000),(315733330643074098997/200000000000000000),(2265039633759088423/1000000000000000000)⟩,(998805417189520419/1000000000000000000),(246288277344019977/500000000000000000),(15862726629741657/100000000000000000),(73874423526438669/1000000000000000000)⟩
theorem valid2100 : certificate2100.Valid := by decide +kernel
theorem sound2100 : certificate2100.Sound := rat_cut_bin_certificate_sound certificate2100 profilesValid2100 numericValid2100 valid2100

def retention2101 : RatCutRetentionCertificate := ⟨(3/125),(1/40),(197003789000000000/29043069902553804151),(1013779347764838937/1000000000000000000),(57/20),(2909544993876394455953/1280000000000000000000),true,MergedCutProfiles.Batch326.profile13047,![MergedCutProfiles.Batch326.profile13047,MergedCutProfiles.Batch326.profile13048,MergedCutProfiles.Batch326.profile13049,MergedCutProfiles.Batch326.profile13050,MergedCutProfiles.Batch325.profile13029,MergedCutProfiles.Batch326.profile13041,MergedCutProfiles.Batch032.profile1305,MergedCutProfiles.Batch326.profile13051,MergedCutProfiles.Batch033.profile1320,MergedCutProfiles.Batch326.profile13052,MergedCutProfiles.Batch033.profile1357,MergedCutProfiles.Batch326.profile13045,MergedCutProfiles.Batch033.profile1345,MergedCutProfiles.Batch326.profile13053,MergedCutProfiles.Batch033.profile1346,MergedCutProfiles.Batch326.profile13054]⟩
theorem profilesValid2101 : retention2101.ProfilesValid := by
  change ∀ j : Fin 16, (retention2101.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch326.valid13047
  · exact MergedCutProfiles.Batch326.valid13048
  · exact MergedCutProfiles.Batch326.valid13049
  · exact MergedCutProfiles.Batch326.valid13050
  · exact MergedCutProfiles.Batch325.valid13029
  · exact MergedCutProfiles.Batch326.valid13041
  · exact MergedCutProfiles.Batch032.valid1305
  · exact MergedCutProfiles.Batch326.valid13051
  · exact MergedCutProfiles.Batch033.valid1320
  · exact MergedCutProfiles.Batch326.valid13052
  · exact MergedCutProfiles.Batch033.valid1357
  · exact MergedCutProfiles.Batch326.valid13045
  · exact MergedCutProfiles.Batch033.valid1345
  · exact MergedCutProfiles.Batch326.valid13053
  · exact MergedCutProfiles.Batch033.valid1346
  · exact MergedCutProfiles.Batch326.valid13054
theorem numericValid2101 : retention2101.NumericValid := by decide +kernel
def certificate2101 : RatCutBinCertificate := ⟨⟨retention2101,(48332530941006109/25000000000000000),(5353370290855499/200000000000000000),(4507535409253092731/500000000000000000),(315733330643074098997/200000000000000000),(451344467190164071/200000000000000000)⟩,(998805417189520419/1000000000000000000),(391120364354616057/1000000000000000000),(120858788219387967/500000000000000000),(37505576582811589/250000000000000000)⟩
theorem valid2101 : certificate2101.Valid := by decide +kernel
theorem sound2101 : certificate2101.Sound := rat_cut_bin_certificate_sound certificate2101 profilesValid2101 numericValid2101 valid2101

def retention2102 : RatCutRetentionCertificate := ⟨(3/125),(1/40),(1555115007060952277/174258419415322824906),(591011367/500000000),(5/2),(17956986063623374003/8000000000000000000),true,MergedCutProfiles.Batch326.profile13055,![MergedCutProfiles.Batch326.profile13055,MergedCutProfiles.Batch326.profile13056,MergedCutProfiles.Batch325.profile13028,MergedCutProfiles.Batch326.profile13057,MergedCutProfiles.Batch033.profile1355,MergedCutProfiles.Batch326.profile13058,MergedCutProfiles.Batch034.profile1367,MergedCutProfiles.Batch033.profile1321,MergedCutProfiles.Batch033.profile1322,MergedCutProfiles.Batch033.profile1345,MergedCutProfiles.Batch326.profile13059,MergedCutProfiles.Batch326.profile13060,MergedCutProfiles.Batch326.profile13061,MergedCutProfiles.Batch034.profile1368,MergedCutProfiles.Batch034.profile1360,MergedCutProfiles.Batch326.profile13062]⟩
theorem profilesValid2102 : retention2102.ProfilesValid := by
  change ∀ j : Fin 16, (retention2102.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch326.valid13055
  · exact MergedCutProfiles.Batch326.valid13056
  · exact MergedCutProfiles.Batch325.valid13028
  · exact MergedCutProfiles.Batch326.valid13057
  · exact MergedCutProfiles.Batch033.valid1355
  · exact MergedCutProfiles.Batch326.valid13058
  · exact MergedCutProfiles.Batch034.valid1367
  · exact MergedCutProfiles.Batch033.valid1321
  · exact MergedCutProfiles.Batch033.valid1322
  · exact MergedCutProfiles.Batch033.valid1345
  · exact MergedCutProfiles.Batch326.valid13059
  · exact MergedCutProfiles.Batch326.valid13060
  · exact MergedCutProfiles.Batch326.valid13061
  · exact MergedCutProfiles.Batch034.valid1368
  · exact MergedCutProfiles.Batch034.valid1360
  · exact MergedCutProfiles.Batch326.valid13062
theorem numericValid2102 : retention2102.NumericValid := by decide +kernel
def certificate2102 : RatCutBinCertificate := ⟨⟨retention2102,(48332530941006109/25000000000000000),(5353370290855499/200000000000000000),(4507535409253092731/500000000000000000),(315733330643074098997/200000000000000000),(2230272654112697189/1000000000000000000)⟩,(998805417189520419/1000000000000000000),(183952326150129583/500000000000000000),(8256638388221159/31250000000000000),(45200528645643921/250000000000000000)⟩
theorem valid2102 : certificate2102.Valid := by decide +kernel
theorem sound2102 : certificate2102.Sound := rat_cut_bin_certificate_sound certificate2102 profilesValid2102 numericValid2102 valid2102

def retention2103 : RatCutRetentionCertificate := ⟨(3/125),(1/40),(14736453812777908697/174258419415322824906),(1555115007060952277/1000000000000000000),(21/10),(1206555868230759539050112932776681028271/622046002824380910800000000000000000000),false,MergedCutProfiles.Batch326.profile13063,(fun _ => MergedCutProfiles.Batch326.profile13063)⟩
theorem profilesValid2103 : retention2103.ProfilesValid := by
  exact MergedCutProfiles.Batch326.valid13063
theorem numericValid2103 : retention2103.NumericValid := by decide +kernel
def certificate2103 : RatCutBinCertificate := ⟨⟨retention2103,(48332530941006109/25000000000000000),(5353370290855499/200000000000000000),(4507535409253092731/500000000000000000),(315733330643074098997/200000000000000000),(1927602474485360127/1000000000000000000)⟩,(998805417189520419/1000000000000000000),(379082981931326679/1000000000000000000),(126601979773109527/500000000000000000),(181179350702896769/1000000000000000000)⟩
theorem valid2103 : certificate2103.Valid := by decide +kernel
theorem sound2103 : certificate2103.Sound := rat_cut_bin_certificate_sound certificate2103 profilesValid2103 numericValid2103 valid2103

def retention2104 : RatCutRetentionCertificate := ⟨(3/125),(1/40),(32000000000000000000/87129209707661412453),(14736453812777908697/1000000000000000000),1,(22920391647680349606861527875728659/18420567265972385871250000000000000),false,MergedCutProfiles.Batch326.profile13064,(fun _ => MergedCutProfiles.Batch326.profile13064)⟩
theorem profilesValid2104 : retention2104.ProfilesValid := by
  exact MergedCutProfiles.Batch326.valid13064
theorem numericValid2104 : retention2104.NumericValid := by decide +kernel
def certificate2104 : RatCutBinCertificate := ⟨⟨retention2104,(48332530941006109/25000000000000000),(5353370290855499/200000000000000000),(4507535409253092731/500000000000000000),(315733330643074098997/200000000000000000),(30963560049429393/25000000000000000)⟩,(998805417189520419/1000000000000000000),(384503501472390903/1000000000000000000),(61996249195138747/250000000000000000),(35372170484122509/125000000000000000)⟩
theorem valid2104 : certificate2104.Valid := by decide +kernel
theorem sound2104 : certificate2104.Sound := rat_cut_bin_certificate_sound certificate2104 profilesValid2104 numericValid2104 valid2104

def retention2105 : RatCutRetentionCertificate := ⟨(3/125),(1/40),(1/2),64,1,(255373261473046173696668873617783571559/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch034.profile1386,(fun _ => MergedCutProfiles.Batch034.profile1386)⟩
theorem profilesValid2105 : retention2105.ProfilesValid := by
  exact MergedCutProfiles.Batch034.valid1386
theorem numericValid2105 : retention2105.NumericValid := by decide +kernel
def certificate2105 : RatCutBinCertificate := ⟨⟨retention2105,(48332530941006109/25000000000000000),(5353370290855499/200000000000000000),(4507535409253092731/500000000000000000),(315733330643074098997/200000000000000000),(991811592508094159/1000000000000000000)⟩,(998805417189520419/1000000000000000000),(228426540722872943/500000000000000000),(92625497931999051/500000000000000000),(90356126540307323/500000000000000000)⟩
theorem valid2105 : certificate2105.Valid := by decide +kernel
theorem sound2105 : certificate2105.Sound := rat_cut_bin_certificate_sound certificate2105 profilesValid2105 numericValid2105 valid2105

def retention2106 : RatCutRetentionCertificate := ⟨(3/125),(1/40),(32000000000000000000/87129209707661412453),(5264479815843020311/1000000000000000000),(11/10),(2622433035009511035999755131154098275439/2105791926337208124400000000000000000000),false,MergedCutProfiles.Batch326.profile13064,(fun _ => MergedCutProfiles.Batch326.profile13064)⟩
theorem profilesValid2106 : retention2106.ProfilesValid := by
  exact MergedCutProfiles.Batch326.valid13064
theorem numericValid2106 : retention2106.NumericValid := by decide +kernel
def certificate2106 : RatCutBinCertificate := ⟨⟨retention2106,(55841041791006109/25000000000000000),(5353370290855499/200000000000000000),(4507535409253092731/500000000000000000),(315733330643074098997/200000000000000000),(619023865942112687/500000000000000000)⟩,(199723966201528603/200000000000000000),(97922533082037299/500000000000000000),(484514141396699277/1000000000000000000),(455907656960601289/1000000000000000000)⟩
theorem valid2106 : certificate2106.Valid := by decide +kernel
theorem sound2106 : certificate2106.Sound := rat_cut_bin_certificate_sound certificate2106 profilesValid2106 numericValid2106 valid2106

def retention2107 : RatCutRetentionCertificate := ⟨(3/125),(1/40),(1/2),64,1,(255373261473046173696668873617783571559/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch034.profile1386,(fun _ => MergedCutProfiles.Batch034.profile1386)⟩
theorem profilesValid2107 : retention2107.ProfilesValid := by
  exact MergedCutProfiles.Batch034.valid1386
theorem numericValid2107 : retention2107.NumericValid := by decide +kernel
def certificate2107 : RatCutBinCertificate := ⟨⟨retention2107,(55841041791006109/25000000000000000),(5353370290855499/200000000000000000),(4507535409253092731/500000000000000000),(315733330643074098997/200000000000000000),(990919844670031233/1000000000000000000)⟩,(199723966201528603/200000000000000000),(122343669505320981/500000000000000000),(12835968475033289/31250000000000000),(400258229868400553/1000000000000000000)⟩
theorem valid2107 : certificate2107.Valid := by decide +kernel
theorem sound2107 : certificate2107.Sound := rat_cut_bin_certificate_sound certificate2107 profilesValid2107 numericValid2107 valid2107

def retention2108 : RatCutRetentionCertificate := ⟨(1/40),(13/500),(337811165760017031/80159877605752572074),(132461980496036479/200000000000000000),4,(36843175781654408087/16000000000000000000),true,MergedCutProfiles.Batch326.profile13065,![MergedCutProfiles.Batch326.profile13065,MergedCutProfiles.Batch326.profile13066,MergedCutProfiles.Batch326.profile13067,MergedCutProfiles.Batch326.profile13068,MergedCutProfiles.Batch326.profile13069,MergedCutProfiles.Batch326.profile13070,MergedCutProfiles.Batch326.profile13071,MergedCutProfiles.Batch326.profile13072,MergedCutProfiles.Batch326.profile13073,MergedCutProfiles.Batch326.profile13074,MergedCutProfiles.Batch326.profile13075,MergedCutProfiles.Batch326.profile13076,MergedCutProfiles.Batch035.profile1409,MergedCutProfiles.Batch326.profile13077,MergedCutProfiles.Batch035.profile1437,MergedCutProfiles.Batch326.profile13078]⟩
theorem profilesValid2108 : retention2108.ProfilesValid := by
  change ∀ j : Fin 16, (retention2108.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch326.valid13065
  · exact MergedCutProfiles.Batch326.valid13066
  · exact MergedCutProfiles.Batch326.valid13067
  · exact MergedCutProfiles.Batch326.valid13068
  · exact MergedCutProfiles.Batch326.valid13069
  · exact MergedCutProfiles.Batch326.valid13070
  · exact MergedCutProfiles.Batch326.valid13071
  · exact MergedCutProfiles.Batch326.valid13072
  · exact MergedCutProfiles.Batch326.valid13073
  · exact MergedCutProfiles.Batch326.valid13074
  · exact MergedCutProfiles.Batch326.valid13075
  · exact MergedCutProfiles.Batch326.valid13076
  · exact MergedCutProfiles.Batch035.valid1409
  · exact MergedCutProfiles.Batch326.valid13077
  · exact MergedCutProfiles.Batch035.valid1437
  · exact MergedCutProfiles.Batch326.valid13078
theorem numericValid2108 : retention2108.NumericValid := by decide +kernel
def certificate2108 : RatCutBinCertificate := ⟨⟨retention2108,(48534072011850779/25000000000000000),(14531335098101001/500000000000000000),(2284636561984684481/250000000000000000),(18404084515066028601/12500000000000000),(2278002387877553619/1000000000000000000)⟩,(499358340259840289/500000000000000000),(485159008016704149/1000000000000000000),(163935783236332507/1000000000000000000),(76727517873812191/1000000000000000000)⟩
theorem valid2108 : certificate2108.Valid := by decide +kernel
theorem sound2108 : certificate2108.Sound := rat_cut_bin_certificate_sound certificate2108 profilesValid2108 numericValid2108 valid2108

def retention2109 : RatCutRetentionCertificate := ⟨(1/40),(13/500),(291388848500000000/40079938802876286037),(337811165760017031/500000000000000000),4,(58534209128944495643/25600000000000000000),true,MergedCutProfiles.Batch326.profile13079,![MergedCutProfiles.Batch326.profile13079,MergedCutProfiles.Batch327.profile13080,MergedCutProfiles.Batch035.profile1407,MergedCutProfiles.Batch326.profile13071,MergedCutProfiles.Batch327.profile13081,MergedCutProfiles.Batch327.profile13082,MergedCutProfiles.Batch326.profile13076,MergedCutProfiles.Batch327.profile13083,MergedCutProfiles.Batch327.profile13084,MergedCutProfiles.Batch327.profile13085,MergedCutProfiles.Batch034.profile1398,MergedCutProfiles.Batch034.profile1399,MergedCutProfiles.Batch035.profile1424,MergedCutProfiles.Batch327.profile13086,MergedCutProfiles.Batch035.profile1413,MergedCutProfiles.Batch327.profile13087]⟩
theorem profilesValid2109 : retention2109.ProfilesValid := by
  change ∀ j : Fin 16, (retention2109.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch326.valid13079
  · exact MergedCutProfiles.Batch327.valid13080
  · exact MergedCutProfiles.Batch035.valid1407
  · exact MergedCutProfiles.Batch326.valid13071
  · exact MergedCutProfiles.Batch327.valid13081
  · exact MergedCutProfiles.Batch327.valid13082
  · exact MergedCutProfiles.Batch326.valid13076
  · exact MergedCutProfiles.Batch327.valid13083
  · exact MergedCutProfiles.Batch327.valid13084
  · exact MergedCutProfiles.Batch327.valid13085
  · exact MergedCutProfiles.Batch034.valid1398
  · exact MergedCutProfiles.Batch034.valid1399
  · exact MergedCutProfiles.Batch035.valid1424
  · exact MergedCutProfiles.Batch327.valid13086
  · exact MergedCutProfiles.Batch035.valid1413
  · exact MergedCutProfiles.Batch327.valid13087
theorem numericValid2109 : retention2109.NumericValid := by decide +kernel
def certificate2109 : RatCutBinCertificate := ⟨⟨retention2109,(48534072011850779/25000000000000000),(14531335098101001/500000000000000000),(2284636561984684481/250000000000000000),(18404084515066028601/12500000000000000),(1130898224624609643/500000000000000000)⟩,(499358340259840289/500000000000000000),(30181098113397079/62500000000000000),(16557670486674007/100000000000000000),(77309380767023893/1000000000000000000)⟩
theorem valid2109 : certificate2109.Valid := by decide +kernel
theorem sound2109 : certificate2109.Sound := rat_cut_bin_certificate_sound certificate2109 profilesValid2109 numericValid2109 valid2109

def retention2110 : RatCutRetentionCertificate := ⟨(1/40),(13/500),(1277238255907498349/160319755211505144148),(582777697/500000000),(5/2),(898749624495435489/400000000000000000),true,MergedCutProfiles.Batch327.profile13088,![MergedCutProfiles.Batch327.profile13088,MergedCutProfiles.Batch035.profile1434,MergedCutProfiles.Batch327.profile13089,MergedCutProfiles.Batch035.profile1435,MergedCutProfiles.Batch327.profile13090,MergedCutProfiles.Batch035.profile1436,MergedCutProfiles.Batch327.profile13091,MergedCutProfiles.Batch327.profile13092,MergedCutProfiles.Batch327.profile13093,MergedCutProfiles.Batch034.profile1398,MergedCutProfiles.Batch034.profile1399,MergedCutProfiles.Batch327.profile13094,MergedCutProfiles.Batch327.profile13095,MergedCutProfiles.Batch035.profile1439,MergedCutProfiles.Batch327.profile13096,MergedCutProfiles.Batch036.profile1440]⟩
theorem profilesValid2110 : retention2110.ProfilesValid := by
  change ∀ j : Fin 16, (retention2110.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch327.valid13088
  · exact MergedCutProfiles.Batch035.valid1434
  · exact MergedCutProfiles.Batch327.valid13089
  · exact MergedCutProfiles.Batch035.valid1435
  · exact MergedCutProfiles.Batch327.valid13090
  · exact MergedCutProfiles.Batch035.valid1436
  · exact MergedCutProfiles.Batch327.valid13091
  · exact MergedCutProfiles.Batch327.valid13092
  · exact MergedCutProfiles.Batch327.valid13093
  · exact MergedCutProfiles.Batch034.valid1398
  · exact MergedCutProfiles.Batch034.valid1399
  · exact MergedCutProfiles.Batch327.valid13094
  · exact MergedCutProfiles.Batch327.valid13095
  · exact MergedCutProfiles.Batch035.valid1439
  · exact MergedCutProfiles.Batch327.valid13096
  · exact MergedCutProfiles.Batch036.valid1440
theorem numericValid2110 : retention2110.NumericValid := by decide +kernel
def certificate2110 : RatCutBinCertificate := ⟨⟨retention2110,(48534072011850779/25000000000000000),(14531335098101001/500000000000000000),(2284636561984684481/250000000000000000),(18404084515066028601/12500000000000000),(1115719505068138847/500000000000000000)⟩,(499358340259840289/500000000000000000),(367845869214747791/1000000000000000000),(264271206242545531/1000000000000000000),(90152654952395841/500000000000000000)⟩
theorem valid2110 : certificate2110.Valid := by decide +kernel
theorem sound2110 : certificate2110.Sound := rat_cut_bin_certificate_sound certificate2110 profilesValid2110 numericValid2110 valid2110

def retention2111 : RatCutRetentionCertificate := ⟨(1/40),(13/500),(2374998073712754467/80159877605752572074),(1277238255907498349/1000000000000000000),(47/20),(683055165092380270591/320000000000000000000),true,MergedCutProfiles.Batch327.profile13097,![MergedCutProfiles.Batch327.profile13097,MergedCutProfiles.Batch326.profile13077,MergedCutProfiles.Batch327.profile13098,MergedCutProfiles.Batch327.profile13096,MergedCutProfiles.Batch035.profile1428,MergedCutProfiles.Batch035.profile1430,MergedCutProfiles.Batch327.profile13099,MergedCutProfiles.Batch036.profile1445,MergedCutProfiles.Batch327.profile13100,MergedCutProfiles.Batch327.profile13101,MergedCutProfiles.Batch327.profile13102,MergedCutProfiles.Batch327.profile13103,MergedCutProfiles.Batch327.profile13104,MergedCutProfiles.Batch327.profile13105,MergedCutProfiles.Batch327.profile13106,MergedCutProfiles.Batch327.profile13107]⟩
theorem profilesValid2111 : retention2111.ProfilesValid := by
  change ∀ j : Fin 16, (retention2111.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch327.valid13097
  · exact MergedCutProfiles.Batch326.valid13077
  · exact MergedCutProfiles.Batch327.valid13098
  · exact MergedCutProfiles.Batch327.valid13096
  · exact MergedCutProfiles.Batch035.valid1428
  · exact MergedCutProfiles.Batch035.valid1430
  · exact MergedCutProfiles.Batch327.valid13099
  · exact MergedCutProfiles.Batch036.valid1445
  · exact MergedCutProfiles.Batch327.valid13100
  · exact MergedCutProfiles.Batch327.valid13101
  · exact MergedCutProfiles.Batch327.valid13102
  · exact MergedCutProfiles.Batch327.valid13103
  · exact MergedCutProfiles.Batch327.valid13104
  · exact MergedCutProfiles.Batch327.valid13105
  · exact MergedCutProfiles.Batch327.valid13106
  · exact MergedCutProfiles.Batch327.valid13107
theorem numericValid2111 : retention2111.NumericValid := by decide +kernel
def certificate2111 : RatCutBinCertificate := ⟨⟨retention2111,(48534072011850779/25000000000000000),(14531335098101001/500000000000000000),(2284636561984684481/250000000000000000),(18404084515066028601/12500000000000000),(1060019222873361393/500000000000000000)⟩,(499358340259840289/500000000000000000),(185869476781155353/500000000000000000),(260398668309384923/1000000000000000000),(180363045454158483/1000000000000000000)⟩
theorem valid2111 : certificate2111.Valid := by decide +kernel
theorem sound2111 : certificate2111.Sound := rat_cut_bin_certificate_sound certificate2111 profilesValid2111 numericValid2111 valid2111

def certificates : List RatCutBinCertificate := [certificate2100,certificate2101,certificate2102,certificate2103,certificate2104,certificate2105,certificate2106,certificate2107,certificate2108,certificate2109,certificate2110,certificate2111]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2100,List.forall_mem_cons.mpr ⟨sound2101,List.forall_mem_cons.mpr ⟨sound2102,List.forall_mem_cons.mpr ⟨sound2103,List.forall_mem_cons.mpr ⟨sound2104,List.forall_mem_cons.mpr ⟨sound2105,List.forall_mem_cons.mpr ⟨sound2106,List.forall_mem_cons.mpr ⟨sound2107,List.forall_mem_cons.mpr ⟨sound2108,List.forall_mem_cons.mpr ⟨sound2109,List.forall_mem_cons.mpr ⟨sound2110,List.forall_mem_cons.mpr ⟨sound2111,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch175
