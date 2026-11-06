import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch272
import Cycle12.MergedCutProfiles.Batch273
import Cycle12.MergedCutProfiles.Batch274

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch142

def retention1704 : RatCutRetentionCertificate := ⟨(517/8000),(259/4000),(1/2),(5195471874925218873/1000000000000000000),(11/10),(686116394422746633474747610807352218677/692729583323362516400000000000000000000),false,MergedCutProfiles.Batch272.profile10918,(fun _ => MergedCutProfiles.Batch272.profile10918)⟩
theorem profilesValid1704 : retention1704.ProfilesValid := by
  exact MergedCutProfiles.Batch272.valid10918
theorem numericValid1704 : retention1704.NumericValid := by decide +kernel
def certificate1704 : RatCutBinCertificate := ⟨⟨retention1704,(1191084783440777191/500000000000000000),(10945118842464967/50000000000000000),(2161684800171714029/125000000000000000),(36033734566090038479/200000000000000000),(239319324518175247/250000000000000000)⟩,(7917020056995903/8000000000000000),(426497749435612387/1000000000000000000),(52515593218277941/250000000000000000),(39210226971626687/250000000000000000)⟩
theorem valid1704 : certificate1704.Valid := by decide +kernel
theorem sound1704 : certificate1704.Sound := rat_cut_bin_certificate_sound certificate1704 profilesValid1704 numericValid1704 valid1704

def retention1705 : RatCutRetentionCertificate := ⟨(517/8000),(259/4000),(1/2),64,1,(15963483178653443181774627687308296719/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch272.profile10918,(fun _ => MergedCutProfiles.Batch272.profile10918)⟩
theorem profilesValid1705 : retention1705.ProfilesValid := by
  exact MergedCutProfiles.Batch272.valid10918
theorem numericValid1705 : retention1705.NumericValid := by decide +kernel
def certificate1705 : RatCutBinCertificate := ⟨⟨retention1705,(1191084783440777191/500000000000000000),(10945118842464967/50000000000000000),(2161684800171714029/125000000000000000),(36033734566090038479/200000000000000000),(241890853367056429/250000000000000000)⟩,(7917020056995903/8000000000000000),(96353250147991373/250000000000000000),(247116827089252213/1000000000000000000),(2913408023432949/12500000000000000)⟩
theorem valid1705 : certificate1705.Valid := by decide +kernel
theorem sound1705 : certificate1705.Sound := rat_cut_bin_certificate_sound certificate1705 profilesValid1705 numericValid1705 valid1705

def retention1706 : RatCutRetentionCertificate := ⟨(517/8000),(259/4000),(2422375847514931825/5205039417310767161),(774015596391450017/250000000000000000),(6/5),(5102914513315915042587251484567909989/4837597477446562606250000000000000000),false,MergedCutProfiles.Batch272.profile10919,(fun _ => MergedCutProfiles.Batch272.profile10919)⟩
theorem profilesValid1706 : retention1706.ProfilesValid := by
  exact MergedCutProfiles.Batch272.valid10919
theorem numericValid1706 : retention1706.NumericValid := by decide +kernel
def certificate1706 : RatCutBinCertificate := ⟨⟨retention1706,(1348163281440777191/500000000000000000),(10945118842464967/50000000000000000),(2161684800171714029/125000000000000000),(36033734566090038479/200000000000000000),(506937496145782063/500000000000000000)⟩,(247063781392214461/250000000000000000),(378155330838753359/1000000000000000000),(254104847780131143/1000000000000000000),(86300824219029833/500000000000000000)⟩
theorem valid1706 : certificate1706.Valid := by decide +kernel
theorem sound1706 : certificate1706.Sound := rat_cut_bin_certificate_sound certificate1706 profilesValid1706 numericValid1706 valid1706

def retention1707 : RatCutRetentionCertificate := ⟨(517/8000),(259/4000),(2571400774466275444/5205039417310767161),(96895033900597273/20000000000000000),(11/10),(2420379268358006368178284639527051943/2422375847514931825000000000000000000),false,MergedCutProfiles.Batch273.profile10920,(fun _ => MergedCutProfiles.Batch273.profile10920)⟩
theorem profilesValid1707 : retention1707.ProfilesValid := by
  exact MergedCutProfiles.Batch273.valid10920
theorem numericValid1707 : retention1707.NumericValid := by decide +kernel
def certificate1707 : RatCutBinCertificate := ⟨⟨retention1707,(1348163281440777191/500000000000000000),(10945118842464967/50000000000000000),(2161684800171714029/125000000000000000),(36033734566090038479/200000000000000000),(9616238434060849/10000000000000000)⟩,(247063781392214461/250000000000000000),(99675729696223773/250000000000000000),(117336459031007723/500000000000000000),(10873739234468957/62500000000000000)⟩
theorem valid1707 : certificate1707.Valid := by decide +kernel
theorem sound1707 : certificate1707.Sound := rat_cut_bin_certificate_sound certificate1707 profilesValid1707 numericValid1707 valid1707

def retention1708 : RatCutRetentionCertificate := ⟨(517/8000),(259/4000),(5194229564421876397/10410078834621534322),(642850193616568861/125000000000000000),(11/10),(3985962166350184484819914755034250383/4017813710103555381250000000000000000),false,MergedCutProfiles.Batch273.profile10921,(fun _ => MergedCutProfiles.Batch273.profile10921)⟩
theorem profilesValid1708 : retention1708.ProfilesValid := by
  exact MergedCutProfiles.Batch273.valid10921
theorem numericValid1708 : retention1708.NumericValid := by decide +kernel
def certificate1708 : RatCutBinCertificate := ⟨⟨retention1708,(1348163281440777191/500000000000000000),(10945118842464967/50000000000000000),(2161684800171714029/125000000000000000),(36033734566090038479/200000000000000000),(47726049097681491/50000000000000000)⟩,(247063781392214461/250000000000000000),(100417445081835939/250000000000000000),(57988976397636771/250000000000000000),(34456108296818839/200000000000000000)⟩
theorem valid1708 : certificate1708.Valid := by decide +kernel
theorem sound1708 : certificate1708.Sound := rat_cut_bin_certificate_sound certificate1708 profilesValid1708 numericValid1708 valid1708

def retention1709 : RatCutRetentionCertificate := ⟨(517/8000),(259/4000),(1/2),(5194229564421876397/1000000000000000000),(11/10),(2057839466086317289083918965120080875431/2077691825768750558800000000000000000000),false,MergedCutProfiles.Batch272.profile10918,(fun _ => MergedCutProfiles.Batch272.profile10918)⟩
theorem profilesValid1709 : retention1709.ProfilesValid := by
  exact MergedCutProfiles.Batch272.valid10918
theorem numericValid1709 : retention1709.NumericValid := by decide +kernel
def certificate1709 : RatCutBinCertificate := ⟨⟨retention1709,(1348163281440777191/500000000000000000),(10945118842464967/50000000000000000),(2161684800171714029/125000000000000000),(36033734566090038479/200000000000000000),(952893635942424243/1000000000000000000)⟩,(247063781392214461/250000000000000000),(25147234347407327/62500000000000000),(231330827693971427/1000000000000000000),(2147370269061281/12500000000000000)⟩
theorem valid1709 : certificate1709.Valid := by decide +kernel
theorem sound1709 : certificate1709.Sound := rat_cut_bin_certificate_sound certificate1709 profilesValid1709 numericValid1709 valid1709

def retention1710 : RatCutRetentionCertificate := ⟨(259/4000),(519/8000),(527090183003769179/5180904945625861658),(872587166596620647/1000000000000000000),(51/20),(2414340982634517332919/1280000000000000000000),true,MergedCutProfiles.Batch273.profile10922,![MergedCutProfiles.Batch273.profile10922,MergedCutProfiles.Batch273.profile10923,MergedCutProfiles.Batch273.profile10924,MergedCutProfiles.Batch273.profile10925,MergedCutProfiles.Batch273.profile10926,MergedCutProfiles.Batch273.profile10927,MergedCutProfiles.Batch273.profile10928,MergedCutProfiles.Batch273.profile10929,MergedCutProfiles.Batch273.profile10930,MergedCutProfiles.Batch273.profile10931,MergedCutProfiles.Batch273.profile10932,MergedCutProfiles.Batch273.profile10933,MergedCutProfiles.Batch273.profile10934,MergedCutProfiles.Batch273.profile10935,MergedCutProfiles.Batch273.profile10936,MergedCutProfiles.Batch273.profile10937]⟩
theorem profilesValid1710 : retention1710.ProfilesValid := by
  change ∀ j : Fin 16, (retention1710.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch273.valid10922
  · exact MergedCutProfiles.Batch273.valid10923
  · exact MergedCutProfiles.Batch273.valid10924
  · exact MergedCutProfiles.Batch273.valid10925
  · exact MergedCutProfiles.Batch273.valid10926
  · exact MergedCutProfiles.Batch273.valid10927
  · exact MergedCutProfiles.Batch273.valid10928
  · exact MergedCutProfiles.Batch273.valid10929
  · exact MergedCutProfiles.Batch273.valid10930
  · exact MergedCutProfiles.Batch273.valid10931
  · exact MergedCutProfiles.Batch273.valid10932
  · exact MergedCutProfiles.Batch273.valid10933
  · exact MergedCutProfiles.Batch273.valid10934
  · exact MergedCutProfiles.Batch273.valid10935
  · exact MergedCutProfiles.Batch273.valid10936
  · exact MergedCutProfiles.Batch273.valid10937
theorem numericValid1710 : retention1710.NumericValid := by decide +kernel
def certificate1710 : RatCutBinCertificate := ⟨⟨retention1710,(478462886308628597/200000000000000000),(219927697911499729/1000000000000000000),(4333713125307063047/250000000000000000),(22470305959290079927/125000000000000000),(361753078158007321/200000000000000000)⟩,(494786538029003481/500000000000000000),(336806503757061641/1000000000000000000),(296656512937844083/1000000000000000000),(157528489797686973/1000000000000000000)⟩
theorem valid1710 : certificate1710.Valid := by decide +kernel
theorem sound1710 : certificate1710.Sound := rat_cut_bin_certificate_sound certificate1710 profilesValid1710 numericValid1710 valid1710

def retention1711 : RatCutRetentionCertificate := ⟨(259/4000),(519/8000),(920199217095549775/5180904945625861658),(527090183003769179/500000000000000000),(43/20),(1078544673030402853163/640000000000000000000),true,MergedCutProfiles.Batch273.profile10938,![MergedCutProfiles.Batch273.profile10938,MergedCutProfiles.Batch273.profile10939,MergedCutProfiles.Batch273.profile10940,MergedCutProfiles.Batch273.profile10941,MergedCutProfiles.Batch273.profile10942,MergedCutProfiles.Batch273.profile10943,MergedCutProfiles.Batch273.profile10944,MergedCutProfiles.Batch273.profile10945,MergedCutProfiles.Batch273.profile10946,MergedCutProfiles.Batch273.profile10947,MergedCutProfiles.Batch273.profile10948,MergedCutProfiles.Batch273.profile10949,MergedCutProfiles.Batch273.profile10950,MergedCutProfiles.Batch273.profile10951,MergedCutProfiles.Batch273.profile10952,MergedCutProfiles.Batch273.profile10953]⟩
theorem profilesValid1711 : retention1711.ProfilesValid := by
  change ∀ j : Fin 16, (retention1711.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch273.valid10938
  · exact MergedCutProfiles.Batch273.valid10939
  · exact MergedCutProfiles.Batch273.valid10940
  · exact MergedCutProfiles.Batch273.valid10941
  · exact MergedCutProfiles.Batch273.valid10942
  · exact MergedCutProfiles.Batch273.valid10943
  · exact MergedCutProfiles.Batch273.valid10944
  · exact MergedCutProfiles.Batch273.valid10945
  · exact MergedCutProfiles.Batch273.valid10946
  · exact MergedCutProfiles.Batch273.valid10947
  · exact MergedCutProfiles.Batch273.valid10948
  · exact MergedCutProfiles.Batch273.valid10949
  · exact MergedCutProfiles.Batch273.valid10950
  · exact MergedCutProfiles.Batch273.valid10951
  · exact MergedCutProfiles.Batch273.valid10952
  · exact MergedCutProfiles.Batch273.valid10953
theorem numericValid1711 : retention1711.NumericValid := by decide +kernel
def certificate1711 : RatCutBinCertificate := ⟨⟨retention1711,(478462886308628597/200000000000000000),(219927697911499729/1000000000000000000),(4333713125307063047/250000000000000000),(22470305959290079927/125000000000000000),(1619935420933227781/1000000000000000000)⟩,(494786538029003481/500000000000000000),(350158844671982819/1000000000000000000),(56477949587950861/200000000000000000),(19707747547460541/125000000000000000)⟩
theorem valid1711 : certificate1711.Valid := by decide +kernel
theorem sound1711 : certificate1711.Sound := rat_cut_bin_certificate_sound certificate1711 profilesValid1711 numericValid1711 valid1711

def retention1712 : RatCutRetentionCertificate := ⟨(259/4000),(519/8000),(3656677387115763265/10361809891251723316),(36807968683821991/20000000000000000),(7/5),(32672831512991184379/25600000000000000000),true,MergedCutProfiles.Batch273.profile10954,![MergedCutProfiles.Batch273.profile10954,MergedCutProfiles.Batch273.profile10955,MergedCutProfiles.Batch273.profile10956,MergedCutProfiles.Batch273.profile10957,MergedCutProfiles.Batch273.profile10958,MergedCutProfiles.Batch273.profile10959,MergedCutProfiles.Batch274.profile10960,MergedCutProfiles.Batch274.profile10961,MergedCutProfiles.Batch274.profile10962,MergedCutProfiles.Batch274.profile10963,MergedCutProfiles.Batch274.profile10964,MergedCutProfiles.Batch274.profile10965,MergedCutProfiles.Batch274.profile10966,MergedCutProfiles.Batch274.profile10967,MergedCutProfiles.Batch274.profile10968,MergedCutProfiles.Batch274.profile10969]⟩
theorem profilesValid1712 : retention1712.ProfilesValid := by
  change ∀ j : Fin 16, (retention1712.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch273.valid10954
  · exact MergedCutProfiles.Batch273.valid10955
  · exact MergedCutProfiles.Batch273.valid10956
  · exact MergedCutProfiles.Batch273.valid10957
  · exact MergedCutProfiles.Batch273.valid10958
  · exact MergedCutProfiles.Batch273.valid10959
  · exact MergedCutProfiles.Batch274.valid10960
  · exact MergedCutProfiles.Batch274.valid10961
  · exact MergedCutProfiles.Batch274.valid10962
  · exact MergedCutProfiles.Batch274.valid10963
  · exact MergedCutProfiles.Batch274.valid10964
  · exact MergedCutProfiles.Batch274.valid10965
  · exact MergedCutProfiles.Batch274.valid10966
  · exact MergedCutProfiles.Batch274.valid10967
  · exact MergedCutProfiles.Batch274.valid10968
  · exact MergedCutProfiles.Batch274.valid10969
theorem numericValid1712 : retention1712.NumericValid := by decide +kernel
def certificate1712 : RatCutBinCertificate := ⟨⟨retention1712,(478462886308628597/200000000000000000),(219927697911499729/1000000000000000000),(4333713125307063047/250000000000000000),(22470305959290079927/125000000000000000),(1233770411980826209/1000000000000000000)⟩,(494786538029003481/500000000000000000),(48740988180929087/125000000000000000),(60709685289051853/250000000000000000),(157489102463101677/1000000000000000000)⟩
theorem valid1712 : certificate1712.Valid := by decide +kernel
theorem sound1712 : certificate1712.Sound := rat_cut_bin_certificate_sound certificate1712 profilesValid1712 numericValid1712 valid1712

def retention1713 : RatCutRetentionCertificate := ⟨(259/4000),(519/8000),(1207883700114289059/2590452472812930829),(731335477423152653/200000000000000000),1,(52035482387380931933/51200000000000000000),true,MergedCutProfiles.Batch274.profile10970,![MergedCutProfiles.Batch274.profile10970,MergedCutProfiles.Batch274.profile10971,MergedCutProfiles.Batch274.profile10972,MergedCutProfiles.Batch274.profile10973,MergedCutProfiles.Batch274.profile10974,MergedCutProfiles.Batch274.profile10975,MergedCutProfiles.Batch274.profile10976,MergedCutProfiles.Batch274.profile10977,MergedCutProfiles.Batch274.profile10978,MergedCutProfiles.Batch274.profile10979,MergedCutProfiles.Batch274.profile10980,MergedCutProfiles.Batch274.profile10981,MergedCutProfiles.Batch274.profile10982,MergedCutProfiles.Batch274.profile10983,MergedCutProfiles.Batch274.profile10984,MergedCutProfiles.Batch274.profile10985]⟩
theorem profilesValid1713 : retention1713.ProfilesValid := by
  change ∀ j : Fin 16, (retention1713.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch274.valid10970
  · exact MergedCutProfiles.Batch274.valid10971
  · exact MergedCutProfiles.Batch274.valid10972
  · exact MergedCutProfiles.Batch274.valid10973
  · exact MergedCutProfiles.Batch274.valid10974
  · exact MergedCutProfiles.Batch274.valid10975
  · exact MergedCutProfiles.Batch274.valid10976
  · exact MergedCutProfiles.Batch274.valid10977
  · exact MergedCutProfiles.Batch274.valid10978
  · exact MergedCutProfiles.Batch274.valid10979
  · exact MergedCutProfiles.Batch274.valid10980
  · exact MergedCutProfiles.Batch274.valid10981
  · exact MergedCutProfiles.Batch274.valid10982
  · exact MergedCutProfiles.Batch274.valid10983
  · exact MergedCutProfiles.Batch274.valid10984
  · exact MergedCutProfiles.Batch274.valid10985
theorem numericValid1713 : retention1713.NumericValid := by decide +kernel
def certificate1713 : RatCutBinCertificate := ⟨⟨retention1713,(478462886308628597/200000000000000000),(219927697911499729/1000000000000000000),(4333713125307063047/250000000000000000),(22470305959290079927/125000000000000000),(985956508816715889/1000000000000000000)⟩,(494786538029003481/500000000000000000),(214869684445134727/500000000000000000),(207312378382385453/1000000000000000000),(39769784895386019/250000000000000000)⟩
theorem valid1713 : certificate1713.Valid := by decide +kernel
theorem sound1713 : certificate1713.Sound := rat_cut_bin_certificate_sound certificate1713 profilesValid1713 numericValid1713 valid1713

def retention1714 : RatCutRetentionCertificate := ⟨(259/4000),(519/8000),(2564385774507626487/5180904945625861658),(1207883700114289059/250000000000000000),(11/10),(120458360958567498964271955778176314399/120788370011428905900000000000000000000),false,MergedCutProfiles.Batch274.profile10986,(fun _ => MergedCutProfiles.Batch274.profile10986)⟩
theorem profilesValid1714 : retention1714.ProfilesValid := by
  exact MergedCutProfiles.Batch274.valid10986
theorem numericValid1714 : retention1714.NumericValid := by decide +kernel
def certificate1714 : RatCutBinCertificate := ⟨⟨retention1714,(478462886308628597/200000000000000000),(219927697911499729/1000000000000000000),(4333713125307063047/250000000000000000),(22470305959290079927/125000000000000000),(9638737015008739/10000000000000000)⟩,(494786538029003481/500000000000000000),(424917661259414059/1000000000000000000),(211411742502545653/1000000000000000000),(78598801563972863/500000000000000000)⟩
theorem valid1714 : certificate1714.Valid := by decide +kernel
theorem sound1714 : certificate1714.Sound := rat_cut_bin_certificate_sound certificate1714 profilesValid1714 numericValid1714 valid1714

def retention1715 : RatCutRetentionCertificate := ⟨(259/4000),(519/8000),(1295014816126351376/2590452472812930829),(2564385774507626487/500000000000000000),(11/10),(126956181579921005494587107133284433269/128219288725381324350000000000000000000),false,MergedCutProfiles.Batch274.profile10987,(fun _ => MergedCutProfiles.Batch274.profile10987)⟩
theorem profilesValid1715 : retention1715.ProfilesValid := by
  exact MergedCutProfiles.Batch274.valid10987
theorem numericValid1715 : retention1715.NumericValid := by decide +kernel
def certificate1715 : RatCutBinCertificate := ⟨⟨retention1715,(478462886308628597/200000000000000000),(219927697911499729/1000000000000000000),(4333713125307063047/250000000000000000),(22470305959290079927/125000000000000000),(191351025062811987/200000000000000000)⟩,(494786538029003481/500000000000000000),(8508276285552593/20000000000000000),(105493702121851897/500000000000000000),(19646995688832273/125000000000000000)⟩
theorem valid1715 : certificate1715.Valid := by decide +kernel
theorem sound1715 : certificate1715.Sound := rat_cut_bin_certificate_sound certificate1715 profilesValid1715 numericValid1715 valid1715

def certificates : List RatCutBinCertificate := [certificate1704,certificate1705,certificate1706,certificate1707,certificate1708,certificate1709,certificate1710,certificate1711,certificate1712,certificate1713,certificate1714,certificate1715]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1704,List.forall_mem_cons.mpr ⟨sound1705,List.forall_mem_cons.mpr ⟨sound1706,List.forall_mem_cons.mpr ⟨sound1707,List.forall_mem_cons.mpr ⟨sound1708,List.forall_mem_cons.mpr ⟨sound1709,List.forall_mem_cons.mpr ⟨sound1710,List.forall_mem_cons.mpr ⟨sound1711,List.forall_mem_cons.mpr ⟨sound1712,List.forall_mem_cons.mpr ⟨sound1713,List.forall_mem_cons.mpr ⟨sound1714,List.forall_mem_cons.mpr ⟨sound1715,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch142
