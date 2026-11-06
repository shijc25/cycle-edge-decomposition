import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch174
import Cycle12.MergedCutProfiles.Batch175
import Cycle12.MergedCutProfiles.Batch176

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch087

def retention1044 : RatCutRetentionCertificate := ⟨(21/400),(211/4000),(1/2),(1675927088301056629/200000000000000000),(21/20),(531705901219467980654861943727809839199/536296668256338121280000000000000000000),false,MergedCutProfiles.Batch174.profile6972,(fun _ => MergedCutProfiles.Batch174.profile6972)⟩
theorem profilesValid1044 : retention1044.ProfilesValid := by
  exact MergedCutProfiles.Batch174.valid6972
theorem numericValid1044 : retention1044.NumericValid := by decide +kernel
def certificate1044 : RatCutBinCertificate := ⟨⟨retention1044,(1282358131055746827/500000000000000000),(135240887695497653/1000000000000000000),(3473464720970437089/250000000000000000),(234731906921777485191/1000000000000000000),(965225337050985831/1000000000000000000)⟩,(247630331440919763/250000000000000000),(82913567929507219/200000000000000000),(44079316933814907/200000000000000000),(181607223241432337/1000000000000000000)⟩
theorem valid1044 : certificate1044.Valid := by decide +kernel
theorem sound1044 : certificate1044.Sound := rat_cut_bin_certificate_sound certificate1044 profilesValid1044 numericValid1044 valid1044

def retention1045 : RatCutRetentionCertificate := ⟨(211/4000),(53/1000),(852542564611018418/16686931111337825223),(168820309823964043/200000000000000000),(57/20),(16367928473883748983/8000000000000000000),true,MergedCutProfiles.Batch174.profile6975,![MergedCutProfiles.Batch174.profile6975,MergedCutProfiles.Batch174.profile6976,MergedCutProfiles.Batch174.profile6977,MergedCutProfiles.Batch174.profile6978,MergedCutProfiles.Batch174.profile6979,MergedCutProfiles.Batch174.profile6980,MergedCutProfiles.Batch174.profile6981,MergedCutProfiles.Batch174.profile6982,MergedCutProfiles.Batch174.profile6983,MergedCutProfiles.Batch174.profile6984,MergedCutProfiles.Batch174.profile6985,MergedCutProfiles.Batch174.profile6986,MergedCutProfiles.Batch174.profile6987,MergedCutProfiles.Batch174.profile6988,MergedCutProfiles.Batch174.profile6989,MergedCutProfiles.Batch174.profile6990]⟩
theorem profilesValid1045 : retention1045.ProfilesValid := by
  change ∀ j : Fin 16, (retention1045.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch174.valid6975
  · exact MergedCutProfiles.Batch174.valid6976
  · exact MergedCutProfiles.Batch174.valid6977
  · exact MergedCutProfiles.Batch174.valid6978
  · exact MergedCutProfiles.Batch174.valid6979
  · exact MergedCutProfiles.Batch174.valid6980
  · exact MergedCutProfiles.Batch174.valid6981
  · exact MergedCutProfiles.Batch174.valid6982
  · exact MergedCutProfiles.Batch174.valid6983
  · exact MergedCutProfiles.Batch174.valid6984
  · exact MergedCutProfiles.Batch174.valid6985
  · exact MergedCutProfiles.Batch174.valid6986
  · exact MergedCutProfiles.Batch174.valid6987
  · exact MergedCutProfiles.Batch174.valid6988
  · exact MergedCutProfiles.Batch174.valid6989
  · exact MergedCutProfiles.Batch174.valid6990
theorem numericValid1045 : retention1045.NumericValid := by decide +kernel
def certificate1045 : RatCutBinCertificate := ⟨⟨retention1045,(552615573897843647/250000000000000000),(136712609017002193/1000000000000000000),(6976658962883345709/500000000000000000),(116588969202694662563/500000000000000000),(992125653367647413/500000000000000000)⟩,(991791473109206273/1000000000000000000),(183553500797057127/500000000000000000),(265010808431319311/1000000000000000000),(14169615823349701/100000000000000000)⟩
theorem valid1045 : certificate1045.Valid := by decide +kernel
theorem sound1045 : certificate1045.Sound := rat_cut_bin_certificate_sound certificate1045 profilesValid1045 numericValid1045 valid1045

def retention1046 : RatCutRetentionCertificate := ⟨(211/4000),(53/1000),(923181432922402034/16686931111337825223),(426271282305509209/500000000000000000),(57/20),(1304245863672567811361/640000000000000000000),true,MergedCutProfiles.Batch174.profile6991,![MergedCutProfiles.Batch174.profile6991,MergedCutProfiles.Batch174.profile6992,MergedCutProfiles.Batch174.profile6993,MergedCutProfiles.Batch174.profile6994,MergedCutProfiles.Batch174.profile6995,MergedCutProfiles.Batch174.profile6996,MergedCutProfiles.Batch174.profile6997,MergedCutProfiles.Batch174.profile6998,MergedCutProfiles.Batch174.profile6999,MergedCutProfiles.Batch175.profile7000,MergedCutProfiles.Batch175.profile7001,MergedCutProfiles.Batch174.profile6987,MergedCutProfiles.Batch175.profile7002,MergedCutProfiles.Batch175.profile7003,MergedCutProfiles.Batch175.profile7004,MergedCutProfiles.Batch175.profile7005]⟩
theorem profilesValid1046 : retention1046.ProfilesValid := by
  change ∀ j : Fin 16, (retention1046.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch174.valid6991
  · exact MergedCutProfiles.Batch174.valid6992
  · exact MergedCutProfiles.Batch174.valid6993
  · exact MergedCutProfiles.Batch174.valid6994
  · exact MergedCutProfiles.Batch174.valid6995
  · exact MergedCutProfiles.Batch174.valid6996
  · exact MergedCutProfiles.Batch174.valid6997
  · exact MergedCutProfiles.Batch174.valid6998
  · exact MergedCutProfiles.Batch174.valid6999
  · exact MergedCutProfiles.Batch175.valid7000
  · exact MergedCutProfiles.Batch175.valid7001
  · exact MergedCutProfiles.Batch174.valid6987
  · exact MergedCutProfiles.Batch175.valid7002
  · exact MergedCutProfiles.Batch175.valid7003
  · exact MergedCutProfiles.Batch175.valid7004
  · exact MergedCutProfiles.Batch175.valid7005
theorem numericValid1046 : retention1046.NumericValid := by decide +kernel
def certificate1046 : RatCutBinCertificate := ⟨⟨retention1046,(552615573897843647/250000000000000000),(136712609017002193/1000000000000000000),(6976658962883345709/500000000000000000),(116588969202694662563/500000000000000000),(1976144558430917823/1000000000000000000)⟩,(991791473109206273/1000000000000000000),(367118664476418603/1000000000000000000),(66249780605584329/250000000000000000),(35388910867359891/250000000000000000)⟩
theorem valid1046 : certificate1046.Valid := by decide +kernel
theorem sound1046 : certificate1046.Sound := rat_cut_bin_certificate_sound certificate1046 profilesValid1046 numericValid1046 valid1046

def retention1047 : RatCutRetentionCertificate := ⟨(211/4000),(53/1000),(476767071907837237/5562310370445941741),(461590716461201017/500000000000000000),(53/20),(310927867148923644667/160000000000000000000),true,MergedCutProfiles.Batch175.profile7006,![MergedCutProfiles.Batch175.profile7006,MergedCutProfiles.Batch175.profile7007,MergedCutProfiles.Batch175.profile7008,MergedCutProfiles.Batch175.profile7009,MergedCutProfiles.Batch175.profile7010,MergedCutProfiles.Batch175.profile7011,MergedCutProfiles.Batch175.profile7012,MergedCutProfiles.Batch175.profile7013,MergedCutProfiles.Batch175.profile7014,MergedCutProfiles.Batch175.profile7015,MergedCutProfiles.Batch175.profile7016,MergedCutProfiles.Batch175.profile7017,MergedCutProfiles.Batch175.profile7018,MergedCutProfiles.Batch175.profile7019,MergedCutProfiles.Batch175.profile7020,MergedCutProfiles.Batch175.profile7021]⟩
theorem profilesValid1047 : retention1047.ProfilesValid := by
  change ∀ j : Fin 16, (retention1047.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch175.valid7006
  · exact MergedCutProfiles.Batch175.valid7007
  · exact MergedCutProfiles.Batch175.valid7008
  · exact MergedCutProfiles.Batch175.valid7009
  · exact MergedCutProfiles.Batch175.valid7010
  · exact MergedCutProfiles.Batch175.valid7011
  · exact MergedCutProfiles.Batch175.valid7012
  · exact MergedCutProfiles.Batch175.valid7013
  · exact MergedCutProfiles.Batch175.valid7014
  · exact MergedCutProfiles.Batch175.valid7015
  · exact MergedCutProfiles.Batch175.valid7016
  · exact MergedCutProfiles.Batch175.valid7017
  · exact MergedCutProfiles.Batch175.valid7018
  · exact MergedCutProfiles.Batch175.valid7019
  · exact MergedCutProfiles.Batch175.valid7020
  · exact MergedCutProfiles.Batch175.valid7021
theorem numericValid1047 : retention1047.NumericValid := by decide +kernel
def certificate1047 : RatCutBinCertificate := ⟨⟨retention1047,(552615573897843647/250000000000000000),(136712609017002193/1000000000000000000),(6976658962883345709/500000000000000000),(116588969202694662563/500000000000000000),(942946132165669577/500000000000000000)⟩,(991791473109206273/1000000000000000000),(372706430061983707/1000000000000000000),(259442633403290559/1000000000000000000),(7081685833287031/50000000000000000)⟩
theorem valid1047 : certificate1047.Valid := by decide +kernel
theorem sound1047 : certificate1047.Sound := rat_cut_bin_certificate_sound certificate1047 profilesValid1047 numericValid1047 valid1047

def retention1048 : RatCutRetentionCertificate := ⟨(211/4000),(53/1000),(3907385493612649849/16686931111337825223),(1430301215723511711/1000000000000000000),(19/10),(1989862763935262510547/1280000000000000000000),true,MergedCutProfiles.Batch175.profile7022,![MergedCutProfiles.Batch175.profile7022,MergedCutProfiles.Batch175.profile7023,MergedCutProfiles.Batch175.profile7024,MergedCutProfiles.Batch175.profile7025,MergedCutProfiles.Batch175.profile7026,MergedCutProfiles.Batch175.profile7027,MergedCutProfiles.Batch175.profile7028,MergedCutProfiles.Batch175.profile7029,MergedCutProfiles.Batch175.profile7030,MergedCutProfiles.Batch175.profile7031,MergedCutProfiles.Batch175.profile7032,MergedCutProfiles.Batch175.profile7033,MergedCutProfiles.Batch175.profile7034,MergedCutProfiles.Batch175.profile7035,MergedCutProfiles.Batch175.profile7036,MergedCutProfiles.Batch175.profile7037]⟩
theorem profilesValid1048 : retention1048.ProfilesValid := by
  change ∀ j : Fin 16, (retention1048.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch175.valid7022
  · exact MergedCutProfiles.Batch175.valid7023
  · exact MergedCutProfiles.Batch175.valid7024
  · exact MergedCutProfiles.Batch175.valid7025
  · exact MergedCutProfiles.Batch175.valid7026
  · exact MergedCutProfiles.Batch175.valid7027
  · exact MergedCutProfiles.Batch175.valid7028
  · exact MergedCutProfiles.Batch175.valid7029
  · exact MergedCutProfiles.Batch175.valid7030
  · exact MergedCutProfiles.Batch175.valid7031
  · exact MergedCutProfiles.Batch175.valid7032
  · exact MergedCutProfiles.Batch175.valid7033
  · exact MergedCutProfiles.Batch175.valid7034
  · exact MergedCutProfiles.Batch175.valid7035
  · exact MergedCutProfiles.Batch175.valid7036
  · exact MergedCutProfiles.Batch175.valid7037
theorem numericValid1048 : retention1048.NumericValid := by decide +kernel
def certificate1048 : RatCutBinCertificate := ⟨⟨retention1048,(552615573897843647/250000000000000000),(136712609017002193/1000000000000000000),(6976658962883345709/500000000000000000),(116588969202694662563/500000000000000000),(302684320056632253/200000000000000000)⟩,(991791473109206273/1000000000000000000),(200273220613726207/500000000000000000),(291227574004163/1250000000000000),(35534361365469253/250000000000000000)⟩
theorem valid1048 : certificate1048.Valid := by decide +kernel
theorem sound1048 : certificate1048.Sound := rat_cut_bin_certificate_sound certificate1048 profilesValid1048 numericValid1048 valid1048

def retention1049 : RatCutRetentionCertificate := ⟨(211/4000),(53/1000),(2437875671627808023/5562310370445941741),(3907385493612649849/1000000000000000000),(11/10),(1402100758296400977637/1280000000000000000000),true,MergedCutProfiles.Batch175.profile7038,![MergedCutProfiles.Batch175.profile7038,MergedCutProfiles.Batch175.profile7039,MergedCutProfiles.Batch176.profile7040,MergedCutProfiles.Batch176.profile7041,MergedCutProfiles.Batch176.profile7042,MergedCutProfiles.Batch176.profile7043,MergedCutProfiles.Batch176.profile7044,MergedCutProfiles.Batch176.profile7045,MergedCutProfiles.Batch176.profile7046,MergedCutProfiles.Batch176.profile7047,MergedCutProfiles.Batch176.profile7048,MergedCutProfiles.Batch176.profile7049,MergedCutProfiles.Batch176.profile7050,MergedCutProfiles.Batch176.profile7051,MergedCutProfiles.Batch176.profile7052,MergedCutProfiles.Batch176.profile7053]⟩
theorem profilesValid1049 : retention1049.ProfilesValid := by
  change ∀ j : Fin 16, (retention1049.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch175.valid7038
  · exact MergedCutProfiles.Batch175.valid7039
  · exact MergedCutProfiles.Batch176.valid7040
  · exact MergedCutProfiles.Batch176.valid7041
  · exact MergedCutProfiles.Batch176.valid7042
  · exact MergedCutProfiles.Batch176.valid7043
  · exact MergedCutProfiles.Batch176.valid7044
  · exact MergedCutProfiles.Batch176.valid7045
  · exact MergedCutProfiles.Batch176.valid7046
  · exact MergedCutProfiles.Batch176.valid7047
  · exact MergedCutProfiles.Batch176.valid7048
  · exact MergedCutProfiles.Batch176.valid7049
  · exact MergedCutProfiles.Batch176.valid7050
  · exact MergedCutProfiles.Batch176.valid7051
  · exact MergedCutProfiles.Batch176.valid7052
  · exact MergedCutProfiles.Batch176.valid7053
theorem numericValid1049 : retention1049.NumericValid := by decide +kernel
def certificate1049 : RatCutBinCertificate := ⟨⟨retention1049,(552615573897843647/250000000000000000),(136712609017002193/1000000000000000000),(6976658962883345709/500000000000000000),(116588969202694662563/500000000000000000),(1071564395670322589/1000000000000000000)⟩,(991791473109206273/1000000000000000000),(230789015422765337/500000000000000000),(18157388370571413/100000000000000000),(28576304049535799/200000000000000000)⟩
theorem valid1049 : certificate1049.Valid := by decide +kernel
theorem sound1049 : certificate1049.Sound := rat_cut_bin_certificate_sound certificate1049 profilesValid1049 numericValid1049 valid1049

def retention1050 : RatCutRetentionCertificate := ⟨(211/4000),(53/1000),(2719860719940594750/5562310370445941741),(7313627014883424069/1000000000000000000),(21/20),(3935211561688002413556161295926175736653/3900601074604492836800000000000000000000),false,MergedCutProfiles.Batch176.profile7054,(fun _ => MergedCutProfiles.Batch176.profile7054)⟩
theorem profilesValid1050 : retention1050.ProfilesValid := by
  exact MergedCutProfiles.Batch176.valid7054
theorem numericValid1050 : retention1050.NumericValid := by decide +kernel
def certificate1050 : RatCutBinCertificate := ⟨⟨retention1050,(552615573897843647/250000000000000000),(136712609017002193/1000000000000000000),(6976658962883345709/500000000000000000),(116588969202694662563/500000000000000000),(61633168609247983/62500000000000000)⟩,(991791473109206273/1000000000000000000),(471137041378502127/1000000000000000000),(43570532412798537/250000000000000000),(72282380976136873/500000000000000000)⟩
theorem valid1050 : certificate1050.Valid := by decide +kernel
theorem sound1050 : certificate1050.Sound := rat_cut_bin_certificate_sound certificate1050 profilesValid1050 numericValid1050 valid1050

def retention1051 : RatCutRetentionCertificate := ⟨(211/4000),(53/1000),(8323589761234202114/16686931111337825223),(32638328639287137/4000000000000000),(21/20),(129648689126479032342025263058008098231/130553314557148548000000000000000000000),false,MergedCutProfiles.Batch176.profile7055,(fun _ => MergedCutProfiles.Batch176.profile7055)⟩
theorem profilesValid1051 : retention1051.ProfilesValid := by
  exact MergedCutProfiles.Batch176.valid7055
theorem numericValid1051 : retention1051.NumericValid := by decide +kernel
def certificate1051 : RatCutBinCertificate := ⟨⟨retention1051,(552615573897843647/250000000000000000),(136712609017002193/1000000000000000000),(6976658962883345709/500000000000000000),(116588969202694662563/500000000000000000),(242582149158078209/250000000000000000)⟩,(991791473109206273/1000000000000000000),(237565847782913557/500000000000000000),(17129263257310573/100000000000000000),(141637394265083489/1000000000000000000)⟩
theorem valid1051 : certificate1051.Valid := by decide +kernel
theorem sound1051 : certificate1051.Sound := rat_cut_bin_certificate_sound certificate1051 profilesValid1051 numericValid1051 valid1051

def retention1052 : RatCutRetentionCertificate := ⟨(211/4000),(53/1000),(1/2),(4161794880617101057/500000000000000000),(21/20),(3300385263035968049760521640694550458991/3329435904493680845600000000000000000000),false,MergedCutProfiles.Batch176.profile7056,(fun _ => MergedCutProfiles.Batch176.profile7056)⟩
theorem profilesValid1052 : retention1052.ProfilesValid := by
  exact MergedCutProfiles.Batch176.valid7056
theorem numericValid1052 : retention1052.NumericValid := by decide +kernel
def certificate1052 : RatCutBinCertificate := ⟨⟨retention1052,(552615573897843647/250000000000000000),(136712609017002193/1000000000000000000),(6976658962883345709/500000000000000000),(116588969202694662563/500000000000000000),(968532397668976199/1000000000000000000)⟩,(991791473109206273/1000000000000000000),(475385157310465749/1000000000000000000),(2138801053572901/12500000000000000),(141517367282085629/1000000000000000000)⟩
theorem valid1052 : certificate1052.Valid := by decide +kernel
theorem sound1052 : certificate1052.Sound := rat_cut_bin_certificate_sound certificate1052 profilesValid1052 numericValid1052 valid1052

def retention1053 : RatCutRetentionCertificate := ⟨(211/4000),(53/1000),(1/2),64,1,(15962375904290348891516058638790210159/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch176.profile7056,(fun _ => MergedCutProfiles.Batch176.profile7056)⟩
theorem profilesValid1053 : retention1053.ProfilesValid := by
  exact MergedCutProfiles.Batch176.valid7056
theorem numericValid1053 : retention1053.NumericValid := by decide +kernel
def certificate1053 : RatCutBinCertificate := ⟨⟨retention1053,(552615573897843647/250000000000000000),(136712609017002193/1000000000000000000),(6976658962883345709/500000000000000000),(116588969202694662563/500000000000000000),(487995251439806897/500000000000000000)⟩,(991791473109206273/1000000000000000000),(88958566243432999/200000000000000000),(97429707399857977/500000000000000000),(185772575385352187/1000000000000000000)⟩
theorem valid1053 : certificate1053.Valid := by decide +kernel
theorem sound1053 : certificate1053.Sound := rat_cut_bin_certificate_sound certificate1053 profilesValid1053 numericValid1053 valid1053

def retention1054 : RatCutRetentionCertificate := ⟨(211/4000),(53/1000),(7600877856182214436/16686931111337825223),(1856499538457767883/500000000000000000),(6/5),(402147468949451693187726405854078516279/371299907691553576600000000000000000000),false,MergedCutProfiles.Batch176.profile7057,(fun _ => MergedCutProfiles.Batch176.profile7057)⟩
theorem profilesValid1054 : retention1054.ProfilesValid := by
  exact MergedCutProfiles.Batch176.valid7057
theorem numericValid1054 : retention1054.NumericValid := by decide +kernel
def certificate1054 : RatCutBinCertificate := ⟨⟨retention1054,(641619588397843647/250000000000000000),(136712609017002193/1000000000000000000),(6976658962883345709/500000000000000000),(116588969202694662563/500000000000000000),(526450375206416209/500000000000000000)⟩,(495233720560450649/500000000000000000),(189388826989206717/500000000000000000),(316875285065439/1250000000000000),(183889855187559293/1000000000000000000)⟩
theorem valid1054 : certificate1054.Valid := by decide +kernel
theorem sound1054 : certificate1054.Sound := rat_cut_bin_certificate_sound certificate1054 profilesValid1054 numericValid1054 valid1054

def retention1055 : RatCutRetentionCertificate := ⟨(211/4000),(53/1000),(8230661555226896731/16686931111337825223),(1900219464045553609/250000000000000000),(21/20),(190374339990922467681305497254892379171/190021946404555360900000000000000000000),false,MergedCutProfiles.Batch176.profile7058,(fun _ => MergedCutProfiles.Batch176.profile7058)⟩
theorem profilesValid1055 : retention1055.ProfilesValid := by
  exact MergedCutProfiles.Batch176.valid7058
theorem numericValid1055 : retention1055.NumericValid := by decide +kernel
def certificate1055 : RatCutBinCertificate := ⟨⟨retention1055,(641619588397843647/250000000000000000),(136712609017002193/1000000000000000000),(6976658962883345709/500000000000000000),(116588969202694662563/500000000000000000),(243862315706652591/250000000000000000)⟩,(495233720560450649/500000000000000000),(408852916611793617/1000000000000000000),(45093617680585399/200000000000000000),(92864625808657127/500000000000000000)⟩
theorem valid1055 : certificate1055.Valid := by decide +kernel
theorem sound1055 : certificate1055.Sound := rat_cut_bin_certificate_sound certificate1055 profilesValid1055 numericValid1055 valid1055

def certificates : List RatCutBinCertificate := [certificate1044,certificate1045,certificate1046,certificate1047,certificate1048,certificate1049,certificate1050,certificate1051,certificate1052,certificate1053,certificate1054,certificate1055]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1044,List.forall_mem_cons.mpr ⟨sound1045,List.forall_mem_cons.mpr ⟨sound1046,List.forall_mem_cons.mpr ⟨sound1047,List.forall_mem_cons.mpr ⟨sound1048,List.forall_mem_cons.mpr ⟨sound1049,List.forall_mem_cons.mpr ⟨sound1050,List.forall_mem_cons.mpr ⟨sound1051,List.forall_mem_cons.mpr ⟨sound1052,List.forall_mem_cons.mpr ⟨sound1053,List.forall_mem_cons.mpr ⟨sound1054,List.forall_mem_cons.mpr ⟨sound1055,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch087
