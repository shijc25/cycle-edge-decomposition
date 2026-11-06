import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch382
import Cycle12.MergedCutProfiles.Batch500
import Cycle12.MergedCutProfiles.Batch501
import Cycle12.MergedCutProfiles.Batch502

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch272

def retention3264 : RatCutRetentionCertificate := ⟨(13/250),(53/1000),(1/2),(20677246035643350787/500000000000000000),1,(10292086783158770972654986738916467269/10338623017821675393500000000000000000),false,MergedCutProfiles.Batch382.profile15294,(fun _ => MergedCutProfiles.Batch382.profile15294)⟩
theorem profilesValid3264 : retention3264.ProfilesValid := by
  exact MergedCutProfiles.Batch382.valid15294
theorem numericValid3264 : retention3264.NumericValid := by decide +kernel
def certificate3264 : RatCutBinCertificate := ⟨⟨retention3264,(1055108355159137459/500000000000000000),(136712609017002193/1000000000000000000),(13779305530758571177/1000000000000000000),(1156382762462842116309/1000000000000000000),(243640508604664547/250000000000000000)⟩,(499206813341826959/500000000000000000),(447945892977329861/1000000000000000000),(96158077000516673/500000000000000000),(91407069558425289/500000000000000000)⟩
theorem valid3264 : certificate3264.Valid := by decide +kernel
theorem sound3264 : certificate3264.Sound := rat_cut_bin_certificate_sound certificate3264 profilesValid3264 numericValid3264 valid3264

def retention3265 : RatCutRetentionCertificate := ⟨(13/250),(53/1000),(38387574222848073005/83434655556689126119),(1239920520969591451/125000000000000000),1,(10439548746573988244767800288581324439/9919364167756731608000000000000000000),false,MergedCutProfiles.Batch500.profile20025,(fun _ => MergedCutProfiles.Batch500.profile20025)⟩
theorem profilesValid3265 : retention3265.ProfilesValid := by
  exact MergedCutProfiles.Batch500.valid20025
theorem numericValid3265 : retention3265.NumericValid := by decide +kernel
def certificate3265 : RatCutBinCertificate := ⟨⟨retention3265,(1106675816159137459/500000000000000000),(136712609017002193/1000000000000000000),(13779305530758571177/1000000000000000000),(1156382762462842116309/1000000000000000000),(1030481095458387581/1000000000000000000)⟩,(124792009337814481/125000000000000000),(29978143695696371/250000000000000000),(24947134536126227/40000000000000000),(581184844943388041/1000000000000000000)⟩
theorem valid3265 : certificate3265.Valid := by decide +kernel
theorem sound3265 : certificate3265.Sound := rat_cut_bin_certificate_sound certificate3265 profilesValid3265 numericValid3265 valid3265

def retention3266 : RatCutRetentionCertificate := ⟨(13/250),(53/1000),(41568242160006671510/83434655556689126119),(7677514844569614601/200000000000000000),1,(38332427760780527565380948834099141541/38387574222848073005000000000000000000),false,MergedCutProfiles.Batch500.profile20026,(fun _ => MergedCutProfiles.Batch500.profile20026)⟩
theorem profilesValid3266 : retention3266.ProfilesValid := by
  exact MergedCutProfiles.Batch500.valid20026
theorem numericValid3266 : retention3266.NumericValid := by decide +kernel
def certificate3266 : RatCutBinCertificate := ⟨⟨retention3266,(1106675816159137459/500000000000000000),(136712609017002193/1000000000000000000),(13779305530758571177/1000000000000000000),(1156382762462842116309/1000000000000000000),(976603396064928221/1000000000000000000)⟩,(124792009337814481/125000000000000000),(126527966131694029/1000000000000000000),(76266641435529461/125000000000000000),(116018761398384123/200000000000000000)⟩
theorem valid3266 : certificate3266.Valid := by decide +kernel
theorem sound3266 : certificate3266.Sound := rat_cut_bin_certificate_sound certificate3266 profilesValid3266 numericValid3266 valid3266

def retention3267 : RatCutRetentionCertificate := ⟨(13/250),(53/1000),(1/2),(4156824216000667151/100000000000000000),1,(10345607828318018972566282184121961941/10392060540001667877500000000000000000),false,MergedCutProfiles.Batch382.profile15294,(fun _ => MergedCutProfiles.Batch382.profile15294)⟩
theorem profilesValid3267 : retention3267.ProfilesValid := by
  exact MergedCutProfiles.Batch382.valid15294
theorem numericValid3267 : retention3267.NumericValid := by decide +kernel
def certificate3267 : RatCutBinCertificate := ⟨⟨retention3267,(1106675816159137459/500000000000000000),(136712609017002193/1000000000000000000),(13779305530758571177/1000000000000000000),(1156382762462842116309/1000000000000000000),(973569952531403163/1000000000000000000)⟩,(124792009337814481/125000000000000000),(63461100612292597/500000000000000000),(121867102550466747/200000000000000000),(578676759671500627/1000000000000000000)⟩
theorem valid3267 : certificate3267.Valid := by decide +kernel
theorem sound3267 : certificate3267.Sound := rat_cut_bin_certificate_sound certificate3267 profilesValid3267 numericValid3267 valid3267

def retention3268 : RatCutRetentionCertificate := ⟨(53/1000),(107/2000),(408645922362244119/40821650359423429750),(404599923130934771/500000000000000000),(67/20),(45625099991594366551/20000000000000000000),true,MergedCutProfiles.Batch500.profile20027,![MergedCutProfiles.Batch500.profile20027,MergedCutProfiles.Batch500.profile20028,MergedCutProfiles.Batch500.profile20029,MergedCutProfiles.Batch500.profile20030,MergedCutProfiles.Batch500.profile20031,MergedCutProfiles.Batch500.profile20032,MergedCutProfiles.Batch500.profile20033,MergedCutProfiles.Batch500.profile20034,MergedCutProfiles.Batch500.profile20035,MergedCutProfiles.Batch500.profile20036,MergedCutProfiles.Batch500.profile20037,MergedCutProfiles.Batch500.profile20038,MergedCutProfiles.Batch500.profile20039,MergedCutProfiles.Batch501.profile20040,MergedCutProfiles.Batch501.profile20041,MergedCutProfiles.Batch501.profile20042]⟩
theorem profilesValid3268 : retention3268.ProfilesValid := by
  change ∀ j : Fin 16, (retention3268.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch500.valid20027
  · exact MergedCutProfiles.Batch500.valid20028
  · exact MergedCutProfiles.Batch500.valid20029
  · exact MergedCutProfiles.Batch500.valid20030
  · exact MergedCutProfiles.Batch500.valid20031
  · exact MergedCutProfiles.Batch500.valid20032
  · exact MergedCutProfiles.Batch500.valid20033
  · exact MergedCutProfiles.Batch500.valid20034
  · exact MergedCutProfiles.Batch500.valid20035
  · exact MergedCutProfiles.Batch500.valid20036
  · exact MergedCutProfiles.Batch500.valid20037
  · exact MergedCutProfiles.Batch500.valid20038
  · exact MergedCutProfiles.Batch500.valid20039
  · exact MergedCutProfiles.Batch501.valid20040
  · exact MergedCutProfiles.Batch501.valid20041
  · exact MergedCutProfiles.Batch501.valid20042
theorem numericValid3268 : retention3268.NumericValid := by decide +kernel
def certificate3268 : RatCutBinCertificate := ⟨⟨retention3268,(2127361553394259841/1000000000000000000),(17460968802135489/125000000000000000),(7008338157695654169/500000000000000000),(573859666037521547669/500000000000000000),(442045749756397067/200000000000000000)⟩,(998399440572570273/1000000000000000000),(195882112366225937/500000000000000000),(241113722179706701/1000000000000000000),(25539672676200083/200000000000000000)⟩
theorem valid3268 : certificate3268.Valid := by decide +kernel
theorem sound3268 : certificate3268.Sound := rat_cut_bin_certificate_sound certificate3268 profilesValid3268 numericValid3268 valid3268

def retention3269 : RatCutRetentionCertificate := ⟨(53/1000),(107/2000),(251805970587539006/20410825179711714875),(408645922362244119/500000000000000000),(33/10),(90518472350096968629/40000000000000000000),true,MergedCutProfiles.Batch501.profile20043,![MergedCutProfiles.Batch501.profile20043,MergedCutProfiles.Batch501.profile20044,MergedCutProfiles.Batch501.profile20045,MergedCutProfiles.Batch501.profile20046,MergedCutProfiles.Batch501.profile20047,MergedCutProfiles.Batch501.profile20048,MergedCutProfiles.Batch501.profile20049,MergedCutProfiles.Batch501.profile20050,MergedCutProfiles.Batch501.profile20051,MergedCutProfiles.Batch501.profile20052,MergedCutProfiles.Batch501.profile20053,MergedCutProfiles.Batch501.profile20054,MergedCutProfiles.Batch501.profile20055,MergedCutProfiles.Batch501.profile20056,MergedCutProfiles.Batch501.profile20057,MergedCutProfiles.Batch501.profile20058]⟩
theorem profilesValid3269 : retention3269.ProfilesValid := by
  change ∀ j : Fin 16, (retention3269.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch501.valid20043
  · exact MergedCutProfiles.Batch501.valid20044
  · exact MergedCutProfiles.Batch501.valid20045
  · exact MergedCutProfiles.Batch501.valid20046
  · exact MergedCutProfiles.Batch501.valid20047
  · exact MergedCutProfiles.Batch501.valid20048
  · exact MergedCutProfiles.Batch501.valid20049
  · exact MergedCutProfiles.Batch501.valid20050
  · exact MergedCutProfiles.Batch501.valid20051
  · exact MergedCutProfiles.Batch501.valid20052
  · exact MergedCutProfiles.Batch501.valid20053
  · exact MergedCutProfiles.Batch501.valid20054
  · exact MergedCutProfiles.Batch501.valid20055
  · exact MergedCutProfiles.Batch501.valid20056
  · exact MergedCutProfiles.Batch501.valid20057
  · exact MergedCutProfiles.Batch501.valid20058
theorem numericValid3269 : retention3269.NumericValid := by decide +kernel
def certificate3269 : RatCutBinCertificate := ⟨⟨retention3269,(2127361553394259841/1000000000000000000),(17460968802135489/125000000000000000),(7008338157695654169/500000000000000000),(573859666037521547669/500000000000000000),(1096497817614321691/500000000000000000)⟩,(998399440572570273/1000000000000000000),(392843464615344709/1000000000000000000),(240103911797215261/1000000000000000000),(25554834655778263/200000000000000000)⟩
theorem valid3269 : certificate3269.Valid := by decide +kernel
theorem sound3269 : certificate3269.Sound := rat_cut_bin_certificate_sound certificate3269 profilesValid3269 numericValid3269 valid3269

def retention3270 : RatCutRetentionCertificate := ⟨(53/1000),(107/2000),(2172947410000000/163286601437693719),(125902985293769503/125000000000000000),(14/5),(360333153114854573741/160000000000000000000),true,MergedCutProfiles.Batch501.profile20059,![MergedCutProfiles.Batch501.profile20059,MergedCutProfiles.Batch501.profile20060,MergedCutProfiles.Batch500.profile20030,MergedCutProfiles.Batch501.profile20061,MergedCutProfiles.Batch501.profile20062,MergedCutProfiles.Batch500.profile20034,MergedCutProfiles.Batch501.profile20063,MergedCutProfiles.Batch501.profile20064,MergedCutProfiles.Batch500.profile20038,MergedCutProfiles.Batch501.profile20065,MergedCutProfiles.Batch501.profile20066,MergedCutProfiles.Batch501.profile20042,MergedCutProfiles.Batch501.profile20056,MergedCutProfiles.Batch501.profile20057,MergedCutProfiles.Batch501.profile20067,MergedCutProfiles.Batch501.profile20068]⟩
theorem profilesValid3270 : retention3270.ProfilesValid := by
  change ∀ j : Fin 16, (retention3270.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch501.valid20059
  · exact MergedCutProfiles.Batch501.valid20060
  · exact MergedCutProfiles.Batch500.valid20030
  · exact MergedCutProfiles.Batch501.valid20061
  · exact MergedCutProfiles.Batch501.valid20062
  · exact MergedCutProfiles.Batch500.valid20034
  · exact MergedCutProfiles.Batch501.valid20063
  · exact MergedCutProfiles.Batch501.valid20064
  · exact MergedCutProfiles.Batch500.valid20038
  · exact MergedCutProfiles.Batch501.valid20065
  · exact MergedCutProfiles.Batch501.valid20066
  · exact MergedCutProfiles.Batch501.valid20042
  · exact MergedCutProfiles.Batch501.valid20056
  · exact MergedCutProfiles.Batch501.valid20057
  · exact MergedCutProfiles.Batch501.valid20067
  · exact MergedCutProfiles.Batch501.valid20068
theorem numericValid3270 : retention3270.NumericValid := by decide +kernel
def certificate3270 : RatCutBinCertificate := ⟨⟨retention3270,(2127361553394259841/1000000000000000000),(17460968802135489/125000000000000000),(7008338157695654169/500000000000000000),(573859666037521547669/500000000000000000),(109635854290746741/50000000000000000)⟩,(998399440572570273/1000000000000000000),(355187014947639869/1000000000000000000),(277150045704977809/1000000000000000000),(84775978809072027/500000000000000000)⟩
theorem valid3270 : certificate3270.Valid := by decide +kernel
theorem sound3270 : certificate3270.Sound := rat_cut_bin_certificate_sound certificate3270 profilesValid3270 numericValid3270 valid3270

def retention3271 : RatCutRetentionCertificate := ⟨(53/1000),(107/2000),(1090679135071614889/81643300718846859500),(217294741/200000000),(13/5),(1791466869205592867/800000000000000000),true,MergedCutProfiles.Batch501.profile20059,![MergedCutProfiles.Batch501.profile20059,MergedCutProfiles.Batch501.profile20060,MergedCutProfiles.Batch500.profile20030,MergedCutProfiles.Batch501.profile20061,MergedCutProfiles.Batch501.profile20062,MergedCutProfiles.Batch500.profile20034,MergedCutProfiles.Batch501.profile20063,MergedCutProfiles.Batch501.profile20064,MergedCutProfiles.Batch500.profile20038,MergedCutProfiles.Batch501.profile20069,MergedCutProfiles.Batch501.profile20054,MergedCutProfiles.Batch501.profile20042,MergedCutProfiles.Batch501.profile20070,MergedCutProfiles.Batch501.profile20071,MergedCutProfiles.Batch501.profile20072,MergedCutProfiles.Batch501.profile20068]⟩
theorem profilesValid3271 : retention3271.ProfilesValid := by
  change ∀ j : Fin 16, (retention3271.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch501.valid20059
  · exact MergedCutProfiles.Batch501.valid20060
  · exact MergedCutProfiles.Batch500.valid20030
  · exact MergedCutProfiles.Batch501.valid20061
  · exact MergedCutProfiles.Batch501.valid20062
  · exact MergedCutProfiles.Batch500.valid20034
  · exact MergedCutProfiles.Batch501.valid20063
  · exact MergedCutProfiles.Batch501.valid20064
  · exact MergedCutProfiles.Batch500.valid20038
  · exact MergedCutProfiles.Batch501.valid20069
  · exact MergedCutProfiles.Batch501.valid20054
  · exact MergedCutProfiles.Batch501.valid20042
  · exact MergedCutProfiles.Batch501.valid20070
  · exact MergedCutProfiles.Batch501.valid20071
  · exact MergedCutProfiles.Batch501.valid20072
  · exact MergedCutProfiles.Batch501.valid20068
theorem numericValid3271 : retention3271.NumericValid := by decide +kernel
def certificate3271 : RatCutBinCertificate := ⟨⟨retention3271,(2127361553394259841/1000000000000000000),(17460968802135489/125000000000000000),(7008338157695654169/500000000000000000),(573859666037521547669/500000000000000000),(436841767005696637/200000000000000000)⟩,(998399440572570273/1000000000000000000),(43086171570360607/125000000000000000),(9005350406433661/31250000000000000),(7449839695386681/40000000000000000)⟩
theorem valid3271 : certificate3271.Valid := by decide +kernel
theorem sound3271 : certificate3271.Sound := rat_cut_bin_certificate_sound certificate3271 profilesValid3271 numericValid3271 valid3271

def retention3272 : RatCutRetentionCertificate := ⟨(53/1000),(107/2000),(57888893985929453/4082165035942342975),(1090679135071614889/1000000000000000000),(13/5),(2863024067053901270741/1280000000000000000000),true,MergedCutProfiles.Batch501.profile20073,![MergedCutProfiles.Batch501.profile20073,MergedCutProfiles.Batch501.profile20074,MergedCutProfiles.Batch501.profile20075,MergedCutProfiles.Batch501.profile20076,MergedCutProfiles.Batch501.profile20077,MergedCutProfiles.Batch501.profile20078,MergedCutProfiles.Batch500.profile20036,MergedCutProfiles.Batch501.profile20079,MergedCutProfiles.Batch502.profile20080,MergedCutProfiles.Batch502.profile20081,MergedCutProfiles.Batch502.profile20082,MergedCutProfiles.Batch502.profile20083,MergedCutProfiles.Batch502.profile20084,MergedCutProfiles.Batch501.profile20067,MergedCutProfiles.Batch501.profile20068,MergedCutProfiles.Batch502.profile20085]⟩
theorem profilesValid3272 : retention3272.ProfilesValid := by
  change ∀ j : Fin 16, (retention3272.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch501.valid20073
  · exact MergedCutProfiles.Batch501.valid20074
  · exact MergedCutProfiles.Batch501.valid20075
  · exact MergedCutProfiles.Batch501.valid20076
  · exact MergedCutProfiles.Batch501.valid20077
  · exact MergedCutProfiles.Batch501.valid20078
  · exact MergedCutProfiles.Batch500.valid20036
  · exact MergedCutProfiles.Batch501.valid20079
  · exact MergedCutProfiles.Batch502.valid20080
  · exact MergedCutProfiles.Batch502.valid20081
  · exact MergedCutProfiles.Batch502.valid20082
  · exact MergedCutProfiles.Batch502.valid20083
  · exact MergedCutProfiles.Batch502.valid20084
  · exact MergedCutProfiles.Batch501.valid20067
  · exact MergedCutProfiles.Batch501.valid20068
  · exact MergedCutProfiles.Batch502.valid20085
theorem numericValid3272 : retention3272.NumericValid := by decide +kernel
def certificate3272 : RatCutBinCertificate := ⟨⟨retention3272,(2127361553394259841/1000000000000000000),(17460968802135489/125000000000000000),(7008338157695654169/500000000000000000),(573859666037521547669/500000000000000000),(87264512402589439/40000000000000000)⟩,(998399440572570273/1000000000000000000),(34451660506123067/100000000000000000),(57671048013078863/200000000000000000),(7454353991991219/40000000000000000)⟩
theorem valid3272 : certificate3272.Valid := by decide +kernel
theorem sound3272 : certificate3272.Sound := rat_cut_bin_certificate_sound certificate3272 profilesValid3272 numericValid3272 valid3272

def retention3273 : RatCutRetentionCertificate := ⟨(53/1000),(107/2000),(2490984522098977161/81643300718846859500),(57888893985929453/50000000000000000),(49/20),(137734586440425472201/64000000000000000000),true,MergedCutProfiles.Batch502.profile20086,![MergedCutProfiles.Batch502.profile20086,MergedCutProfiles.Batch502.profile20087,MergedCutProfiles.Batch502.profile20088,MergedCutProfiles.Batch502.profile20089,MergedCutProfiles.Batch502.profile20090,MergedCutProfiles.Batch502.profile20084,MergedCutProfiles.Batch501.profile20068,MergedCutProfiles.Batch502.profile20091,MergedCutProfiles.Batch502.profile20092,MergedCutProfiles.Batch502.profile20093,MergedCutProfiles.Batch502.profile20094,MergedCutProfiles.Batch502.profile20095,MergedCutProfiles.Batch502.profile20096,MergedCutProfiles.Batch502.profile20097,MergedCutProfiles.Batch502.profile20098,MergedCutProfiles.Batch502.profile20099]⟩
theorem profilesValid3273 : retention3273.ProfilesValid := by
  change ∀ j : Fin 16, (retention3273.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch502.valid20086
  · exact MergedCutProfiles.Batch502.valid20087
  · exact MergedCutProfiles.Batch502.valid20088
  · exact MergedCutProfiles.Batch502.valid20089
  · exact MergedCutProfiles.Batch502.valid20090
  · exact MergedCutProfiles.Batch502.valid20084
  · exact MergedCutProfiles.Batch501.valid20068
  · exact MergedCutProfiles.Batch502.valid20091
  · exact MergedCutProfiles.Batch502.valid20092
  · exact MergedCutProfiles.Batch502.valid20093
  · exact MergedCutProfiles.Batch502.valid20094
  · exact MergedCutProfiles.Batch502.valid20095
  · exact MergedCutProfiles.Batch502.valid20096
  · exact MergedCutProfiles.Batch502.valid20097
  · exact MergedCutProfiles.Batch502.valid20098
  · exact MergedCutProfiles.Batch502.valid20099
theorem numericValid3273 : retention3273.NumericValid := by decide +kernel
def certificate3273 : RatCutBinCertificate := ⟨⟨retention3273,(2127361553394259841/1000000000000000000),(17460968802135489/125000000000000000),(7008338157695654169/500000000000000000),(573859666037521547669/500000000000000000),(2100158445026897107/1000000000000000000)⟩,(998399440572570273/1000000000000000000),(348812083206540627/1000000000000000000),(283805365145727161/1000000000000000000),(23309141874497391/125000000000000000)⟩
theorem valid3273 : certificate3273.Valid := by decide +kernel
theorem sound3273 : certificate3273.Sound := rat_cut_bin_certificate_sound certificate3273 profilesValid3273 numericValid3273 valid3273

def retention3274 : RatCutRetentionCertificate := ⟨(53/1000),(107/2000),(21798695939619020263/81643300718846859500),(2490984522098977161/1000000000000000000),(3/2),(11843253979817233877305812751324370131/7971150470716726915200000000000000000),false,MergedCutProfiles.Batch502.profile20100,(fun _ => MergedCutProfiles.Batch502.profile20100)⟩
theorem profilesValid3274 : retention3274.ProfilesValid := by
  exact MergedCutProfiles.Batch502.valid20100
theorem numericValid3274 : retention3274.NumericValid := by decide +kernel
def certificate3274 : RatCutBinCertificate := ⟨⟨retention3274,(2127361553394259841/1000000000000000000),(17460968802135489/125000000000000000),(7008338157695654169/500000000000000000),(573859666037521547669/500000000000000000),(726981146032948981/500000000000000000)⟩,(998399440572570273/1000000000000000000),(194952140996313499/500000000000000000),(4857219780031497/20000000000000000),(37315770591700101/200000000000000000)⟩
theorem valid3274 : certificate3274.Valid := by decide +kernel
theorem sound3274 : certificate3274.Sound := rat_cut_bin_certificate_sound certificate3274 profilesValid3274 numericValid3274 valid3274

def retention3275 : RatCutRetentionCertificate := ⟨(53/1000),(107/2000),(19800809473254156847/40821650359423429750),(21798695939619020263/1000000000000000000),1,(88882641803545195389555812097323178547/87194783758476081052000000000000000000),false,MergedCutProfiles.Batch502.profile20101,(fun _ => MergedCutProfiles.Batch502.profile20101)⟩
theorem profilesValid3275 : retention3275.ProfilesValid := by
  exact MergedCutProfiles.Batch502.valid20101
theorem numericValid3275 : retention3275.NumericValid := by decide +kernel
def certificate3275 : RatCutBinCertificate := ⟨⟨retention3275,(2127361553394259841/1000000000000000000),(17460968802135489/125000000000000000),(7008338157695654169/500000000000000000),(573859666037521547669/500000000000000000),(249539073942431033/250000000000000000)⟩,(998399440572570273/1000000000000000000),(8805994790305607/20000000000000000),(49630549189964537/250000000000000000),(18916842045889139/100000000000000000)⟩
theorem valid3275 : certificate3275.Valid := by decide +kernel
theorem sound3275 : certificate3275.Sound := rat_cut_bin_certificate_sound certificate3275 profilesValid3275 numericValid3275 valid3275

def certificates : List RatCutBinCertificate := [certificate3264,certificate3265,certificate3266,certificate3267,certificate3268,certificate3269,certificate3270,certificate3271,certificate3272,certificate3273,certificate3274,certificate3275]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3264,List.forall_mem_cons.mpr ⟨sound3265,List.forall_mem_cons.mpr ⟨sound3266,List.forall_mem_cons.mpr ⟨sound3267,List.forall_mem_cons.mpr ⟨sound3268,List.forall_mem_cons.mpr ⟨sound3269,List.forall_mem_cons.mpr ⟨sound3270,List.forall_mem_cons.mpr ⟨sound3271,List.forall_mem_cons.mpr ⟨sound3272,List.forall_mem_cons.mpr ⟨sound3273,List.forall_mem_cons.mpr ⟨sound3274,List.forall_mem_cons.mpr ⟨sound3275,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch272
