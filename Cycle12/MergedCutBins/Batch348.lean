import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch225
import Cycle12.MergedCutProfiles.Batch399
import Cycle12.MergedCutProfiles.Batch400
import Cycle12.MergedCutProfiles.Batch402
import Cycle12.MergedCutProfiles.Batch522
import Cycle12.MergedCutProfiles.Batch523
import Cycle12.MergedCutProfiles.Batch524
import Cycle12.MergedCutProfiles.Batch525
import Cycle12.MergedCutProfiles.Batch626
import Cycle12.MergedCutProfiles.Batch627
import Cycle12.MergedCutProfiles.Batch628

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch348

def retention4176 : RatCutRetentionCertificate := ⟨(59/1000),(119/2000),(1/2),64,1,(102162675905069115123294709018435311/102400000000000000000000000000000000),false,MergedCutProfiles.Batch399.profile15991,(fun _ => MergedCutProfiles.Batch399.profile15991)⟩
theorem profilesValid4176 : retention4176.ProfilesValid := by
  exact MergedCutProfiles.Batch399.valid15991
theorem numericValid4176 : retention4176.NumericValid := by decide +kernel
def certificate4176 : RatCutBinCertificate := ⟨⟨retention4176,(1910495617183645427/1000000000000000000),(178859476136284067/1000000000000000000),(15581497503419628473/1000000000000000000),(995296067866497899553/250000000000000000),(97575185274046497/100000000000000000)⟩,(999604227260020369/1000000000000000000),(53257181727470299/1000000000000000000),(779687407462786399/1000000000000000000),(46816041205631663/62500000000000000)⟩
theorem valid4176 : certificate4176.Valid := by decide +kernel
theorem sound4176 : certificate4176.Sound := rat_cut_bin_certificate_sound certificate4176 profilesValid4176 numericValid4176 valid4176

def retention4177 : RatCutRetentionCertificate := ⟨(119/2000),(3/50),(761187697940497159/249739220709829794675),(746189293148217977/1000000000000000000),(15/4),(113527668236156928699726923383548970919/47756114761485950528000000000000000000),true,MergedCutProfiles.Batch626.profile25048,![MergedCutProfiles.Batch626.profile25048,MergedCutProfiles.Batch626.profile25049,MergedCutProfiles.Batch626.profile25050,MergedCutProfiles.Batch626.profile25051,MergedCutProfiles.Batch626.profile25052,MergedCutProfiles.Batch523.profile20947,MergedCutProfiles.Batch626.profile25053,MergedCutProfiles.Batch626.profile25054,MergedCutProfiles.Batch626.profile25055,MergedCutProfiles.Batch626.profile25056,MergedCutProfiles.Batch523.profile20921,MergedCutProfiles.Batch626.profile25057,MergedCutProfiles.Batch400.profile16011,MergedCutProfiles.Batch400.profile16026,MergedCutProfiles.Batch626.profile25058,MergedCutProfiles.Batch626.profile25059]⟩
theorem profilesValid4177 : retention4177.ProfilesValid := by
  change ∀ j : Fin 16, (retention4177.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch626.valid25048
  · exact MergedCutProfiles.Batch626.valid25049
  · exact MergedCutProfiles.Batch626.valid25050
  · exact MergedCutProfiles.Batch626.valid25051
  · exact MergedCutProfiles.Batch626.valid25052
  · exact MergedCutProfiles.Batch523.valid20947
  · exact MergedCutProfiles.Batch626.valid25053
  · exact MergedCutProfiles.Batch626.valid25054
  · exact MergedCutProfiles.Batch626.valid25055
  · exact MergedCutProfiles.Batch626.valid25056
  · exact MergedCutProfiles.Batch523.valid20921
  · exact MergedCutProfiles.Batch626.valid25057
  · exact MergedCutProfiles.Batch400.valid16011
  · exact MergedCutProfiles.Batch400.valid16026
  · exact MergedCutProfiles.Batch626.valid25058
  · exact MergedCutProfiles.Batch626.valid25059
theorem numericValid4177 : retention4177.NumericValid := by decide +kernel
def certificate4177 : RatCutBinCertificate := ⟨⟨retention4177,(257874923728195143/125000000000000000),(182428996879551849/1000000000000000000),(15723748980414544917/1000000000000000000),(1969422841286305343947/500000000000000000),(2287479920568150823/1000000000000000000)⟩,(99956988122453683/100000000000000000),(48005900267929091/100000000000000000),(41912847895798149/250000000000000000),(41959733602250297/500000000000000000)⟩
theorem valid4177 : certificate4177.Valid := by decide +kernel
theorem sound4177 : certificate4177.Sound := rat_cut_bin_certificate_sound certificate4177 profilesValid4177 numericValid4177 valid4177

def retention4178 : RatCutRetentionCertificate := ⟨(119/2000),(3/50),(14746533240000000/3329856276131063929),(761187697940497159/1000000000000000000),(37/10),(3025211649917541855747/1280000000000000000000),true,MergedCutProfiles.Batch626.profile25060,![MergedCutProfiles.Batch626.profile25060,MergedCutProfiles.Batch626.profile25050,MergedCutProfiles.Batch626.profile25061,MergedCutProfiles.Batch626.profile25062,MergedCutProfiles.Batch626.profile25063,MergedCutProfiles.Batch626.profile25064,MergedCutProfiles.Batch626.profile25065,MergedCutProfiles.Batch626.profile25066,MergedCutProfiles.Batch626.profile25067,MergedCutProfiles.Batch626.profile25068,MergedCutProfiles.Batch626.profile25059,MergedCutProfiles.Batch626.profile25069,MergedCutProfiles.Batch626.profile25070,MergedCutProfiles.Batch626.profile25071,MergedCutProfiles.Batch626.profile25072,MergedCutProfiles.Batch522.profile20911]⟩
theorem profilesValid4178 : retention4178.ProfilesValid := by
  change ∀ j : Fin 16, (retention4178.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch626.valid25060
  · exact MergedCutProfiles.Batch626.valid25050
  · exact MergedCutProfiles.Batch626.valid25061
  · exact MergedCutProfiles.Batch626.valid25062
  · exact MergedCutProfiles.Batch626.valid25063
  · exact MergedCutProfiles.Batch626.valid25064
  · exact MergedCutProfiles.Batch626.valid25065
  · exact MergedCutProfiles.Batch626.valid25066
  · exact MergedCutProfiles.Batch626.valid25067
  · exact MergedCutProfiles.Batch626.valid25068
  · exact MergedCutProfiles.Batch626.valid25059
  · exact MergedCutProfiles.Batch626.valid25069
  · exact MergedCutProfiles.Batch626.valid25070
  · exact MergedCutProfiles.Batch626.valid25071
  · exact MergedCutProfiles.Batch626.valid25072
  · exact MergedCutProfiles.Batch522.valid20911
theorem numericValid4178 : retention4178.NumericValid := by decide +kernel
def certificate4178 : RatCutBinCertificate := ⟨⟨retention4178,(257874923728195143/125000000000000000),(182428996879551849/1000000000000000000),(15723748980414544917/1000000000000000000),(1969422841286305343947/500000000000000000),(2274884944512726303/1000000000000000000)⟩,(99956988122453683/100000000000000000),(477245522033597653/1000000000000000000),(16972430414856959/100000000000000000),(85609266926095517/1000000000000000000)⟩
theorem valid4178 : certificate4178.Valid := by decide +kernel
theorem sound4178 : certificate4178.Sound := rat_cut_bin_certificate_sound certificate4178 profilesValid4178 numericValid4178 valid4178

def retention4179 : RatCutRetentionCertificate := ⟨(119/2000),(3/50),(499141779792896124/83246406903276598225),(1105989993/1000000000),(27/10),(18626771219618183923/8000000000000000000),true,MergedCutProfiles.Batch626.profile25049,![MergedCutProfiles.Batch626.profile25049,MergedCutProfiles.Batch626.profile25051,MergedCutProfiles.Batch626.profile25062,MergedCutProfiles.Batch626.profile25054,MergedCutProfiles.Batch626.profile25073,MergedCutProfiles.Batch626.profile25057,MergedCutProfiles.Batch626.profile25074,MergedCutProfiles.Batch626.profile25075,MergedCutProfiles.Batch626.profile25069,MergedCutProfiles.Batch626.profile25076,MergedCutProfiles.Batch626.profile25072,MergedCutProfiles.Batch626.profile25077,MergedCutProfiles.Batch626.profile25078,MergedCutProfiles.Batch523.profile20924,MergedCutProfiles.Batch626.profile25079,MergedCutProfiles.Batch627.profile25080]⟩
theorem profilesValid4179 : retention4179.ProfilesValid := by
  change ∀ j : Fin 16, (retention4179.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch626.valid25049
  · exact MergedCutProfiles.Batch626.valid25051
  · exact MergedCutProfiles.Batch626.valid25062
  · exact MergedCutProfiles.Batch626.valid25054
  · exact MergedCutProfiles.Batch626.valid25073
  · exact MergedCutProfiles.Batch626.valid25057
  · exact MergedCutProfiles.Batch626.valid25074
  · exact MergedCutProfiles.Batch626.valid25075
  · exact MergedCutProfiles.Batch626.valid25069
  · exact MergedCutProfiles.Batch626.valid25076
  · exact MergedCutProfiles.Batch626.valid25072
  · exact MergedCutProfiles.Batch626.valid25077
  · exact MergedCutProfiles.Batch626.valid25078
  · exact MergedCutProfiles.Batch523.valid20924
  · exact MergedCutProfiles.Batch626.valid25079
  · exact MergedCutProfiles.Batch627.valid25080
theorem numericValid4179 : retention4179.NumericValid := by decide +kernel
def certificate4179 : RatCutBinCertificate := ⟨⟨retention4179,(257874923728195143/125000000000000000),(182428996879551849/1000000000000000000),(15723748980414544917/1000000000000000000),(1969422841286305343947/500000000000000000),(1131860194429292731/500000000000000000)⟩,(99956988122453683/100000000000000000),(394318032504257357/1000000000000000000),(119364497132986099/500000000000000000),(39049328315478811/250000000000000000)⟩
theorem valid4179 : certificate4179.Valid := by decide +kernel
theorem sound4179 : certificate4179.Sound := rat_cut_bin_certificate_sound certificate4179 profilesValid4179 numericValid4179 valid4179

def retention4180 : RatCutRetentionCertificate := ⟨(119/2000),(3/50),(7328158339548785648/83246406903276598225),(374356334844672093/250000000000000000),(43/20),(626967416150515386021/320000000000000000000),true,MergedCutProfiles.Batch523.profile20937,![MergedCutProfiles.Batch523.profile20937,MergedCutProfiles.Batch523.profile20941,MergedCutProfiles.Batch627.profile25081,MergedCutProfiles.Batch524.profile20962,MergedCutProfiles.Batch627.profile25082,MergedCutProfiles.Batch627.profile25083,MergedCutProfiles.Batch627.profile25084,MergedCutProfiles.Batch627.profile25085,MergedCutProfiles.Batch627.profile25086,MergedCutProfiles.Batch627.profile25087,MergedCutProfiles.Batch627.profile25088,MergedCutProfiles.Batch627.profile25089,MergedCutProfiles.Batch627.profile25090,MergedCutProfiles.Batch627.profile25091,MergedCutProfiles.Batch627.profile25092,MergedCutProfiles.Batch627.profile25093]⟩
theorem profilesValid4180 : retention4180.ProfilesValid := by
  change ∀ j : Fin 16, (retention4180.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch523.valid20937
  · exact MergedCutProfiles.Batch523.valid20941
  · exact MergedCutProfiles.Batch627.valid25081
  · exact MergedCutProfiles.Batch524.valid20962
  · exact MergedCutProfiles.Batch627.valid25082
  · exact MergedCutProfiles.Batch627.valid25083
  · exact MergedCutProfiles.Batch627.valid25084
  · exact MergedCutProfiles.Batch627.valid25085
  · exact MergedCutProfiles.Batch627.valid25086
  · exact MergedCutProfiles.Batch627.valid25087
  · exact MergedCutProfiles.Batch627.valid25088
  · exact MergedCutProfiles.Batch627.valid25089
  · exact MergedCutProfiles.Batch627.valid25090
  · exact MergedCutProfiles.Batch627.valid25091
  · exact MergedCutProfiles.Batch627.valid25092
  · exact MergedCutProfiles.Batch627.valid25093
theorem numericValid4180 : retention4180.NumericValid := by decide +kernel
def certificate4180 : RatCutBinCertificate := ⟨⟨retention4180,(257874923728195143/125000000000000000),(182428996879551849/1000000000000000000),(15723748980414544917/1000000000000000000),(1969422841286305343947/500000000000000000),(1907811778037618829/1000000000000000000)⟩,(99956988122453683/100000000000000000),(102371039079085241/250000000000000000),(56226003618008259/250000000000000000),(156370122256408479/1000000000000000000)⟩
theorem valid4180 : certificate4180.Valid := by decide +kernel
theorem sound4180 : certificate4180.Sound := rat_cut_bin_certificate_sound certificate4180 profilesValid4180 numericValid4180 valid4180

def retention4181 : RatCutRetentionCertificate := ⟨(119/2000),(3/50),(2560000000000000000/9989568828393191787),(1374029688665397309/62500000000000000),1,(4686217658468078200276090387190497601/3140639288378050992000000000000000000),false,MergedCutProfiles.Batch627.profile25094,(fun _ => MergedCutProfiles.Batch627.profile25094)⟩
theorem profilesValid4181 : retention4181.ProfilesValid := by
  exact MergedCutProfiles.Batch627.valid25094
theorem numericValid4181 : retention4181.NumericValid := by decide +kernel
def certificate4181 : RatCutBinCertificate := ⟨⟨retention4181,(257874923728195143/125000000000000000),(182428996879551849/1000000000000000000),(15723748980414544917/1000000000000000000),(1969422841286305343947/500000000000000000),(183523372179952753/125000000000000000)⟩,(99956988122453683/100000000000000000),(83075492790452247/250000000000000000),(301587689117830533/1000000000000000000),(414883852892126311/1000000000000000000)⟩
theorem valid4181 : certificate4181.Valid := by decide +kernel
theorem sound4181 : certificate4181.Sound := rat_cut_bin_certificate_sound certificate4181 profilesValid4181 numericValid4181 valid4181

def retention4182 : RatCutRetentionCertificate := ⟨(119/2000),(3/50),(1/2),64,1,(15962965249201187188825037783071732831/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch402.profile16087,(fun _ => MergedCutProfiles.Batch402.profile16087)⟩
theorem profilesValid4182 : retention4182.ProfilesValid := by
  exact MergedCutProfiles.Batch402.valid16087
theorem numericValid4182 : retention4182.NumericValid := by decide +kernel
def certificate4182 : RatCutBinCertificate := ⟨⟨retention4182,(257874923728195143/125000000000000000),(182428996879551849/1000000000000000000),(15723748980414544917/1000000000000000000),(1969422841286305343947/500000000000000000),(973750121396667937/1000000000000000000)⟩,(99956988122453683/100000000000000000),(486578588174516941/1000000000000000000),(162911110240430899/1000000000000000000),(31237870368067337/200000000000000000)⟩
theorem valid4182 : certificate4182.Valid := by decide +kernel
theorem sound4182 : certificate4182.Sound := rat_cut_bin_certificate_sound certificate4182 profilesValid4182 numericValid4182 valid4182

def retention4183 : RatCutRetentionCertificate := ⟨(119/2000),(3/50),(2560000000000000000/9989568828393191787),(24558981787317954221/1000000000000000000),1,(5244642106550569355921778095212187763/3508425969616850603000000000000000000),false,MergedCutProfiles.Batch627.profile25094,(fun _ => MergedCutProfiles.Batch627.profile25094)⟩
theorem profilesValid4183 : retention4183.ProfilesValid := by
  exact MergedCutProfiles.Batch627.valid25094
theorem numericValid4183 : retention4183.NumericValid := by decide +kernel
def certificate4183 : RatCutBinCertificate := ⟨⟨retention4183,(239172704353195143/125000000000000000),(182428996879551849/1000000000000000000),(15723748980414544917/1000000000000000000),(1969422841286305343947/500000000000000000),(736335523083852317/500000000000000000)⟩,(999601078033274921/1000000000000000000),(2196673782769731/62500000000000000),(829434243067810219/1000000000000000000),(287977155326445859/250000000000000000)⟩
theorem valid4183 : certificate4183.Valid := by decide +kernel
theorem sound4183 : certificate4183.Sound := rat_cut_bin_certificate_sound certificate4183 profilesValid4183 numericValid4183 valid4183

def retention4184 : RatCutRetentionCertificate := ⟨(119/2000),(3/50),(1/2),64,1,(15962965249201187188825037783071732831/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch402.profile16087,(fun _ => MergedCutProfiles.Batch402.profile16087)⟩
theorem profilesValid4184 : retention4184.ProfilesValid := by
  exact MergedCutProfiles.Batch402.valid16087
theorem numericValid4184 : retention4184.NumericValid := by decide +kernel
def certificate4184 : RatCutBinCertificate := ⟨⟨retention4184,(239172704353195143/125000000000000000),(182428996879551849/1000000000000000000),(15723748980414544917/1000000000000000000),(1969422841286305343947/500000000000000000),(975486007459623563/1000000000000000000)⟩,(999601078033274921/1000000000000000000),(53060367497186361/1000000000000000000),(780208750551992273/1000000000000000000),(93669245077555389/125000000000000000)⟩
theorem valid4184 : certificate4184.Valid := by decide +kernel
theorem sound4184 : certificate4184.Sound := rat_cut_bin_certificate_sound certificate4184 profilesValid4184 numericValid4184 valid4184

def retention4185 : RatCutRetentionCertificate := ⟨(3/50),(121/2000),(253524178552715898/81625649514144777227),(376521057256508759/500000000000000000),(15/4),(304810827827107928683/128000000000000000000),true,MergedCutProfiles.Batch627.profile25095,![MergedCutProfiles.Batch627.profile25095,MergedCutProfiles.Batch627.profile25096,MergedCutProfiles.Batch627.profile25097,MergedCutProfiles.Batch627.profile25098,MergedCutProfiles.Batch627.profile25099,MergedCutProfiles.Batch627.profile25100,MergedCutProfiles.Batch627.profile25101,MergedCutProfiles.Batch627.profile25102,MergedCutProfiles.Batch627.profile25103,MergedCutProfiles.Batch627.profile25104,MergedCutProfiles.Batch627.profile25105,MergedCutProfiles.Batch627.profile25106,MergedCutProfiles.Batch402.profile16107,MergedCutProfiles.Batch524.profile20977,MergedCutProfiles.Batch627.profile25107,MergedCutProfiles.Batch627.profile25108]⟩
theorem profilesValid4185 : retention4185.ProfilesValid := by
  change ∀ j : Fin 16, (retention4185.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch627.valid25095
  · exact MergedCutProfiles.Batch627.valid25096
  · exact MergedCutProfiles.Batch627.valid25097
  · exact MergedCutProfiles.Batch627.valid25098
  · exact MergedCutProfiles.Batch627.valid25099
  · exact MergedCutProfiles.Batch627.valid25100
  · exact MergedCutProfiles.Batch627.valid25101
  · exact MergedCutProfiles.Batch627.valid25102
  · exact MergedCutProfiles.Batch627.valid25103
  · exact MergedCutProfiles.Batch627.valid25104
  · exact MergedCutProfiles.Batch627.valid25105
  · exact MergedCutProfiles.Batch627.valid25106
  · exact MergedCutProfiles.Batch402.valid16107
  · exact MergedCutProfiles.Batch524.valid20977
  · exact MergedCutProfiles.Batch627.valid25107
  · exact MergedCutProfiles.Batch627.valid25108
theorem numericValid4185 : retention4185.NumericValid := by decide +kernel
def certificate4185 : RatCutBinCertificate := ⟨⟨retention4185,(2070374835686652571/1000000000000000000),(93024059904071007/500000000000000000),(793399026498316747/50000000000000000),(3897625990151809333379/1000000000000000000),(1145151596860069861/500000000000000000)⟩,(99956567334231509/100000000000000000),(471572934506832251/1000000000000000000),(86977138677321823/500000000000000000),(8730457911031457/100000000000000000)⟩
theorem valid4185 : certificate4185.Valid := by decide +kernel
theorem sound4185 : certificate4185.Sound := rat_cut_bin_certificate_sound certificate4185 profilesValid4185 numericValid4185 valid4185

def retention4186 : RatCutRetentionCertificate := ⟨(3/50),(121/2000),(372560442000000000/81625649514144777227),(380286267829073847/500000000000000000),(37/10),(1512090895834243750131/640000000000000000000),true,MergedCutProfiles.Batch627.profile25109,![MergedCutProfiles.Batch627.profile25109,MergedCutProfiles.Batch627.profile25110,MergedCutProfiles.Batch627.profile25111,MergedCutProfiles.Batch627.profile25100,MergedCutProfiles.Batch627.profile25112,MergedCutProfiles.Batch627.profile25113,MergedCutProfiles.Batch627.profile25114,MergedCutProfiles.Batch525.profile21002,MergedCutProfiles.Batch627.profile25115,MergedCutProfiles.Batch627.profile25116,MergedCutProfiles.Batch627.profile25108,MergedCutProfiles.Batch627.profile25117,MergedCutProfiles.Batch627.profile25118,MergedCutProfiles.Batch627.profile25119,MergedCutProfiles.Batch225.profile9017,MergedCutProfiles.Batch225.profile9033]⟩
theorem profilesValid4186 : retention4186.ProfilesValid := by
  change ∀ j : Fin 16, (retention4186.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch627.valid25109
  · exact MergedCutProfiles.Batch627.valid25110
  · exact MergedCutProfiles.Batch627.valid25111
  · exact MergedCutProfiles.Batch627.valid25100
  · exact MergedCutProfiles.Batch627.valid25112
  · exact MergedCutProfiles.Batch627.valid25113
  · exact MergedCutProfiles.Batch627.valid25114
  · exact MergedCutProfiles.Batch525.valid21002
  · exact MergedCutProfiles.Batch627.valid25115
  · exact MergedCutProfiles.Batch627.valid25116
  · exact MergedCutProfiles.Batch627.valid25108
  · exact MergedCutProfiles.Batch627.valid25117
  · exact MergedCutProfiles.Batch627.valid25118
  · exact MergedCutProfiles.Batch627.valid25119
  · exact MergedCutProfiles.Batch225.valid9017
  · exact MergedCutProfiles.Batch225.valid9033
theorem numericValid4186 : retention4186.NumericValid := by decide +kernel
def certificate4186 : RatCutBinCertificate := ⟨⟨retention4186,(2070374835686652571/1000000000000000000),(93024059904071007/500000000000000000),(793399026498316747/50000000000000000),(3897625990151809333379/1000000000000000000),(454564874552570409/200000000000000000)⟩,(99956567334231509/100000000000000000),(236254716980179737/500000000000000000),(5414101924253289/31250000000000000),(87310165755590209/1000000000000000000)⟩
theorem valid4186 : certificate4186.Valid := by decide +kernel
theorem sound4186 : certificate4186.Sound := rat_cut_bin_certificate_sound certificate4186 profilesValid4186 numericValid4186 valid4186

def retention4187 : RatCutRetentionCertificate := ⟨(3/50),(121/2000),(1899796253774067485/244876948542434331681),(558840663/500000000),(53/20),(9236349029067085927/4000000000000000000),true,MergedCutProfiles.Batch628.profile25120,![MergedCutProfiles.Batch628.profile25120,MergedCutProfiles.Batch627.profile25099,MergedCutProfiles.Batch628.profile25121,MergedCutProfiles.Batch627.profile25104,MergedCutProfiles.Batch628.profile25122,MergedCutProfiles.Batch627.profile25107,MergedCutProfiles.Batch627.profile25117,MergedCutProfiles.Batch628.profile25123,MergedCutProfiles.Batch524.profile20990,MergedCutProfiles.Batch628.profile25124,MergedCutProfiles.Batch628.profile25125,MergedCutProfiles.Batch628.profile25126,MergedCutProfiles.Batch628.profile25127,MergedCutProfiles.Batch525.profile21005,MergedCutProfiles.Batch524.profile20979,MergedCutProfiles.Batch628.profile25128]⟩
theorem profilesValid4187 : retention4187.ProfilesValid := by
  change ∀ j : Fin 16, (retention4187.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch628.valid25120
  · exact MergedCutProfiles.Batch627.valid25099
  · exact MergedCutProfiles.Batch628.valid25121
  · exact MergedCutProfiles.Batch627.valid25104
  · exact MergedCutProfiles.Batch628.valid25122
  · exact MergedCutProfiles.Batch627.valid25107
  · exact MergedCutProfiles.Batch627.valid25117
  · exact MergedCutProfiles.Batch628.valid25123
  · exact MergedCutProfiles.Batch524.valid20990
  · exact MergedCutProfiles.Batch628.valid25124
  · exact MergedCutProfiles.Batch628.valid25125
  · exact MergedCutProfiles.Batch628.valid25126
  · exact MergedCutProfiles.Batch628.valid25127
  · exact MergedCutProfiles.Batch525.valid21005
  · exact MergedCutProfiles.Batch524.valid20979
  · exact MergedCutProfiles.Batch628.valid25128
theorem numericValid4187 : retention4187.NumericValid := by decide +kernel
def certificate4187 : RatCutBinCertificate := ⟨⟨retention4187,(2070374835686652571/1000000000000000000),(93024059904071007/500000000000000000),(793399026498316747/50000000000000000),(3897625990151809333379/1000000000000000000),(561189613210907673/250000000000000000)⟩,(99956567334231509/100000000000000000),(24462045130726763/62500000000000000),(241462012415726093/1000000000000000000),(79483977002274847/500000000000000000)⟩
theorem valid4187 : certificate4187.Valid := by decide +kernel
theorem sound4187 : certificate4187.Sound := rat_cut_bin_certificate_sound certificate4187 profilesValid4187 numericValid4187 valid4187

def certificates : List RatCutBinCertificate := [certificate4176,certificate4177,certificate4178,certificate4179,certificate4180,certificate4181,certificate4182,certificate4183,certificate4184,certificate4185,certificate4186,certificate4187]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4176,List.forall_mem_cons.mpr ⟨sound4177,List.forall_mem_cons.mpr ⟨sound4178,List.forall_mem_cons.mpr ⟨sound4179,List.forall_mem_cons.mpr ⟨sound4180,List.forall_mem_cons.mpr ⟨sound4181,List.forall_mem_cons.mpr ⟨sound4182,List.forall_mem_cons.mpr ⟨sound4183,List.forall_mem_cons.mpr ⟨sound4184,List.forall_mem_cons.mpr ⟨sound4185,List.forall_mem_cons.mpr ⟨sound4186,List.forall_mem_cons.mpr ⟨sound4187,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch348
