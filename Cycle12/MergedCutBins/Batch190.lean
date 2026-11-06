import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch350
import Cycle12.MergedCutProfiles.Batch351
import Cycle12.MergedCutProfiles.Batch352
import Cycle12.MergedCutProfiles.Batch353

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch190

def retention2280 : RatCutRetentionCertificate := ⟨(39/1000),(1/25),(1054712886456046123/63019021664182630395),(1046173503/1000000000),(53/20),(1760588796948490351/800000000000000000),true,MergedCutProfiles.Batch351.profile14071,![MergedCutProfiles.Batch351.profile14071,MergedCutProfiles.Batch351.profile14058,MergedCutProfiles.Batch351.profile14059,MergedCutProfiles.Batch351.profile14072,MergedCutProfiles.Batch351.profile14073,MergedCutProfiles.Batch351.profile14074,MergedCutProfiles.Batch351.profile14048,MergedCutProfiles.Batch350.profile14036,MergedCutProfiles.Batch351.profile14075,MergedCutProfiles.Batch351.profile14076,MergedCutProfiles.Batch351.profile14077,MergedCutProfiles.Batch351.profile14078,MergedCutProfiles.Batch351.profile14079,MergedCutProfiles.Batch352.profile14080,MergedCutProfiles.Batch352.profile14081,MergedCutProfiles.Batch352.profile14082]⟩
theorem profilesValid2280 : retention2280.ProfilesValid := by
  change ∀ j : Fin 16, (retention2280.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch351.valid14071
  · exact MergedCutProfiles.Batch351.valid14058
  · exact MergedCutProfiles.Batch351.valid14059
  · exact MergedCutProfiles.Batch351.valid14072
  · exact MergedCutProfiles.Batch351.valid14073
  · exact MergedCutProfiles.Batch351.valid14074
  · exact MergedCutProfiles.Batch351.valid14048
  · exact MergedCutProfiles.Batch350.valid14036
  · exact MergedCutProfiles.Batch351.valid14075
  · exact MergedCutProfiles.Batch351.valid14076
  · exact MergedCutProfiles.Batch351.valid14077
  · exact MergedCutProfiles.Batch351.valid14078
  · exact MergedCutProfiles.Batch351.valid14079
  · exact MergedCutProfiles.Batch352.valid14080
  · exact MergedCutProfiles.Batch352.valid14081
  · exact MergedCutProfiles.Batch352.valid14082
theorem numericValid2280 : retention2280.NumericValid := by decide +kernel
def certificate2280 : RatCutBinCertificate := ⟨⟨retention2280,(127449921297576803/62500000000000000),(1140020255178431/15625000000000000),(11180342851196610183/1000000000000000000),(708361321849244584829/1000000000000000000),(270683721306044183/125000000000000000)⟩,(99731946768931759/100000000000000000),(45858175075367133/125000000000000000),(132626485884741007/500000000000000000),(83445045993911161/500000000000000000)⟩
theorem valid2280 : certificate2280.Valid := by decide +kernel
theorem sound2280 : certificate2280.Sound := rat_cut_bin_certificate_sound certificate2280 profilesValid2280 numericValid2280 valid2280

def retention2281 : RatCutRetentionCertificate := ⟨(39/1000),(1/25),(392236594079673576/21006340554727543465),(1054712886456046123/1000000000000000000),(53/20),(2808484255909015184403/1280000000000000000000),true,MergedCutProfiles.Batch352.profile14083,![MergedCutProfiles.Batch352.profile14083,MergedCutProfiles.Batch352.profile14084,MergedCutProfiles.Batch352.profile14085,MergedCutProfiles.Batch352.profile14086,MergedCutProfiles.Batch352.profile14087,MergedCutProfiles.Batch352.profile14088,MergedCutProfiles.Batch352.profile14089,MergedCutProfiles.Batch351.profile14064,MergedCutProfiles.Batch351.profile14076,MergedCutProfiles.Batch352.profile14090,MergedCutProfiles.Batch351.profile14054,MergedCutProfiles.Batch352.profile14091,MergedCutProfiles.Batch352.profile14092,MergedCutProfiles.Batch352.profile14093,MergedCutProfiles.Batch352.profile14094,MergedCutProfiles.Batch352.profile14095]⟩
theorem profilesValid2281 : retention2281.ProfilesValid := by
  change ∀ j : Fin 16, (retention2281.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch352.valid14083
  · exact MergedCutProfiles.Batch352.valid14084
  · exact MergedCutProfiles.Batch352.valid14085
  · exact MergedCutProfiles.Batch352.valid14086
  · exact MergedCutProfiles.Batch352.valid14087
  · exact MergedCutProfiles.Batch352.valid14088
  · exact MergedCutProfiles.Batch352.valid14089
  · exact MergedCutProfiles.Batch351.valid14064
  · exact MergedCutProfiles.Batch351.valid14076
  · exact MergedCutProfiles.Batch352.valid14090
  · exact MergedCutProfiles.Batch351.valid14054
  · exact MergedCutProfiles.Batch352.valid14091
  · exact MergedCutProfiles.Batch352.valid14092
  · exact MergedCutProfiles.Batch352.valid14093
  · exact MergedCutProfiles.Batch352.valid14094
  · exact MergedCutProfiles.Batch352.valid14095
theorem numericValid2281 : retention2281.NumericValid := by decide +kernel
def certificate2281 : RatCutBinCertificate := ⟨⟨retention2281,(127449921297576803/62500000000000000),(1140020255178431/15625000000000000),(11180342851196610183/1000000000000000000),(708361321849244584829/1000000000000000000),(2158862109799407361/1000000000000000000)⟩,(99731946768931759/100000000000000000),(183344918633731099/500000000000000000),(33178630431193763/125000000000000000),(3338286791291981/20000000000000000)⟩
theorem valid2281 : certificate2281.Valid := by decide +kernel
theorem sound2281 : certificate2281.Sound := rat_cut_bin_certificate_sound certificate2281 profilesValid2281 numericValid2281 valid2281

def retention2282 : RatCutRetentionCertificate := ⟨(39/1000),(1/25),(3246754788149231299/63019021664182630395),(147088722779877591/125000000000000000),(12/5),(82138250246169833641/40000000000000000000),true,MergedCutProfiles.Batch352.profile14096,![MergedCutProfiles.Batch352.profile14096,MergedCutProfiles.Batch351.profile14047,MergedCutProfiles.Batch352.profile14097,MergedCutProfiles.Batch351.profile14054,MergedCutProfiles.Batch352.profile14098,MergedCutProfiles.Batch352.profile14099,MergedCutProfiles.Batch352.profile14100,MergedCutProfiles.Batch352.profile14101,MergedCutProfiles.Batch352.profile14102,MergedCutProfiles.Batch352.profile14103,MergedCutProfiles.Batch352.profile14104,MergedCutProfiles.Batch352.profile14105,MergedCutProfiles.Batch352.profile14106,MergedCutProfiles.Batch352.profile14107,MergedCutProfiles.Batch352.profile14108,MergedCutProfiles.Batch352.profile14109]⟩
theorem profilesValid2282 : retention2282.ProfilesValid := by
  change ∀ j : Fin 16, (retention2282.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch352.valid14096
  · exact MergedCutProfiles.Batch351.valid14047
  · exact MergedCutProfiles.Batch352.valid14097
  · exact MergedCutProfiles.Batch351.valid14054
  · exact MergedCutProfiles.Batch352.valid14098
  · exact MergedCutProfiles.Batch352.valid14099
  · exact MergedCutProfiles.Batch352.valid14100
  · exact MergedCutProfiles.Batch352.valid14101
  · exact MergedCutProfiles.Batch352.valid14102
  · exact MergedCutProfiles.Batch352.valid14103
  · exact MergedCutProfiles.Batch352.valid14104
  · exact MergedCutProfiles.Batch352.valid14105
  · exact MergedCutProfiles.Batch352.valid14106
  · exact MergedCutProfiles.Batch352.valid14107
  · exact MergedCutProfiles.Batch352.valid14108
  · exact MergedCutProfiles.Batch352.valid14109
theorem numericValid2282 : retention2282.NumericValid := by decide +kernel
def certificate2282 : RatCutBinCertificate := ⟨⟨retention2282,(127449921297576803/62500000000000000),(1140020255178431/15625000000000000),(11180342851196610183/1000000000000000000),(708361321849244584829/1000000000000000000),(2021517054585711317/1000000000000000000)⟩,(99731946768931759/100000000000000000),(373990707208457999/1000000000000000000),(258177419329896159/1000000000000000000),(166985738423519961/1000000000000000000)⟩
theorem valid2282 : certificate2282.Valid := by decide +kernel
theorem sound2282 : certificate2282.Sound := rat_cut_bin_certificate_sound certificate2282 profilesValid2282 numericValid2282 valid2282

def retention2283 : RatCutRetentionCertificate := ⟨(39/1000),(1/25),(4258132098416474027/12603804332836526079),(3246754788149231299/1000000000000000000),(13/10),(1720131868134551387361454417416696794671/1298701915259692519600000000000000000000),false,MergedCutProfiles.Batch352.profile14110,(fun _ => MergedCutProfiles.Batch352.profile14110)⟩
theorem profilesValid2283 : retention2283.ProfilesValid := by
  exact MergedCutProfiles.Batch352.valid14110
theorem numericValid2283 : retention2283.NumericValid := by decide +kernel
def certificate2283 : RatCutBinCertificate := ⟨⟨retention2283,(127449921297576803/62500000000000000),(1140020255178431/15625000000000000),(11180342851196610183/1000000000000000000),(708361321849244584829/1000000000000000000),(653600358796472539/500000000000000000)⟩,(99731946768931759/100000000000000000),(53528051804102437/125000000000000000),(104297260162792361/500000000000000000),(168891104767997901/1000000000000000000)⟩
theorem valid2283 : certificate2283.Valid := by decide +kernel
theorem sound2283 : certificate2283.Sound := rat_cut_bin_certificate_sound certificate2283 profilesValid2283 numericValid2283 valid2283

def retention2284 : RatCutRetentionCertificate := ⟨(39/1000),(1/25),(30766632538259193683/63019021664182630395),(4258132098416474027/200000000000000000),1,(86253698641807447538460761336932610691/85162641968329480540000000000000000000),false,MergedCutProfiles.Batch352.profile14111,(fun _ => MergedCutProfiles.Batch352.profile14111)⟩
theorem profilesValid2284 : retention2284.ProfilesValid := by
  exact MergedCutProfiles.Batch352.valid14111
theorem numericValid2284 : retention2284.NumericValid := by decide +kernel
def certificate2284 : RatCutBinCertificate := ⟨⟨retention2284,(127449921297576803/62500000000000000),(1140020255178431/15625000000000000),(11180342851196610183/1000000000000000000),(708361321849244584829/1000000000000000000),(999503867310544911/1000000000000000000)⟩,(99731946768931759/100000000000000000),(465459131673125173/1000000000000000000),(89294841462831531/500000000000000000),(21253547666606737/125000000000000000)⟩
theorem valid2284 : certificate2284.Valid := by decide +kernel
theorem sound2284 : certificate2284.Sound := rat_cut_bin_certificate_sound certificate2284 profilesValid2284 numericValid2284 valid2284

def retention2285 : RatCutRetentionCertificate := ⟨(39/1000),(1/25),(31385041852278203477/63019021664182630395),(30766632538259193683/1000000000000000000),1,(24545644281278217422933579139085526063/24613306030607354946400000000000000000),false,MergedCutProfiles.Batch352.profile14112,(fun _ => MergedCutProfiles.Batch352.profile14112)⟩
theorem profilesValid2285 : retention2285.ProfilesValid := by
  exact MergedCutProfiles.Batch352.valid14112
theorem numericValid2285 : retention2285.NumericValid := by decide +kernel
def certificate2285 : RatCutBinCertificate := ⟨⟨retention2285,(127449921297576803/62500000000000000),(1140020255178431/15625000000000000),(11180342851196610183/1000000000000000000),(708361321849244584829/1000000000000000000),(245985862361621937/250000000000000000)⟩,(99731946768931759/100000000000000000),(11687370090517547/25000000000000000),(1416299180583577/8000000000000000),(10521000853002299/62500000000000000)⟩
theorem valid2285 : certificate2285.Valid := by decide +kernel
theorem sound2285 : certificate2285.Sound := rat_cut_bin_certificate_sound certificate2285 profilesValid2285 numericValid2285 valid2285

def retention2286 : RatCutRetentionCertificate := ⟨(39/1000),(1/25),(1/2),(31385041852278203477/1000000000000000000),1,(124726555556668330563802373034795347907/125540167409112813908000000000000000000),false,MergedCutProfiles.Batch352.profile14113,(fun _ => MergedCutProfiles.Batch352.profile14113)⟩
theorem profilesValid2286 : retention2286.ProfilesValid := by
  exact MergedCutProfiles.Batch352.valid14113
theorem numericValid2286 : retention2286.NumericValid := by decide +kernel
def certificate2286 : RatCutBinCertificate := ⟨⟨retention2286,(127449921297576803/62500000000000000),(1140020255178431/15625000000000000),(11180342851196610183/1000000000000000000),(708361321849244584829/1000000000000000000),(490105776160891979/500000000000000000)⟩,(99731946768931759/100000000000000000),(93807603032672553/200000000000000000),(175866542574335469/1000000000000000000),(166709620812880117/1000000000000000000)⟩
theorem valid2286 : certificate2286.Valid := by decide +kernel
theorem sound2286 : certificate2286.Sound := rat_cut_bin_certificate_sound certificate2286 profilesValid2286 numericValid2286 valid2286

def retention2287 : RatCutRetentionCertificate := ⟨(39/1000),(1/25),(27447335238436487369/63019021664182630395),(1117147137904386749/200000000000000000),(21/20),(392928721763639128932170559856500603191/357487084129403759680000000000000000000),false,MergedCutProfiles.Batch352.profile14114,(fun _ => MergedCutProfiles.Batch352.profile14114)⟩
theorem profilesValid2287 : retention2287.ProfilesValid := by
  exact MergedCutProfiles.Batch352.valid14114
theorem numericValid2287 : retention2287.NumericValid := by decide +kernel
def certificate2287 : RatCutBinCertificate := ⟨⟨retention2287,(146336559610076803/62500000000000000),(1140020255178431/15625000000000000),(11180342851196610183/1000000000000000000),(708361321849244584829/1000000000000000000),(216619446464607633/200000000000000000)⟩,(249230538104164693/250000000000000000),(222243738076747249/1000000000000000000),(443334965522742881/1000000000000000000),(193813455679487839/500000000000000000)⟩
theorem valid2287 : certificate2287.Valid := by decide +kernel
theorem sound2287 : certificate2287.Sound := rat_cut_bin_certificate_sound certificate2287 profilesValid2287 numericValid2287 valid2287

def retention2288 : RatCutRetentionCertificate := ⟨(39/1000),(1/25),(31237627800664403896/63019021664182630395),(27447335238436487369/1000000000000000000),1,(21976756398180961569683711870105470119/21957868190749189895200000000000000000),false,MergedCutProfiles.Batch352.profile14115,(fun _ => MergedCutProfiles.Batch352.profile14115)⟩
theorem profilesValid2288 : retention2288.ProfilesValid := by
  exact MergedCutProfiles.Batch352.valid14115
theorem numericValid2288 : retention2288.NumericValid := by decide +kernel
def certificate2288 : RatCutBinCertificate := ⟨⟨retention2288,(146336559610076803/62500000000000000),(1140020255178431/15625000000000000),(11180342851196610183/1000000000000000000),(708361321849244584829/1000000000000000000),(492790303094006371/500000000000000000)⟩,(249230538104164693/250000000000000000),(244233273362658063/1000000000000000000),(411389507250222667/1000000000000000000),(390177472450474973/1000000000000000000)⟩
theorem valid2288 : certificate2288.Valid := by decide +kernel
theorem sound2288 : certificate2288.Sound := rat_cut_bin_certificate_sound certificate2288 profilesValid2288 numericValid2288 valid2288

def retention2289 : RatCutRetentionCertificate := ⟨(39/1000),(1/25),(1/2),(3904703475083050487/125000000000000000),1,(124136009710247773081855939316565117039/124950511202657615584000000000000000000),false,MergedCutProfiles.Batch352.profile14113,(fun _ => MergedCutProfiles.Batch352.profile14113)⟩
theorem profilesValid2289 : retention2289.ProfilesValid := by
  exact MergedCutProfiles.Batch352.valid14113
theorem numericValid2289 : retention2289.NumericValid := by decide +kernel
def certificate2289 : RatCutBinCertificate := ⟨⟨retention2289,(146336559610076803/62500000000000000),(1140020255178431/15625000000000000),(11180342851196610183/1000000000000000000),(708361321849244584829/1000000000000000000),(978201818186253409/1000000000000000000)⟩,(249230538104164693/250000000000000000),(123037788898394147/500000000000000000),(102200991245904281/250000000000000000),(193269384854483273/500000000000000000)⟩
theorem valid2289 : certificate2289.Valid := by decide +kernel
theorem sound2289 : certificate2289.Sound := rat_cut_bin_certificate_sound certificate2289 profilesValid2289 numericValid2289 valid2289

def retention2290 : RatCutRetentionCertificate := ⟨(1/25),(41/1000),(257669242740510623/19886583873014966189),(153070837271590469/200000000000000000),(69/20),(17916589576081207947/8000000000000000000),true,MergedCutProfiles.Batch352.profile14116,![MergedCutProfiles.Batch352.profile14116,MergedCutProfiles.Batch352.profile14117,MergedCutProfiles.Batch352.profile14118,MergedCutProfiles.Batch352.profile14119,MergedCutProfiles.Batch353.profile14120,MergedCutProfiles.Batch353.profile14121,MergedCutProfiles.Batch353.profile14122,MergedCutProfiles.Batch353.profile14123,MergedCutProfiles.Batch353.profile14124,MergedCutProfiles.Batch353.profile14125,MergedCutProfiles.Batch353.profile14126,MergedCutProfiles.Batch353.profile14127,MergedCutProfiles.Batch353.profile14128,MergedCutProfiles.Batch353.profile14129,MergedCutProfiles.Batch353.profile14130,MergedCutProfiles.Batch353.profile14131]⟩
theorem profilesValid2290 : retention2290.ProfilesValid := by
  change ∀ j : Fin 16, (retention2290.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch352.valid14116
  · exact MergedCutProfiles.Batch352.valid14117
  · exact MergedCutProfiles.Batch352.valid14118
  · exact MergedCutProfiles.Batch352.valid14119
  · exact MergedCutProfiles.Batch353.valid14120
  · exact MergedCutProfiles.Batch353.valid14121
  · exact MergedCutProfiles.Batch353.valid14122
  · exact MergedCutProfiles.Batch353.valid14123
  · exact MergedCutProfiles.Batch353.valid14124
  · exact MergedCutProfiles.Batch353.valid14125
  · exact MergedCutProfiles.Batch353.valid14126
  · exact MergedCutProfiles.Batch353.valid14127
  · exact MergedCutProfiles.Batch353.valid14128
  · exact MergedCutProfiles.Batch353.valid14129
  · exact MergedCutProfiles.Batch353.valid14130
  · exact MergedCutProfiles.Batch353.valid14131
theorem numericValid2290 : retention2290.NumericValid := by decide +kernel
def certificate2290 : RatCutBinCertificate := ⟨⟨retention2290,(410698976025986613/200000000000000000),(77009395027439323/1000000000000000000),(11352405535282405683/1000000000000000000),(340472333310433663033/500000000000000000),(2191513324252492083/1000000000000000000)⟩,(997203749536676761/1000000000000000000),(103995144786100451/250000000000000000),(43831016486083793/200000000000000000),(55924050913350789/500000000000000000)⟩
theorem valid2290 : certificate2290.Valid := by decide +kernel
theorem sound2290 : certificate2290.Sound := rat_cut_bin_certificate_sound certificate2290 profilesValid2290 numericValid2290 valid2290

def retention2291 : RatCutRetentionCertificate := ⟨(1/25),(41/1000),(933877555226453527/59659751619044898567),(773007728221531869/1000000000000000000),(17/5),(2844015426152099497529/1280000000000000000000),true,MergedCutProfiles.Batch353.profile14132,![MergedCutProfiles.Batch353.profile14132,MergedCutProfiles.Batch353.profile14133,MergedCutProfiles.Batch353.profile14134,MergedCutProfiles.Batch353.profile14135,MergedCutProfiles.Batch353.profile14136,MergedCutProfiles.Batch353.profile14137,MergedCutProfiles.Batch353.profile14138,MergedCutProfiles.Batch353.profile14139,MergedCutProfiles.Batch353.profile14140,MergedCutProfiles.Batch353.profile14141,MergedCutProfiles.Batch353.profile14142,MergedCutProfiles.Batch353.profile14143,MergedCutProfiles.Batch353.profile14144,MergedCutProfiles.Batch353.profile14145,MergedCutProfiles.Batch353.profile14146,MergedCutProfiles.Batch353.profile14147]⟩
theorem profilesValid2291 : retention2291.ProfilesValid := by
  change ∀ j : Fin 16, (retention2291.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch353.valid14132
  · exact MergedCutProfiles.Batch353.valid14133
  · exact MergedCutProfiles.Batch353.valid14134
  · exact MergedCutProfiles.Batch353.valid14135
  · exact MergedCutProfiles.Batch353.valid14136
  · exact MergedCutProfiles.Batch353.valid14137
  · exact MergedCutProfiles.Batch353.valid14138
  · exact MergedCutProfiles.Batch353.valid14139
  · exact MergedCutProfiles.Batch353.valid14140
  · exact MergedCutProfiles.Batch353.valid14141
  · exact MergedCutProfiles.Batch353.valid14142
  · exact MergedCutProfiles.Batch353.valid14143
  · exact MergedCutProfiles.Batch353.valid14144
  · exact MergedCutProfiles.Batch353.valid14145
  · exact MergedCutProfiles.Batch353.valid14146
  · exact MergedCutProfiles.Batch353.valid14147
theorem numericValid2291 : retention2291.NumericValid := by decide +kernel
def certificate2291 : RatCutBinCertificate := ⟨⟨retention2291,(410698976025986613/200000000000000000),(77009395027439323/1000000000000000000),(11352405535282405683/1000000000000000000),(340472333310433663033/500000000000000000),(4349046393227271/2000000000000000)⟩,(997203749536676761/1000000000000000000),(417109670838175409/1000000000000000000),(54541574140533837/250000000000000000),(559273644450801/5000000000000000)⟩
theorem valid2291 : certificate2291.Valid := by decide +kernel
theorem sound2291 : certificate2291.Sound := rat_cut_bin_certificate_sound certificate2291 profilesValid2291 numericValid2291 valid2291

def certificates : List RatCutBinCertificate := [certificate2280,certificate2281,certificate2282,certificate2283,certificate2284,certificate2285,certificate2286,certificate2287,certificate2288,certificate2289,certificate2290,certificate2291]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2280,List.forall_mem_cons.mpr ⟨sound2281,List.forall_mem_cons.mpr ⟨sound2282,List.forall_mem_cons.mpr ⟨sound2283,List.forall_mem_cons.mpr ⟨sound2284,List.forall_mem_cons.mpr ⟨sound2285,List.forall_mem_cons.mpr ⟨sound2286,List.forall_mem_cons.mpr ⟨sound2287,List.forall_mem_cons.mpr ⟨sound2288,List.forall_mem_cons.mpr ⟨sound2289,List.forall_mem_cons.mpr ⟨sound2290,List.forall_mem_cons.mpr ⟨sound2291,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch190
