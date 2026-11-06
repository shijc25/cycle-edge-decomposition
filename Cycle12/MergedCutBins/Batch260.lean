import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch361
import Cycle12.MergedCutProfiles.Batch362
import Cycle12.MergedCutProfiles.Batch479
import Cycle12.MergedCutProfiles.Batch480

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch260

def retention3120 : RatCutRetentionCertificate := ⟨(43/1000),(11/250),(1/2),(6297004915624715033/100000000000000000),1,(2010086721500966759402419833519799659/2015041572999908810560000000000000000),false,MergedCutProfiles.Batch361.profile14446,(fun _ => MergedCutProfiles.Batch361.profile14446)⟩
theorem profilesValid3120 : retention3120.ProfilesValid := by
  exact MergedCutProfiles.Batch361.valid14446
theorem numericValid3120 : retention3120.NumericValid := by decide +kernel
def certificate3120 : RatCutBinCertificate := ⟨⟨retention3120,(1006649867131201179/500000000000000000),(5622540848385301/62500000000000000),(5947016094090640243/500000000000000000),(1523646054422456694899/1000000000000000000),(982313436652733857/1000000000000000000)⟩,(499395739503336353/500000000000000000),(473622938721054113/1000000000000000000),(5388055801877979/31250000000000000),(166563390334679921/1000000000000000000)⟩
theorem valid3120 : certificate3120.Valid := by decide +kernel
theorem sound3120 : certificate3120.Sound := rat_cut_bin_certificate_sound certificate3120 profilesValid3120 numericValid3120 valid3120

def retention3121 : RatCutRetentionCertificate := ⟨(43/1000),(11/250),(2773423594421306709/6066651441615842921),(5004058123042717313/500000000000000000),1,(10590944629540947299766796535357988651/10008116246085434626000000000000000000),false,MergedCutProfiles.Batch479.profile19192,(fun _ => MergedCutProfiles.Batch479.profile19192)⟩
theorem profilesValid3121 : retention3121.ProfilesValid := by
  exact MergedCutProfiles.Batch479.valid19192
theorem numericValid3121 : retention3121.NumericValid := by decide +kernel
def certificate3121 : RatCutBinCertificate := ⟨⟨retention3121,(1076991215131201179/500000000000000000),(5622540848385301/62500000000000000),(5947016094090640243/500000000000000000),(1523646054422456694899/1000000000000000000),(1041943805140948737/1000000000000000000)⟩,(998707021365851179/1000000000000000000),(1901798203472431/15625000000000000),(4843416220045421/7812500000000000),(292128360158700023/500000000000000000)⟩
theorem valid3121 : certificate3121.Valid := by decide +kernel
theorem sound3121 : certificate3121.Sound := rat_cut_bin_certificate_sound certificate3121 profilesValid3121 numericValid3121 valid3121

def retention3122 : RatCutRetentionCertificate := ⟨(43/1000),(11/250),(63067627072091139401/127399680273932701341),(58241895482847440889/1000000000000000000),1,(209478946078635640024752006139450967/208006769581598003175000000000000000),false,MergedCutProfiles.Batch479.profile19193,(fun _ => MergedCutProfiles.Batch479.profile19193)⟩
theorem profilesValid3122 : retention3122.ProfilesValid := by
  exact MergedCutProfiles.Batch479.valid19193
theorem numericValid3122 : retention3122.NumericValid := by decide +kernel
def certificate3122 : RatCutBinCertificate := ⟨⟨retention3122,(1076991215131201179/500000000000000000),(5622540848385301/62500000000000000),(5947016094090640243/500000000000000000),(1523646054422456694899/1000000000000000000),(990785853090892123/1000000000000000000)⟩,(998707021365851179/1000000000000000000),(127999686749148687/1000000000000000000),(121432192526023221/200000000000000000),(590732136569752013/1000000000000000000)⟩
theorem valid3122 : certificate3122.Valid := by decide +kernel
theorem sound3122 : certificate3122.Sound := rat_cut_bin_certificate_sound certificate3122 profilesValid3122 numericValid3122 valid3122

def retention3123 : RatCutRetentionCertificate := ⟨(43/1000),(11/250),(63698303342812050796/127399680273932701341),(63067627072091139401/1000000000000000000),1,(251657793465350840388661156371149431003/252270508288364557604000000000000000000),false,MergedCutProfiles.Batch479.profile19194,(fun _ => MergedCutProfiles.Batch479.profile19194)⟩
theorem profilesValid3123 : retention3123.ProfilesValid := by
  exact MergedCutProfiles.Batch479.valid19194
theorem numericValid3123 : retention3123.NumericValid := by decide +kernel
def certificate3123 : RatCutBinCertificate := ⟨⟨retention3123,(1076991215131201179/500000000000000000),(5622540848385301/62500000000000000),(5947016094090640243/500000000000000000),(1523646054422456694899/1000000000000000000),(981279512238090771/1000000000000000000)⟩,(998707021365851179/1000000000000000000),(129239709226041051/1000000000000000000),(151167042341439473/250000000000000000),(583495964023675619/1000000000000000000)⟩
theorem valid3123 : certificate3123.Valid := by decide +kernel
theorem sound3123 : certificate3123.Sound := rat_cut_bin_certificate_sound certificate3123 profilesValid3123 numericValid3123 valid3123

def retention3124 : RatCutRetentionCertificate := ⟨(43/1000),(11/250),(1/2),(15924575835703012699/250000000000000000),1,(10167131774867528022236094533333000559/10191728534849928127360000000000000000),false,MergedCutProfiles.Batch361.profile14446,(fun _ => MergedCutProfiles.Batch361.profile14446)⟩
theorem profilesValid3124 : retention3124.ProfilesValid := by
  exact MergedCutProfiles.Batch361.valid14446
theorem numericValid3124 : retention3124.NumericValid := by decide +kernel
def certificate3124 : RatCutBinCertificate := ⟨⟨retention3124,(1076991215131201179/500000000000000000),(5622540848385301/62500000000000000),(5947016094090640243/500000000000000000),(1523646054422456694899/1000000000000000000),(981294909077387707/1000000000000000000)⟩,(998707021365851179/1000000000000000000),(64618840706286001/500000000000000000),(604672237327648173/1000000000000000000),(583597496169049917/1000000000000000000)⟩
theorem valid3124 : certificate3124.Valid := by decide +kernel
theorem sound3124 : certificate3124.Sound := rat_cut_bin_certificate_sound certificate3124 profilesValid3124 numericValid3124 valid3124

def retention3125 : RatCutRetentionCertificate := ⟨(11/250),(9/200),(187749692899345429/30282170708668115662),(368100564453181901/500000000000000000),(37/10),(1478725038548102746153/640000000000000000000),true,MergedCutProfiles.Batch479.profile19195,![MergedCutProfiles.Batch479.profile19195,MergedCutProfiles.Batch479.profile19196,MergedCutProfiles.Batch479.profile19197,MergedCutProfiles.Batch479.profile19198,MergedCutProfiles.Batch479.profile19199,MergedCutProfiles.Batch480.profile19200,MergedCutProfiles.Batch362.profile14500,MergedCutProfiles.Batch361.profile14452,MergedCutProfiles.Batch480.profile19201,MergedCutProfiles.Batch480.profile19202,MergedCutProfiles.Batch480.profile19203,MergedCutProfiles.Batch480.profile19204,MergedCutProfiles.Batch480.profile19205,MergedCutProfiles.Batch362.profile14502,MergedCutProfiles.Batch480.profile19206,MergedCutProfiles.Batch361.profile14455]⟩
theorem profilesValid3125 : retention3125.ProfilesValid := by
  change ∀ j : Fin 16, (retention3125.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch479.valid19195
  · exact MergedCutProfiles.Batch479.valid19196
  · exact MergedCutProfiles.Batch479.valid19197
  · exact MergedCutProfiles.Batch479.valid19198
  · exact MergedCutProfiles.Batch479.valid19199
  · exact MergedCutProfiles.Batch480.valid19200
  · exact MergedCutProfiles.Batch362.valid14500
  · exact MergedCutProfiles.Batch361.valid14452
  · exact MergedCutProfiles.Batch480.valid19201
  · exact MergedCutProfiles.Batch480.valid19202
  · exact MergedCutProfiles.Batch480.valid19203
  · exact MergedCutProfiles.Batch480.valid19204
  · exact MergedCutProfiles.Batch480.valid19205
  · exact MergedCutProfiles.Batch362.valid14502
  · exact MergedCutProfiles.Batch480.valid19206
  · exact MergedCutProfiles.Batch361.valid14455
theorem numericValid3125 : retention3125.NumericValid := by decide +kernel
def certificate3125 : RatCutBinCertificate := ⟨⟨retention3125,(507351104734127217/250000000000000000),(11819389720817643/125000000000000000),(1208333206821552487/100000000000000000),(1471754506257890891311/1000000000000000000),(2251748263627493753/1000000000000000000)⟩,(499372494528345371/500000000000000000),(455891320102613151/1000000000000000000),(46501359810962267/250000000000000000),(46195127334751557/500000000000000000)⟩
theorem valid3125 : certificate3125.Valid := by decide +kernel
theorem sound3125 : certificate3125.Sound := rat_cut_bin_certificate_sound certificate3125 profilesValid3125 numericValid3125 valid3125

def retention3126 : RatCutRetentionCertificate := ⟨(11/250),(9/200),(139971542625000000/15141085354334057831),(187749692899345429/250000000000000000),(73/20),(732336524630154959789/320000000000000000000),true,MergedCutProfiles.Batch480.profile19207,![MergedCutProfiles.Batch480.profile19207,MergedCutProfiles.Batch479.profile19197,MergedCutProfiles.Batch480.profile19208,MergedCutProfiles.Batch480.profile19200,MergedCutProfiles.Batch480.profile19209,MergedCutProfiles.Batch480.profile19201,MergedCutProfiles.Batch362.profile14501,MergedCutProfiles.Batch480.profile19204,MergedCutProfiles.Batch361.profile14454,MergedCutProfiles.Batch362.profile14517,MergedCutProfiles.Batch480.profile19210,MergedCutProfiles.Batch480.profile19211,MergedCutProfiles.Batch480.profile19212,MergedCutProfiles.Batch362.profile14504,MergedCutProfiles.Batch480.profile19213,MergedCutProfiles.Batch362.profile14487]⟩
theorem profilesValid3126 : retention3126.ProfilesValid := by
  change ∀ j : Fin 16, (retention3126.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch480.valid19207
  · exact MergedCutProfiles.Batch479.valid19197
  · exact MergedCutProfiles.Batch480.valid19208
  · exact MergedCutProfiles.Batch480.valid19200
  · exact MergedCutProfiles.Batch480.valid19209
  · exact MergedCutProfiles.Batch480.valid19201
  · exact MergedCutProfiles.Batch362.valid14501
  · exact MergedCutProfiles.Batch480.valid19204
  · exact MergedCutProfiles.Batch361.valid14454
  · exact MergedCutProfiles.Batch362.valid14517
  · exact MergedCutProfiles.Batch480.valid19210
  · exact MergedCutProfiles.Batch480.valid19211
  · exact MergedCutProfiles.Batch480.valid19212
  · exact MergedCutProfiles.Batch362.valid14504
  · exact MergedCutProfiles.Batch480.valid19213
  · exact MergedCutProfiles.Batch362.valid14487
theorem numericValid3126 : retention3126.NumericValid := by decide +kernel
def certificate3126 : RatCutBinCertificate := ⟨⟨retention3126,(507351104734127217/250000000000000000),(11819389720817643/125000000000000000),(1208333206821552487/100000000000000000),(1471754506257890891311/1000000000000000000),(2230586087716086107/1000000000000000000)⟩,(499372494528345371/500000000000000000),(227586968840152271/500000000000000000),(46642375738742469/250000000000000000),(93093357277074047/1000000000000000000)⟩
theorem valid3126 : certificate3126.Valid := by decide +kernel
theorem sound3126 : certificate3126.Sound := rat_cut_bin_certificate_sound certificate3126 profilesValid3126 numericValid3126 valid3126

def retention3127 : RatCutRetentionCertificate := ⟨(11/250),(9/200),(175709720511241899/15141085354334057831),(1119772341/1000000000),(13/5),(35989964858119086581/16000000000000000000),true,MergedCutProfiles.Batch480.profile19214,![MergedCutProfiles.Batch480.profile19214,MergedCutProfiles.Batch480.profile19215,MergedCutProfiles.Batch480.profile19216,MergedCutProfiles.Batch480.profile19209,MergedCutProfiles.Batch361.profile14468,MergedCutProfiles.Batch480.profile19217,MergedCutProfiles.Batch480.profile19205,MergedCutProfiles.Batch480.profile19206,MergedCutProfiles.Batch362.profile14485,MergedCutProfiles.Batch361.profile14456,MergedCutProfiles.Batch480.profile19218,MergedCutProfiles.Batch480.profile19219,MergedCutProfiles.Batch480.profile19220,MergedCutProfiles.Batch480.profile19221,MergedCutProfiles.Batch362.profile14506,MergedCutProfiles.Batch480.profile19222]⟩
theorem profilesValid3127 : retention3127.ProfilesValid := by
  change ∀ j : Fin 16, (retention3127.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch480.valid19214
  · exact MergedCutProfiles.Batch480.valid19215
  · exact MergedCutProfiles.Batch480.valid19216
  · exact MergedCutProfiles.Batch480.valid19209
  · exact MergedCutProfiles.Batch361.valid14468
  · exact MergedCutProfiles.Batch480.valid19217
  · exact MergedCutProfiles.Batch480.valid19205
  · exact MergedCutProfiles.Batch480.valid19206
  · exact MergedCutProfiles.Batch362.valid14485
  · exact MergedCutProfiles.Batch361.valid14456
  · exact MergedCutProfiles.Batch480.valid19218
  · exact MergedCutProfiles.Batch480.valid19219
  · exact MergedCutProfiles.Batch480.valid19220
  · exact MergedCutProfiles.Batch480.valid19221
  · exact MergedCutProfiles.Batch362.valid14506
  · exact MergedCutProfiles.Batch480.valid19222
theorem numericValid3127 : retention3127.NumericValid := by decide +kernel
def certificate3127 : RatCutBinCertificate := ⟨⟨retention3127,(507351104734127217/250000000000000000),(11819389720817643/125000000000000000),(1208333206821552487/100000000000000000),(1471754506257890891311/1000000000000000000),(88323293208438649/40000000000000000)⟩,(499372494528345371/500000000000000000),(376351071655144093/1000000000000000000),(127931785439211309/500000000000000000),(5249365690636343/31250000000000000)⟩
theorem valid3127 : certificate3127.Valid := by decide +kernel
theorem sound3127 : certificate3127.Sound := rat_cut_bin_certificate_sound certificate3127 profilesValid3127 numericValid3127 valid3127

def retention3128 : RatCutRetentionCertificate := ⟨(11/250),(9/200),(9403037485145260837/121128682834672462648),(175709720511241899/125000000000000000),(43/20),(315094765174893137703/160000000000000000000),true,MergedCutProfiles.Batch361.profile14469,![MergedCutProfiles.Batch361.profile14469,MergedCutProfiles.Batch361.profile14472,MergedCutProfiles.Batch361.profile14476,MergedCutProfiles.Batch362.profile14480,MergedCutProfiles.Batch480.profile19223,MergedCutProfiles.Batch480.profile19224,MergedCutProfiles.Batch480.profile19225,MergedCutProfiles.Batch480.profile19226,MergedCutProfiles.Batch480.profile19227,MergedCutProfiles.Batch480.profile19228,MergedCutProfiles.Batch480.profile19229,MergedCutProfiles.Batch480.profile19230,MergedCutProfiles.Batch480.profile19231,MergedCutProfiles.Batch480.profile19232,MergedCutProfiles.Batch480.profile19233,MergedCutProfiles.Batch480.profile19234]⟩
theorem profilesValid3128 : retention3128.ProfilesValid := by
  change ∀ j : Fin 16, (retention3128.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch361.valid14469
  · exact MergedCutProfiles.Batch361.valid14472
  · exact MergedCutProfiles.Batch361.valid14476
  · exact MergedCutProfiles.Batch362.valid14480
  · exact MergedCutProfiles.Batch480.valid19223
  · exact MergedCutProfiles.Batch480.valid19224
  · exact MergedCutProfiles.Batch480.valid19225
  · exact MergedCutProfiles.Batch480.valid19226
  · exact MergedCutProfiles.Batch480.valid19227
  · exact MergedCutProfiles.Batch480.valid19228
  · exact MergedCutProfiles.Batch480.valid19229
  · exact MergedCutProfiles.Batch480.valid19230
  · exact MergedCutProfiles.Batch480.valid19231
  · exact MergedCutProfiles.Batch480.valid19232
  · exact MergedCutProfiles.Batch480.valid19233
  · exact MergedCutProfiles.Batch480.valid19234
theorem numericValid3128 : retention3128.NumericValid := by decide +kernel
def certificate3128 : RatCutBinCertificate := ⟨⟨retention3128,(507351104734127217/250000000000000000),(11819389720817643/125000000000000000),(1208333206821552487/100000000000000000),(1471754506257890891311/1000000000000000000),(1935198264636348471/1000000000000000000)⟩,(499372494528345371/500000000000000000),(389975534366067417/1000000000000000000),(242793890050040653/1000000000000000000),(33628726991150769/200000000000000000)⟩
theorem valid3128 : certificate3128.Valid := by decide +kernel
theorem sound3128 : certificate3128.Sound := rat_cut_bin_certificate_sound certificate3128 profilesValid3128 numericValid3128 valid3128

def retention3129 : RatCutRetentionCertificate := ⟨(11/250),(9/200),(6705305853452329053/15141085354334057831),(9403037485145260837/1000000000000000000),(21/20),(16635428395688034173774650540153387892591/15044859976232417339200000000000000000000),false,MergedCutProfiles.Batch480.profile19235,(fun _ => MergedCutProfiles.Batch480.profile19235)⟩
theorem profilesValid3129 : retention3129.ProfilesValid := by
  exact MergedCutProfiles.Batch480.valid19235
theorem numericValid3129 : retention3129.NumericValid := by decide +kernel
def certificate3129 : RatCutBinCertificate := ⟨⟨retention3129,(507351104734127217/250000000000000000),(11819389720817643/125000000000000000),(1208333206821552487/100000000000000000),(1471754506257890891311/1000000000000000000),(544523488480100879/500000000000000000)⟩,(499372494528345371/500000000000000000),(229744130692562151/500000000000000000),(183194217278755217/1000000000000000000),(171716395101821701/1000000000000000000)⟩
theorem valid3129 : certificate3129.Valid := by decide +kernel
theorem sound3129 : certificate3129.Sound := rat_cut_bin_certificate_sound certificate3129 profilesValid3129 numericValid3129 valid3129

def retention3130 : RatCutRetentionCertificate := ⟨(11/250),(9/200),(59847179963251434693/121128682834672462648),(6705305853452329053/125000000000000000),1,(14427796786696665906180938041961795121/14304652487364968646400000000000000000),false,MergedCutProfiles.Batch480.profile19236,(fun _ => MergedCutProfiles.Batch480.profile19236)⟩
theorem profilesValid3130 : retention3130.ProfilesValid := by
  exact MergedCutProfiles.Batch480.valid19236
theorem numericValid3130 : retention3130.NumericValid := by decide +kernel
def certificate3130 : RatCutBinCertificate := ⟨⟨retention3130,(507351104734127217/250000000000000000),(11819389720817643/125000000000000000),(1208333206821552487/100000000000000000),(1471754506257890891311/1000000000000000000),(198545613748310313/200000000000000000)⟩,(499372494528345371/500000000000000000),(466940765348477459/1000000000000000000),(17745899551129299/100000000000000000),(172748091076684329/1000000000000000000)⟩
theorem valid3130 : certificate3130.Valid := by decide +kernel
theorem sound3130 : certificate3130.Sound := rat_cut_bin_certificate_sound certificate3130 profilesValid3130 numericValid3130 valid3130

def retention3131 : RatCutRetentionCertificate := ⟨(11/250),(9/200),(7555706470360493630/15141085354334057831),(59847179963251434693/1000000000000000000),1,(79739079589092157191690365457936485769/79796239951001912924000000000000000000),false,MergedCutProfiles.Batch480.profile19237,(fun _ => MergedCutProfiles.Batch480.profile19237)⟩
theorem profilesValid3131 : retention3131.ProfilesValid := by
  exact MergedCutProfiles.Batch480.valid19237
theorem numericValid3131 : retention3131.NumericValid := by decide +kernel
def certificate3131 : RatCutBinCertificate := ⟨⟨retention3131,(507351104734127217/250000000000000000),(11819389720817643/125000000000000000),(1208333206821552487/100000000000000000),(1471754506257890891311/1000000000000000000),(196680610612325953/200000000000000000)⟩,(499372494528345371/500000000000000000),(235271268171579463/500000000000000000),(174729930307899093/1000000000000000000),(168837870441082847/1000000000000000000)⟩
theorem valid3131 : certificate3131.Valid := by decide +kernel
theorem sound3131 : certificate3131.Sound := rat_cut_bin_certificate_sound certificate3131 profilesValid3131 numericValid3131 valid3131

def certificates : List RatCutBinCertificate := [certificate3120,certificate3121,certificate3122,certificate3123,certificate3124,certificate3125,certificate3126,certificate3127,certificate3128,certificate3129,certificate3130,certificate3131]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3120,List.forall_mem_cons.mpr ⟨sound3121,List.forall_mem_cons.mpr ⟨sound3122,List.forall_mem_cons.mpr ⟨sound3123,List.forall_mem_cons.mpr ⟨sound3124,List.forall_mem_cons.mpr ⟨sound3125,List.forall_mem_cons.mpr ⟨sound3126,List.forall_mem_cons.mpr ⟨sound3127,List.forall_mem_cons.mpr ⟨sound3128,List.forall_mem_cons.mpr ⟨sound3129,List.forall_mem_cons.mpr ⟨sound3130,List.forall_mem_cons.mpr ⟨sound3131,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch260
