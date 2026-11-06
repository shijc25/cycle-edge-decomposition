import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch201
import Cycle12.MergedCutProfiles.Batch202
import Cycle12.MergedCutProfiles.Batch203

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch102

def retention1224 : RatCutRetentionCertificate := ⟨(227/4000),(57/1000),(3492229096395658022/7044818956914543545),(6514530258763630581/1000000000000000000),(21/20),(10341917143296012824229785841493147318799/10423248414021808929600000000000000000000),false,MergedCutProfiles.Batch201.profile8077,(fun _ => MergedCutProfiles.Batch201.profile8077)⟩
theorem profilesValid1224 : retention1224.ProfilesValid := by
  exact MergedCutProfiles.Batch201.valid8077
theorem numericValid1224 : retention1224.NumericValid := by decide +kernel
def certificate1224 : RatCutBinCertificate := ⟨⟨retention1224,(2609683666695265191/1000000000000000000),(161735409484216873/1000000000000000000),(14959933277224716671/1000000000000000000),(211095948276747537531/1000000000000000000),(962569201331067187/1000000000000000000)⟩,(989595294535436387/1000000000000000000),(414809556665763139/1000000000000000000),(44036765038609443/200000000000000000),(88008397748086329/500000000000000000)⟩
theorem valid1224 : certificate1224.Valid := by decide +kernel
theorem sound1224 : certificate1224.Sound := rat_cut_bin_certificate_sound certificate1224 profilesValid1224 numericValid1224 valid1224

def retention1225 : RatCutRetentionCertificate := ⟨(227/4000),(57/1000),(1/2),(1746114548197829011/250000000000000000),(21/20),(172228910518876176168488308608366811811/174611454819782901100000000000000000000),false,MergedCutProfiles.Batch201.profile8075,(fun _ => MergedCutProfiles.Batch201.profile8075)⟩
theorem profilesValid1225 : retention1225.ProfilesValid := by
  exact MergedCutProfiles.Batch201.valid8075
theorem numericValid1225 : retention1225.NumericValid := by decide +kernel
def certificate1225 : RatCutBinCertificate := ⟨⟨retention1225,(2609683666695265191/1000000000000000000),(161735409484216873/1000000000000000000),(14959933277224716671/1000000000000000000),(211095948276747537531/1000000000000000000),(956727462433893681/1000000000000000000)⟩,(989595294535436387/1000000000000000000),(417342366914492799/1000000000000000000),(43592579263903461/200000000000000000),(87348606624922729/500000000000000000)⟩
theorem valid1225 : certificate1225.Valid := by decide +kernel
theorem sound1225 : certificate1225.Sound := rat_cut_bin_certificate_sound certificate1225 profilesValid1225 numericValid1225 valid1225

def retention1226 : RatCutRetentionCertificate := ⟨(57/1000),(229/4000),(971962305541090460/13945916804907706299),(854026925781557751/1000000000000000000),(11/4),(508448238622784591083/256000000000000000000),true,MergedCutProfiles.Batch201.profile8078,![MergedCutProfiles.Batch201.profile8078,MergedCutProfiles.Batch201.profile8079,MergedCutProfiles.Batch202.profile8080,MergedCutProfiles.Batch202.profile8081,MergedCutProfiles.Batch202.profile8082,MergedCutProfiles.Batch202.profile8083,MergedCutProfiles.Batch202.profile8084,MergedCutProfiles.Batch202.profile8085,MergedCutProfiles.Batch202.profile8086,MergedCutProfiles.Batch202.profile8087,MergedCutProfiles.Batch202.profile8088,MergedCutProfiles.Batch202.profile8089,MergedCutProfiles.Batch202.profile8090,MergedCutProfiles.Batch202.profile8091,MergedCutProfiles.Batch202.profile8092,MergedCutProfiles.Batch202.profile8093]⟩
theorem profilesValid1226 : retention1226.ProfilesValid := by
  change ∀ j : Fin 16, (retention1226.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch201.valid8078
  · exact MergedCutProfiles.Batch201.valid8079
  · exact MergedCutProfiles.Batch202.valid8080
  · exact MergedCutProfiles.Batch202.valid8081
  · exact MergedCutProfiles.Batch202.valid8082
  · exact MergedCutProfiles.Batch202.valid8083
  · exact MergedCutProfiles.Batch202.valid8084
  · exact MergedCutProfiles.Batch202.valid8085
  · exact MergedCutProfiles.Batch202.valid8086
  · exact MergedCutProfiles.Batch202.valid8087
  · exact MergedCutProfiles.Batch202.valid8088
  · exact MergedCutProfiles.Batch202.valid8089
  · exact MergedCutProfiles.Batch202.valid8090
  · exact MergedCutProfiles.Batch202.valid8091
  · exact MergedCutProfiles.Batch202.valid8092
  · exact MergedCutProfiles.Batch202.valid8093
theorem numericValid1226 : retention1226.NumericValid := by decide +kernel
def certificate1226 : RatCutBinCertificate := ⟨⟨retention1226,(568538020547612741/250000000000000000),(163394722365440633/1000000000000000000),(15026486207675484803/1000000000000000000),(52468180930640026063/250000000000000000),(1918099651106408827/1000000000000000000)⟩,(495450069802897567/500000000000000000),(71831044163929743/200000000000000000),(17066570965234569/62500000000000000),(72622949277580087/500000000000000000)⟩
theorem valid1226 : certificate1226.Valid := by decide +kernel
theorem sound1226 : certificate1226.Sound := rat_cut_bin_certificate_sound certificate1226 profilesValid1226 numericValid1226 valid1226

def retention1227 : RatCutRetentionCertificate := ⟨(57/1000),(229/4000),(1680060729616462361/13945916804907706299),(48598115277054523/50000000000000000),(49/20),(117764456502588970843/64000000000000000000),true,MergedCutProfiles.Batch202.profile8094,![MergedCutProfiles.Batch202.profile8094,MergedCutProfiles.Batch202.profile8095,MergedCutProfiles.Batch202.profile8096,MergedCutProfiles.Batch202.profile8097,MergedCutProfiles.Batch202.profile8098,MergedCutProfiles.Batch202.profile8099,MergedCutProfiles.Batch202.profile8100,MergedCutProfiles.Batch202.profile8101,MergedCutProfiles.Batch202.profile8102,MergedCutProfiles.Batch202.profile8103,MergedCutProfiles.Batch202.profile8104,MergedCutProfiles.Batch202.profile8105,MergedCutProfiles.Batch202.profile8106,MergedCutProfiles.Batch202.profile8107,MergedCutProfiles.Batch202.profile8108,MergedCutProfiles.Batch202.profile8109]⟩
theorem profilesValid1227 : retention1227.ProfilesValid := by
  change ∀ j : Fin 16, (retention1227.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch202.valid8094
  · exact MergedCutProfiles.Batch202.valid8095
  · exact MergedCutProfiles.Batch202.valid8096
  · exact MergedCutProfiles.Batch202.valid8097
  · exact MergedCutProfiles.Batch202.valid8098
  · exact MergedCutProfiles.Batch202.valid8099
  · exact MergedCutProfiles.Batch202.valid8100
  · exact MergedCutProfiles.Batch202.valid8101
  · exact MergedCutProfiles.Batch202.valid8102
  · exact MergedCutProfiles.Batch202.valid8103
  · exact MergedCutProfiles.Batch202.valid8104
  · exact MergedCutProfiles.Batch202.valid8105
  · exact MergedCutProfiles.Batch202.valid8106
  · exact MergedCutProfiles.Batch202.valid8107
  · exact MergedCutProfiles.Batch202.valid8108
  · exact MergedCutProfiles.Batch202.valid8109
theorem numericValid1227 : retention1227.NumericValid := by decide +kernel
def certificate1227 : RatCutBinCertificate := ⟨⟨retention1227,(568538020547612741/250000000000000000),(163394722365440633/1000000000000000000),(15026486207675484803/1000000000000000000),(52468180930640026063/250000000000000000),(1779464676748908927/1000000000000000000)⟩,(495450069802897567/500000000000000000),(368150996450388197/1000000000000000000),(263966208373994191/1000000000000000000),(145314529478412223/1000000000000000000)⟩
theorem valid1227 : certificate1227.Valid := by decide +kernel
theorem sound1227 : certificate1227.Sound := rat_cut_bin_certificate_sound certificate1227 profilesValid1227 numericValid1227 valid1227

def retention1228 : RatCutRetentionCertificate := ⟨(57/1000),(229/4000),(1398846671683693520/4648638934969235433),(1680060729616462361/1000000000000000000),(8/5),(1788535818825115805533/1280000000000000000000),true,MergedCutProfiles.Batch202.profile8110,![MergedCutProfiles.Batch202.profile8110,MergedCutProfiles.Batch202.profile8098,MergedCutProfiles.Batch202.profile8111,MergedCutProfiles.Batch202.profile8103,MergedCutProfiles.Batch202.profile8112,MergedCutProfiles.Batch202.profile8113,MergedCutProfiles.Batch202.profile8114,MergedCutProfiles.Batch202.profile8115,MergedCutProfiles.Batch202.profile8116,MergedCutProfiles.Batch202.profile8117,MergedCutProfiles.Batch202.profile8118,MergedCutProfiles.Batch202.profile8119,MergedCutProfiles.Batch203.profile8120,MergedCutProfiles.Batch203.profile8121,MergedCutProfiles.Batch203.profile8122,MergedCutProfiles.Batch203.profile8123]⟩
theorem profilesValid1228 : retention1228.ProfilesValid := by
  change ∀ j : Fin 16, (retention1228.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch202.valid8110
  · exact MergedCutProfiles.Batch202.valid8098
  · exact MergedCutProfiles.Batch202.valid8111
  · exact MergedCutProfiles.Batch202.valid8103
  · exact MergedCutProfiles.Batch202.valid8112
  · exact MergedCutProfiles.Batch202.valid8113
  · exact MergedCutProfiles.Batch202.valid8114
  · exact MergedCutProfiles.Batch202.valid8115
  · exact MergedCutProfiles.Batch202.valid8116
  · exact MergedCutProfiles.Batch202.valid8117
  · exact MergedCutProfiles.Batch202.valid8118
  · exact MergedCutProfiles.Batch202.valid8119
  · exact MergedCutProfiles.Batch203.valid8120
  · exact MergedCutProfiles.Batch203.valid8121
  · exact MergedCutProfiles.Batch203.valid8122
  · exact MergedCutProfiles.Batch203.valid8123
theorem numericValid1228 : retention1228.NumericValid := by decide +kernel
def certificate1228 : RatCutBinCertificate := ⟨⟨retention1228,(568538020547612741/250000000000000000),(163394722365440633/1000000000000000000),(15026486207675484803/1000000000000000000),(52468180930640026063/250000000000000000),(169714542242407307/125000000000000000)⟩,(495450069802897567/500000000000000000),(406565601008133759/1000000000000000000),(227520198677111147/1000000000000000000),(72589501393794391/500000000000000000)⟩
theorem valid1228 : certificate1228.Valid := by decide +kernel
theorem sound1228 : certificate1228.Sound := rat_cut_bin_certificate_sound certificate1228 profilesValid1228 numericValid1228 valid1228

def retention1229 : RatCutRetentionCertificate := ⟨(57/1000),(229/4000),(6373662567284042993/13945916804907706299),(52456750188138507/12500000000000000),1,(1657600200911407503/1600000000000000000),true,MergedCutProfiles.Batch203.profile8124,![MergedCutProfiles.Batch203.profile8124,MergedCutProfiles.Batch203.profile8125,MergedCutProfiles.Batch203.profile8126,MergedCutProfiles.Batch203.profile8127,MergedCutProfiles.Batch203.profile8128,MergedCutProfiles.Batch203.profile8129,MergedCutProfiles.Batch203.profile8130,MergedCutProfiles.Batch203.profile8131,MergedCutProfiles.Batch203.profile8132,MergedCutProfiles.Batch203.profile8133,MergedCutProfiles.Batch203.profile8134,MergedCutProfiles.Batch203.profile8135,MergedCutProfiles.Batch203.profile8136,MergedCutProfiles.Batch203.profile8137,MergedCutProfiles.Batch203.profile8138,MergedCutProfiles.Batch203.profile8139]⟩
theorem profilesValid1229 : retention1229.ProfilesValid := by
  change ∀ j : Fin 16, (retention1229.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch203.valid8124
  · exact MergedCutProfiles.Batch203.valid8125
  · exact MergedCutProfiles.Batch203.valid8126
  · exact MergedCutProfiles.Batch203.valid8127
  · exact MergedCutProfiles.Batch203.valid8128
  · exact MergedCutProfiles.Batch203.valid8129
  · exact MergedCutProfiles.Batch203.valid8130
  · exact MergedCutProfiles.Batch203.valid8131
  · exact MergedCutProfiles.Batch203.valid8132
  · exact MergedCutProfiles.Batch203.valid8133
  · exact MergedCutProfiles.Batch203.valid8134
  · exact MergedCutProfiles.Batch203.valid8135
  · exact MergedCutProfiles.Batch203.valid8136
  · exact MergedCutProfiles.Batch203.valid8137
  · exact MergedCutProfiles.Batch203.valid8138
  · exact MergedCutProfiles.Batch203.valid8139
theorem numericValid1229 : retention1229.NumericValid := by decide +kernel
def certificate1229 : RatCutBinCertificate := ⟨⟨retention1229,(568538020547612741/250000000000000000),(163394722365440633/1000000000000000000),(15026486207675484803/1000000000000000000),(52468180930640026063/250000000000000000),(1011266905887782659/1000000000000000000)⟩,(495450069802897567/500000000000000000),(461924673421920781/1000000000000000000),(7252241008225471/40000000000000000),(73122115179027127/500000000000000000)⟩
theorem valid1229 : certificate1229.Valid := by decide +kernel
theorem sound1229 : certificate1229.Sound := rat_cut_bin_certificate_sound certificate1229 profilesValid1229 numericValid1229 valid1229

def retention1230 : RatCutRetentionCertificate := ⟨(57/1000),(229/4000),(6833428960786346753/13945916804907706299),(6373662567284042993/1000000000000000000),(11/10),(2589916386677673756004215126834937926191/2549465026913617197200000000000000000000),false,MergedCutProfiles.Batch203.profile8140,(fun _ => MergedCutProfiles.Batch203.profile8140)⟩
theorem profilesValid1230 : retention1230.ProfilesValid := by
  exact MergedCutProfiles.Batch203.valid8140
theorem numericValid1230 : retention1230.NumericValid := by decide +kernel
def certificate1230 : RatCutBinCertificate := ⟨⟨retention1230,(568538020547612741/250000000000000000),(163394722365440633/1000000000000000000),(15026486207675484803/1000000000000000000),(52468180930640026063/250000000000000000),(494331045609691443/500000000000000000)⟩,(495450069802897567/500000000000000000),(90581882834529303/200000000000000000),(94178739257041311/500000000000000000),(148585647323688149/1000000000000000000)⟩
theorem valid1230 : certificate1230.Valid := by decide +kernel
theorem sound1230 : certificate1230.Sound := rat_cut_bin_certificate_sound certificate1230 profilesValid1230 numericValid1230 valid1230

def retention1231 : RatCutRetentionCertificate := ⟨(57/1000),(229/4000),(766862583377134469/1549546311656411811),(6833428960786346753/1000000000000000000),(21/20),(10883114158859274440322602901079840724351/10933486337258154804800000000000000000000),false,MergedCutProfiles.Batch203.profile8141,(fun _ => MergedCutProfiles.Batch203.profile8141)⟩
theorem profilesValid1231 : retention1231.ProfilesValid := by
  exact MergedCutProfiles.Batch203.valid8141
theorem numericValid1231 : retention1231.NumericValid := by decide +kernel
def certificate1231 : RatCutBinCertificate := ⟨⟨retention1231,(568538020547612741/250000000000000000),(163394722365440633/1000000000000000000),(15026486207675484803/1000000000000000000),(52468180930640026063/250000000000000000),(969424972039424077/1000000000000000000)⟩,(495450069802897567/500000000000000000),(229653794037743819/500000000000000000),(183334750709612663/1000000000000000000),(148501502973070623/1000000000000000000)⟩
theorem valid1231 : certificate1231.Valid := by decide +kernel
theorem sound1231 : certificate1231.Sound := rat_cut_bin_certificate_sound certificate1231 profilesValid1231 numericValid1231 valid1231

def retention1232 : RatCutRetentionCertificate := ⟨(57/1000),(229/4000),(6970780882898152324/13945916804907706299),(6901763250394210221/1000000000000000000),(21/20),(10891267933152650985942703278274568721239/11042821200630736353600000000000000000000),false,MergedCutProfiles.Batch203.profile8142,(fun _ => MergedCutProfiles.Batch203.profile8142)⟩
theorem profilesValid1232 : retention1232.ProfilesValid := by
  exact MergedCutProfiles.Batch203.valid8142
theorem numericValid1232 : retention1232.NumericValid := by decide +kernel
def certificate1232 : RatCutBinCertificate := ⟨⟨retention1232,(568538020547612741/250000000000000000),(163394722365440633/1000000000000000000),(15026486207675484803/1000000000000000000),(52468180930640026063/250000000000000000),(960308002976027293/1000000000000000000)⟩,(495450069802897567/500000000000000000),(463309392006967053/1000000000000000000),(180238614958647923/1000000000000000000),(28987772445664519/200000000000000000)⟩
theorem valid1232 : certificate1232.Valid := by decide +kernel
theorem sound1232 : certificate1232.Sound := rat_cut_bin_certificate_sound certificate1232 profilesValid1232 numericValid1232 valid1232

def retention1233 : RatCutRetentionCertificate := ⟨(57/1000),(229/4000),(1/2),(1742695220724538081/250000000000000000),(21/20),(171881088065923389382256336930978284331/174269522072453808100000000000000000000),false,MergedCutProfiles.Batch203.profile8143,(fun _ => MergedCutProfiles.Batch203.profile8143)⟩
theorem profilesValid1233 : retention1233.ProfilesValid := by
  exact MergedCutProfiles.Batch203.valid8143
theorem numericValid1233 : retention1233.NumericValid := by decide +kernel
def certificate1233 : RatCutBinCertificate := ⟨⟨retention1233,(568538020547612741/250000000000000000),(163394722365440633/1000000000000000000),(15026486207675484803/1000000000000000000),(52468180930640026063/250000000000000000),(96032677165622249/100000000000000000)⟩,(495450069802897567/500000000000000000),(92589025437189191/200000000000000000),(18051900685438873/100000000000000000),(18166122556759919/125000000000000000)⟩
theorem valid1233 : certificate1233.Valid := by decide +kernel
theorem sound1233 : certificate1233.Sound := rat_cut_bin_certificate_sound certificate1233 profilesValid1233 numericValid1233 valid1233

def retention1234 : RatCutRetentionCertificate := ⟨(57/1000),(229/4000),(1/2),64,1,(255403780475701238566389064402623374359/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch203.profile8143,(fun _ => MergedCutProfiles.Batch203.profile8143)⟩
theorem profilesValid1234 : retention1234.ProfilesValid := by
  exact MergedCutProfiles.Batch203.valid8143
theorem numericValid1234 : retention1234.NumericValid := by decide +kernel
def certificate1234 : RatCutBinCertificate := ⟨⟨retention1234,(568538020547612741/250000000000000000),(163394722365440633/1000000000000000000),(15026486207675484803/1000000000000000000),(52468180930640026063/250000000000000000),(486471042319754123/500000000000000000)⟩,(495450069802897567/500000000000000000),(106425205099911927/250000000000000000),(210742204454956633/1000000000000000000),(40022894167048117/200000000000000000)⟩
theorem valid1234 : certificate1234.Valid := by decide +kernel
theorem sound1234 : certificate1234.Sound := rat_cut_bin_certificate_sound certificate1234 profilesValid1234 numericValid1234 valid1234

def retention1235 : RatCutRetentionCertificate := ⟨(57/1000),(229/4000),(6460153988903492317/13945916804907706299),(725492933332147771/200000000000000000),(6/5),(2212116770592305706281812399984331633/2072836952377565060000000000000000000),false,MergedCutProfiles.Batch203.profile8144,(fun _ => MergedCutProfiles.Batch203.profile8144)⟩
theorem profilesValid1235 : retention1235.ProfilesValid := by
  exact MergedCutProfiles.Batch203.valid8144
theorem numericValid1235 : retention1235.NumericValid := by decide +kernel
def certificate1235 : RatCutBinCertificate := ⟨⟨retention1235,(652886521547612741/250000000000000000),(163394722365440633/1000000000000000000),(15026486207675484803/1000000000000000000),(52468180930640026063/250000000000000000),(3228468426575057/3125000000000000)⟩,(1979094719004583/2000000000000000),(9625976110706557/25000000000000000),(49494706005266827/200000000000000000),(3516560762924549/20000000000000000)⟩
theorem valid1235 : certificate1235.Valid := by decide +kernel
theorem sound1235 : certificate1235.Sound := rat_cut_bin_certificate_sound certificate1235 profilesValid1235 numericValid1235 valid1235

def certificates : List RatCutBinCertificate := [certificate1224,certificate1225,certificate1226,certificate1227,certificate1228,certificate1229,certificate1230,certificate1231,certificate1232,certificate1233,certificate1234,certificate1235]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1224,List.forall_mem_cons.mpr ⟨sound1225,List.forall_mem_cons.mpr ⟨sound1226,List.forall_mem_cons.mpr ⟨sound1227,List.forall_mem_cons.mpr ⟨sound1228,List.forall_mem_cons.mpr ⟨sound1229,List.forall_mem_cons.mpr ⟨sound1230,List.forall_mem_cons.mpr ⟨sound1231,List.forall_mem_cons.mpr ⟨sound1232,List.forall_mem_cons.mpr ⟨sound1233,List.forall_mem_cons.mpr ⟨sound1234,List.forall_mem_cons.mpr ⟨sound1235,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch102
