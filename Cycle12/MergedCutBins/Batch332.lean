import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch352
import Cycle12.MergedCutProfiles.Batch353
import Cycle12.MergedCutProfiles.Batch354
import Cycle12.MergedCutProfiles.Batch355
import Cycle12.MergedCutProfiles.Batch356
import Cycle12.MergedCutProfiles.Batch474
import Cycle12.MergedCutProfiles.Batch475
import Cycle12.MergedCutProfiles.Batch476
import Cycle12.MergedCutProfiles.Batch602
import Cycle12.MergedCutProfiles.Batch603
import Cycle12.MergedCutProfiles.Batch604

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch332

def retention3984 : RatCutRetentionCertificate := ⟨(1/25),(41/1000),(298568226323743172/298298758095224492837),(585370505487193749/1000000000000000000),4,(572742597264706005461/256000000000000000000),true,MergedCutProfiles.Batch602.profile24115,![MergedCutProfiles.Batch602.profile24115,MergedCutProfiles.Batch602.profile24116,MergedCutProfiles.Batch602.profile24117,MergedCutProfiles.Batch602.profile24118,MergedCutProfiles.Batch602.profile24119,MergedCutProfiles.Batch603.profile24120,MergedCutProfiles.Batch603.profile24121,MergedCutProfiles.Batch603.profile24122,MergedCutProfiles.Batch603.profile24123,MergedCutProfiles.Batch603.profile24124,MergedCutProfiles.Batch603.profile24125,MergedCutProfiles.Batch603.profile24126,MergedCutProfiles.Batch352.profile14116,MergedCutProfiles.Batch603.profile24127,MergedCutProfiles.Batch474.profile18990,MergedCutProfiles.Batch353.profile14132]⟩
theorem profilesValid3984 : retention3984.ProfilesValid := by
  change ∀ j : Fin 16, (retention3984.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch602.valid24115
  · exact MergedCutProfiles.Batch602.valid24116
  · exact MergedCutProfiles.Batch602.valid24117
  · exact MergedCutProfiles.Batch602.valid24118
  · exact MergedCutProfiles.Batch602.valid24119
  · exact MergedCutProfiles.Batch603.valid24120
  · exact MergedCutProfiles.Batch603.valid24121
  · exact MergedCutProfiles.Batch603.valid24122
  · exact MergedCutProfiles.Batch603.valid24123
  · exact MergedCutProfiles.Batch603.valid24124
  · exact MergedCutProfiles.Batch603.valid24125
  · exact MergedCutProfiles.Batch603.valid24126
  · exact MergedCutProfiles.Batch352.valid14116
  · exact MergedCutProfiles.Batch603.valid24127
  · exact MergedCutProfiles.Batch474.valid18990
  · exact MergedCutProfiles.Batch353.valid14132
theorem numericValid3984 : retention3984.NumericValid := by decide +kernel
def certificate3984 : RatCutBinCertificate := ⟨⟨retention3984,(1879310693912993307/1000000000000000000),(77009395027439323/1000000000000000000),(354771271768005051/31250000000000000),(1361922342917941387443/200000000000000000),(27328541384172661/12500000000000000)⟩,(49987207575576837/50000000000000000),(712898648588691231/1000000000000000000),(22922515287432689/500000000000000000),(20309044438677539/1000000000000000000)⟩
theorem valid3984 : certificate3984.Valid := by decide +kernel
theorem sound3984 : certificate3984.Sound := rat_cut_bin_certificate_sound certificate3984 profilesValid3984 numericValid3984 valid3984

def retention3985 : RatCutRetentionCertificate := ⟨(1/25),(41/1000),(568330522000000000/298298758095224492837),(74642056580935793/125000000000000000),4,(4504722954377703697/2000000000000000000),true,MergedCutProfiles.Batch602.profile24116,![MergedCutProfiles.Batch602.profile24116,MergedCutProfiles.Batch603.profile24128,MergedCutProfiles.Batch603.profile24129,MergedCutProfiles.Batch474.profile18989,MergedCutProfiles.Batch603.profile24130,MergedCutProfiles.Batch603.profile24131,MergedCutProfiles.Batch603.profile24132,MergedCutProfiles.Batch603.profile24133,MergedCutProfiles.Batch603.profile24134,MergedCutProfiles.Batch474.profile18970,MergedCutProfiles.Batch603.profile24135,MergedCutProfiles.Batch474.profile18991,MergedCutProfiles.Batch475.profile19004,MergedCutProfiles.Batch603.profile24136,MergedCutProfiles.Batch474.profile18972,MergedCutProfiles.Batch603.profile24137]⟩
theorem profilesValid3985 : retention3985.ProfilesValid := by
  change ∀ j : Fin 16, (retention3985.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch602.valid24116
  · exact MergedCutProfiles.Batch603.valid24128
  · exact MergedCutProfiles.Batch603.valid24129
  · exact MergedCutProfiles.Batch474.valid18989
  · exact MergedCutProfiles.Batch603.valid24130
  · exact MergedCutProfiles.Batch603.valid24131
  · exact MergedCutProfiles.Batch603.valid24132
  · exact MergedCutProfiles.Batch603.valid24133
  · exact MergedCutProfiles.Batch603.valid24134
  · exact MergedCutProfiles.Batch474.valid18970
  · exact MergedCutProfiles.Batch603.valid24135
  · exact MergedCutProfiles.Batch474.valid18991
  · exact MergedCutProfiles.Batch475.valid19004
  · exact MergedCutProfiles.Batch603.valid24136
  · exact MergedCutProfiles.Batch474.valid18972
  · exact MergedCutProfiles.Batch603.valid24137
theorem numericValid3985 : retention3985.NumericValid := by decide +kernel
def certificate3985 : RatCutBinCertificate := ⟨⟨retention3985,(1879310693912993307/1000000000000000000),(77009395027439323/1000000000000000000),(354771271768005051/31250000000000000),(1361922342917941387443/200000000000000000),(440273804442030913/200000000000000000)⟩,(49987207575576837/50000000000000000),(174688405590478679/250000000000000000),(12693300295392117/250000000000000000),(4540601894237711/200000000000000000)⟩
theorem valid3985 : certificate3985.Valid := by decide +kernel
theorem sound3985 : certificate3985.Sound := rat_cut_bin_certificate_sound certificate3985 profilesValid3985 numericValid3985 valid3985

def retention3986 : RatCutRetentionCertificate := ⟨(1/25),(41/1000),(995244567907935838/298298758095224492837),(284165261/250000000),(11/4),(18766510774945350619/8000000000000000000),true,MergedCutProfiles.Batch603.profile24138,![MergedCutProfiles.Batch603.profile24138,MergedCutProfiles.Batch474.profile18980,MergedCutProfiles.Batch603.profile24124,MergedCutProfiles.Batch603.profile24132,MergedCutProfiles.Batch603.profile24139,MergedCutProfiles.Batch603.profile24140,MergedCutProfiles.Batch603.profile24141,MergedCutProfiles.Batch603.profile24136,MergedCutProfiles.Batch474.profile18992,MergedCutProfiles.Batch474.profile18973,MergedCutProfiles.Batch603.profile24142,MergedCutProfiles.Batch603.profile24143,MergedCutProfiles.Batch474.profile18974,MergedCutProfiles.Batch353.profile14134,MergedCutProfiles.Batch603.profile24144,MergedCutProfiles.Batch603.profile24145]⟩
theorem profilesValid3986 : retention3986.ProfilesValid := by
  change ∀ j : Fin 16, (retention3986.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch603.valid24138
  · exact MergedCutProfiles.Batch474.valid18980
  · exact MergedCutProfiles.Batch603.valid24124
  · exact MergedCutProfiles.Batch603.valid24132
  · exact MergedCutProfiles.Batch603.valid24139
  · exact MergedCutProfiles.Batch603.valid24140
  · exact MergedCutProfiles.Batch603.valid24141
  · exact MergedCutProfiles.Batch603.valid24136
  · exact MergedCutProfiles.Batch474.valid18992
  · exact MergedCutProfiles.Batch474.valid18973
  · exact MergedCutProfiles.Batch603.valid24142
  · exact MergedCutProfiles.Batch603.valid24143
  · exact MergedCutProfiles.Batch474.valid18974
  · exact MergedCutProfiles.Batch353.valid14134
  · exact MergedCutProfiles.Batch603.valid24144
  · exact MergedCutProfiles.Batch603.valid24145
theorem numericValid3986 : retention3986.NumericValid := by decide +kernel
def certificate3986 : RatCutBinCertificate := ⟨⟨retention3986,(1879310693912993307/1000000000000000000),(77009395027439323/1000000000000000000),(354771271768005051/31250000000000000),(1361922342917941387443/200000000000000000),(1155378286610008251/500000000000000000)⟩,(49987207575576837/50000000000000000),(457362913650679087/1000000000000000000),(92425942380870983/500000000000000000),(122382047067600707/1000000000000000000)⟩
theorem valid3986 : certificate3986.Valid := by decide +kernel
theorem sound3986 : certificate3986.Sound := rat_cut_bin_certificate_sound certificate3986 profilesValid3986 numericValid3986 valid3986

def retention3987 : RatCutRetentionCertificate := ⟨(1/25),(41/1000),(32000000000000000000/298298758095224492837),(497622283953967919/250000000000000000),(37/20),(375185786806538409546174583354529405431/199048913581587167600000000000000000000),false,MergedCutProfiles.Batch603.profile24146,(fun _ => MergedCutProfiles.Batch603.profile24146)⟩
theorem profilesValid3987 : retention3987.ProfilesValid := by
  exact MergedCutProfiles.Batch603.valid24146
theorem numericValid3987 : retention3987.NumericValid := by decide +kernel
def certificate3987 : RatCutBinCertificate := ⟨⟨retention3987,(1879310693912993307/1000000000000000000),(77009395027439323/1000000000000000000),(354771271768005051/31250000000000000),(1361922342917941387443/200000000000000000),(1861308440704334673/1000000000000000000)⟩,(49987207575576837/50000000000000000),(445022635906965273/1000000000000000000),(19467330110715837/100000000000000000),(6151530953653647/40000000000000000)⟩
theorem valid3987 : certificate3987.Valid := by decide +kernel
theorem sound3987 : certificate3987.Sound := rat_cut_bin_certificate_sound certificate3987 profilesValid3987 numericValid3987 valid3987

def retention3988 : RatCutRetentionCertificate := ⟨(1/25),(41/1000),(1/2),64,1,(255384100590301156902854846823122473239/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch354.profile14195,(fun _ => MergedCutProfiles.Batch354.profile14195)⟩
theorem profilesValid3988 : retention3988.ProfilesValid := by
  exact MergedCutProfiles.Batch354.valid14195
theorem numericValid3988 : retention3988.NumericValid := by decide +kernel
def certificate3988 : RatCutBinCertificate := ⟨⟨retention3988,(1879310693912993307/1000000000000000000),(77009395027439323/1000000000000000000),(354771271768005051/31250000000000000),(1361922342917941387443/200000000000000000),(123105760911392691/125000000000000000)⟩,(49987207575576837/50000000000000000),(541765097664406997/1000000000000000000),(63087363435004299/500000000000000000),(122347875194223839/1000000000000000000)⟩
theorem valid3988 : certificate3988.Valid := by decide +kernel
theorem sound3988 : certificate3988.Sound := rat_cut_bin_certificate_sound certificate3988 profilesValid3988 numericValid3988 valid3988

def retention3989 : RatCutRetentionCertificate := ⟨(1/25),(41/1000),(32000000000000000000/298298758095224492837),(23933415582803348961/1000000000000000000),1,(44336788485441510034847899926918047921/23933415582803348961000000000000000000),false,MergedCutProfiles.Batch603.profile24146,(fun _ => MergedCutProfiles.Batch603.profile24146)⟩
theorem profilesValid3989 : retention3989.ProfilesValid := by
  exact MergedCutProfiles.Batch603.valid24146
theorem numericValid3989 : retention3989.NumericValid := by decide +kernel
def certificate3989 : RatCutBinCertificate := ⟨⟨retention3989,(1832242798912993307/1000000000000000000),(77009395027439323/1000000000000000000),(354771271768005051/31250000000000000),(1361922342917941387443/200000000000000000),(184007690690137127/100000000000000000)⟩,(499875279719392311/500000000000000000),(6414313809188389/200000000000000000),(104781773699836513/125000000000000000),(286392804948051871/200000000000000000)⟩
theorem valid3989 : certificate3989.Valid := by decide +kernel
theorem sound3989 : certificate3989.Sound := rat_cut_bin_certificate_sound certificate3989 profilesValid3989 numericValid3989 valid3989

def retention3990 : RatCutRetentionCertificate := ⟨(1/25),(41/1000),(1/2),64,1,(255384100590301156902854846823122473239/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch354.profile14195,(fun _ => MergedCutProfiles.Batch354.profile14195)⟩
theorem profilesValid3990 : retention3990.ProfilesValid := by
  exact MergedCutProfiles.Batch354.valid14195
theorem numericValid3990 : retention3990.NumericValid := by decide +kernel
def certificate3990 : RatCutBinCertificate := ⟨⟨retention3990,(1832242798912993307/1000000000000000000),(77009395027439323/1000000000000000000),(354771271768005051/31250000000000000),(1361922342917941387443/200000000000000000),(985165366134308899/1000000000000000000)⟩,(499875279719392311/500000000000000000),(59902789519587251/1000000000000000000),(372226389345893/488281250000000),(739439406983486257/1000000000000000000)⟩
theorem valid3990 : certificate3990.Valid := by decide +kernel
theorem sound3990 : certificate3990.Sound := rat_cut_bin_certificate_sound certificate3990 profilesValid3990 numericValid3990 valid3990

def retention3991 : RatCutRetentionCertificate := ⟨(41/1000),(21/500),(297267497513959982/282724551084683841297),(588648509928633627/1000000000000000000),4,(574512119408908961211/256000000000000000000),true,MergedCutProfiles.Batch603.profile24147,![MergedCutProfiles.Batch603.profile24147,MergedCutProfiles.Batch603.profile24148,MergedCutProfiles.Batch603.profile24149,MergedCutProfiles.Batch603.profile24150,MergedCutProfiles.Batch603.profile24151,MergedCutProfiles.Batch603.profile24152,MergedCutProfiles.Batch603.profile24153,MergedCutProfiles.Batch603.profile24154,MergedCutProfiles.Batch603.profile24155,MergedCutProfiles.Batch603.profile24156,MergedCutProfiles.Batch476.profile19062,MergedCutProfiles.Batch603.profile24157,MergedCutProfiles.Batch476.profile19041,MergedCutProfiles.Batch603.profile24158,MergedCutProfiles.Batch476.profile19052,MergedCutProfiles.Batch603.profile24159]⟩
theorem profilesValid3991 : retention3991.ProfilesValid := by
  change ∀ j : Fin 16, (retention3991.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch603.valid24147
  · exact MergedCutProfiles.Batch603.valid24148
  · exact MergedCutProfiles.Batch603.valid24149
  · exact MergedCutProfiles.Batch603.valid24150
  · exact MergedCutProfiles.Batch603.valid24151
  · exact MergedCutProfiles.Batch603.valid24152
  · exact MergedCutProfiles.Batch603.valid24153
  · exact MergedCutProfiles.Batch603.valid24154
  · exact MergedCutProfiles.Batch603.valid24155
  · exact MergedCutProfiles.Batch603.valid24156
  · exact MergedCutProfiles.Batch476.valid19062
  · exact MergedCutProfiles.Batch603.valid24157
  · exact MergedCutProfiles.Batch476.valid19041
  · exact MergedCutProfiles.Batch603.valid24158
  · exact MergedCutProfiles.Batch476.valid19052
  · exact MergedCutProfiles.Batch603.valid24159
theorem numericValid3991 : retention3991.NumericValid := by decide +kernel
def certificate3991 : RatCutBinCertificate := ⟨⟨retention3991,(376815787954060891/200000000000000000),(81190354661587239/1000000000000000000),(11528872124124012319/1000000000000000000),(6554467217879598236817/1000000000000000000),(2191114312601716089/1000000000000000000)⟩,(99973468084633257/100000000000000000),(17710922471148997/25000000000000000),(5921118691058343/125000000000000000),(2630460309697829/125000000000000000)⟩
theorem valid3991 : certificate3991.Valid := by decide +kernel
theorem sound3991 : certificate3991.Sound := rat_cut_bin_certificate_sound certificate3991 profilesValid3991 numericValid3991 valid3991

def retention3992 : RatCutRetentionCertificate := ⟨(41/1000),(21/500),(559088946500000000/282724551084683841297),(148633748756979991/250000000000000000),4,(4496383931117590201/2000000000000000000),true,MergedCutProfiles.Batch604.profile24160,![MergedCutProfiles.Batch604.profile24160,MergedCutProfiles.Batch604.profile24161,MergedCutProfiles.Batch604.profile24162,MergedCutProfiles.Batch476.profile19051,MergedCutProfiles.Batch604.profile24163,MergedCutProfiles.Batch476.profile19062,MergedCutProfiles.Batch354.profile14198,MergedCutProfiles.Batch476.profile19052,MergedCutProfiles.Batch604.profile24164,MergedCutProfiles.Batch356.profile14250,MergedCutProfiles.Batch604.profile24165,MergedCutProfiles.Batch476.profile19063,MergedCutProfiles.Batch604.profile24166,MergedCutProfiles.Batch604.profile24167,MergedCutProfiles.Batch604.profile24168,MergedCutProfiles.Batch476.profile19054]⟩
theorem profilesValid3992 : retention3992.ProfilesValid := by
  change ∀ j : Fin 16, (retention3992.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch604.valid24160
  · exact MergedCutProfiles.Batch604.valid24161
  · exact MergedCutProfiles.Batch604.valid24162
  · exact MergedCutProfiles.Batch476.valid19051
  · exact MergedCutProfiles.Batch604.valid24163
  · exact MergedCutProfiles.Batch476.valid19062
  · exact MergedCutProfiles.Batch354.valid14198
  · exact MergedCutProfiles.Batch476.valid19052
  · exact MergedCutProfiles.Batch604.valid24164
  · exact MergedCutProfiles.Batch356.valid14250
  · exact MergedCutProfiles.Batch604.valid24165
  · exact MergedCutProfiles.Batch476.valid19063
  · exact MergedCutProfiles.Batch604.valid24166
  · exact MergedCutProfiles.Batch604.valid24167
  · exact MergedCutProfiles.Batch604.valid24168
  · exact MergedCutProfiles.Batch476.valid19054
theorem numericValid3992 : retention3992.NumericValid := by decide +kernel
def certificate3992 : RatCutBinCertificate := ⟨⟨retention3992,(376815787954060891/200000000000000000),(81190354661587239/1000000000000000000),(11528872124124012319/1000000000000000000),(6554467217879598236817/1000000000000000000),(2195118314483895233/1000000000000000000)⟩,(99973468084633257/100000000000000000),(702513472734873829/1000000000000000000),(12358888407856627/250000000000000000),(4407113586978231/200000000000000000)⟩
theorem valid3992 : certificate3992.Valid := by decide +kernel
theorem sound3992 : certificate3992.Sound := rat_cut_bin_certificate_sound certificate3992 profilesValid3992 numericValid3992 valid3992

def retention3993 : RatCutRetentionCertificate := ⟨(41/1000),(21/500),(1181278266585308339/565449102169367682594),(1118177893/1000000000),(14/5),(2646180930992152012194247691683460319/1118177893000000000000000000000000000),true,MergedCutProfiles.Batch603.profile24148,![MergedCutProfiles.Batch603.profile24148,MergedCutProfiles.Batch603.profile24150,MergedCutProfiles.Batch603.profile24152,MergedCutProfiles.Batch603.profile24154,MergedCutProfiles.Batch603.profile24156,MergedCutProfiles.Batch603.profile24157,MergedCutProfiles.Batch604.profile24169,MergedCutProfiles.Batch603.profile24159,MergedCutProfiles.Batch604.profile24170,MergedCutProfiles.Batch604.profile24171,MergedCutProfiles.Batch604.profile24172,MergedCutProfiles.Batch475.profile19029,MergedCutProfiles.Batch354.profile14199,MergedCutProfiles.Batch604.profile24173,MergedCutProfiles.Batch604.profile24174,MergedCutProfiles.Batch356.profile14264]⟩
theorem profilesValid3993 : retention3993.ProfilesValid := by
  change ∀ j : Fin 16, (retention3993.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch603.valid24148
  · exact MergedCutProfiles.Batch603.valid24150
  · exact MergedCutProfiles.Batch603.valid24152
  · exact MergedCutProfiles.Batch603.valid24154
  · exact MergedCutProfiles.Batch603.valid24156
  · exact MergedCutProfiles.Batch603.valid24157
  · exact MergedCutProfiles.Batch604.valid24169
  · exact MergedCutProfiles.Batch603.valid24159
  · exact MergedCutProfiles.Batch604.valid24170
  · exact MergedCutProfiles.Batch604.valid24171
  · exact MergedCutProfiles.Batch604.valid24172
  · exact MergedCutProfiles.Batch475.valid19029
  · exact MergedCutProfiles.Batch354.valid14199
  · exact MergedCutProfiles.Batch604.valid24173
  · exact MergedCutProfiles.Batch604.valid24174
  · exact MergedCutProfiles.Batch356.valid14264
theorem numericValid3993 : retention3993.NumericValid := by decide +kernel
def certificate3993 : RatCutBinCertificate := ⟨⟨retention3993,(376815787954060891/200000000000000000),(81190354661587239/1000000000000000000),(11528872124124012319/1000000000000000000),(6554467217879598236817/1000000000000000000),(582340017404322381/250000000000000000)⟩,(99973468084633257/100000000000000000),(57205863609417383/125000000000000000),(4615745293104803/25000000000000000),(24262889058131463/200000000000000000)⟩
theorem valid3993 : certificate3993.Valid := by decide +kernel
theorem sound3993 : certificate3993.Sound := rat_cut_bin_certificate_sound certificate3993 profilesValid3993 numericValid3993 valid3993

def retention3994 : RatCutRetentionCertificate := ⟨(41/1000),(21/500),(2789051465369805278/282724551084683841297),(1181278266585308339/1000000000000000000),(53/20),(730775635180241354109/320000000000000000000),true,MergedCutProfiles.Batch604.profile24163,![MergedCutProfiles.Batch604.profile24163,MergedCutProfiles.Batch356.profile14250,MergedCutProfiles.Batch604.profile24168,MergedCutProfiles.Batch604.profile24175,MergedCutProfiles.Batch355.profile14216,MergedCutProfiles.Batch604.profile24176,MergedCutProfiles.Batch355.profile14202,MergedCutProfiles.Batch604.profile24177,MergedCutProfiles.Batch476.profile19058,MergedCutProfiles.Batch355.profile14219,MergedCutProfiles.Batch476.profile19050,MergedCutProfiles.Batch604.profile24178,MergedCutProfiles.Batch355.profile14234,MergedCutProfiles.Batch604.profile24179,MergedCutProfiles.Batch355.profile14222,MergedCutProfiles.Batch604.profile24180]⟩
theorem profilesValid3994 : retention3994.ProfilesValid := by
  change ∀ j : Fin 16, (retention3994.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch604.valid24163
  · exact MergedCutProfiles.Batch356.valid14250
  · exact MergedCutProfiles.Batch604.valid24168
  · exact MergedCutProfiles.Batch604.valid24175
  · exact MergedCutProfiles.Batch355.valid14216
  · exact MergedCutProfiles.Batch604.valid24176
  · exact MergedCutProfiles.Batch355.valid14202
  · exact MergedCutProfiles.Batch604.valid24177
  · exact MergedCutProfiles.Batch476.valid19058
  · exact MergedCutProfiles.Batch355.valid14219
  · exact MergedCutProfiles.Batch476.valid19050
  · exact MergedCutProfiles.Batch604.valid24178
  · exact MergedCutProfiles.Batch355.valid14234
  · exact MergedCutProfiles.Batch604.valid24179
  · exact MergedCutProfiles.Batch355.valid14222
  · exact MergedCutProfiles.Batch604.valid24180
theorem numericValid3994 : retention3994.NumericValid := by decide +kernel
def certificate3994 : RatCutBinCertificate := ⟨⟨retention3994,(376815787954060891/200000000000000000),(81190354661587239/1000000000000000000),(11528872124124012319/1000000000000000000),(6554467217879598236817/1000000000000000000),(562128152527871137/250000000000000000)⟩,(99973468084633257/100000000000000000),(57657617025356461/125000000000000000),(36363827563020037/200000000000000000),(121336858100029951/1000000000000000000)⟩
theorem valid3994 : certificate3994.Valid := by decide +kernel
theorem sound3994 : certificate3994.Sound := rat_cut_bin_certificate_sound certificate3994 profilesValid3994 numericValid3994 valid3994

def retention3995 : RatCutRetentionCertificate := ⟨(41/1000),(21/500),(32000000000000000000/282724551084683841297),(1394525732684902639/250000000000000000),(6/5),(1030483586795554976166830020212199283439/557810293073961055600000000000000000000),false,MergedCutProfiles.Batch604.profile24181,(fun _ => MergedCutProfiles.Batch604.profile24181)⟩
theorem profilesValid3995 : retention3995.ProfilesValid := by
  exact MergedCutProfiles.Batch604.valid24181
theorem numericValid3995 : retention3995.NumericValid := by decide +kernel
def certificate3995 : RatCutBinCertificate := ⟨⟨retention3995,(376815787954060891/200000000000000000),(81190354661587239/1000000000000000000),(11528872124124012319/1000000000000000000),(6554467217879598236817/1000000000000000000),(915725400416098399/500000000000000000)⟩,(99973468084633257/100000000000000000),(346091617295862523/1000000000000000000),(286680775839892017/1000000000000000000),(178097631722945051/500000000000000000)⟩
theorem valid3995 : certificate3995.Valid := by decide +kernel
theorem sound3995 : certificate3995.Sound := rat_cut_bin_certificate_sound certificate3995 profilesValid3995 numericValid3995 valid3995

def certificates : List RatCutBinCertificate := [certificate3984,certificate3985,certificate3986,certificate3987,certificate3988,certificate3989,certificate3990,certificate3991,certificate3992,certificate3993,certificate3994,certificate3995]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3984,List.forall_mem_cons.mpr ⟨sound3985,List.forall_mem_cons.mpr ⟨sound3986,List.forall_mem_cons.mpr ⟨sound3987,List.forall_mem_cons.mpr ⟨sound3988,List.forall_mem_cons.mpr ⟨sound3989,List.forall_mem_cons.mpr ⟨sound3990,List.forall_mem_cons.mpr ⟨sound3991,List.forall_mem_cons.mpr ⟨sound3992,List.forall_mem_cons.mpr ⟨sound3993,List.forall_mem_cons.mpr ⟨sound3994,List.forall_mem_cons.mpr ⟨sound3995,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch332
