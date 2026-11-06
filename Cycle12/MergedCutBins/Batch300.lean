import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch431
import Cycle12.MergedCutProfiles.Batch432
import Cycle12.MergedCutProfiles.Batch433
import Cycle12.MergedCutProfiles.Batch434
import Cycle12.MergedCutProfiles.Batch552
import Cycle12.MergedCutProfiles.Batch553
import Cycle12.MergedCutProfiles.Batch554
import Cycle12.MergedCutProfiles.Batch555

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch300

def retention3600 : RatCutRetentionCertificate := ⟨(131/2000),(33/500),(22962109234296582469/49701584545203616610),(8574242735071908409/1000000000000000000),1,(35817721367604793638945380660952137323/34296970940287633636000000000000000000),false,MergedCutProfiles.Batch552.profile22118,(fun _ => MergedCutProfiles.Batch552.profile22118)⟩
theorem profilesValid3600 : retention3600.ProfilesValid := by
  exact MergedCutProfiles.Batch552.valid22118
theorem numericValid3600 : retention3600.NumericValid := by decide +kernel
def certificate3600 : RatCutBinCertificate := ⟨⟨retention3600,(1168237638436812739/500000000000000000),(229314578619222081/1000000000000000000),(17595682100602456807/1000000000000000000),(21933004553258183467/25000000000000000),(1013889773102354983/1000000000000000000)⟩,(199587011383515789/200000000000000000),(117282488604301001/1000000000000000000),(314574704900789283/500000000000000000),(71146739964774493/125000000000000000)⟩
theorem valid3600 : certificate3600.Valid := by decide +kernel
theorem sound3600 : certificate3600.Sound := rat_cut_bin_certificate_sound certificate3600 profilesValid3600 numericValid3600 valid3600

def retention3601 : RatCutRetentionCertificate := ⟨(131/2000),(33/500),(189372992838709171/382319881116950897),(22962109234296582469/1000000000000000000),1,(91837772913173602208193454874750920923/91848436937186329876000000000000000000),false,MergedCutProfiles.Batch552.profile22119,(fun _ => MergedCutProfiles.Batch552.profile22119)⟩
theorem profilesValid3601 : retention3601.ProfilesValid := by
  exact MergedCutProfiles.Batch552.valid22119
theorem numericValid3601 : retention3601.NumericValid := by decide +kernel
def certificate3601 : RatCutBinCertificate := ⟨⟨retention3601,(1168237638436812739/500000000000000000),(229314578619222081/1000000000000000000),(17595682100602456807/1000000000000000000),(21933004553258183467/25000000000000000),(969433587246890649/1000000000000000000)⟩,(199587011383515789/200000000000000000),(7666301057403589/62500000000000000),(77251760272903091/125000000000000000),(573633258743707401/1000000000000000000)⟩
theorem valid3601 : certificate3601.Valid := by decide +kernel
theorem sound3601 : certificate3601.Sound := rat_cut_bin_certificate_sound certificate3601 profilesValid3601 numericValid3601 valid3601

def retention3602 : RatCutRetentionCertificate := ⟨(131/2000),(33/500),(1/2),(2461848906903219223/100000000000000000),1,(781059359839799541008799248902223843/787791650209030151360000000000000000),false,MergedCutProfiles.Batch431.profile17278,(fun _ => MergedCutProfiles.Batch431.profile17278)⟩
theorem profilesValid3602 : retention3602.ProfilesValid := by
  exact MergedCutProfiles.Batch431.valid17278
theorem numericValid3602 : retention3602.NumericValid := by decide +kernel
def certificate3602 : RatCutBinCertificate := ⟨⟨retention3602,(1168237638436812739/500000000000000000),(229314578619222081/1000000000000000000),(17595682100602456807/1000000000000000000),(21933004553258183467/25000000000000000),(240250984979461497/250000000000000000)⟩,(199587011383515789/200000000000000000),(24747352392761209/200000000000000000),(38488184946930729/62500000000000000),(568356059040442359/1000000000000000000)⟩
theorem valid3602 : certificate3602.Valid := by decide +kernel
theorem sound3602 : certificate3602.Sound := rat_cut_bin_certificate_sound certificate3602 profilesValid3602 numericValid3602 valid3602

def retention3603 : RatCutRetentionCertificate := ⟨(33/500),(133/2000),(477611937052448927/24400471323788476259),(47288310599252369/50000000000000000),(11/4),(28148089750604089717/12800000000000000000),true,MergedCutProfiles.Batch553.profile22120,![MergedCutProfiles.Batch553.profile22120,MergedCutProfiles.Batch553.profile22121,MergedCutProfiles.Batch553.profile22122,MergedCutProfiles.Batch553.profile22123,MergedCutProfiles.Batch553.profile22124,MergedCutProfiles.Batch553.profile22125,MergedCutProfiles.Batch553.profile22126,MergedCutProfiles.Batch553.profile22127,MergedCutProfiles.Batch553.profile22128,MergedCutProfiles.Batch553.profile22129,MergedCutProfiles.Batch553.profile22130,MergedCutProfiles.Batch553.profile22131,MergedCutProfiles.Batch553.profile22132,MergedCutProfiles.Batch432.profile17318,MergedCutProfiles.Batch553.profile22133,MergedCutProfiles.Batch553.profile22134]⟩
theorem profilesValid3603 : retention3603.ProfilesValid := by
  change ∀ j : Fin 16, (retention3603.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch553.valid22120
  · exact MergedCutProfiles.Batch553.valid22121
  · exact MergedCutProfiles.Batch553.valid22122
  · exact MergedCutProfiles.Batch553.valid22123
  · exact MergedCutProfiles.Batch553.valid22124
  · exact MergedCutProfiles.Batch553.valid22125
  · exact MergedCutProfiles.Batch553.valid22126
  · exact MergedCutProfiles.Batch553.valid22127
  · exact MergedCutProfiles.Batch553.valid22128
  · exact MergedCutProfiles.Batch553.valid22129
  · exact MergedCutProfiles.Batch553.valid22130
  · exact MergedCutProfiles.Batch553.valid22131
  · exact MergedCutProfiles.Batch553.valid22132
  · exact MergedCutProfiles.Batch432.valid17318
  · exact MergedCutProfiles.Batch553.valid22133
  · exact MergedCutProfiles.Batch553.valid22134
theorem numericValid3603 : retention3603.NumericValid := by decide +kernel
def certificate3603 : RatCutBinCertificate := ⟨⟨retention3603,(574207895863854579/250000000000000000),(233579791654726571/1000000000000000000),(17766695161368751747/1000000000000000000),(217451032822346997693/250000000000000000),(2116020340985719073/1000000000000000000)⟩,(99796365706726051/100000000000000000),(279585493369142681/1000000000000000000),(364058065092927193/1000000000000000000),(13477675822095423/62500000000000000)⟩
theorem valid3603 : certificate3603.Valid := by decide +kernel
theorem sound3603 : certificate3603.Sound := rat_cut_bin_certificate_sound certificate3603 profilesValid3603 numericValid3603 valid3603

def retention3604 : RatCutRetentionCertificate := ⟨(33/500),(133/2000),(554492631632023132/24400471323788476259),(477611937052448927/500000000000000000),(11/4),(4383333610209797407/2000000000000000000),true,MergedCutProfiles.Batch553.profile22135,![MergedCutProfiles.Batch553.profile22135,MergedCutProfiles.Batch553.profile22136,MergedCutProfiles.Batch553.profile22137,MergedCutProfiles.Batch553.profile22138,MergedCutProfiles.Batch553.profile22139,MergedCutProfiles.Batch553.profile22126,MergedCutProfiles.Batch553.profile22140,MergedCutProfiles.Batch553.profile22141,MergedCutProfiles.Batch553.profile22142,MergedCutProfiles.Batch553.profile22143,MergedCutProfiles.Batch432.profile17286,MergedCutProfiles.Batch553.profile22144,MergedCutProfiles.Batch553.profile22145,MergedCutProfiles.Batch553.profile22146,MergedCutProfiles.Batch553.profile22147,MergedCutProfiles.Batch553.profile22148]⟩
theorem profilesValid3604 : retention3604.ProfilesValid := by
  change ∀ j : Fin 16, (retention3604.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch553.valid22135
  · exact MergedCutProfiles.Batch553.valid22136
  · exact MergedCutProfiles.Batch553.valid22137
  · exact MergedCutProfiles.Batch553.valid22138
  · exact MergedCutProfiles.Batch553.valid22139
  · exact MergedCutProfiles.Batch553.valid22126
  · exact MergedCutProfiles.Batch553.valid22140
  · exact MergedCutProfiles.Batch553.valid22141
  · exact MergedCutProfiles.Batch553.valid22142
  · exact MergedCutProfiles.Batch553.valid22143
  · exact MergedCutProfiles.Batch432.valid17286
  · exact MergedCutProfiles.Batch553.valid22144
  · exact MergedCutProfiles.Batch553.valid22145
  · exact MergedCutProfiles.Batch553.valid22146
  · exact MergedCutProfiles.Batch553.valid22147
  · exact MergedCutProfiles.Batch553.valid22148
theorem numericValid3604 : retention3604.NumericValid := by decide +kernel
def certificate3604 : RatCutBinCertificate := ⟨⟨retention3604,(574207895863854579/250000000000000000),(233579791654726571/1000000000000000000),(17766695161368751747/1000000000000000000),(217451032822346997693/250000000000000000),(1054308859608300887/500000000000000000)⟩,(99796365706726051/100000000000000000),(279366680411290019/1000000000000000000),(9108419727369953/25000000000000000),(43142348895995077/200000000000000000)⟩
theorem valid3604 : certificate3604.Valid := by decide +kernel
theorem sound3604 : certificate3604.Sound := rat_cut_bin_certificate_sound certificate3604 profilesValid3604 numericValid3604 valid3604

def retention3605 : RatCutRetentionCertificate := ⟨(33/500),(133/2000),(561930102500000000/24400471323788476259),(138623157908005783/125000000000000000),(12/5),(21701757443338958979/10000000000000000000),true,MergedCutProfiles.Batch553.profile22135,![MergedCutProfiles.Batch553.profile22135,MergedCutProfiles.Batch553.profile22136,MergedCutProfiles.Batch553.profile22149,MergedCutProfiles.Batch553.profile22150,MergedCutProfiles.Batch553.profile22151,MergedCutProfiles.Batch553.profile22152,MergedCutProfiles.Batch553.profile22153,MergedCutProfiles.Batch553.profile22154,MergedCutProfiles.Batch553.profile22155,MergedCutProfiles.Batch553.profile22156,MergedCutProfiles.Batch432.profile17302,MergedCutProfiles.Batch553.profile22157,MergedCutProfiles.Batch553.profile22158,MergedCutProfiles.Batch553.profile22159,MergedCutProfiles.Batch554.profile22160,MergedCutProfiles.Batch554.profile22161]⟩
theorem profilesValid3605 : retention3605.ProfilesValid := by
  change ∀ j : Fin 16, (retention3605.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch553.valid22135
  · exact MergedCutProfiles.Batch553.valid22136
  · exact MergedCutProfiles.Batch553.valid22149
  · exact MergedCutProfiles.Batch553.valid22150
  · exact MergedCutProfiles.Batch553.valid22151
  · exact MergedCutProfiles.Batch553.valid22152
  · exact MergedCutProfiles.Batch553.valid22153
  · exact MergedCutProfiles.Batch553.valid22154
  · exact MergedCutProfiles.Batch553.valid22155
  · exact MergedCutProfiles.Batch553.valid22156
  · exact MergedCutProfiles.Batch432.valid17302
  · exact MergedCutProfiles.Batch553.valid22157
  · exact MergedCutProfiles.Batch553.valid22158
  · exact MergedCutProfiles.Batch553.valid22159
  · exact MergedCutProfiles.Batch554.valid22160
  · exact MergedCutProfiles.Batch554.valid22161
theorem numericValid3605 : retention3605.NumericValid := by decide +kernel
def certificate3605 : RatCutBinCertificate := ⟨⟨retention3605,(574207895863854579/250000000000000000),(233579791654726571/1000000000000000000),(17766695161368751747/1000000000000000000),(217451032822346997693/250000000000000000),(2097696638692430067/1000000000000000000)⟩,(99796365706726051/100000000000000000),(6602292517887661/25000000000000000),(384221938134317737/1000000000000000000),(126094794625462689/500000000000000000)⟩
theorem valid3605 : certificate3605.Valid := by decide +kernel
theorem sound3605 : certificate3605.Sound := rat_cut_bin_certificate_sound certificate3605 profilesValid3605 numericValid3605 valid3605

def retention3606 : RatCutRetentionCertificate := ⟨(33/500),(133/2000),(1380371545414808781/48800942647576952518),(224772041/200000000),(12/5),(8624729576690278473/4000000000000000000),true,MergedCutProfiles.Batch554.profile22162,![MergedCutProfiles.Batch554.profile22162,MergedCutProfiles.Batch554.profile22163,MergedCutProfiles.Batch554.profile22164,MergedCutProfiles.Batch553.profile22139,MergedCutProfiles.Batch554.profile22165,MergedCutProfiles.Batch554.profile22166,MergedCutProfiles.Batch554.profile22167,MergedCutProfiles.Batch554.profile22168,MergedCutProfiles.Batch553.profile22132,MergedCutProfiles.Batch554.profile22169,MergedCutProfiles.Batch554.profile22170,MergedCutProfiles.Batch553.profile22147,MergedCutProfiles.Batch554.profile22161,MergedCutProfiles.Batch554.profile22171,MergedCutProfiles.Batch554.profile22172,MergedCutProfiles.Batch433.profile17333]⟩
theorem profilesValid3606 : retention3606.ProfilesValid := by
  change ∀ j : Fin 16, (retention3606.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch554.valid22162
  · exact MergedCutProfiles.Batch554.valid22163
  · exact MergedCutProfiles.Batch554.valid22164
  · exact MergedCutProfiles.Batch553.valid22139
  · exact MergedCutProfiles.Batch554.valid22165
  · exact MergedCutProfiles.Batch554.valid22166
  · exact MergedCutProfiles.Batch554.valid22167
  · exact MergedCutProfiles.Batch554.valid22168
  · exact MergedCutProfiles.Batch553.valid22132
  · exact MergedCutProfiles.Batch554.valid22169
  · exact MergedCutProfiles.Batch554.valid22170
  · exact MergedCutProfiles.Batch553.valid22147
  · exact MergedCutProfiles.Batch554.valid22161
  · exact MergedCutProfiles.Batch554.valid22171
  · exact MergedCutProfiles.Batch554.valid22172
  · exact MergedCutProfiles.Batch433.valid17333
theorem numericValid3606 : retention3606.NumericValid := by decide +kernel
def certificate3606 : RatCutBinCertificate := ⟨⟨retention3606,(574207895863854579/250000000000000000),(233579791654726571/1000000000000000000),(17766695161368751747/1000000000000000000),(217451032822346997693/250000000000000000),(1041851692655903429/500000000000000000)⟩,(99796365706726051/100000000000000000),(264480421557069437/1000000000000000000),(76741049810038051/200000000000000000),(125701470867376429/500000000000000000)⟩
theorem valid3606 : certificate3606.Valid := by decide +kernel
theorem sound3606 : certificate3606.Sound := rat_cut_bin_certificate_sound certificate3606 profilesValid3606 numericValid3606 valid3606

def retention3607 : RatCutRetentionCertificate := ⟨(33/500),(133/2000),(4693804246680911631/48800942647576952518),(1380371545414808781/1000000000000000000),(21/10),(2467752957632151817833/1280000000000000000000),true,MergedCutProfiles.Batch554.profile22173,![MergedCutProfiles.Batch554.profile22173,MergedCutProfiles.Batch554.profile22174,MergedCutProfiles.Batch554.profile22175,MergedCutProfiles.Batch433.profile17320,MergedCutProfiles.Batch554.profile22176,MergedCutProfiles.Batch554.profile22177,MergedCutProfiles.Batch554.profile22178,MergedCutProfiles.Batch433.profile17326,MergedCutProfiles.Batch554.profile22179,MergedCutProfiles.Batch554.profile22180,MergedCutProfiles.Batch554.profile22181,MergedCutProfiles.Batch554.profile22182,MergedCutProfiles.Batch554.profile22183,MergedCutProfiles.Batch554.profile22184,MergedCutProfiles.Batch554.profile22185,MergedCutProfiles.Batch554.profile22186]⟩
theorem profilesValid3607 : retention3607.ProfilesValid := by
  change ∀ j : Fin 16, (retention3607.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch554.valid22173
  · exact MergedCutProfiles.Batch554.valid22174
  · exact MergedCutProfiles.Batch554.valid22175
  · exact MergedCutProfiles.Batch433.valid17320
  · exact MergedCutProfiles.Batch554.valid22176
  · exact MergedCutProfiles.Batch554.valid22177
  · exact MergedCutProfiles.Batch554.valid22178
  · exact MergedCutProfiles.Batch433.valid17326
  · exact MergedCutProfiles.Batch554.valid22179
  · exact MergedCutProfiles.Batch554.valid22180
  · exact MergedCutProfiles.Batch554.valid22181
  · exact MergedCutProfiles.Batch554.valid22182
  · exact MergedCutProfiles.Batch554.valid22183
  · exact MergedCutProfiles.Batch554.valid22184
  · exact MergedCutProfiles.Batch554.valid22185
  · exact MergedCutProfiles.Batch554.valid22186
theorem numericValid3607 : retention3607.NumericValid := by decide +kernel
def certificate3607 : RatCutBinCertificate := ⟨⟨retention3607,(574207895863854579/250000000000000000),(233579791654726571/1000000000000000000),(17766695161368751747/1000000000000000000),(217451032822346997693/250000000000000000),(1864513304292359211/1000000000000000000)⟩,(99796365706726051/100000000000000000),(137065841432038727/500000000000000000),(74211229425584891/200000000000000000),(125796484339702691/500000000000000000)⟩
theorem valid3607 : certificate3607.Valid := by decide +kernel
theorem sound3607 : certificate3607.Sound := rat_cut_bin_certificate_sound certificate3607 profilesValid3607 numericValid3607 valid3607

def retention3608 : RatCutRetentionCertificate := ⟨(33/500),(133/2000),(19669929269450821779/48800942647576952518),(4693804246680911631/1000000000000000000),(21/20),(1480211367286128685479/1280000000000000000000),true,MergedCutProfiles.Batch432.profile17305,![MergedCutProfiles.Batch432.profile17305,MergedCutProfiles.Batch554.profile22187,MergedCutProfiles.Batch554.profile22188,MergedCutProfiles.Batch554.profile22189,MergedCutProfiles.Batch554.profile22190,MergedCutProfiles.Batch554.profile22191,MergedCutProfiles.Batch554.profile22192,MergedCutProfiles.Batch554.profile22193,MergedCutProfiles.Batch554.profile22194,MergedCutProfiles.Batch554.profile22195,MergedCutProfiles.Batch554.profile22196,MergedCutProfiles.Batch554.profile22197,MergedCutProfiles.Batch554.profile22198,MergedCutProfiles.Batch554.profile22199,MergedCutProfiles.Batch555.profile22200,MergedCutProfiles.Batch555.profile22201]⟩
theorem profilesValid3608 : retention3608.ProfilesValid := by
  change ∀ j : Fin 16, (retention3608.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch432.valid17305
  · exact MergedCutProfiles.Batch554.valid22187
  · exact MergedCutProfiles.Batch554.valid22188
  · exact MergedCutProfiles.Batch554.valid22189
  · exact MergedCutProfiles.Batch554.valid22190
  · exact MergedCutProfiles.Batch554.valid22191
  · exact MergedCutProfiles.Batch554.valid22192
  · exact MergedCutProfiles.Batch554.valid22193
  · exact MergedCutProfiles.Batch554.valid22194
  · exact MergedCutProfiles.Batch554.valid22195
  · exact MergedCutProfiles.Batch554.valid22196
  · exact MergedCutProfiles.Batch554.valid22197
  · exact MergedCutProfiles.Batch554.valid22198
  · exact MergedCutProfiles.Batch554.valid22199
  · exact MergedCutProfiles.Batch555.valid22200
  · exact MergedCutProfiles.Batch555.valid22201
theorem numericValid3608 : retention3608.NumericValid := by decide +kernel
def certificate3608 : RatCutBinCertificate := ⟨⟨retention3608,(574207895863854579/250000000000000000),(233579791654726571/1000000000000000000),(17766695161368751747/1000000000000000000),(217451032822346997693/250000000000000000),(1124706993431414541/1000000000000000000)⟩,(99796365706726051/100000000000000000),(43064615242951789/125000000000000000),(288354902452080439/1000000000000000000),(63287529798948951/250000000000000000)⟩
theorem valid3608 : certificate3608.Valid := by decide +kernel
theorem sound3608 : certificate3608.Sound := rat_cut_bin_certificate_sound certificate3608 profilesValid3608 numericValid3608 valid3608

def retention3609 : RatCutRetentionCertificate := ⟨(33/500),(133/2000),(24001051781064880131/48800942647576952518),(19669929269450821779/1000000000000000000),1,(15812891446525855566135191825390225167/15735943415560657423200000000000000000),false,MergedCutProfiles.Batch555.profile22202,(fun _ => MergedCutProfiles.Batch555.profile22202)⟩
theorem profilesValid3609 : retention3609.ProfilesValid := by
  exact MergedCutProfiles.Batch555.valid22202
theorem numericValid3609 : retention3609.NumericValid := by decide +kernel
def certificate3609 : RatCutBinCertificate := ⟨⟨retention3609,(574207895863854579/250000000000000000),(233579791654726571/1000000000000000000),(17766695161368751747/1000000000000000000),(217451032822346997693/250000000000000000),(487346480293332097/500000000000000000)⟩,(99796365706726051/100000000000000000),(357305514019652923/1000000000000000000),(137481882082814979/500000000000000000),(254814416233666647/1000000000000000000)⟩
theorem valid3609 : certificate3609.Valid := by decide +kernel
theorem sound3609 : certificate3609.Sound := rat_cut_bin_certificate_sound certificate3609 profilesValid3609 numericValid3609 valid3609

def retention3610 : RatCutRetentionCertificate := ⟨(33/500),(133/2000),(24241062298875528933/48800942647576952518),(24001051781064880131/1000000000000000000),1,(95774323951450363369598829199701908483/96004207124259520524000000000000000000),false,MergedCutProfiles.Batch555.profile22203,(fun _ => MergedCutProfiles.Batch555.profile22203)⟩
theorem profilesValid3610 : retention3610.ProfilesValid := by
  exact MergedCutProfiles.Batch555.valid22203
theorem numericValid3610 : retention3610.NumericValid := by decide +kernel
def certificate3610 : RatCutBinCertificate := ⟨⟨retention3610,(574207895863854579/250000000000000000),(233579791654726571/1000000000000000000),(17766695161368751747/1000000000000000000),(217451032822346997693/250000000000000000),(193481714014821357/200000000000000000)⟩,(99796365706726051/100000000000000000),(35770315926293981/100000000000000000),(2144959348025091/7812500000000000),(254781267708375953/1000000000000000000)⟩
theorem valid3610 : certificate3610.Valid := by decide +kernel
theorem sound3610 : certificate3610.Sound := rat_cut_bin_certificate_sound certificate3610 profilesValid3610 numericValid3610 valid3610

def retention3611 : RatCutRetentionCertificate := ⟨(33/500),(133/2000),(1/2),(24241062298875528933/1000000000000000000),1,(24030140151687090324479438687866981589/24241062298875528933000000000000000000),false,MergedCutProfiles.Batch434.profile17377,(fun _ => MergedCutProfiles.Batch434.profile17377)⟩
theorem profilesValid3611 : retention3611.ProfilesValid := by
  exact MergedCutProfiles.Batch434.valid17377
theorem numericValid3611 : retention3611.NumericValid := by decide +kernel
def certificate3611 : RatCutBinCertificate := ⟨⟨retention3611,(574207895863854579/250000000000000000),(233579791654726571/1000000000000000000),(17766695161368751747/1000000000000000000),(217451032822346997693/250000000000000000),(961102057468410413/1000000000000000000)⟩,(99796365706726051/100000000000000000),(359946544969813321/1000000000000000000),(272255790619378207/1000000000000000000),(251160123137255673/1000000000000000000)⟩
theorem valid3611 : certificate3611.Valid := by decide +kernel
theorem sound3611 : certificate3611.Sound := rat_cut_bin_certificate_sound certificate3611 profilesValid3611 numericValid3611 valid3611

def certificates : List RatCutBinCertificate := [certificate3600,certificate3601,certificate3602,certificate3603,certificate3604,certificate3605,certificate3606,certificate3607,certificate3608,certificate3609,certificate3610,certificate3611]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3600,List.forall_mem_cons.mpr ⟨sound3601,List.forall_mem_cons.mpr ⟨sound3602,List.forall_mem_cons.mpr ⟨sound3603,List.forall_mem_cons.mpr ⟨sound3604,List.forall_mem_cons.mpr ⟨sound3605,List.forall_mem_cons.mpr ⟨sound3606,List.forall_mem_cons.mpr ⟨sound3607,List.forall_mem_cons.mpr ⟨sound3608,List.forall_mem_cons.mpr ⟨sound3609,List.forall_mem_cons.mpr ⟨sound3610,List.forall_mem_cons.mpr ⟨sound3611,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch300
