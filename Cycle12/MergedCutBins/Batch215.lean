import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch225
import Cycle12.MergedCutProfiles.Batch226
import Cycle12.MergedCutProfiles.Batch227
import Cycle12.MergedCutProfiles.Batch403
import Cycle12.MergedCutProfiles.Batch404
import Cycle12.MergedCutProfiles.Batch405

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch215

def retention2580 : RatCutRetentionCertificate := ⟨(3/50),(121/2000),(2153377981110932045/24487694854243433168),(221115007604568551/200000000000000000),(47/20),(24873174549268493409/12800000000000000000),true,MergedCutProfiles.Batch403.profile16133,![MergedCutProfiles.Batch403.profile16133,MergedCutProfiles.Batch403.profile16134,MergedCutProfiles.Batch403.profile16135,MergedCutProfiles.Batch403.profile16136,MergedCutProfiles.Batch225.profile9038,MergedCutProfiles.Batch403.profile16137,MergedCutProfiles.Batch225.profile9025,MergedCutProfiles.Batch403.profile16138,MergedCutProfiles.Batch403.profile16139,MergedCutProfiles.Batch226.profile9044,MergedCutProfiles.Batch403.profile16140,MergedCutProfiles.Batch403.profile16141,MergedCutProfiles.Batch403.profile16142,MergedCutProfiles.Batch403.profile16143,MergedCutProfiles.Batch403.profile16144,MergedCutProfiles.Batch403.profile16145]⟩
theorem profilesValid2580 : retention2580.ProfilesValid := by
  change ∀ j : Fin 16, (retention2580.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch403.valid16133
  · exact MergedCutProfiles.Batch403.valid16134
  · exact MergedCutProfiles.Batch403.valid16135
  · exact MergedCutProfiles.Batch403.valid16136
  · exact MergedCutProfiles.Batch225.valid9038
  · exact MergedCutProfiles.Batch403.valid16137
  · exact MergedCutProfiles.Batch225.valid9025
  · exact MergedCutProfiles.Batch403.valid16138
  · exact MergedCutProfiles.Batch403.valid16139
  · exact MergedCutProfiles.Batch226.valid9044
  · exact MergedCutProfiles.Batch403.valid16140
  · exact MergedCutProfiles.Batch403.valid16141
  · exact MergedCutProfiles.Batch403.valid16142
  · exact MergedCutProfiles.Batch403.valid16143
  · exact MergedCutProfiles.Batch403.valid16144
  · exact MergedCutProfiles.Batch403.valid16145
theorem numericValid2580 : retention2580.NumericValid := by decide +kernel
def certificate2580 : RatCutBinCertificate := ⟨⟨retention2580,(284126762733315713/125000000000000000),(93024059904071007/500000000000000000),(15866339644806527893/1000000000000000000),(12178821694455002887/31250000000000000),(1880570043786690107/1000000000000000000)⟩,(995226413818562761/1000000000000000000),(38270396768909749/125000000000000000),(331431243193689087/1000000000000000000),(201620844804207953/1000000000000000000)⟩
theorem valid2580 : certificate2580.Valid := by decide +kernel
theorem sound2580 : certificate2580.Sound := rat_cut_bin_certificate_sound certificate2580 profilesValid2580 numericValid2580 valid2580

def retention2581 : RatCutRetentionCertificate := ⟨(3/50),(121/2000),(1830582270770130631/6121923713560858292),(430675596222186409/200000000000000000),(3/2),(72112818538923413649/51200000000000000000),true,MergedCutProfiles.Batch403.profile16146,![MergedCutProfiles.Batch403.profile16146,MergedCutProfiles.Batch403.profile16147,MergedCutProfiles.Batch403.profile16148,MergedCutProfiles.Batch403.profile16149,MergedCutProfiles.Batch403.profile16150,MergedCutProfiles.Batch403.profile16151,MergedCutProfiles.Batch403.profile16152,MergedCutProfiles.Batch403.profile16153,MergedCutProfiles.Batch403.profile16154,MergedCutProfiles.Batch403.profile16155,MergedCutProfiles.Batch403.profile16156,MergedCutProfiles.Batch403.profile16157,MergedCutProfiles.Batch403.profile16158,MergedCutProfiles.Batch403.profile16159,MergedCutProfiles.Batch404.profile16160,MergedCutProfiles.Batch404.profile16161]⟩
theorem profilesValid2581 : retention2581.ProfilesValid := by
  change ∀ j : Fin 16, (retention2581.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch403.valid16146
  · exact MergedCutProfiles.Batch403.valid16147
  · exact MergedCutProfiles.Batch403.valid16148
  · exact MergedCutProfiles.Batch403.valid16149
  · exact MergedCutProfiles.Batch403.valid16150
  · exact MergedCutProfiles.Batch403.valid16151
  · exact MergedCutProfiles.Batch403.valid16152
  · exact MergedCutProfiles.Batch403.valid16153
  · exact MergedCutProfiles.Batch403.valid16154
  · exact MergedCutProfiles.Batch403.valid16155
  · exact MergedCutProfiles.Batch403.valid16156
  · exact MergedCutProfiles.Batch403.valid16157
  · exact MergedCutProfiles.Batch403.valid16158
  · exact MergedCutProfiles.Batch403.valid16159
  · exact MergedCutProfiles.Batch404.valid16160
  · exact MergedCutProfiles.Batch404.valid16161
theorem numericValid2581 : retention2581.NumericValid := by decide +kernel
def certificate2581 : RatCutBinCertificate := ⟨⟨retention2581,(284126762733315713/125000000000000000),(93024059904071007/500000000000000000),(15866339644806527893/1000000000000000000),(12178821694455002887/31250000000000000),(684233828813929317/500000000000000000)⟩,(995226413818562761/1000000000000000000),(346759166840482207/1000000000000000000),(142986617858199641/500000000000000000),(202316845734184207/1000000000000000000)⟩
theorem valid2581 : certificate2581.Valid := by decide +kernel
theorem sound2581 : certificate2581.Sound := rat_cut_bin_certificate_sound certificate2581 profilesValid2581 numericValid2581 valid2581

def retention2582 : RatCutRetentionCertificate := ⟨(3/50),(121/2000),(716128702747737470/1530480928390214573),(1830582270770130631/250000000000000000),1,(65795463401505899371/64000000000000000000),true,MergedCutProfiles.Batch404.profile16162,![MergedCutProfiles.Batch404.profile16162,MergedCutProfiles.Batch404.profile16163,MergedCutProfiles.Batch404.profile16164,MergedCutProfiles.Batch404.profile16165,MergedCutProfiles.Batch404.profile16166,MergedCutProfiles.Batch404.profile16167,MergedCutProfiles.Batch404.profile16168,MergedCutProfiles.Batch404.profile16169,MergedCutProfiles.Batch404.profile16170,MergedCutProfiles.Batch404.profile16171,MergedCutProfiles.Batch404.profile16172,MergedCutProfiles.Batch404.profile16173,MergedCutProfiles.Batch404.profile16174,MergedCutProfiles.Batch404.profile16175,MergedCutProfiles.Batch404.profile16176,MergedCutProfiles.Batch404.profile16177]⟩
theorem profilesValid2582 : retention2582.ProfilesValid := by
  change ∀ j : Fin 16, (retention2582.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch404.valid16162
  · exact MergedCutProfiles.Batch404.valid16163
  · exact MergedCutProfiles.Batch404.valid16164
  · exact MergedCutProfiles.Batch404.valid16165
  · exact MergedCutProfiles.Batch404.valid16166
  · exact MergedCutProfiles.Batch404.valid16167
  · exact MergedCutProfiles.Batch404.valid16168
  · exact MergedCutProfiles.Batch404.valid16169
  · exact MergedCutProfiles.Batch404.valid16170
  · exact MergedCutProfiles.Batch404.valid16171
  · exact MergedCutProfiles.Batch404.valid16172
  · exact MergedCutProfiles.Batch404.valid16173
  · exact MergedCutProfiles.Batch404.valid16174
  · exact MergedCutProfiles.Batch404.valid16175
  · exact MergedCutProfiles.Batch404.valid16176
  · exact MergedCutProfiles.Batch404.valid16177
theorem numericValid2582 : retention2582.NumericValid := by decide +kernel
def certificate2582 : RatCutBinCertificate := ⟨⟨retention2582,(284126762733315713/125000000000000000),(93024059904071007/500000000000000000),(15866339644806527893/1000000000000000000),(12178821694455002887/31250000000000000),(250349774382989797/250000000000000000)⟩,(995226413818562761/1000000000000000000),(398569194430064087/1000000000000000000),(117397949773133259/500000000000000000),(205774498598812871/1000000000000000000)⟩
theorem valid2582 : certificate2582.Valid := by decide +kernel
theorem sound2582 : certificate2582.Sound := rat_cut_bin_certificate_sound certificate2582 profilesValid2582 numericValid2582 valid2582

def retention2583 : RatCutRetentionCertificate := ⟨(3/50),(121/2000),(6081480387123816335/12243847427121716584),(71612870274773747/6250000000000000),(21/20),(179764836653315337141120390509643491/179032175686934367500000000000000000),false,MergedCutProfiles.Batch404.profile16178,(fun _ => MergedCutProfiles.Batch404.profile16178)⟩
theorem profilesValid2583 : retention2583.ProfilesValid := by
  exact MergedCutProfiles.Batch404.valid16178
theorem numericValid2583 : retention2583.NumericValid := by decide +kernel
def certificate2583 : RatCutBinCertificate := ⟨⟨retention2583,(284126762733315713/125000000000000000),(93024059904071007/500000000000000000),(15866339644806527893/1000000000000000000),(12178821694455002887/31250000000000000),(48805264374365863/50000000000000000)⟩,(995226413818562761/1000000000000000000),(99320410145088409/250000000000000000),(235982313323674403/1000000000000000000),(202619878489815171/1000000000000000000)⟩
theorem valid2583 : certificate2583.Valid := by decide +kernel
theorem sound2583 : certificate2583.Sound := rat_cut_bin_certificate_sound certificate2583 profilesValid2583 numericValid2583 valid2583

def retention2584 : RatCutRetentionCertificate := ⟨(3/50),(121/2000),(1/2),(1216296077424763267/100000000000000000),(21/20),(194300890563478628425773940142390984751/194607372387962122720000000000000000000),false,MergedCutProfiles.Batch227.profile9095,(fun _ => MergedCutProfiles.Batch227.profile9095)⟩
theorem profilesValid2584 : retention2584.ProfilesValid := by
  exact MergedCutProfiles.Batch227.valid9095
theorem numericValid2584 : retention2584.NumericValid := by decide +kernel
def certificate2584 : RatCutBinCertificate := ⟨⟨retention2584,(284126762733315713/125000000000000000),(93024059904071007/500000000000000000),(15866339644806527893/1000000000000000000),(12178821694455002887/31250000000000000),(194087627359648407/200000000000000000)⟩,(995226413818562761/1000000000000000000),(398402845094283983/1000000000000000000),(117474473822371877/500000000000000000),(100740243924849551/500000000000000000)⟩
theorem valid2584 : certificate2584.Valid := by decide +kernel
theorem sound2584 : certificate2584.Sound := rat_cut_bin_certificate_sound certificate2584 profilesValid2584 numericValid2584 valid2584

def retention2585 : RatCutRetentionCertificate := ⟨(3/50),(121/2000),(2755949850610783881/6121923713560858292),(634123955301402821/125000000000000000),(21/20),(8455267292920547160700533482850835649/7926549441267535262500000000000000000),false,MergedCutProfiles.Batch404.profile16179,(fun _ => MergedCutProfiles.Batch404.profile16179)⟩
theorem profilesValid2585 : retention2585.ProfilesValid := by
  exact MergedCutProfiles.Batch404.valid16179
theorem numericValid2585 : retention2585.NumericValid := by decide +kernel
def certificate2585 : RatCutBinCertificate := ⟨⟨retention2585,(316122172483315713/125000000000000000),(93024059904071007/500000000000000000),(15866339644806527893/1000000000000000000),(12178821694455002887/31250000000000000),(64722620203785849/62500000000000000)⟩,(994688224993736523/1000000000000000000),(113272896171634879/500000000000000000),(699077729985969/1600000000000000),(361488226492239649/1000000000000000000)⟩
theorem valid2585 : certificate2585.Valid := by decide +kernel
theorem sound2585 : certificate2585.Sound := rat_cut_bin_certificate_sound certificate2585 profilesValid2585 numericValid2585 valid2585

def retention2586 : RatCutRetentionCertificate := ⟨(3/50),(121/2000),(12056567055478715437/24487694854243433168),(2755949850610783881/250000000000000000),1,(8761636786195758408861993741058640371/8819039521954508419200000000000000000),false,MergedCutProfiles.Batch404.profile16180,(fun _ => MergedCutProfiles.Batch404.profile16180)⟩
theorem profilesValid2586 : retention2586.ProfilesValid := by
  exact MergedCutProfiles.Batch404.valid16180
theorem numericValid2586 : retention2586.NumericValid := by decide +kernel
def certificate2586 : RatCutBinCertificate := ⟨⟨retention2586,(316122172483315713/125000000000000000),(93024059904071007/500000000000000000),(15866339644806527893/1000000000000000000),(12178821694455002887/31250000000000000),(15059922872139421/15625000000000000)⟩,(994688224993736523/1000000000000000000),(60851229954357837/250000000000000000),(412556497478682021/1000000000000000000),(90907604003167829/250000000000000000)⟩
theorem valid2586 : certificate2586.Valid := by decide +kernel
theorem sound2586 : certificate2586.Sound := rat_cut_bin_certificate_sound certificate2586 profilesValid2586 numericValid2586 valid2586

def retention2587 : RatCutRetentionCertificate := ⟨(3/50),(121/2000),(761070795377093912/1530480928390214573),(12056567055478715437/1000000000000000000),1,(47552890840757652707951272844510235267/48226268221914861748000000000000000000),false,MergedCutProfiles.Batch404.profile16181,(fun _ => MergedCutProfiles.Batch404.profile16181)⟩
theorem profilesValid2587 : retention2587.ProfilesValid := by
  exact MergedCutProfiles.Batch404.valid16181
theorem numericValid2587 : retention2587.NumericValid := by decide +kernel
def certificate2587 : RatCutBinCertificate := ⟨⟨retention2587,(316122172483315713/125000000000000000),(93024059904071007/500000000000000000),(15866339644806527893/1000000000000000000),(12178821694455002887/31250000000000000),(239095313443080489/250000000000000000)⟩,(994688224993736523/1000000000000000000),(122650980192380907/500000000000000000),(81977604104392019/200000000000000000),(361184584032717361/1000000000000000000)⟩
theorem valid2587 : certificate2587.Valid := by decide +kernel
theorem sound2587 : certificate2587.Sound := rat_cut_bin_certificate_sound certificate2587 profilesValid2587 numericValid2587 valid2587

def retention2588 : RatCutRetentionCertificate := ⟨(3/50),(121/2000),(1/2),(95133849422136739/7812500000000000),1,(9556718954412205209615396711044939003/9741706180826802073600000000000000000),false,MergedCutProfiles.Batch227.profile9095,(fun _ => MergedCutProfiles.Batch227.profile9095)⟩
theorem profilesValid2588 : retention2588.ProfilesValid := by
  exact MergedCutProfiles.Batch227.valid9095
theorem numericValid2588 : retention2588.NumericValid := by decide +kernel
def certificate2588 : RatCutBinCertificate := ⟨⟨retention2588,(316122172483315713/125000000000000000),(93024059904071007/500000000000000000),(15866339644806527893/1000000000000000000),(12178821694455002887/31250000000000000),(475677469475233171/500000000000000000)⟩,(994688224993736523/1000000000000000000),(246597969717169729/1000000000000000000),(102018325799481717/250000000000000000),(358093931610419403/1000000000000000000)⟩
theorem valid2588 : certificate2588.Valid := by decide +kernel
theorem sound2588 : certificate2588.Sound := rat_cut_bin_certificate_sound certificate2588 profilesValid2588 numericValid2588 valid2588

def retention2589 : RatCutRetentionCertificate := ⟨(121/2000),(61/1000),(466287987517355528/12006982453999286597),(923342549539317877/1000000000000000000),(27/10),(167908565412778969383/80000000000000000000),true,MergedCutProfiles.Batch404.profile16182,![MergedCutProfiles.Batch404.profile16182,MergedCutProfiles.Batch404.profile16183,MergedCutProfiles.Batch404.profile16184,MergedCutProfiles.Batch404.profile16185,MergedCutProfiles.Batch404.profile16186,MergedCutProfiles.Batch404.profile16187,MergedCutProfiles.Batch404.profile16188,MergedCutProfiles.Batch404.profile16189,MergedCutProfiles.Batch404.profile16190,MergedCutProfiles.Batch404.profile16191,MergedCutProfiles.Batch404.profile16192,MergedCutProfiles.Batch404.profile16193,MergedCutProfiles.Batch404.profile16194,MergedCutProfiles.Batch404.profile16195,MergedCutProfiles.Batch404.profile16196,MergedCutProfiles.Batch404.profile16197]⟩
theorem profilesValid2589 : retention2589.ProfilesValid := by
  change ∀ j : Fin 16, (retention2589.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch404.valid16182
  · exact MergedCutProfiles.Batch404.valid16183
  · exact MergedCutProfiles.Batch404.valid16184
  · exact MergedCutProfiles.Batch404.valid16185
  · exact MergedCutProfiles.Batch404.valid16186
  · exact MergedCutProfiles.Batch404.valid16187
  · exact MergedCutProfiles.Batch404.valid16188
  · exact MergedCutProfiles.Batch404.valid16189
  · exact MergedCutProfiles.Batch404.valid16190
  · exact MergedCutProfiles.Batch404.valid16191
  · exact MergedCutProfiles.Batch404.valid16192
  · exact MergedCutProfiles.Batch404.valid16193
  · exact MergedCutProfiles.Batch404.valid16194
  · exact MergedCutProfiles.Batch404.valid16195
  · exact MergedCutProfiles.Batch404.valid16196
  · exact MergedCutProfiles.Batch404.valid16197
theorem numericValid2589 : retention2589.NumericValid := by decide +kernel
def certificate2589 : RatCutBinCertificate := ⟨⟨retention2589,(1138008499066886571/500000000000000000),(9485872639178457/50000000000000000),(16012521855722338481/1000000000000000000),(192854032378345754617/500000000000000000),(2026033409402451567/1000000000000000000)⟩,(248797892784723967/250000000000000000),(299972244210092373/1000000000000000000),(338818551354931111/1000000000000000000),(48574383873440901/250000000000000000)⟩
theorem valid2589 : certificate2589.Valid := by decide +kernel
theorem sound2589 : certificate2589.Sound := rat_cut_bin_certificate_sound certificate2589 profilesValid2589 numericValid2589 valid2589

def retention2590 : RatCutRetentionCertificate := ⟨(121/2000),(61/1000),(484995494000000000/12006982453999286597),(58285998439669441/62500000000000000),(53/20),(41725832070979271627/20000000000000000000),true,MergedCutProfiles.Batch404.profile16198,![MergedCutProfiles.Batch404.profile16198,MergedCutProfiles.Batch404.profile16199,MergedCutProfiles.Batch405.profile16200,MergedCutProfiles.Batch405.profile16201,MergedCutProfiles.Batch405.profile16202,MergedCutProfiles.Batch405.profile16203,MergedCutProfiles.Batch405.profile16204,MergedCutProfiles.Batch405.profile16205,MergedCutProfiles.Batch405.profile16206,MergedCutProfiles.Batch405.profile16207,MergedCutProfiles.Batch405.profile16208,MergedCutProfiles.Batch405.profile16209,MergedCutProfiles.Batch405.profile16210,MergedCutProfiles.Batch405.profile16211,MergedCutProfiles.Batch405.profile16212,MergedCutProfiles.Batch405.profile16213]⟩
theorem profilesValid2590 : retention2590.ProfilesValid := by
  change ∀ j : Fin 16, (retention2590.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch404.valid16198
  · exact MergedCutProfiles.Batch404.valid16199
  · exact MergedCutProfiles.Batch405.valid16200
  · exact MergedCutProfiles.Batch405.valid16201
  · exact MergedCutProfiles.Batch405.valid16202
  · exact MergedCutProfiles.Batch405.valid16203
  · exact MergedCutProfiles.Batch405.valid16204
  · exact MergedCutProfiles.Batch405.valid16205
  · exact MergedCutProfiles.Batch405.valid16206
  · exact MergedCutProfiles.Batch405.valid16207
  · exact MergedCutProfiles.Batch405.valid16208
  · exact MergedCutProfiles.Batch405.valid16209
  · exact MergedCutProfiles.Batch405.valid16210
  · exact MergedCutProfiles.Batch405.valid16211
  · exact MergedCutProfiles.Batch405.valid16212
  · exact MergedCutProfiles.Batch405.valid16213
theorem numericValid2590 : retention2590.NumericValid := by decide +kernel
def certificate2590 : RatCutBinCertificate := ⟨⟨retention2590,(1138008499066886571/500000000000000000),(9485872639178457/50000000000000000),(16012521855722338481/1000000000000000000),(192854032378345754617/500000000000000000),(2014816407764012043/1000000000000000000)⟩,(248797892784723967/250000000000000000),(300447984748007237/1000000000000000000),(67649279407155803/200000000000000000),(9776678742040959/50000000000000000)⟩
theorem valid2590 : certificate2590.Valid := by decide +kernel
theorem sound2590 : certificate2590.Sound := rat_cut_bin_certificate_sound certificate2590 profilesValid2590 numericValid2590 valid2590

def retention2591 : RatCutRetentionCertificate := ⟨(121/2000),(61/1000),(999847671360378109/24013964907998573194),(242497747/250000000),(51/20),(2076426449947986051/1000000000000000000),true,MergedCutProfiles.Batch405.profile16214,![MergedCutProfiles.Batch405.profile16214,MergedCutProfiles.Batch405.profile16215,MergedCutProfiles.Batch405.profile16216,MergedCutProfiles.Batch405.profile16217,MergedCutProfiles.Batch405.profile16218,MergedCutProfiles.Batch405.profile16219,MergedCutProfiles.Batch405.profile16220,MergedCutProfiles.Batch405.profile16221,MergedCutProfiles.Batch405.profile16222,MergedCutProfiles.Batch405.profile16223,MergedCutProfiles.Batch405.profile16224,MergedCutProfiles.Batch405.profile16225,MergedCutProfiles.Batch405.profile16226,MergedCutProfiles.Batch404.profile16196,MergedCutProfiles.Batch405.profile16227,MergedCutProfiles.Batch405.profile16228]⟩
theorem profilesValid2591 : retention2591.ProfilesValid := by
  change ∀ j : Fin 16, (retention2591.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch405.valid16214
  · exact MergedCutProfiles.Batch405.valid16215
  · exact MergedCutProfiles.Batch405.valid16216
  · exact MergedCutProfiles.Batch405.valid16217
  · exact MergedCutProfiles.Batch405.valid16218
  · exact MergedCutProfiles.Batch405.valid16219
  · exact MergedCutProfiles.Batch405.valid16220
  · exact MergedCutProfiles.Batch405.valid16221
  · exact MergedCutProfiles.Batch405.valid16222
  · exact MergedCutProfiles.Batch405.valid16223
  · exact MergedCutProfiles.Batch405.valid16224
  · exact MergedCutProfiles.Batch405.valid16225
  · exact MergedCutProfiles.Batch405.valid16226
  · exact MergedCutProfiles.Batch404.valid16196
  · exact MergedCutProfiles.Batch405.valid16227
  · exact MergedCutProfiles.Batch405.valid16228
theorem numericValid2591 : retention2591.NumericValid := by decide +kernel
def certificate2591 : RatCutBinCertificate := ⟨⟨retention2591,(1138008499066886571/500000000000000000),(9485872639178457/50000000000000000),(16012521855722338481/1000000000000000000),(192854032378345754617/500000000000000000),(2007648443262570147/1000000000000000000)⟩,(248797892784723967/250000000000000000),(148448793111176083/500000000000000000),(342534480800896713/1000000000000000000),(203390757719859771/1000000000000000000)⟩
theorem valid2591 : certificate2591.Valid := by decide +kernel
theorem sound2591 : certificate2591.Sound := rat_cut_bin_certificate_sound certificate2591 profilesValid2591 numericValid2591 valid2591

def certificates : List RatCutBinCertificate := [certificate2580,certificate2581,certificate2582,certificate2583,certificate2584,certificate2585,certificate2586,certificate2587,certificate2588,certificate2589,certificate2590,certificate2591]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2580,List.forall_mem_cons.mpr ⟨sound2581,List.forall_mem_cons.mpr ⟨sound2582,List.forall_mem_cons.mpr ⟨sound2583,List.forall_mem_cons.mpr ⟨sound2584,List.forall_mem_cons.mpr ⟨sound2585,List.forall_mem_cons.mpr ⟨sound2586,List.forall_mem_cons.mpr ⟨sound2587,List.forall_mem_cons.mpr ⟨sound2588,List.forall_mem_cons.mpr ⟨sound2589,List.forall_mem_cons.mpr ⟨sound2590,List.forall_mem_cons.mpr ⟨sound2591,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch215
