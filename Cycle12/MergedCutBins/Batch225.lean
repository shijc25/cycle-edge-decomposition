import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch427
import Cycle12.MergedCutProfiles.Batch428
import Cycle12.MergedCutProfiles.Batch429

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch225

def retention2700 : RatCutRetentionCertificate := ⟨(129/2000),(13/200),(10266951888450570517/20627668549903675062),(2541324724864002603/250000000000000000),1,(9975121042703736362815105692510902519/10165298899456010412000000000000000000),false,MergedCutProfiles.Batch427.profile17086,(fun _ => MergedCutProfiles.Batch427.profile17086)⟩
theorem profilesValid2700 : retention2700.ProfilesValid := by
  exact MergedCutProfiles.Batch427.valid17086
theorem numericValid2700 : retention2700.NumericValid := by decide +kernel
def certificate2700 : RatCutBinCertificate := ⟨⟨retention2700,(644396879280307411/250000000000000000),(55239130418189853/250000000000000000),(17259045206314115447/1000000000000000000),(357140519850849198987/1000000000000000000),(118536281360668511/125000000000000000)⟩,(994338794346485983/1000000000000000000),(242182904023524141/1000000000000000000),(207141576435233679/500000000000000000),(11162322912187977/31250000000000000)⟩
theorem valid2700 : certificate2700.Valid := by decide +kernel
theorem sound2700 : certificate2700.Sound := rat_cut_bin_certificate_sound certificate2700 profilesValid2700 numericValid2700 valid2700

def retention2701 : RatCutRetentionCertificate := ⟨(129/2000),(13/200),(1/2),(10266951888450570517/1000000000000000000),1,(8026342395241637781681027406989459431/8213561510760456413600000000000000000),false,MergedCutProfiles.Batch427.profile17083,(fun _ => MergedCutProfiles.Batch427.profile17083)⟩
theorem profilesValid2701 : retention2701.ProfilesValid := by
  exact MergedCutProfiles.Batch427.valid17083
theorem numericValid2701 : retention2701.NumericValid := by decide +kernel
def certificate2701 : RatCutBinCertificate := ⟨⟨retention2701,(644396879280307411/250000000000000000),(55239130418189853/250000000000000000),(17259045206314115447/1000000000000000000),(357140519850849198987/1000000000000000000),(94420490448709859/100000000000000000)⟩,(994338794346485983/1000000000000000000),(243230770911281477/1000000000000000000),(82560438508014563/200000000000000000),(4435174532639751/12500000000000000)⟩
theorem valid2701 : certificate2701.Valid := by decide +kernel
theorem sound2701 : certificate2701.Sound := rat_cut_bin_certificate_sound certificate2701 profilesValid2701 numericValid2701 valid2701

def retention2702 : RatCutRetentionCertificate := ⟨(13/200),(131/2000),(192129823557380341/4049927709295342925),(190227548076614199/200000000000000000),(51/20),(4112608675247934717/2000000000000000000),true,MergedCutProfiles.Batch427.profile17087,![MergedCutProfiles.Batch427.profile17087,MergedCutProfiles.Batch427.profile17088,MergedCutProfiles.Batch427.profile17089,MergedCutProfiles.Batch427.profile17090,MergedCutProfiles.Batch427.profile17091,MergedCutProfiles.Batch427.profile17092,MergedCutProfiles.Batch427.profile17093,MergedCutProfiles.Batch427.profile17094,MergedCutProfiles.Batch427.profile17095,MergedCutProfiles.Batch427.profile17096,MergedCutProfiles.Batch427.profile17097,MergedCutProfiles.Batch427.profile17098,MergedCutProfiles.Batch427.profile17099,MergedCutProfiles.Batch427.profile17100,MergedCutProfiles.Batch427.profile17101,MergedCutProfiles.Batch427.profile17102]⟩
theorem profilesValid2702 : retention2702.ProfilesValid := by
  change ∀ j : Fin 16, (retention2702.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch427.valid17087
  · exact MergedCutProfiles.Batch427.valid17088
  · exact MergedCutProfiles.Batch427.valid17089
  · exact MergedCutProfiles.Batch427.valid17090
  · exact MergedCutProfiles.Batch427.valid17091
  · exact MergedCutProfiles.Batch427.valid17092
  · exact MergedCutProfiles.Batch427.valid17093
  · exact MergedCutProfiles.Batch427.valid17094
  · exact MergedCutProfiles.Batch427.valid17095
  · exact MergedCutProfiles.Batch427.valid17096
  · exact MergedCutProfiles.Batch427.valid17097
  · exact MergedCutProfiles.Batch427.valid17098
  · exact MergedCutProfiles.Batch427.valid17099
  · exact MergedCutProfiles.Batch427.valid17100
  · exact MergedCutProfiles.Batch427.valid17101
  · exact MergedCutProfiles.Batch427.valid17102
theorem numericValid2702 : retention2702.NumericValid := by decide +kernel
def certificate2702 : RatCutBinCertificate := ⟨⟨retention2702,(2343127524524707053/1000000000000000000),(225107070921290071/1000000000000000000),(4356274722595414287/250000000000000000),(88493122161958402527/250000000000000000),(494774015650502929/250000000000000000)⟩,(62177209425696241/62500000000000000),(69054168882748939/250000000000000000),(73673636542830891/200000000000000000),(215236797009407673/1000000000000000000)⟩
theorem valid2702 : certificate2702.Valid := by decide +kernel
theorem sound2702 : certificate2702.Sound := rat_cut_bin_certificate_sound certificate2702 profilesValid2702 numericValid2702 valid2702

def retention2703 : RatCutRetentionCertificate := ⟨(13/200),(131/2000),(52934136000000/1072828532263667),(192129823557380341/200000000000000000),(51/20),(1644038001369627339/800000000000000000),true,MergedCutProfiles.Batch427.profile17103,![MergedCutProfiles.Batch427.profile17103,MergedCutProfiles.Batch427.profile17104,MergedCutProfiles.Batch427.profile17105,MergedCutProfiles.Batch427.profile17106,MergedCutProfiles.Batch427.profile17107,MergedCutProfiles.Batch427.profile17108,MergedCutProfiles.Batch427.profile17109,MergedCutProfiles.Batch427.profile17110,MergedCutProfiles.Batch427.profile17111,MergedCutProfiles.Batch427.profile17112,MergedCutProfiles.Batch427.profile17113,MergedCutProfiles.Batch427.profile17114,MergedCutProfiles.Batch427.profile17115,MergedCutProfiles.Batch427.profile17116,MergedCutProfiles.Batch427.profile17117,MergedCutProfiles.Batch427.profile17118]⟩
theorem profilesValid2703 : retention2703.ProfilesValid := by
  change ∀ j : Fin 16, (retention2703.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch427.valid17103
  · exact MergedCutProfiles.Batch427.valid17104
  · exact MergedCutProfiles.Batch427.valid17105
  · exact MergedCutProfiles.Batch427.valid17106
  · exact MergedCutProfiles.Batch427.valid17107
  · exact MergedCutProfiles.Batch427.valid17108
  · exact MergedCutProfiles.Batch427.valid17109
  · exact MergedCutProfiles.Batch427.valid17110
  · exact MergedCutProfiles.Batch427.valid17111
  · exact MergedCutProfiles.Batch427.valid17112
  · exact MergedCutProfiles.Batch427.valid17113
  · exact MergedCutProfiles.Batch427.valid17114
  · exact MergedCutProfiles.Batch427.valid17115
  · exact MergedCutProfiles.Batch427.valid17116
  · exact MergedCutProfiles.Batch427.valid17117
  · exact MergedCutProfiles.Batch427.valid17118
theorem numericValid2703 : retention2703.NumericValid := by decide +kernel
def certificate2703 : RatCutBinCertificate := ⟨⟨retention2703,(2343127524524707053/1000000000000000000),(225107070921290071/1000000000000000000),(4356274722595414287/250000000000000000),(88493122161958402527/250000000000000000),(1977839427074820987/1000000000000000000)⟩,(62177209425696241/62500000000000000),(137670765692879143/500000000000000000),(369494507045949887/1000000000000000000),(4326234133874793/20000000000000000)⟩
theorem valid2703 : certificate2703.Valid := by decide +kernel
theorem sound2703 : certificate2703.Sound := rat_cut_bin_certificate_sound certificate2703 profilesValid2703 numericValid2703 valid2703

def retention2704 : RatCutRetentionCertificate := ⟨(13/200),(131/2000),(1183896230262462478/20249638546476714625),(999131817/1000000000),(49/20),(8089200121007025057/4000000000000000000),true,MergedCutProfiles.Batch427.profile17119,![MergedCutProfiles.Batch427.profile17119,MergedCutProfiles.Batch428.profile17120,MergedCutProfiles.Batch428.profile17121,MergedCutProfiles.Batch428.profile17122,MergedCutProfiles.Batch428.profile17123,MergedCutProfiles.Batch428.profile17124,MergedCutProfiles.Batch428.profile17125,MergedCutProfiles.Batch428.profile17126,MergedCutProfiles.Batch428.profile17127,MergedCutProfiles.Batch428.profile17128,MergedCutProfiles.Batch427.profile17115,MergedCutProfiles.Batch428.profile17129,MergedCutProfiles.Batch427.profile17102,MergedCutProfiles.Batch428.profile17130,MergedCutProfiles.Batch428.profile17131,MergedCutProfiles.Batch428.profile17132]⟩
theorem profilesValid2704 : retention2704.ProfilesValid := by
  change ∀ j : Fin 16, (retention2704.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch427.valid17119
  · exact MergedCutProfiles.Batch428.valid17120
  · exact MergedCutProfiles.Batch428.valid17121
  · exact MergedCutProfiles.Batch428.valid17122
  · exact MergedCutProfiles.Batch428.valid17123
  · exact MergedCutProfiles.Batch428.valid17124
  · exact MergedCutProfiles.Batch428.valid17125
  · exact MergedCutProfiles.Batch428.valid17126
  · exact MergedCutProfiles.Batch428.valid17127
  · exact MergedCutProfiles.Batch428.valid17128
  · exact MergedCutProfiles.Batch427.valid17115
  · exact MergedCutProfiles.Batch428.valid17129
  · exact MergedCutProfiles.Batch427.valid17102
  · exact MergedCutProfiles.Batch428.valid17130
  · exact MergedCutProfiles.Batch428.valid17131
  · exact MergedCutProfiles.Batch428.valid17132
theorem numericValid2704 : retention2704.NumericValid := by decide +kernel
def certificate2704 : RatCutBinCertificate := ⟨⟨retention2704,(2343127524524707053/1000000000000000000),(225107070921290071/1000000000000000000),(4356274722595414287/250000000000000000),(88493122161958402527/250000000000000000),(1948119709229500287/1000000000000000000)⟩,(62177209425696241/62500000000000000),(275433633378139327/1000000000000000000),(369375840553524543/1000000000000000000),(220314346682688529/1000000000000000000)⟩
theorem valid2704 : certificate2704.Valid := by decide +kernel
theorem sound2704 : certificate2704.Sound := rat_cut_bin_certificate_sound certificate2704 profilesValid2704 numericValid2704 valid2704

def retention2705 : RatCutRetentionCertificate := ⟨(13/200),(131/2000),(20175673082034088/161997108371813717),(591948115131231239/500000000000000000),(43/20),(1173719402807263478183/640000000000000000000),true,MergedCutProfiles.Batch428.profile17133,![MergedCutProfiles.Batch428.profile17133,MergedCutProfiles.Batch428.profile17134,MergedCutProfiles.Batch428.profile17135,MergedCutProfiles.Batch428.profile17136,MergedCutProfiles.Batch428.profile17137,MergedCutProfiles.Batch428.profile17138,MergedCutProfiles.Batch428.profile17139,MergedCutProfiles.Batch428.profile17140,MergedCutProfiles.Batch428.profile17141,MergedCutProfiles.Batch428.profile17142,MergedCutProfiles.Batch428.profile17143,MergedCutProfiles.Batch428.profile17144,MergedCutProfiles.Batch428.profile17145,MergedCutProfiles.Batch428.profile17146,MergedCutProfiles.Batch428.profile17147,MergedCutProfiles.Batch428.profile17148]⟩
theorem profilesValid2705 : retention2705.ProfilesValid := by
  change ∀ j : Fin 16, (retention2705.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch428.valid17133
  · exact MergedCutProfiles.Batch428.valid17134
  · exact MergedCutProfiles.Batch428.valid17135
  · exact MergedCutProfiles.Batch428.valid17136
  · exact MergedCutProfiles.Batch428.valid17137
  · exact MergedCutProfiles.Batch428.valid17138
  · exact MergedCutProfiles.Batch428.valid17139
  · exact MergedCutProfiles.Batch428.valid17140
  · exact MergedCutProfiles.Batch428.valid17141
  · exact MergedCutProfiles.Batch428.valid17142
  · exact MergedCutProfiles.Batch428.valid17143
  · exact MergedCutProfiles.Batch428.valid17144
  · exact MergedCutProfiles.Batch428.valid17145
  · exact MergedCutProfiles.Batch428.valid17146
  · exact MergedCutProfiles.Batch428.valid17147
  · exact MergedCutProfiles.Batch428.valid17148
theorem numericValid2705 : retention2705.NumericValid := by decide +kernel
def certificate2705 : RatCutBinCertificate := ⟨⟨retention2705,(2343127524524707053/1000000000000000000),(225107070921290071/1000000000000000000),(4356274722595414287/250000000000000000),(88493122161958402527/250000000000000000),(442210049535523701/250000000000000000)⟩,(62177209425696241/62500000000000000),(7143049986218019/25000000000000000),(356310154500597873/1000000000000000000),(220165669065837537/1000000000000000000)⟩
theorem valid2705 : certificate2705.Valid := by decide +kernel
theorem sound2705 : certificate2705.Sound := rat_cut_bin_certificate_sound certificate2705 profilesValid2705 numericValid2705 valid2705

def retention2706 : RatCutRetentionCertificate := ⟨(13/200),(131/2000),(1419681471204878587/4049927709295342925),(2521959135254261/1000000000000000),(13/10),(8223401634054466229/6400000000000000000),true,MergedCutProfiles.Batch428.profile17124,![MergedCutProfiles.Batch428.profile17124,MergedCutProfiles.Batch428.profile17129,MergedCutProfiles.Batch428.profile17149,MergedCutProfiles.Batch428.profile17150,MergedCutProfiles.Batch428.profile17151,MergedCutProfiles.Batch428.profile17152,MergedCutProfiles.Batch428.profile17153,MergedCutProfiles.Batch428.profile17154,MergedCutProfiles.Batch428.profile17155,MergedCutProfiles.Batch428.profile17156,MergedCutProfiles.Batch428.profile17157,MergedCutProfiles.Batch428.profile17158,MergedCutProfiles.Batch428.profile17159,MergedCutProfiles.Batch429.profile17160,MergedCutProfiles.Batch429.profile17161,MergedCutProfiles.Batch429.profile17162]⟩
theorem profilesValid2706 : retention2706.ProfilesValid := by
  change ∀ j : Fin 16, (retention2706.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch428.valid17124
  · exact MergedCutProfiles.Batch428.valid17129
  · exact MergedCutProfiles.Batch428.valid17149
  · exact MergedCutProfiles.Batch428.valid17150
  · exact MergedCutProfiles.Batch428.valid17151
  · exact MergedCutProfiles.Batch428.valid17152
  · exact MergedCutProfiles.Batch428.valid17153
  · exact MergedCutProfiles.Batch428.valid17154
  · exact MergedCutProfiles.Batch428.valid17155
  · exact MergedCutProfiles.Batch428.valid17156
  · exact MergedCutProfiles.Batch428.valid17157
  · exact MergedCutProfiles.Batch428.valid17158
  · exact MergedCutProfiles.Batch428.valid17159
  · exact MergedCutProfiles.Batch429.valid17160
  · exact MergedCutProfiles.Batch429.valid17161
  · exact MergedCutProfiles.Batch429.valid17162
theorem numericValid2706 : retention2706.NumericValid := by decide +kernel
def certificate2706 : RatCutBinCertificate := ⟨⟨retention2706,(2343127524524707053/1000000000000000000),(225107070921290071/1000000000000000000),(4356274722595414287/250000000000000000),(88493122161958402527/250000000000000000),(1245548108854940647/1000000000000000000)⟩,(62177209425696241/62500000000000000),(166968796427707311/500000000000000000),(74947537248333207/250000000000000000),(220946579067061129/1000000000000000000)⟩
theorem valid2706 : certificate2706.Valid := by decide +kernel
theorem sound2706 : certificate2706.Sound := rat_cut_bin_certificate_sound certificate2706 profilesValid2706 numericValid2706 valid2706

def retention2707 : RatCutRetentionCertificate := ⟨(13/200),(131/2000),(9663256461962682634/20249638546476714625),(1419681471204878587/200000000000000000),1,(51682347855044736187/51200000000000000000),true,MergedCutProfiles.Batch429.profile17163,![MergedCutProfiles.Batch429.profile17163,MergedCutProfiles.Batch429.profile17164,MergedCutProfiles.Batch429.profile17165,MergedCutProfiles.Batch429.profile17166,MergedCutProfiles.Batch429.profile17167,MergedCutProfiles.Batch429.profile17168,MergedCutProfiles.Batch429.profile17169,MergedCutProfiles.Batch429.profile17170,MergedCutProfiles.Batch429.profile17171,MergedCutProfiles.Batch429.profile17172,MergedCutProfiles.Batch429.profile17173,MergedCutProfiles.Batch429.profile17174,MergedCutProfiles.Batch429.profile17175,MergedCutProfiles.Batch429.profile17176,MergedCutProfiles.Batch429.profile17177,MergedCutProfiles.Batch429.profile17178]⟩
theorem profilesValid2707 : retention2707.ProfilesValid := by
  change ∀ j : Fin 16, (retention2707.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch429.valid17163
  · exact MergedCutProfiles.Batch429.valid17164
  · exact MergedCutProfiles.Batch429.valid17165
  · exact MergedCutProfiles.Batch429.valid17166
  · exact MergedCutProfiles.Batch429.valid17167
  · exact MergedCutProfiles.Batch429.valid17168
  · exact MergedCutProfiles.Batch429.valid17169
  · exact MergedCutProfiles.Batch429.valid17170
  · exact MergedCutProfiles.Batch429.valid17171
  · exact MergedCutProfiles.Batch429.valid17172
  · exact MergedCutProfiles.Batch429.valid17173
  · exact MergedCutProfiles.Batch429.valid17174
  · exact MergedCutProfiles.Batch429.valid17175
  · exact MergedCutProfiles.Batch429.valid17176
  · exact MergedCutProfiles.Batch429.valid17177
  · exact MergedCutProfiles.Batch429.valid17178
theorem numericValid2707 : retention2707.NumericValid := by decide +kernel
def certificate2707 : RatCutBinCertificate := ⟨⟨retention2707,(2343127524524707053/1000000000000000000),(225107070921290071/1000000000000000000),(4356274722595414287/250000000000000000),(88493122161958402527/250000000000000000),(979148326572880523/1000000000000000000)⟩,(62177209425696241/62500000000000000),(372674581658363923/1000000000000000000),(259474065186233073/1000000000000000000),(44403558174268373/200000000000000000)⟩
theorem valid2707 : certificate2707.Valid := by decide +kernel
theorem sound2707 : certificate2707.Sound := rat_cut_bin_certificate_sound certificate2707 profilesValid2707 numericValid2707 valid2707

def retention2708 : RatCutRetentionCertificate := ⟨(13/200),(131/2000),(10055623423976780021/20249638546476714625),(4831628230981341317/500000000000000000),(21/20),(31987729759600268488242432672236770271/31944649461033661600000000000000000000),false,MergedCutProfiles.Batch429.profile17179,(fun _ => MergedCutProfiles.Batch429.profile17179)⟩
theorem profilesValid2708 : retention2708.ProfilesValid := by
  exact MergedCutProfiles.Batch429.valid17179
theorem numericValid2708 : retention2708.NumericValid := by decide +kernel
def certificate2708 : RatCutBinCertificate := ⟨⟨retention2708,(2343127524524707053/1000000000000000000),(225107070921290071/1000000000000000000),(4356274722595414287/250000000000000000),(88493122161958402527/250000000000000000),(193912658182243969/200000000000000000)⟩,(62177209425696241/62500000000000000),(184330113290470479/500000000000000000),(263457756680998333/1000000000000000000),(6930032510565583/31250000000000000)⟩
theorem valid2708 : certificate2708.Valid := by decide +kernel
theorem sound2708 : certificate2708.Sound := rat_cut_bin_certificate_sound certificate2708 profilesValid2708 numericValid2708 valid2708

def retention2709 : RatCutRetentionCertificate := ⟨(13/200),(131/2000),(1/2),(10055623423976780021/1000000000000000000),(21/20),(16015826385655280085870492150819409582839/16088997478362848033600000000000000000000),false,MergedCutProfiles.Batch429.profile17180,(fun _ => MergedCutProfiles.Batch429.profile17180)⟩
theorem profilesValid2709 : retention2709.ProfilesValid := by
  exact MergedCutProfiles.Batch429.valid17180
theorem numericValid2709 : retention2709.NumericValid := by decide +kernel
def certificate2709 : RatCutBinCertificate := ⟨⟨retention2709,(2343127524524707053/1000000000000000000),(225107070921290071/1000000000000000000),(4356274722595414287/250000000000000000),(88493122161958402527/250000000000000000),(963666880308102539/1000000000000000000)⟩,(62177209425696241/62500000000000000),(37007950061220917/100000000000000000),(262044357660360013/1000000000000000000),(44011177908171127/200000000000000000)⟩
theorem valid2709 : certificate2709.Valid := by decide +kernel
theorem sound2709 : certificate2709.Sound := rat_cut_bin_certificate_sound certificate2709 profilesValid2709 numericValid2709 valid2709

def retention2710 : RatCutRetentionCertificate := ⟨(13/200),(131/2000),(9230361554101649228/20249638546476714625),(4786389565516300381/1000000000000000000),(21/20),(8063347349108714283778373460671986693239/7658223304826080609600000000000000000000),false,MergedCutProfiles.Batch429.profile17181,(fun _ => MergedCutProfiles.Batch429.profile17181)⟩
theorem profilesValid2710 : retention2710.ProfilesValid := by
  exact MergedCutProfiles.Batch429.valid17181
theorem numericValid2710 : retention2710.NumericValid := by decide +kernel
def certificate2710 : RatCutBinCertificate := ⟨⟨retention2710,(2585937105524707053/1000000000000000000),(225107070921290071/1000000000000000000),(4356274722595414287/250000000000000000),(88493122161958402527/250000000000000000),(1017819192869084531/1000000000000000000)⟩,(994299292264416211/1000000000000000000),(444058734046709/1953125000000000),(435722051202929343/1000000000000000000),(351851934675690921/1000000000000000000)⟩
theorem valid2710 : certificate2710.Valid := by decide +kernel
theorem sound2710 : certificate2710.Sound := rat_cut_bin_certificate_sound certificate2710 profilesValid2710 numericValid2710 valid2710

def retention2711 : RatCutRetentionCertificate := ⟨(13/200),(131/2000),(9995158904230597532/20249638546476714625),(2307590388525412307/250000000000000000),1,(7285371533866713663984536981531789651/7384289243281319382400000000000000000),false,MergedCutProfiles.Batch429.profile17182,(fun _ => MergedCutProfiles.Batch429.profile17182)⟩
theorem profilesValid2711 : retention2711.ProfilesValid := by
  exact MergedCutProfiles.Batch429.valid17182
theorem numericValid2711 : retention2711.NumericValid := by decide +kernel
def certificate2711 : RatCutBinCertificate := ⟨⟨retention2711,(2585937105524707053/1000000000000000000),(225107070921290071/1000000000000000000),(4356274722595414287/250000000000000000),(88493122161958402527/250000000000000000),(953195433633759689/1000000000000000000)⟩,(994299292264416211/1000000000000000000),(60693064873919671/250000000000000000),(413449663078873313/1000000000000000000),(355052580952391399/1000000000000000000)⟩
theorem valid2711 : certificate2711.Valid := by decide +kernel
theorem sound2711 : certificate2711.Sound := rat_cut_bin_certificate_sound certificate2711 profilesValid2711 numericValid2711 valid2711

def certificates : List RatCutBinCertificate := [certificate2700,certificate2701,certificate2702,certificate2703,certificate2704,certificate2705,certificate2706,certificate2707,certificate2708,certificate2709,certificate2710,certificate2711]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2700,List.forall_mem_cons.mpr ⟨sound2701,List.forall_mem_cons.mpr ⟨sound2702,List.forall_mem_cons.mpr ⟨sound2703,List.forall_mem_cons.mpr ⟨sound2704,List.forall_mem_cons.mpr ⟨sound2705,List.forall_mem_cons.mpr ⟨sound2706,List.forall_mem_cons.mpr ⟨sound2707,List.forall_mem_cons.mpr ⟨sound2708,List.forall_mem_cons.mpr ⟨sound2709,List.forall_mem_cons.mpr ⟨sound2710,List.forall_mem_cons.mpr ⟨sound2711,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch225
