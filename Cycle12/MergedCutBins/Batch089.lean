import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch178
import Cycle12.MergedCutProfiles.Batch179
import Cycle12.MergedCutProfiles.Batch180

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch089

def retention1068 : RatCutRetentionCertificate := ⟨(53/1000),(213/4000),(8160511155360059587/16506479533787880736),(7536095138854764901/1000000000000000000),(21/20),(12050636492002217591462517825266753140799/12057752222167623841600000000000000000000),false,MergedCutProfiles.Batch178.profile7139,(fun _ => MergedCutProfiles.Batch178.profile7139)⟩
theorem profilesValid1068 : retention1068.ProfilesValid := by
  exact MergedCutProfiles.Batch178.valid7139
theorem numericValid1068 : retention1068.NumericValid := by decide +kernel
def certificate1068 : RatCutBinCertificate := ⟨⟨retention1068,(2569472782008153677/1000000000000000000),(138194877202670159/1000000000000000000),(14013165961528612701/1000000000000000000),(57911559766397994477/250000000000000000),(972801280024847159/1000000000000000000)⟩,(990409283933989647/1000000000000000000),(1596519715268469/3906250000000000),(45119357206916699/200000000000000000),(92602573060290121/500000000000000000)⟩
theorem valid1068 : certificate1068.Valid := by decide +kernel
theorem sound1068 : certificate1068.Sound := rat_cut_bin_certificate_sound certificate1068 profilesValid1068 numericValid1068 valid1068

def retention1069 : RatCutRetentionCertificate := ⟨(53/1000),(213/4000),(8242116266913660183/16506479533787880736),(8160511155360059587/1000000000000000000),(21/20),(12953362230507000788495766566106629107151/13056817848576095339200000000000000000000),false,MergedCutProfiles.Batch178.profile7140,(fun _ => MergedCutProfiles.Batch178.profile7140)⟩
theorem profilesValid1069 : retention1069.ProfilesValid := by
  exact MergedCutProfiles.Batch178.valid7140
theorem numericValid1069 : retention1069.NumericValid := by decide +kernel
def certificate1069 : RatCutBinCertificate := ⟨⟨retention1069,(2569472782008153677/1000000000000000000),(138194877202670159/1000000000000000000),(14013165961528612701/1000000000000000000),(57911559766397994477/250000000000000000),(482734038433877971/500000000000000000)⟩,(990409283933989647/1000000000000000000),(6434584259426757/15625000000000000),(22283102107242909/100000000000000000),(91582569540861821/500000000000000000)⟩
theorem valid1069 : certificate1069.Valid := by decide +kernel
theorem sound1069 : certificate1069.Sound := rat_cut_bin_certificate_sound certificate1069 profilesValid1069 numericValid1069 valid1069

def retention1070 : RatCutRetentionCertificate := ⟨(53/1000),(213/4000),(1/2),(8242116266913660183/1000000000000000000),(21/20),(13069080953132415029490033090451974959711/13187386027061856292800000000000000000000),false,MergedCutProfiles.Batch178.profile7137,(fun _ => MergedCutProfiles.Batch178.profile7137)⟩
theorem profilesValid1070 : retention1070.ProfilesValid := by
  exact MergedCutProfiles.Batch178.valid7137
theorem numericValid1070 : retention1070.NumericValid := by decide +kernel
def certificate1070 : RatCutBinCertificate := ⟨⟨retention1070,(2569472782008153677/1000000000000000000),(138194877202670159/1000000000000000000),(14013165961528612701/1000000000000000000),(57911559766397994477/250000000000000000),(30138140963251491/31250000000000000)⟩,(990409283933989647/1000000000000000000),(412260709641465137/1000000000000000000),(222434423806081347/1000000000000000000),(182836065178960019/1000000000000000000)⟩
theorem valid1070 : certificate1070.Valid := by decide +kernel
theorem sound1070 : certificate1070.Sound := rat_cut_bin_certificate_sound certificate1070 profilesValid1070 numericValid1070 valid1070

def retention1071 : RatCutRetentionCertificate := ⟨(213/4000),(107/2000),(426191979840175481/8164330071884685950),(105493064316875119/125000000000000000),(57/20),(40875134560070312211/20000000000000000000),true,MergedCutProfiles.Batch178.profile7141,![MergedCutProfiles.Batch178.profile7141,MergedCutProfiles.Batch178.profile7142,MergedCutProfiles.Batch178.profile7143,MergedCutProfiles.Batch178.profile7144,MergedCutProfiles.Batch178.profile7145,MergedCutProfiles.Batch178.profile7146,MergedCutProfiles.Batch178.profile7147,MergedCutProfiles.Batch178.profile7148,MergedCutProfiles.Batch178.profile7149,MergedCutProfiles.Batch178.profile7150,MergedCutProfiles.Batch178.profile7151,MergedCutProfiles.Batch178.profile7152,MergedCutProfiles.Batch178.profile7153,MergedCutProfiles.Batch178.profile7154,MergedCutProfiles.Batch178.profile7155,MergedCutProfiles.Batch178.profile7156]⟩
theorem profilesValid1071 : retention1071.ProfilesValid := by
  change ∀ j : Fin 16, (retention1071.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch178.valid7141
  · exact MergedCutProfiles.Batch178.valid7142
  · exact MergedCutProfiles.Batch178.valid7143
  · exact MergedCutProfiles.Batch178.valid7144
  · exact MergedCutProfiles.Batch178.valid7145
  · exact MergedCutProfiles.Batch178.valid7146
  · exact MergedCutProfiles.Batch178.valid7147
  · exact MergedCutProfiles.Batch178.valid7148
  · exact MergedCutProfiles.Batch178.valid7149
  · exact MergedCutProfiles.Batch178.valid7150
  · exact MergedCutProfiles.Batch178.valid7151
  · exact MergedCutProfiles.Batch178.valid7152
  · exact MergedCutProfiles.Batch178.valid7153
  · exact MergedCutProfiles.Batch178.valid7154
  · exact MergedCutProfiles.Batch178.valid7155
  · exact MergedCutProfiles.Batch178.valid7156
theorem numericValid1071 : retention1071.NumericValid := by decide +kernel
def certificate1071 : RatCutBinCertificate := ⟨⟨retention1071,(2218850897971299201/1000000000000000000),(17460968802135489/125000000000000000),(14073406348625911771/1000000000000000000),(28767052000251793197/125000000000000000),(396194757322217347/200000000000000000)⟩,(495839751853237429/500000000000000000),(73168383433704539/200000000000000000),(266280601503886439/1000000000000000000),(28433390749494183/200000000000000000)⟩
theorem valid1071 : certificate1071.Valid := by decide +kernel
theorem sound1071 : certificate1071.Sound := rat_cut_bin_certificate_sound certificate1071 profilesValid1071 numericValid1071 valid1071

def retention1072 : RatCutRetentionCertificate := ⟨(213/4000),(107/2000),(913870976742260497/16328660143769371900),(426191979840175481/500000000000000000),(57/20),(1303152423150556302209/640000000000000000000),true,MergedCutProfiles.Batch178.profile7157,![MergedCutProfiles.Batch178.profile7157,MergedCutProfiles.Batch178.profile7158,MergedCutProfiles.Batch178.profile7159,MergedCutProfiles.Batch179.profile7160,MergedCutProfiles.Batch179.profile7161,MergedCutProfiles.Batch179.profile7162,MergedCutProfiles.Batch179.profile7163,MergedCutProfiles.Batch179.profile7164,MergedCutProfiles.Batch179.profile7165,MergedCutProfiles.Batch179.profile7166,MergedCutProfiles.Batch179.profile7167,MergedCutProfiles.Batch179.profile7168,MergedCutProfiles.Batch179.profile7169,MergedCutProfiles.Batch178.profile7155,MergedCutProfiles.Batch179.profile7170,MergedCutProfiles.Batch179.profile7171]⟩
theorem profilesValid1072 : retention1072.ProfilesValid := by
  change ∀ j : Fin 16, (retention1072.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch178.valid7157
  · exact MergedCutProfiles.Batch178.valid7158
  · exact MergedCutProfiles.Batch178.valid7159
  · exact MergedCutProfiles.Batch179.valid7160
  · exact MergedCutProfiles.Batch179.valid7161
  · exact MergedCutProfiles.Batch179.valid7162
  · exact MergedCutProfiles.Batch179.valid7163
  · exact MergedCutProfiles.Batch179.valid7164
  · exact MergedCutProfiles.Batch179.valid7165
  · exact MergedCutProfiles.Batch179.valid7166
  · exact MergedCutProfiles.Batch179.valid7167
  · exact MergedCutProfiles.Batch179.valid7168
  · exact MergedCutProfiles.Batch179.valid7169
  · exact MergedCutProfiles.Batch178.valid7155
  · exact MergedCutProfiles.Batch179.valid7170
  · exact MergedCutProfiles.Batch179.valid7171
theorem numericValid1072 : retention1072.NumericValid := by decide +kernel
def certificate1072 : RatCutBinCertificate := ⟨⟨retention1072,(2218850897971299201/1000000000000000000),(17460968802135489/125000000000000000),(14073406348625911771/1000000000000000000),(28767052000251793197/125000000000000000),(986696438304396179/500000000000000000)⟩,(495839751853237429/500000000000000000),(45719605529259179/125000000000000000),(266366147726773549/1000000000000000000),(17763264374004587/125000000000000000)⟩
theorem valid1072 : certificate1072.Valid := by decide +kernel
theorem sound1072 : certificate1072.Sound := rat_cut_bin_certificate_sound certificate1072 profilesValid1072 numericValid1072 valid1072

def retention1073 : RatCutRetentionCertificate := ⟨(213/4000),(107/2000),(680314677225198077/8164330071884685950),(913870976742260497/1000000000000000000),(53/20),(623473232590431571847/320000000000000000000),true,MergedCutProfiles.Batch179.profile7172,![MergedCutProfiles.Batch179.profile7172,MergedCutProfiles.Batch178.profile7159,MergedCutProfiles.Batch179.profile7173,MergedCutProfiles.Batch179.profile7174,MergedCutProfiles.Batch178.profile7148,MergedCutProfiles.Batch179.profile7175,MergedCutProfiles.Batch179.profile7176,MergedCutProfiles.Batch179.profile7177,MergedCutProfiles.Batch179.profile7178,MergedCutProfiles.Batch178.profile7156,MergedCutProfiles.Batch179.profile7179,MergedCutProfiles.Batch179.profile7180,MergedCutProfiles.Batch179.profile7181,MergedCutProfiles.Batch179.profile7182,MergedCutProfiles.Batch179.profile7183,MergedCutProfiles.Batch179.profile7184]⟩
theorem profilesValid1073 : retention1073.ProfilesValid := by
  change ∀ j : Fin 16, (retention1073.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch179.valid7172
  · exact MergedCutProfiles.Batch178.valid7159
  · exact MergedCutProfiles.Batch179.valid7173
  · exact MergedCutProfiles.Batch179.valid7174
  · exact MergedCutProfiles.Batch178.valid7148
  · exact MergedCutProfiles.Batch179.valid7175
  · exact MergedCutProfiles.Batch179.valid7176
  · exact MergedCutProfiles.Batch179.valid7177
  · exact MergedCutProfiles.Batch179.valid7178
  · exact MergedCutProfiles.Batch178.valid7156
  · exact MergedCutProfiles.Batch179.valid7179
  · exact MergedCutProfiles.Batch179.valid7180
  · exact MergedCutProfiles.Batch179.valid7181
  · exact MergedCutProfiles.Batch179.valid7182
  · exact MergedCutProfiles.Batch179.valid7183
  · exact MergedCutProfiles.Batch179.valid7184
theorem numericValid1073 : retention1073.NumericValid := by decide +kernel
def certificate1073 : RatCutBinCertificate := ⟨⟨retention1073,(2218850897971299201/1000000000000000000),(17460968802135489/125000000000000000),(14073406348625911771/1000000000000000000),(28767052000251793197/125000000000000000),(944988415673008167/500000000000000000)⟩,(495839751853237429/500000000000000000),(185714533941340117/500000000000000000),(260705420813336597/1000000000000000000),(35553360120728477/250000000000000000)⟩
theorem valid1073 : certificate1073.Valid := by decide +kernel
theorem sound1073 : certificate1073.Sound := rat_cut_bin_certificate_sound certificate1073 profilesValid1073 numericValid1073 valid1073

def retention1074 : RatCutRetentionCertificate := ⟨(213/4000),(107/2000),(3607733648303416401/16328660143769371900),(680314677225198077/500000000000000000),(39/20),(1014291479950662550437/640000000000000000000),true,MergedCutProfiles.Batch179.profile7185,![MergedCutProfiles.Batch179.profile7185,MergedCutProfiles.Batch179.profile7186,MergedCutProfiles.Batch179.profile7187,MergedCutProfiles.Batch179.profile7188,MergedCutProfiles.Batch179.profile7189,MergedCutProfiles.Batch179.profile7190,MergedCutProfiles.Batch179.profile7191,MergedCutProfiles.Batch179.profile7192,MergedCutProfiles.Batch179.profile7193,MergedCutProfiles.Batch179.profile7194,MergedCutProfiles.Batch179.profile7195,MergedCutProfiles.Batch179.profile7196,MergedCutProfiles.Batch179.profile7197,MergedCutProfiles.Batch179.profile7198,MergedCutProfiles.Batch179.profile7199,MergedCutProfiles.Batch180.profile7200]⟩
theorem profilesValid1074 : retention1074.ProfilesValid := by
  change ∀ j : Fin 16, (retention1074.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch179.valid7185
  · exact MergedCutProfiles.Batch179.valid7186
  · exact MergedCutProfiles.Batch179.valid7187
  · exact MergedCutProfiles.Batch179.valid7188
  · exact MergedCutProfiles.Batch179.valid7189
  · exact MergedCutProfiles.Batch179.valid7190
  · exact MergedCutProfiles.Batch179.valid7191
  · exact MergedCutProfiles.Batch179.valid7192
  · exact MergedCutProfiles.Batch179.valid7193
  · exact MergedCutProfiles.Batch179.valid7194
  · exact MergedCutProfiles.Batch179.valid7195
  · exact MergedCutProfiles.Batch179.valid7196
  · exact MergedCutProfiles.Batch179.valid7197
  · exact MergedCutProfiles.Batch179.valid7198
  · exact MergedCutProfiles.Batch179.valid7199
  · exact MergedCutProfiles.Batch180.valid7200
theorem numericValid1074 : retention1074.NumericValid := by decide +kernel
def certificate1074 : RatCutBinCertificate := ⟨⟨retention1074,(2218850897971299201/1000000000000000000),(17460968802135489/125000000000000000),(14073406348625911771/1000000000000000000),(28767052000251793197/125000000000000000),(192734337624794409/125000000000000000)⟩,(495839751853237429/500000000000000000),(39686339529802173/100000000000000000),(236368601359548563/1000000000000000000),(71291345550817191/500000000000000000)⟩
theorem valid1074 : certificate1074.Valid := by decide +kernel
theorem sound1074 : certificate1074.Sound := rat_cut_bin_certificate_sound certificate1074 profilesValid1074 numericValid1074 valid1074

def retention1075 : RatCutRetentionCertificate := ⟨(213/4000),(107/2000),(3513472144714375003/8164330071884685950),(3607733648303416401/1000000000000000000),(11/10),(1417168268083982320413/1280000000000000000000),true,MergedCutProfiles.Batch180.profile7201,![MergedCutProfiles.Batch180.profile7201,MergedCutProfiles.Batch180.profile7202,MergedCutProfiles.Batch180.profile7203,MergedCutProfiles.Batch180.profile7204,MergedCutProfiles.Batch180.profile7205,MergedCutProfiles.Batch180.profile7206,MergedCutProfiles.Batch180.profile7207,MergedCutProfiles.Batch180.profile7208,MergedCutProfiles.Batch180.profile7209,MergedCutProfiles.Batch180.profile7210,MergedCutProfiles.Batch180.profile7211,MergedCutProfiles.Batch180.profile7212,MergedCutProfiles.Batch180.profile7213,MergedCutProfiles.Batch180.profile7214,MergedCutProfiles.Batch180.profile7215,MergedCutProfiles.Batch180.profile7216]⟩
theorem profilesValid1075 : retention1075.ProfilesValid := by
  change ∀ j : Fin 16, (retention1075.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch180.valid7201
  · exact MergedCutProfiles.Batch180.valid7202
  · exact MergedCutProfiles.Batch180.valid7203
  · exact MergedCutProfiles.Batch180.valid7204
  · exact MergedCutProfiles.Batch180.valid7205
  · exact MergedCutProfiles.Batch180.valid7206
  · exact MergedCutProfiles.Batch180.valid7207
  · exact MergedCutProfiles.Batch180.valid7208
  · exact MergedCutProfiles.Batch180.valid7209
  · exact MergedCutProfiles.Batch180.valid7210
  · exact MergedCutProfiles.Batch180.valid7211
  · exact MergedCutProfiles.Batch180.valid7212
  · exact MergedCutProfiles.Batch180.valid7213
  · exact MergedCutProfiles.Batch180.valid7214
  · exact MergedCutProfiles.Batch180.valid7215
  · exact MergedCutProfiles.Batch180.valid7216
theorem numericValid1075 : retention1075.NumericValid := by decide +kernel
def certificate1075 : RatCutBinCertificate := ⟨⟨retention1075,(2218850897971299201/1000000000000000000),(17460968802135489/125000000000000000),(14073406348625911771/1000000000000000000),(28767052000251793197/125000000000000000),(1082933105212534467/1000000000000000000)⟩,(495839751853237429/500000000000000000),(459072707328964527/1000000000000000000),(183517554650963277/1000000000000000000),(143410268163580611/1000000000000000000)⟩
theorem valid1075 : certificate1075.Valid := by decide +kernel
theorem sound1075 : certificate1075.Sound := rat_cut_bin_certificate_sound certificate1075 profilesValid1075 numericValid1075 valid1075

def retention1076 : RatCutRetentionCertificate := ⟨(213/4000),(107/2000),(1999329519444484007/4082165035942342975),(3513472144714375003/500000000000000000),(21/20),(2827866293897183030914415017321928656191/2810777715771500002400000000000000000000),false,MergedCutProfiles.Batch180.profile7217,(fun _ => MergedCutProfiles.Batch180.profile7217)⟩
theorem profilesValid1076 : retention1076.ProfilesValid := by
  exact MergedCutProfiles.Batch180.valid7217
theorem numericValid1076 : retention1076.NumericValid := by decide +kernel
def certificate1076 : RatCutBinCertificate := ⟨⟨retention1076,(2218850897971299201/1000000000000000000),(17460968802135489/125000000000000000),(14073406348625911771/1000000000000000000),(28767052000251793197/125000000000000000),(491476518914316553/500000000000000000)⟩,(495839751853237429/500000000000000000),(471366201566430917/1000000000000000000),(87054859523574101/500000000000000000),(143350849724412199/1000000000000000000)⟩
theorem valid1076 : certificate1076.Valid := by decide +kernel
theorem sound1076 : certificate1076.Sound := rat_cut_bin_certificate_sound certificate1076 profilesValid1076 numericValid1076 valid1076

def retention1077 : RatCutRetentionCertificate := ⟨(213/4000),(107/2000),(8077291258555715389/16328660143769371900),(1999329519444484007/250000000000000000),(21/20),(800156674048106332004005755794317840511/799731807777793602800000000000000000000),false,MergedCutProfiles.Batch180.profile7218,(fun _ => MergedCutProfiles.Batch180.profile7218)⟩
theorem profilesValid1077 : retention1077.ProfilesValid := by
  exact MergedCutProfiles.Batch180.valid7218
theorem numericValid1077 : retention1077.NumericValid := by decide +kernel
def certificate1077 : RatCutBinCertificate := ⟨⟨retention1077,(2218850897971299201/1000000000000000000),(17460968802135489/125000000000000000),(14073406348625911771/1000000000000000000),(28767052000251793197/125000000000000000),(30543902116146147/31250000000000000)⟩,(495839751853237429/500000000000000000),(46961265288988429/100000000000000000),(35086371092581829/200000000000000000),(145705448630687531/1000000000000000000)⟩
theorem valid1077 : certificate1077.Valid := by decide +kernel
theorem sound1077 : certificate1077.Sound := rat_cut_bin_certificate_sound certificate1077 profilesValid1077 numericValid1077 valid1077

def retention1078 : RatCutRetentionCertificate := ⟨(213/4000),(107/2000),(8158064171141272543/16328660143769371900),(8077291258555715389/1000000000000000000),(21/20),(12810616576178108211324986265804004655279/12923666013689144622400000000000000000000),false,MergedCutProfiles.Batch180.profile7219,(fun _ => MergedCutProfiles.Batch180.profile7219)⟩
theorem profilesValid1078 : retention1078.ProfilesValid := by
  exact MergedCutProfiles.Batch180.valid7219
theorem numericValid1078 : retention1078.NumericValid := by decide +kernel
def certificate1078 : RatCutBinCertificate := ⟨⟨retention1078,(2218850897971299201/1000000000000000000),(17460968802135489/125000000000000000),(14073406348625911771/1000000000000000000),(28767052000251793197/125000000000000000),(193625229787231659/200000000000000000)⟩,(495839751853237429/500000000000000000),(236896453470410499/500000000000000000),(17229079219729181/100000000000000000),(1136098422894711/8000000000000000)⟩
theorem valid1078 : certificate1078.Valid := by decide +kernel
theorem sound1078 : certificate1078.Sound := rat_cut_bin_certificate_sound certificate1078 profilesValid1078 numericValid1078 valid1078

def retention1079 : RatCutRetentionCertificate := ⟨(213/4000),(107/2000),(1/2),(8158064171141272543/1000000000000000000),(21/20),(12932413876634833752289914060257079103631/13052902673826036068800000000000000000000),false,MergedCutProfiles.Batch180.profile7220,(fun _ => MergedCutProfiles.Batch180.profile7220)⟩
theorem profilesValid1079 : retention1079.ProfilesValid := by
  exact MergedCutProfiles.Batch180.valid7220
theorem numericValid1079 : retention1079.NumericValid := by decide +kernel
def certificate1079 : RatCutBinCertificate := ⟨⟨retention1079,(2218850897971299201/1000000000000000000),(17460968802135489/125000000000000000),(14073406348625911771/1000000000000000000),(28767052000251793197/125000000000000000),(120955354359193627/125000000000000000)⟩,(495839751853237429/500000000000000000),(3789695689830719/8000000000000000),(34470252798742659/200000000000000000),(142136776144829013/1000000000000000000)⟩
theorem valid1079 : certificate1079.Valid := by decide +kernel
theorem sound1079 : certificate1079.Sound := rat_cut_bin_certificate_sound certificate1079 profilesValid1079 numericValid1079 valid1079

def certificates : List RatCutBinCertificate := [certificate1068,certificate1069,certificate1070,certificate1071,certificate1072,certificate1073,certificate1074,certificate1075,certificate1076,certificate1077,certificate1078,certificate1079]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1068,List.forall_mem_cons.mpr ⟨sound1069,List.forall_mem_cons.mpr ⟨sound1070,List.forall_mem_cons.mpr ⟨sound1071,List.forall_mem_cons.mpr ⟨sound1072,List.forall_mem_cons.mpr ⟨sound1073,List.forall_mem_cons.mpr ⟨sound1074,List.forall_mem_cons.mpr ⟨sound1075,List.forall_mem_cons.mpr ⟨sound1076,List.forall_mem_cons.mpr ⟨sound1077,List.forall_mem_cons.mpr ⟨sound1078,List.forall_mem_cons.mpr ⟨sound1079,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch089
