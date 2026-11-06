import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch359
import Cycle12.MergedCutProfiles.Batch360
import Cycle12.MergedCutProfiles.Batch478
import Cycle12.MergedCutProfiles.Batch479

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch259

def retention3108 : RatCutRetentionCertificate := ⟨(21/500),(43/1000),(61343638630711898399/134129227617246420223),(100295051192647949/10000000000000000),1,(2652625827158237839229757932015052579/2507376279816198725000000000000000000),false,MergedCutProfiles.Batch478.profile19131,(fun _ => MergedCutProfiles.Batch478.profile19131)⟩
theorem profilesValid3108 : retention3108.ProfilesValid := by
  exact MergedCutProfiles.Batch478.valid19131
theorem numericValid3108 : retention3108.NumericValid := by decide +kernel
def certificate3108 : RatCutBinCertificate := ⟨⟨retention3108,(1073303076798281483/500000000000000000),(21376650541548341/250000000000000000),(2341848866977126349/200000000000000000),(1542141089801017007/976562500000000),(1042253251303901933/1000000000000000000)⟩,(998750886322762501/1000000000000000000),(30378649182092239/250000000000000000),(620370027378095743/1000000000000000000),(292473928923859059/500000000000000000)⟩
theorem valid3108 : certificate3108.Valid := by decide +kernel
theorem sound3108 : certificate3108.Sound := rat_cut_bin_certificate_sound certificate3108 profilesValid3108 numericValid3108 valid3108

def retention3109 : RatCutRetentionCertificate := ⟨(21/500),(43/1000),(64000000000000000000/134129227617246420223),(61343638630711898399/1000000000000000000),1,(255910497050193074502840994537546289283/245374554522847593596000000000000000000),false,MergedCutProfiles.Batch478.profile19130,(fun _ => MergedCutProfiles.Batch478.profile19130)⟩
theorem profilesValid3109 : retention3109.ProfilesValid := by
  exact MergedCutProfiles.Batch478.valid19130
theorem numericValid3109 : retention3109.NumericValid := by decide +kernel
def certificate3109 : RatCutBinCertificate := ⟨⟨retention3109,(1073303076798281483/500000000000000000),(21376650541548341/250000000000000000),(2341848866977126349/200000000000000000),(1542141089801017007/976562500000000),(1027262626450909127/1000000000000000000)⟩,(998750886322762501/1000000000000000000),(61643916686906421/500000000000000000),(616729209553332629/1000000000000000000),(19447596121546323/31250000000000000)⟩
theorem valid3109 : certificate3109.Valid := by decide +kernel
theorem sound3109 : certificate3109.Sound := rat_cut_bin_certificate_sound certificate3109 profilesValid3109 numericValid3109 valid3109

def retention3110 : RatCutRetentionCertificate := ⟨(21/500),(43/1000),(1/2),64,1,(63846487671256044251940764516727514191/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch359.profile14365,(fun _ => MergedCutProfiles.Batch359.profile14365)⟩
theorem profilesValid3110 : retention3110.ProfilesValid := by
  exact MergedCutProfiles.Batch359.valid14365
theorem numericValid3110 : retention3110.NumericValid := by decide +kernel
def certificate3110 : RatCutBinCertificate := ⟨⟨retention3110,(1073303076798281483/500000000000000000),(21376650541548341/250000000000000000),(2341848866977126349/200000000000000000),(1542141089801017007/976562500000000),(61370362094040157/62500000000000000)⟩,(998750886322762501/1000000000000000000),(2015315597783673/15625000000000000),(605188996060168407/1000000000000000000),(116906769908259011/200000000000000000)⟩
theorem valid3110 : certificate3110.Valid := by decide +kernel
theorem sound3110 : certificate3110.Sound := rat_cut_bin_certificate_sound certificate3110 profilesValid3110 numericValid3110 valid3110

def retention3111 : RatCutRetentionCertificate := ⟨(43/1000),(11/250),(737021151139741126/127399680273932701341),(729723912019545669/1000000000000000000),(15/4),(592870457202429300417/256000000000000000000),true,MergedCutProfiles.Batch478.profile19132,![MergedCutProfiles.Batch478.profile19132,MergedCutProfiles.Batch478.profile19133,MergedCutProfiles.Batch478.profile19134,MergedCutProfiles.Batch360.profile14414,MergedCutProfiles.Batch478.profile19135,MergedCutProfiles.Batch478.profile19136,MergedCutProfiles.Batch360.profile14401,MergedCutProfiles.Batch359.profile14371,MergedCutProfiles.Batch478.profile19137,MergedCutProfiles.Batch478.profile19138,MergedCutProfiles.Batch478.profile19139,MergedCutProfiles.Batch478.profile19140,MergedCutProfiles.Batch478.profile19141,MergedCutProfiles.Batch360.profile14403,MergedCutProfiles.Batch478.profile19142,MergedCutProfiles.Batch478.profile19143]⟩
theorem profilesValid3111 : retention3111.ProfilesValid := by
  change ∀ j : Fin 16, (retention3111.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch478.valid19132
  · exact MergedCutProfiles.Batch478.valid19133
  · exact MergedCutProfiles.Batch478.valid19134
  · exact MergedCutProfiles.Batch360.valid14414
  · exact MergedCutProfiles.Batch478.valid19135
  · exact MergedCutProfiles.Batch478.valid19136
  · exact MergedCutProfiles.Batch360.valid14401
  · exact MergedCutProfiles.Batch359.valid14371
  · exact MergedCutProfiles.Batch478.valid19137
  · exact MergedCutProfiles.Batch478.valid19138
  · exact MergedCutProfiles.Batch478.valid19139
  · exact MergedCutProfiles.Batch478.valid19140
  · exact MergedCutProfiles.Batch478.valid19141
  · exact MergedCutProfiles.Batch360.valid14403
  · exact MergedCutProfiles.Batch478.valid19142
  · exact MergedCutProfiles.Batch478.valid19143
theorem numericValid3111 : retention3111.NumericValid := by decide +kernel
def certificate3111 : RatCutBinCertificate := ⟨⟨retention3111,(1006649867131201179/500000000000000000),(5622540848385301/62500000000000000),(5947016094090640243/500000000000000000),(1523646054422456694899/1000000000000000000),(1129397714878219213/500000000000000000)⟩,(499395739503336353/500000000000000000),(461548262991823517/1000000000000000000),(181596898128227901/1000000000000000000),(3580913737091827/40000000000000000)⟩
theorem valid3111 : certificate3111.Valid := by decide +kernel
theorem sound3111 : certificate3111.Sound := rat_cut_bin_certificate_sound certificate3111 profilesValid3111 numericValid3111 valid3111

def retention3112 : RatCutRetentionCertificate := ⟨(43/1000),(11/250),(13339991635806718/1745201099642913717),(368510575569870563/500000000000000000),(37/10),(1470865683179970440199/640000000000000000000),true,MergedCutProfiles.Batch478.profile19144,![MergedCutProfiles.Batch478.profile19144,MergedCutProfiles.Batch478.profile19145,MergedCutProfiles.Batch360.profile14414,MergedCutProfiles.Batch478.profile19146,MergedCutProfiles.Batch478.profile19147,MergedCutProfiles.Batch360.profile14415,MergedCutProfiles.Batch478.profile19148,MergedCutProfiles.Batch360.profile14402,MergedCutProfiles.Batch478.profile19140,MergedCutProfiles.Batch478.profile19149,MergedCutProfiles.Batch478.profile19150,MergedCutProfiles.Batch478.profile19143,MergedCutProfiles.Batch478.profile19151,MergedCutProfiles.Batch478.profile19152,MergedCutProfiles.Batch478.profile19153,MergedCutProfiles.Batch478.profile19154]⟩
theorem profilesValid3112 : retention3112.ProfilesValid := by
  change ∀ j : Fin 16, (retention3112.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch478.valid19144
  · exact MergedCutProfiles.Batch478.valid19145
  · exact MergedCutProfiles.Batch360.valid14414
  · exact MergedCutProfiles.Batch478.valid19146
  · exact MergedCutProfiles.Batch478.valid19147
  · exact MergedCutProfiles.Batch360.valid14415
  · exact MergedCutProfiles.Batch478.valid19148
  · exact MergedCutProfiles.Batch360.valid14402
  · exact MergedCutProfiles.Batch478.valid19140
  · exact MergedCutProfiles.Batch478.valid19149
  · exact MergedCutProfiles.Batch478.valid19150
  · exact MergedCutProfiles.Batch478.valid19143
  · exact MergedCutProfiles.Batch478.valid19151
  · exact MergedCutProfiles.Batch478.valid19152
  · exact MergedCutProfiles.Batch478.valid19153
  · exact MergedCutProfiles.Batch478.valid19154
theorem numericValid3112 : retention3112.NumericValid := by decide +kernel
def certificate3112 : RatCutBinCertificate := ⟨⟨retention3112,(1006649867131201179/500000000000000000),(5622540848385301/62500000000000000),(5947016094090640243/500000000000000000),(1523646054422456694899/1000000000000000000),(2241884229298409917/1000000000000000000)⟩,(499395739503336353/500000000000000000),(92490082089146503/200000000000000000),(45225068185815807/250000000000000000),(11194443974467797/125000000000000000)⟩
theorem valid3112 : certificate3112.Valid := by decide +kernel
theorem sound3112 : certificate3112.Sound := rat_cut_bin_certificate_sound certificate3112 profilesValid3112 numericValid3112 valid3112

def retention3113 : RatCutRetentionCertificate := ⟨(43/1000),(11/250),(15181921000000000/1745201099642913717),(486909694706945207/500000000000000000),(29/10),(1454683605131121360747/640000000000000000000),true,MergedCutProfiles.Batch478.profile19155,![MergedCutProfiles.Batch478.profile19155,MergedCutProfiles.Batch478.profile19134,MergedCutProfiles.Batch478.profile19156,MergedCutProfiles.Batch478.profile19136,MergedCutProfiles.Batch478.profile19157,MergedCutProfiles.Batch478.profile19137,MergedCutProfiles.Batch360.profile14402,MergedCutProfiles.Batch478.profile19158,MergedCutProfiles.Batch359.profile14373,MergedCutProfiles.Batch478.profile19159,MergedCutProfiles.Batch479.profile19160,MergedCutProfiles.Batch479.profile19161,MergedCutProfiles.Batch360.profile14417,MergedCutProfiles.Batch360.profile14405,MergedCutProfiles.Batch479.profile19162,MergedCutProfiles.Batch479.profile19163]⟩
theorem profilesValid3113 : retention3113.ProfilesValid := by
  change ∀ j : Fin 16, (retention3113.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch478.valid19155
  · exact MergedCutProfiles.Batch478.valid19134
  · exact MergedCutProfiles.Batch478.valid19156
  · exact MergedCutProfiles.Batch478.valid19136
  · exact MergedCutProfiles.Batch478.valid19157
  · exact MergedCutProfiles.Batch478.valid19137
  · exact MergedCutProfiles.Batch360.valid14402
  · exact MergedCutProfiles.Batch478.valid19158
  · exact MergedCutProfiles.Batch359.valid14373
  · exact MergedCutProfiles.Batch478.valid19159
  · exact MergedCutProfiles.Batch479.valid19160
  · exact MergedCutProfiles.Batch479.valid19161
  · exact MergedCutProfiles.Batch360.valid14417
  · exact MergedCutProfiles.Batch360.valid14405
  · exact MergedCutProfiles.Batch479.valid19162
  · exact MergedCutProfiles.Batch479.valid19163
theorem numericValid3113 : retention3113.NumericValid := by decide +kernel
def certificate3113 : RatCutBinCertificate := ⟨⟨retention3113,(1006649867131201179/500000000000000000),(5622540848385301/62500000000000000),(5947016094090640243/500000000000000000),(1523646054422456694899/1000000000000000000),(1114391061061306469/500000000000000000)⟩,(499395739503336353/500000000000000000),(40207723158496707/100000000000000000),(46316896285857453/200000000000000000),(139711530929239679/1000000000000000000)⟩
theorem valid3113 : certificate3113.Valid := by decide +kernel
theorem sound3113 : certificate3113.Sound := rat_cut_bin_certificate_sound certificate3113 profilesValid3113 numericValid3113 valid3113

def retention3114 : RatCutRetentionCertificate := ⟨(43/1000),(11/250),(1108297303447597463/127399680273932701341),(1108280233/1000000000),(13/5),(9050310165033749213/4000000000000000000),true,MergedCutProfiles.Batch478.profile19155,![MergedCutProfiles.Batch478.profile19155,MergedCutProfiles.Batch478.profile19134,MergedCutProfiles.Batch478.profile19156,MergedCutProfiles.Batch478.profile19136,MergedCutProfiles.Batch478.profile19157,MergedCutProfiles.Batch478.profile19137,MergedCutProfiles.Batch360.profile14402,MergedCutProfiles.Batch478.profile19158,MergedCutProfiles.Batch359.profile14373,MergedCutProfiles.Batch478.profile19159,MergedCutProfiles.Batch479.profile19160,MergedCutProfiles.Batch479.profile19161,MergedCutProfiles.Batch360.profile14417,MergedCutProfiles.Batch360.profile14405,MergedCutProfiles.Batch479.profile19162,MergedCutProfiles.Batch479.profile19163]⟩
theorem profilesValid3114 : retention3114.ProfilesValid := by
  change ∀ j : Fin 16, (retention3114.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch478.valid19155
  · exact MergedCutProfiles.Batch478.valid19134
  · exact MergedCutProfiles.Batch478.valid19156
  · exact MergedCutProfiles.Batch478.valid19136
  · exact MergedCutProfiles.Batch478.valid19157
  · exact MergedCutProfiles.Batch478.valid19137
  · exact MergedCutProfiles.Batch360.valid14402
  · exact MergedCutProfiles.Batch478.valid19158
  · exact MergedCutProfiles.Batch359.valid14373
  · exact MergedCutProfiles.Batch478.valid19159
  · exact MergedCutProfiles.Batch479.valid19160
  · exact MergedCutProfiles.Batch479.valid19161
  · exact MergedCutProfiles.Batch360.valid14417
  · exact MergedCutProfiles.Batch360.valid14405
  · exact MergedCutProfiles.Batch479.valid19162
  · exact MergedCutProfiles.Batch479.valid19163
theorem numericValid3114 : retention3114.NumericValid := by decide +kernel
def certificate3114 : RatCutBinCertificate := ⟨⟨retention3114,(1006649867131201179/500000000000000000),(5622540848385301/62500000000000000),(5947016094090640243/500000000000000000),(1523646054422456694899/1000000000000000000),(2222984927304804847/1000000000000000000)⟩,(499395739503336353/500000000000000000),(37923935200405917/100000000000000000),(253052324322929979/1000000000000000000),(166617416551256763/1000000000000000000)⟩
theorem valid3114 : certificate3114.Valid := by decide +kernel
theorem sound3114 : certificate3114.Sound := rat_cut_bin_certificate_sound certificate3114 profilesValid3114 numericValid3114 valid3114

def retention3115 : RatCutRetentionCertificate := ⟨(43/1000),(11/250),(159911468068867634/18199954324847528763),(1108297303447597463/1000000000000000000),(13/5),(180957051728390750591/80000000000000000000),true,MergedCutProfiles.Batch478.profile19155,![MergedCutProfiles.Batch478.profile19155,MergedCutProfiles.Batch478.profile19134,MergedCutProfiles.Batch479.profile19164,MergedCutProfiles.Batch478.profile19136,MergedCutProfiles.Batch479.profile19165,MergedCutProfiles.Batch479.profile19166,MergedCutProfiles.Batch360.profile14402,MergedCutProfiles.Batch478.profile19158,MergedCutProfiles.Batch359.profile14373,MergedCutProfiles.Batch478.profile19159,MergedCutProfiles.Batch479.profile19167,MergedCutProfiles.Batch479.profile19168,MergedCutProfiles.Batch478.profile19153,MergedCutProfiles.Batch478.profile19154,MergedCutProfiles.Batch479.profile19169,MergedCutProfiles.Batch479.profile19163]⟩
theorem profilesValid3115 : retention3115.ProfilesValid := by
  change ∀ j : Fin 16, (retention3115.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch478.valid19155
  · exact MergedCutProfiles.Batch478.valid19134
  · exact MergedCutProfiles.Batch479.valid19164
  · exact MergedCutProfiles.Batch478.valid19136
  · exact MergedCutProfiles.Batch479.valid19165
  · exact MergedCutProfiles.Batch479.valid19166
  · exact MergedCutProfiles.Batch360.valid14402
  · exact MergedCutProfiles.Batch478.valid19158
  · exact MergedCutProfiles.Batch359.valid14373
  · exact MergedCutProfiles.Batch478.valid19159
  · exact MergedCutProfiles.Batch479.valid19167
  · exact MergedCutProfiles.Batch479.valid19168
  · exact MergedCutProfiles.Batch478.valid19153
  · exact MergedCutProfiles.Batch478.valid19154
  · exact MergedCutProfiles.Batch479.valid19169
  · exact MergedCutProfiles.Batch479.valid19163
theorem numericValid3115 : retention3115.NumericValid := by decide +kernel
def certificate3115 : RatCutBinCertificate := ⟨⟨retention3115,(1006649867131201179/500000000000000000),(5622540848385301/62500000000000000),(5947016094090640243/500000000000000000),(1523646054422456694899/1000000000000000000),(2222370532663747019/1000000000000000000)⟩,(499395739503336353/500000000000000000),(75868306181977347/200000000000000000),(126476637087779183/500000000000000000),(666069130881397/4000000000000000)⟩
theorem valid3115 : certificate3115.Valid := by decide +kernel
theorem sound3115 : certificate3115.Sound := rat_cut_bin_certificate_sound certificate3115 profilesValid3115 numericValid3115 valid3115

def retention3116 : RatCutRetentionCertificate := ⟨(43/1000),(11/250),(6236788421359029/581733699880971239),(559690138241036719/500000000000000000),(13/5),(1442192017054835123051/640000000000000000000),true,MergedCutProfiles.Batch479.profile19170,![MergedCutProfiles.Batch479.profile19170,MergedCutProfiles.Batch479.profile19171,MergedCutProfiles.Batch479.profile19172,MergedCutProfiles.Batch478.profile19157,MergedCutProfiles.Batch478.profile19148,MergedCutProfiles.Batch478.profile19139,MergedCutProfiles.Batch478.profile19141,MergedCutProfiles.Batch479.profile19173,MergedCutProfiles.Batch479.profile19167,MergedCutProfiles.Batch478.profile19152,MergedCutProfiles.Batch479.profile19174,MergedCutProfiles.Batch359.profile14390,MergedCutProfiles.Batch479.profile19163,MergedCutProfiles.Batch479.profile19175,MergedCutProfiles.Batch479.profile19176,MergedCutProfiles.Batch359.profile14379]⟩
theorem profilesValid3116 : retention3116.ProfilesValid := by
  change ∀ j : Fin 16, (retention3116.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch479.valid19170
  · exact MergedCutProfiles.Batch479.valid19171
  · exact MergedCutProfiles.Batch479.valid19172
  · exact MergedCutProfiles.Batch478.valid19157
  · exact MergedCutProfiles.Batch478.valid19148
  · exact MergedCutProfiles.Batch478.valid19139
  · exact MergedCutProfiles.Batch478.valid19141
  · exact MergedCutProfiles.Batch479.valid19173
  · exact MergedCutProfiles.Batch479.valid19167
  · exact MergedCutProfiles.Batch478.valid19152
  · exact MergedCutProfiles.Batch479.valid19174
  · exact MergedCutProfiles.Batch359.valid14390
  · exact MergedCutProfiles.Batch479.valid19163
  · exact MergedCutProfiles.Batch479.valid19175
  · exact MergedCutProfiles.Batch479.valid19176
  · exact MergedCutProfiles.Batch359.valid14379
theorem numericValid3116 : retention3116.NumericValid := by decide +kernel
def certificate3116 : RatCutBinCertificate := ⟨⟨retention3116,(1006649867131201179/500000000000000000),(5622540848385301/62500000000000000),(5947016094090640243/500000000000000000),(1523646054422456694899/1000000000000000000),(2213832420739025671/1000000000000000000)⟩,(499395739503336353/500000000000000000),(23692791481016741/62500000000000000),(253202328361916453/1000000000000000000),(41640823720204943/250000000000000000)⟩
theorem valid3116 : certificate3116.Valid := by decide +kernel
theorem sound3116 : certificate3116.Sound := rat_cut_bin_certificate_sound certificate3116 profilesValid3116 numericValid3116 valid3116

def retention3117 : RatCutRetentionCertificate := ⟨(43/1000),(11/250),(8271300146586475906/127399680273932701341),(1365856664277627351/1000000000000000000),(9/4),(516123675353214196131/256000000000000000000),true,MergedCutProfiles.Batch479.profile19177,![MergedCutProfiles.Batch479.profile19177,MergedCutProfiles.Batch479.profile19162,MergedCutProfiles.Batch479.profile19178,MergedCutProfiles.Batch479.profile19179,MergedCutProfiles.Batch360.profile14413,MergedCutProfiles.Batch479.profile19180,MergedCutProfiles.Batch479.profile19181,MergedCutProfiles.Batch479.profile19182,MergedCutProfiles.Batch479.profile19183,MergedCutProfiles.Batch479.profile19184,MergedCutProfiles.Batch479.profile19185,MergedCutProfiles.Batch360.profile14439,MergedCutProfiles.Batch479.profile19186,MergedCutProfiles.Batch479.profile19187,MergedCutProfiles.Batch479.profile19188,MergedCutProfiles.Batch479.profile19189]⟩
theorem profilesValid3117 : retention3117.ProfilesValid := by
  change ∀ j : Fin 16, (retention3117.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch479.valid19177
  · exact MergedCutProfiles.Batch479.valid19162
  · exact MergedCutProfiles.Batch479.valid19178
  · exact MergedCutProfiles.Batch479.valid19179
  · exact MergedCutProfiles.Batch360.valid14413
  · exact MergedCutProfiles.Batch479.valid19180
  · exact MergedCutProfiles.Batch479.valid19181
  · exact MergedCutProfiles.Batch479.valid19182
  · exact MergedCutProfiles.Batch479.valid19183
  · exact MergedCutProfiles.Batch479.valid19184
  · exact MergedCutProfiles.Batch479.valid19185
  · exact MergedCutProfiles.Batch360.valid14439
  · exact MergedCutProfiles.Batch479.valid19186
  · exact MergedCutProfiles.Batch479.valid19187
  · exact MergedCutProfiles.Batch479.valid19188
  · exact MergedCutProfiles.Batch479.valid19189
theorem numericValid3117 : retention3117.NumericValid := by decide +kernel
def certificate3117 : RatCutBinCertificate := ⟨⟨retention3117,(1006649867131201179/500000000000000000),(5622540848385301/62500000000000000),(5947016094090640243/500000000000000000),(1523646054422456694899/1000000000000000000),(198184531163045217/100000000000000000)⟩,(499395739503336353/500000000000000000),(388789722804559179/1000000000000000000),(121956136984882797/500000000000000000),(166750945452491897/1000000000000000000)⟩
theorem valid3117 : certificate3117.Valid := by decide +kernel
theorem sound3117 : certificate3117.Sound := rat_cut_bin_certificate_sound certificate3117 profilesValid3117 numericValid3117 valid3117

def retention3118 : RatCutRetentionCertificate := ⟨(43/1000),(11/250),(55329427067940771146/127399680273932701341),(4135650073293237953/500000000000000000),(21/20),(3700772112590858403434583153064146120551/3308520058634590362400000000000000000000),false,MergedCutProfiles.Batch479.profile19190,(fun _ => MergedCutProfiles.Batch479.profile19190)⟩
theorem profilesValid3118 : retention3118.ProfilesValid := by
  exact MergedCutProfiles.Batch479.valid19190
theorem numericValid3118 : retention3118.NumericValid := by decide +kernel
def certificate3118 : RatCutBinCertificate := ⟨⟨retention3118,(1006649867131201179/500000000000000000),(5622540848385301/62500000000000000),(5947016094090640243/500000000000000000),(1523646054422456694899/1000000000000000000),(1102569055104384993/1000000000000000000)⟩,(499395739503336353/500000000000000000),(231280808915297517/500000000000000000),(180814521889521099/1000000000000000000),(10573113910795449/62500000000000000)⟩
theorem valid3118 : certificate3118.Valid := by decide +kernel
theorem sound3118 : certificate3118.Sound := rat_cut_bin_certificate_sound certificate3118 profilesValid3118 numericValid3118 valid3118

def retention3119 : RatCutRetentionCertificate := ⟨(43/1000),(11/250),(8995721308035307190/18199954324847528763),(27664713533970385573/500000000000000000),1,(11158489265730942545872514162748652527/11065885413588154229200000000000000000),false,MergedCutProfiles.Batch479.profile19191,(fun _ => MergedCutProfiles.Batch479.profile19191)⟩
theorem profilesValid3119 : retention3119.ProfilesValid := by
  exact MergedCutProfiles.Batch479.valid19191
theorem numericValid3119 : retention3119.NumericValid := by decide +kernel
def certificate3119 : RatCutBinCertificate := ⟨⟨retention3119,(1006649867131201179/500000000000000000),(5622540848385301/62500000000000000),(5947016094090640243/500000000000000000),(1523646054422456694899/1000000000000000000),(248285194014234703/250000000000000000)⟩,(499395739503336353/500000000000000000),(117350142677561643/250000000000000000),(175592204007989357/1000000000000000000),(171103572060643951/1000000000000000000)⟩
theorem valid3119 : certificate3119.Valid := by decide +kernel
theorem sound3119 : certificate3119.Sound := rat_cut_bin_certificate_sound certificate3119 profilesValid3119 numericValid3119 valid3119

def certificates : List RatCutBinCertificate := [certificate3108,certificate3109,certificate3110,certificate3111,certificate3112,certificate3113,certificate3114,certificate3115,certificate3116,certificate3117,certificate3118,certificate3119]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3108,List.forall_mem_cons.mpr ⟨sound3109,List.forall_mem_cons.mpr ⟨sound3110,List.forall_mem_cons.mpr ⟨sound3111,List.forall_mem_cons.mpr ⟨sound3112,List.forall_mem_cons.mpr ⟨sound3113,List.forall_mem_cons.mpr ⟨sound3114,List.forall_mem_cons.mpr ⟨sound3115,List.forall_mem_cons.mpr ⟨sound3116,List.forall_mem_cons.mpr ⟨sound3117,List.forall_mem_cons.mpr ⟨sound3118,List.forall_mem_cons.mpr ⟨sound3119,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch259
