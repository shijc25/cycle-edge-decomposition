import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch429
import Cycle12.MergedCutProfiles.Batch430
import Cycle12.MergedCutProfiles.Batch431

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch226

def retention2712 : RatCutRetentionCertificate := ⟨(13/200),(131/2000),(10095110493272903508/20249638546476714625),(2498789726057649383/250000000000000000),1,(489431543720014495551848018960991951/499757945211529876600000000000000000),false,MergedCutProfiles.Batch429.profile17183,(fun _ => MergedCutProfiles.Batch429.profile17183)⟩
theorem profilesValid2712 : retention2712.ProfilesValid := by
  exact MergedCutProfiles.Batch429.valid17183
theorem numericValid2712 : retention2712.NumericValid := by decide +kernel
def certificate2712 : RatCutBinCertificate := ⟨⟨retention2712,(2585937105524707053/1000000000000000000),(225107070921290071/1000000000000000000),(4356274722595414287/250000000000000000),(88493122161958402527/250000000000000000),(472964250902247387/500000000000000000)⟩,(994299292264416211/1000000000000000000),(48927463063600329/200000000000000000),(205410647394323297/500000000000000000),(352873952220634029/1000000000000000000)⟩
theorem valid2712 : certificate2712.Valid := by decide +kernel
theorem sound2712 : certificate2712.Sound := rat_cut_bin_certificate_sound certificate2712 profilesValid2712 numericValid2712 valid2712

def retention2713 : RatCutRetentionCertificate := ⟨(13/200),(131/2000),(1/2),(2523777623318225877/250000000000000000),1,(1972167571002956503414674846332389363/2019022098654580701600000000000000000),false,MergedCutProfiles.Batch429.profile17180,(fun _ => MergedCutProfiles.Batch429.profile17180)⟩
theorem profilesValid2713 : retention2713.ProfilesValid := by
  exact MergedCutProfiles.Batch429.valid17180
theorem numericValid2713 : retention2713.NumericValid := by decide +kernel
def certificate2713 : RatCutBinCertificate := ⟨⟨retention2713,(2585937105524707053/1000000000000000000),(225107070921290071/1000000000000000000),(4356274722595414287/250000000000000000),(88493122161958402527/250000000000000000),(47169239183249291/50000000000000000)⟩,(994299292264416211/1000000000000000000),(122648474499038047/500000000000000000),(409895050713106877/1000000000000000000),(351514372920163247/1000000000000000000)⟩
theorem valid2713 : certificate2713.Valid := by decide +kernel
theorem sound2713 : certificate2713.Sound := rat_cut_bin_certificate_sound certificate2713 profilesValid2713 numericValid2713 valid2713

def retention2714 : RatCutRetentionCertificate := ⟨(131/2000),(33/500),(483761930995088797/9940316909040723322),(957944417812057023/1000000000000000000),(51/20),(10283045662775085333/5000000000000000000),true,MergedCutProfiles.Batch429.profile17184,![MergedCutProfiles.Batch429.profile17184,MergedCutProfiles.Batch429.profile17185,MergedCutProfiles.Batch429.profile17186,MergedCutProfiles.Batch429.profile17187,MergedCutProfiles.Batch429.profile17188,MergedCutProfiles.Batch429.profile17189,MergedCutProfiles.Batch429.profile17190,MergedCutProfiles.Batch429.profile17191,MergedCutProfiles.Batch429.profile17192,MergedCutProfiles.Batch429.profile17193,MergedCutProfiles.Batch429.profile17194,MergedCutProfiles.Batch429.profile17195,MergedCutProfiles.Batch429.profile17196,MergedCutProfiles.Batch429.profile17197,MergedCutProfiles.Batch429.profile17198,MergedCutProfiles.Batch429.profile17199]⟩
theorem profilesValid2714 : retention2714.ProfilesValid := by
  change ∀ j : Fin 16, (retention2714.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch429.valid17184
  · exact MergedCutProfiles.Batch429.valid17185
  · exact MergedCutProfiles.Batch429.valid17186
  · exact MergedCutProfiles.Batch429.valid17187
  · exact MergedCutProfiles.Batch429.valid17188
  · exact MergedCutProfiles.Batch429.valid17189
  · exact MergedCutProfiles.Batch429.valid17190
  · exact MergedCutProfiles.Batch429.valid17191
  · exact MergedCutProfiles.Batch429.valid17192
  · exact MergedCutProfiles.Batch429.valid17193
  · exact MergedCutProfiles.Batch429.valid17194
  · exact MergedCutProfiles.Batch429.valid17195
  · exact MergedCutProfiles.Batch429.valid17196
  · exact MergedCutProfiles.Batch429.valid17197
  · exact MergedCutProfiles.Batch429.valid17198
  · exact MergedCutProfiles.Batch429.valid17199
theorem numericValid2714 : retention2714.NumericValid := by decide +kernel
def certificate2714 : RatCutBinCertificate := ⟨⟨retention2714,(1176621513092031847/500000000000000000),(229314578619222081/1000000000000000000),(4398392572121590119/250000000000000000),(175442977448303472037/500000000000000000),(3165398688785679/1600000000000000)⟩,(497397524929653203/500000000000000000),(271206833614272957/1000000000000000000),(93713346274468041/250000000000000000),(219332749977699999/1000000000000000000)⟩
theorem valid2714 : certificate2714.Valid := by decide +kernel
theorem sound2714 : certificate2714.Sound := rat_cut_bin_certificate_sound certificate2714 profilesValid2714 numericValid2714 valid2714

def retention2715 : RatCutRetentionCertificate := ⟨(131/2000),(33/500),(245443704500000000/4970158454520361661),(483761930995088797/500000000000000000),(5/2),(261930164809286779941/128000000000000000000),true,MergedCutProfiles.Batch430.profile17200,![MergedCutProfiles.Batch430.profile17200,MergedCutProfiles.Batch430.profile17201,MergedCutProfiles.Batch430.profile17202,MergedCutProfiles.Batch430.profile17203,MergedCutProfiles.Batch430.profile17204,MergedCutProfiles.Batch430.profile17205,MergedCutProfiles.Batch430.profile17206,MergedCutProfiles.Batch430.profile17207,MergedCutProfiles.Batch430.profile17208,MergedCutProfiles.Batch430.profile17209,MergedCutProfiles.Batch430.profile17210,MergedCutProfiles.Batch430.profile17211,MergedCutProfiles.Batch430.profile17212,MergedCutProfiles.Batch430.profile17213,MergedCutProfiles.Batch430.profile17214,MergedCutProfiles.Batch430.profile17215]⟩
theorem profilesValid2715 : retention2715.ProfilesValid := by
  change ∀ j : Fin 16, (retention2715.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch430.valid17200
  · exact MergedCutProfiles.Batch430.valid17201
  · exact MergedCutProfiles.Batch430.valid17202
  · exact MergedCutProfiles.Batch430.valid17203
  · exact MergedCutProfiles.Batch430.valid17204
  · exact MergedCutProfiles.Batch430.valid17205
  · exact MergedCutProfiles.Batch430.valid17206
  · exact MergedCutProfiles.Batch430.valid17207
  · exact MergedCutProfiles.Batch430.valid17208
  · exact MergedCutProfiles.Batch430.valid17209
  · exact MergedCutProfiles.Batch430.valid17210
  · exact MergedCutProfiles.Batch430.valid17211
  · exact MergedCutProfiles.Batch430.valid17212
  · exact MergedCutProfiles.Batch430.valid17213
  · exact MergedCutProfiles.Batch430.valid17214
  · exact MergedCutProfiles.Batch430.valid17215
theorem numericValid2715 : retention2715.NumericValid := by decide +kernel
def certificate2715 : RatCutBinCertificate := ⟨⟨retention2715,(1176621513092031847/500000000000000000),(229314578619222081/1000000000000000000),(4398392572121590119/250000000000000000),(175442977448303472037/500000000000000000),(984814138029281523/500000000000000000)⟩,(497397524929653203/500000000000000000),(271388088443754631/1000000000000000000),(37461716220960249/100000000000000000),(27653363255216219/125000000000000000)⟩
theorem valid2715 : certificate2715.Valid := by decide +kernel
theorem sound2715 : certificate2715.Sound := rat_cut_bin_certificate_sound certificate2715 profilesValid2715 numericValid2715 valid2715

def retention2716 : RatCutRetentionCertificate := ⟨(131/2000),(33/500),(39896789863337431/764639762233901794),(490887409/500000000),(5/2),(8181335725765812941/4000000000000000000),true,MergedCutProfiles.Batch430.profile17216,![MergedCutProfiles.Batch430.profile17216,MergedCutProfiles.Batch430.profile17217,MergedCutProfiles.Batch430.profile17218,MergedCutProfiles.Batch430.profile17219,MergedCutProfiles.Batch430.profile17220,MergedCutProfiles.Batch430.profile17221,MergedCutProfiles.Batch430.profile17222,MergedCutProfiles.Batch430.profile17223,MergedCutProfiles.Batch430.profile17224,MergedCutProfiles.Batch430.profile17225,MergedCutProfiles.Batch430.profile17226,MergedCutProfiles.Batch430.profile17227,MergedCutProfiles.Batch430.profile17228,MergedCutProfiles.Batch429.profile17198,MergedCutProfiles.Batch430.profile17229,MergedCutProfiles.Batch430.profile17230]⟩
theorem profilesValid2716 : retention2716.ProfilesValid := by
  change ∀ j : Fin 16, (retention2716.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch430.valid17216
  · exact MergedCutProfiles.Batch430.valid17217
  · exact MergedCutProfiles.Batch430.valid17218
  · exact MergedCutProfiles.Batch430.valid17219
  · exact MergedCutProfiles.Batch430.valid17220
  · exact MergedCutProfiles.Batch430.valid17221
  · exact MergedCutProfiles.Batch430.valid17222
  · exact MergedCutProfiles.Batch430.valid17223
  · exact MergedCutProfiles.Batch430.valid17224
  · exact MergedCutProfiles.Batch430.valid17225
  · exact MergedCutProfiles.Batch430.valid17226
  · exact MergedCutProfiles.Batch430.valid17227
  · exact MergedCutProfiles.Batch430.valid17228
  · exact MergedCutProfiles.Batch429.valid17198
  · exact MergedCutProfiles.Batch430.valid17229
  · exact MergedCutProfiles.Batch430.valid17230
theorem numericValid2716 : retention2716.NumericValid := by decide +kernel
def certificate2716 : RatCutBinCertificate := ⟨⟨retention2716,(1176621513092031847/500000000000000000),(229314578619222081/1000000000000000000),(4398392572121590119/250000000000000000),(175442977448303472037/500000000000000000),(1537994605984459/781250000000000)⟩,(497397524929653203/500000000000000000),(135019791308423799/500000000000000000),(94094375323181967/250000000000000000),(4459586032076943/20000000000000000)⟩
theorem valid2716 : certificate2716.Valid := by decide +kernel
theorem sound2716 : certificate2716.Sound := rat_cut_bin_certificate_sound certificate2716 profilesValid2716 numericValid2716 valid2716

def retention2717 : RatCutRetentionCertificate := ⟨(131/2000),(33/500),(1499001720241894917/19880633818081446644),(518658268223386603/500000000000000000),(47/20),(1260146764082536859347/640000000000000000000),true,MergedCutProfiles.Batch430.profile17231,![MergedCutProfiles.Batch430.profile17231,MergedCutProfiles.Batch430.profile17232,MergedCutProfiles.Batch430.profile17233,MergedCutProfiles.Batch430.profile17234,MergedCutProfiles.Batch430.profile17235,MergedCutProfiles.Batch430.profile17236,MergedCutProfiles.Batch430.profile17237,MergedCutProfiles.Batch430.profile17238,MergedCutProfiles.Batch430.profile17228,MergedCutProfiles.Batch430.profile17239,MergedCutProfiles.Batch431.profile17240,MergedCutProfiles.Batch431.profile17241,MergedCutProfiles.Batch431.profile17242,MergedCutProfiles.Batch431.profile17243,MergedCutProfiles.Batch431.profile17244,MergedCutProfiles.Batch431.profile17245]⟩
theorem profilesValid2717 : retention2717.ProfilesValid := by
  change ∀ j : Fin 16, (retention2717.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch430.valid17231
  · exact MergedCutProfiles.Batch430.valid17232
  · exact MergedCutProfiles.Batch430.valid17233
  · exact MergedCutProfiles.Batch430.valid17234
  · exact MergedCutProfiles.Batch430.valid17235
  · exact MergedCutProfiles.Batch430.valid17236
  · exact MergedCutProfiles.Batch430.valid17237
  · exact MergedCutProfiles.Batch430.valid17238
  · exact MergedCutProfiles.Batch430.valid17228
  · exact MergedCutProfiles.Batch430.valid17239
  · exact MergedCutProfiles.Batch431.valid17240
  · exact MergedCutProfiles.Batch431.valid17241
  · exact MergedCutProfiles.Batch431.valid17242
  · exact MergedCutProfiles.Batch431.valid17243
  · exact MergedCutProfiles.Batch431.valid17244
  · exact MergedCutProfiles.Batch431.valid17245
theorem numericValid2717 : retention2717.NumericValid := by decide +kernel
def certificate2717 : RatCutBinCertificate := ⟨⟨retention2717,(1176621513092031847/500000000000000000),(229314578619222081/1000000000000000000),(4398392572121590119/250000000000000000),(175442977448303472037/500000000000000000),(1896880401423375829/1000000000000000000)⟩,(497397524929653203/500000000000000000),(274649215855191589/1000000000000000000),(370387482529421093/1000000000000000000),(223188741343435461/1000000000000000000)⟩
theorem valid2717 : certificate2717.Valid := by decide +kernel
theorem sound2717 : certificate2717.Sound := rat_cut_bin_certificate_sound certificate2717 profilesValid2717 numericValid2717 valid2717

def retention2718 : RatCutRetentionCertificate := ⟨(131/2000),(33/500),(1034004111739999353/4970158454520361661),(1499001720241894917/1000000000000000000),(9/5),(2065843825654787088873/1280000000000000000000),true,MergedCutProfiles.Batch430.profile17219,![MergedCutProfiles.Batch430.profile17219,MergedCutProfiles.Batch430.profile17223,MergedCutProfiles.Batch431.profile17246,MergedCutProfiles.Batch430.profile17230,MergedCutProfiles.Batch431.profile17247,MergedCutProfiles.Batch431.profile17248,MergedCutProfiles.Batch431.profile17249,MergedCutProfiles.Batch431.profile17250,MergedCutProfiles.Batch431.profile17251,MergedCutProfiles.Batch431.profile17252,MergedCutProfiles.Batch431.profile17253,MergedCutProfiles.Batch431.profile17254,MergedCutProfiles.Batch431.profile17255,MergedCutProfiles.Batch431.profile17256,MergedCutProfiles.Batch431.profile17257,MergedCutProfiles.Batch431.profile17258]⟩
theorem profilesValid2718 : retention2718.ProfilesValid := by
  change ∀ j : Fin 16, (retention2718.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch430.valid17219
  · exact MergedCutProfiles.Batch430.valid17223
  · exact MergedCutProfiles.Batch431.valid17246
  · exact MergedCutProfiles.Batch430.valid17230
  · exact MergedCutProfiles.Batch431.valid17247
  · exact MergedCutProfiles.Batch431.valid17248
  · exact MergedCutProfiles.Batch431.valid17249
  · exact MergedCutProfiles.Batch431.valid17250
  · exact MergedCutProfiles.Batch431.valid17251
  · exact MergedCutProfiles.Batch431.valid17252
  · exact MergedCutProfiles.Batch431.valid17253
  · exact MergedCutProfiles.Batch431.valid17254
  · exact MergedCutProfiles.Batch431.valid17255
  · exact MergedCutProfiles.Batch431.valid17256
  · exact MergedCutProfiles.Batch431.valid17257
  · exact MergedCutProfiles.Batch431.valid17258
theorem numericValid2718 : retention2718.NumericValid := by decide +kernel
def certificate2718 : RatCutBinCertificate := ⟨⟨retention2718,(1176621513092031847/500000000000000000),(229314578619222081/1000000000000000000),(4398392572121590119/250000000000000000),(175442977448303472037/500000000000000000),(389679303781460661/250000000000000000)⟩,(497397524929653203/500000000000000000),(18568669816076717/62500000000000000),(342290435803777667/1000000000000000000),(111501960744518507/500000000000000000)⟩
theorem valid2718 : certificate2718.Valid := by decide +kernel
theorem sound2718 : certificate2718.Sound := rat_cut_bin_certificate_sound certificate2718 profilesValid2718 numericValid2718 valid2718

def retention2719 : RatCutRetentionCertificate := ⟨(131/2000),(33/500),(8551504787640704779/19880633818081446644),(1034004111739999353/250000000000000000),(11/10),(356105296355650230189/320000000000000000000),true,MergedCutProfiles.Batch431.profile17259,![MergedCutProfiles.Batch431.profile17259,MergedCutProfiles.Batch431.profile17260,MergedCutProfiles.Batch431.profile17261,MergedCutProfiles.Batch431.profile17262,MergedCutProfiles.Batch431.profile17263,MergedCutProfiles.Batch431.profile17264,MergedCutProfiles.Batch431.profile17265,MergedCutProfiles.Batch431.profile17266,MergedCutProfiles.Batch431.profile17267,MergedCutProfiles.Batch431.profile17268,MergedCutProfiles.Batch431.profile17269,MergedCutProfiles.Batch431.profile17270,MergedCutProfiles.Batch431.profile17271,MergedCutProfiles.Batch431.profile17272,MergedCutProfiles.Batch431.profile17273,MergedCutProfiles.Batch431.profile17274]⟩
theorem profilesValid2719 : retention2719.ProfilesValid := by
  change ∀ j : Fin 16, (retention2719.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch431.valid17259
  · exact MergedCutProfiles.Batch431.valid17260
  · exact MergedCutProfiles.Batch431.valid17261
  · exact MergedCutProfiles.Batch431.valid17262
  · exact MergedCutProfiles.Batch431.valid17263
  · exact MergedCutProfiles.Batch431.valid17264
  · exact MergedCutProfiles.Batch431.valid17265
  · exact MergedCutProfiles.Batch431.valid17266
  · exact MergedCutProfiles.Batch431.valid17267
  · exact MergedCutProfiles.Batch431.valid17268
  · exact MergedCutProfiles.Batch431.valid17269
  · exact MergedCutProfiles.Batch431.valid17270
  · exact MergedCutProfiles.Batch431.valid17271
  · exact MergedCutProfiles.Batch431.valid17272
  · exact MergedCutProfiles.Batch431.valid17273
  · exact MergedCutProfiles.Batch431.valid17274
theorem numericValid2719 : retention2719.NumericValid := by decide +kernel
def certificate2719 : RatCutBinCertificate := ⟨⟨retention2719,(1176621513092031847/500000000000000000),(229314578619222081/1000000000000000000),(4398392572121590119/250000000000000000),(175442977448303472037/500000000000000000),(269771205120548823/250000000000000000)⟩,(497397524929653203/500000000000000000),(176155800900953919/500000000000000000),(140068829800295129/500000000000000000),(224747138539971857/1000000000000000000)⟩
theorem valid2719 : certificate2719.Valid := by decide +kernel
theorem sound2719 : certificate2719.Sound := rat_cut_bin_certificate_sound certificate2719 profilesValid2719 numericValid2719 valid2719

def retention2720 : RatCutRetentionCertificate := ⟨(131/2000),(33/500),(9732410136406989699/19880633818081446644),(8551504787640704779/1000000000000000000),(21/20),(13850353864922193861921109031854549453359/13682407660225127646400000000000000000000),false,MergedCutProfiles.Batch431.profile17275,(fun _ => MergedCutProfiles.Batch431.profile17275)⟩
theorem profilesValid2720 : retention2720.ProfilesValid := by
  exact MergedCutProfiles.Batch431.valid17275
theorem numericValid2720 : retention2720.NumericValid := by decide +kernel
def certificate2720 : RatCutBinCertificate := ⟨⟨retention2720,(1176621513092031847/500000000000000000),(229314578619222081/1000000000000000000),(4398392572121590119/250000000000000000),(175442977448303472037/500000000000000000),(980066489218611069/1000000000000000000)⟩,(497397524929653203/500000000000000000),(363073783695496019/1000000000000000000),(269074300917155723/1000000000000000000),(28279884460439007/125000000000000000)⟩
theorem valid2720 : certificate2720.Valid := by decide +kernel
theorem sound2720 : certificate2720.Sound := rat_cut_bin_certificate_sound certificate2720 profilesValid2720 numericValid2720 valid2720

def retention2721 : RatCutRetentionCertificate := ⟨(131/2000),(33/500),(2457433559442764899/4970158454520361661),(9732410136406989699/1000000000000000000),(21/20),(505172701590473540441269226899855347929/502317942524231726400000000000000000000),false,MergedCutProfiles.Batch431.profile17276,(fun _ => MergedCutProfiles.Batch431.profile17276)⟩
theorem profilesValid2721 : retention2721.ProfilesValid := by
  exact MergedCutProfiles.Batch431.valid17276
theorem numericValid2721 : retention2721.NumericValid := by decide +kernel
def certificate2721 : RatCutBinCertificate := ⟨⟨retention2721,(1176621513092031847/500000000000000000),(229314578619222081/1000000000000000000),(4398392572121590119/250000000000000000),(175442977448303472037/500000000000000000),(243368834051624007/250000000000000000)⟩,(497397524929653203/500000000000000000),(22668158473208237/62500000000000000),(269462746387054083/1000000000000000000),(227780085665368537/1000000000000000000)⟩
theorem valid2721 : certificate2721.Valid := by decide +kernel
theorem sound2721 : certificate2721.Sound := rat_cut_bin_certificate_sound certificate2721 profilesValid2721 numericValid2721 valid2721

def retention2722 : RatCutRetentionCertificate := ⟨(131/2000),(33/500),(190923684233630196/382319881116950897),(2457433559442764899/250000000000000000),(21/20),(1912630702395930621927220100939558997/1919869968314660077343750000000000000),false,MergedCutProfiles.Batch431.profile17277,(fun _ => MergedCutProfiles.Batch431.profile17277)⟩
theorem profilesValid2722 : retention2722.ProfilesValid := by
  exact MergedCutProfiles.Batch431.valid17277
theorem numericValid2722 : retention2722.NumericValid := by decide +kernel
def certificate2722 : RatCutBinCertificate := ⟨⟨retention2722,(1176621513092031847/500000000000000000),(229314578619222081/1000000000000000000),(4398392572121590119/250000000000000000),(175442977448303472037/500000000000000000),(241005369656715797/250000000000000000)⟩,(497397524929653203/500000000000000000),(91510399757487309/250000000000000000),(266079886367035393/1000000000000000000),(111549478049885717/500000000000000000)⟩
theorem valid2722 : certificate2722.Valid := by decide +kernel
theorem sound2722 : certificate2722.Sound := rat_cut_bin_certificate_sound certificate2722 profilesValid2722 numericValid2722 valid2722

def retention2723 : RatCutRetentionCertificate := ⟨(131/2000),(33/500),(1/2),(620501973759298137/62500000000000000),(21/20),(988052207013415766475446575822240368671/992803158014877019200000000000000000000),false,MergedCutProfiles.Batch431.profile17278,(fun _ => MergedCutProfiles.Batch431.profile17278)⟩
theorem profilesValid2723 : retention2723.ProfilesValid := by
  exact MergedCutProfiles.Batch431.valid17278
theorem numericValid2723 : retention2723.NumericValid := by decide +kernel
def certificate2723 : RatCutBinCertificate := ⟨⟨retention2723,(1176621513092031847/500000000000000000),(229314578619222081/1000000000000000000),(4398392572121590119/250000000000000000),(175442977448303472037/500000000000000000),(240751703621246713/250000000000000000)⟩,(497397524929653203/500000000000000000),(45777921084179433/125000000000000000),(132948635373817101/500000000000000000),(55727768403580157/250000000000000000)⟩
theorem valid2723 : certificate2723.Valid := by decide +kernel
theorem sound2723 : certificate2723.Sound := rat_cut_bin_certificate_sound certificate2723 profilesValid2723 numericValid2723 valid2723

def certificates : List RatCutBinCertificate := [certificate2712,certificate2713,certificate2714,certificate2715,certificate2716,certificate2717,certificate2718,certificate2719,certificate2720,certificate2721,certificate2722,certificate2723]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2712,List.forall_mem_cons.mpr ⟨sound2713,List.forall_mem_cons.mpr ⟨sound2714,List.forall_mem_cons.mpr ⟨sound2715,List.forall_mem_cons.mpr ⟨sound2716,List.forall_mem_cons.mpr ⟨sound2717,List.forall_mem_cons.mpr ⟨sound2718,List.forall_mem_cons.mpr ⟨sound2719,List.forall_mem_cons.mpr ⟨sound2720,List.forall_mem_cons.mpr ⟨sound2721,List.forall_mem_cons.mpr ⟨sound2722,List.forall_mem_cons.mpr ⟨sound2723,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch226
