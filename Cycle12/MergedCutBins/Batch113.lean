import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch221
import Cycle12.MergedCutProfiles.Batch222
import Cycle12.MergedCutProfiles.Batch223

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch113

def retention1356 : RatCutRetentionCertificate := ⟨(237/4000),(119/2000),(1097095319656868391/2547307847567706842),(3110971704388536801/1000000000000000000),(23/20),(1421754229692009058017/1280000000000000000000),true,MergedCutProfiles.Batch221.profile8843,![MergedCutProfiles.Batch221.profile8843,MergedCutProfiles.Batch221.profile8844,MergedCutProfiles.Batch221.profile8845,MergedCutProfiles.Batch221.profile8846,MergedCutProfiles.Batch221.profile8847,MergedCutProfiles.Batch221.profile8848,MergedCutProfiles.Batch221.profile8849,MergedCutProfiles.Batch221.profile8850,MergedCutProfiles.Batch221.profile8851,MergedCutProfiles.Batch221.profile8852,MergedCutProfiles.Batch221.profile8853,MergedCutProfiles.Batch221.profile8854,MergedCutProfiles.Batch221.profile8855,MergedCutProfiles.Batch221.profile8856,MergedCutProfiles.Batch221.profile8857,MergedCutProfiles.Batch221.profile8858]⟩
theorem profilesValid1356 : retention1356.ProfilesValid := by
  change ∀ j : Fin 16, (retention1356.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch221.valid8843
  · exact MergedCutProfiles.Batch221.valid8844
  · exact MergedCutProfiles.Batch221.valid8845
  · exact MergedCutProfiles.Batch221.valid8846
  · exact MergedCutProfiles.Batch221.valid8847
  · exact MergedCutProfiles.Batch221.valid8848
  · exact MergedCutProfiles.Batch221.valid8849
  · exact MergedCutProfiles.Batch221.valid8850
  · exact MergedCutProfiles.Batch221.valid8851
  · exact MergedCutProfiles.Batch221.valid8852
  · exact MergedCutProfiles.Batch221.valid8853
  · exact MergedCutProfiles.Batch221.valid8854
  · exact MergedCutProfiles.Batch221.valid8855
  · exact MergedCutProfiles.Batch221.valid8856
  · exact MergedCutProfiles.Batch221.valid8857
  · exact MergedCutProfiles.Batch221.valid8858
theorem numericValid1356 : retention1356.NumericValid := by decide +kernel
def certificate1356 : RatCutBinCertificate := ⟨⟨retention1356,(2303314778672908521/1000000000000000000),(178859476136284067/1000000000000000000),(3911561957736737917/250000000000000000),(19958276023943220001/100000000000000000),(108045811533702439/100000000000000000)⟩,(99048287419965671/100000000000000000),(21821206996107561/50000000000000000),(50429601484239557/250000000000000000),(74238675017972111/500000000000000000)⟩
theorem valid1356 : certificate1356.Valid := by decide +kernel
theorem sound1356 : certificate1356.Sound := rat_cut_bin_certificate_sound certificate1356 profilesValid1356 numericValid1356 valid1356

def retention1357 : RatCutRetentionCertificate := ⟨(237/4000),(119/2000),(6242984056481468077/12736539237838534210),(1097095319656868391/200000000000000000),(11/10),(29582015835415345867056942962103997437/29255875190849823760000000000000000000),false,MergedCutProfiles.Batch221.profile8859,(fun _ => MergedCutProfiles.Batch221.profile8859)⟩
theorem profilesValid1357 : retention1357.ProfilesValid := by
  exact MergedCutProfiles.Batch221.valid8859
theorem numericValid1357 : retention1357.NumericValid := by decide +kernel
def certificate1357 : RatCutBinCertificate := ⟨⟨retention1357,(2303314778672908521/1000000000000000000),(178859476136284067/1000000000000000000),(3911561957736737917/250000000000000000),(19958276023943220001/100000000000000000),(122772535959599701/125000000000000000)⟩,(99048287419965671/100000000000000000),(112348856747132437/250000000000000000),(191154414691964933/1000000000000000000),(29427529957109141/200000000000000000)⟩
theorem valid1357 : certificate1357.Valid := by decide +kernel
theorem sound1357 : certificate1357.Sound := rat_cut_bin_certificate_sound certificate1357 profilesValid1357 numericValid1357 valid1357

def retention1358 : RatCutRetentionCertificate := ⟨(237/4000),(119/2000),(3152706948523141379/6368269618919267105),(6242984056481468077/1000000000000000000),(21/20),(9907966511367120485925379485145003417751/9988774490370348923200000000000000000000),false,MergedCutProfiles.Batch221.profile8860,(fun _ => MergedCutProfiles.Batch221.profile8860)⟩
theorem profilesValid1358 : retention1358.ProfilesValid := by
  exact MergedCutProfiles.Batch221.valid8860
theorem numericValid1358 : retention1358.NumericValid := by decide +kernel
def certificate1358 : RatCutBinCertificate := ⟨⟨retention1358,(2303314778672908521/1000000000000000000),(178859476136284067/1000000000000000000),(3911561957736737917/250000000000000000),(19958276023943220001/100000000000000000),(96425957477174693/100000000000000000)⟩,(99048287419965671/100000000000000000),(28298542535775907/62500000000000000),(5889457195335963/31250000000000000),(30048297520870587/200000000000000000)⟩
theorem valid1358 : certificate1358.Valid := by decide +kernel
theorem sound1358 : certificate1358.Sound := rat_cut_bin_certificate_sound certificate1358 profilesValid1358 numericValid1358 valid1358

def retention1359 : RatCutRetentionCertificate := ⟨(237/4000),(119/2000),(1/2),(3152706948523141379/500000000000000000),(21/20),(2479102684114706951138670174395989401479/2522165558818513103200000000000000000000),false,MergedCutProfiles.Batch221.profile8861,(fun _ => MergedCutProfiles.Batch221.profile8861)⟩
theorem profilesValid1359 : retention1359.ProfilesValid := by
  exact MergedCutProfiles.Batch221.valid8861
theorem numericValid1359 : retention1359.NumericValid := by decide +kernel
def certificate1359 : RatCutBinCertificate := ⟨⟨retention1359,(2303314778672908521/1000000000000000000),(178859476136284067/1000000000000000000),(3911561957736737917/250000000000000000),(19958276023943220001/100000000000000000),(955275721375980427/1000000000000000000)⟩,(99048287419965671/100000000000000000),(456675058523992689/1000000000000000000),(92695245613014399/500000000000000000),(73380614619847287/500000000000000000)⟩
theorem valid1359 : certificate1359.Valid := by decide +kernel
theorem sound1359 : certificate1359.Sound := rat_cut_bin_certificate_sound certificate1359 profilesValid1359 numericValid1359 valid1359

def retention1360 : RatCutRetentionCertificate := ⟨(237/4000),(119/2000),(1/2),64,1,(255407084582233976006471371880529704599/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch221.profile8861,(fun _ => MergedCutProfiles.Batch221.profile8861)⟩
theorem profilesValid1360 : retention1360.ProfilesValid := by
  exact MergedCutProfiles.Batch221.valid8861
theorem numericValid1360 : retention1360.NumericValid := by decide +kernel
def certificate1360 : RatCutBinCertificate := ⟨⟨retention1360,(2303314778672908521/1000000000000000000),(178859476136284067/1000000000000000000),(3911561957736737917/250000000000000000),(19958276023943220001/100000000000000000),(971353301766792969/1000000000000000000)⟩,(99048287419965671/100000000000000000),(52152881778580427/125000000000000000),(218067171640003589/1000000000000000000),(206648730319539573/1000000000000000000)⟩
theorem valid1360 : certificate1360.Valid := by decide +kernel
theorem sound1360 : certificate1360.Sound := rat_cut_bin_certificate_sound certificate1360 profilesValid1360 numericValid1360 valid1360

def retention1361 : RatCutRetentionCertificate := ⟨(237/4000),(119/2000),(1178690580232093265/2547307847567706842),(1791724087690645273/500000000000000000),(6/5),(95647345775473643883852064726601117271/89586204384532263650000000000000000000),false,MergedCutProfiles.Batch221.profile8862,(fun _ => MergedCutProfiles.Batch221.profile8862)⟩
theorem profilesValid1361 : retention1361.ProfilesValid := by
  exact MergedCutProfiles.Batch221.valid8862
theorem numericValid1361 : retention1361.NumericValid := by decide +kernel
def certificate1361 : RatCutBinCertificate := ⟨⟨retention1361,(2637037490672908521/1000000000000000000),(178859476136284067/1000000000000000000),(3911561957736737917/250000000000000000),(19958276023943220001/100000000000000000),(1031475315197056497/1000000000000000000)⟩,(989100723903492569/1000000000000000000),(383106791176119459/1000000000000000000),(249322425347876497/1000000000000000000),(88227873953004059/500000000000000000)⟩
theorem valid1361 : certificate1361.Valid := by decide +kernel
theorem sound1361 : certificate1361.Sound := rat_cut_bin_certificate_sound certificate1361 profilesValid1361 numericValid1361 valid1361

def retention1362 : RatCutRetentionCertificate := ⟨(237/4000),(119/2000),(631857920131175617/1273653923783853421),(235738116046418653/40000000000000000),(21/20),(372561023927364079140083851037496449079/377180985674269844800000000000000000000),false,MergedCutProfiles.Batch221.profile8863,(fun _ => MergedCutProfiles.Batch221.profile8863)⟩
theorem profilesValid1362 : retention1362.ProfilesValid := by
  exact MergedCutProfiles.Batch221.valid8863
theorem numericValid1362 : retention1362.NumericValid := by decide +kernel
def certificate1362 : RatCutBinCertificate := ⟨⟨retention1362,(2637037490672908521/1000000000000000000),(178859476136284067/1000000000000000000),(3911561957736737917/250000000000000000),(19958276023943220001/100000000000000000),(59755894017579191/62500000000000000)⟩,(989100723903492569/1000000000000000000),(206655973376800751/500000000000000000),(110752145973773677/500000000000000000),(43440051106354463/250000000000000000)⟩
theorem valid1362 : certificate1362.Valid := by decide +kernel
theorem sound1362 : certificate1362.Sound := rat_cut_bin_certificate_sound certificate1362 profilesValid1362 numericValid1362 valid1362

def retention1363 : RatCutRetentionCertificate := ⟨(237/4000),(119/2000),(1/2),(631857920131175617/100000000000000000),(21/20),(99378702409132111716691714931925478919/101097267220988098720000000000000000000),false,MergedCutProfiles.Batch221.profile8861,(fun _ => MergedCutProfiles.Batch221.profile8861)⟩
theorem profilesValid1363 : retention1363.ProfilesValid := by
  exact MergedCutProfiles.Batch221.valid8861
theorem numericValid1363 : retention1363.NumericValid := by decide +kernel
def certificate1363 : RatCutBinCertificate := ⟨⟨retention1363,(2637037490672908521/1000000000000000000),(178859476136284067/1000000000000000000),(3911561957736737917/250000000000000000),(19958276023943220001/100000000000000000),(951344150626595839/1000000000000000000)⟩,(989100723903492569/1000000000000000000),(16615026136325033/40000000000000000),(8787443894809461/40000000000000000),(173082799127607683/1000000000000000000)⟩
theorem valid1363 : certificate1363.Valid := by decide +kernel
theorem sound1363 : certificate1363.Sound := rat_cut_bin_certificate_sound certificate1363 profilesValid1363 numericValid1363 valid1363

def retention1364 : RatCutRetentionCertificate := ⟨(119/2000),(239/4000),(191967855388834176/2101821367760234893),(435864302863164401/500000000000000000),(53/20),(1230578894667241253961/640000000000000000000),true,MergedCutProfiles.Batch221.profile8864,![MergedCutProfiles.Batch221.profile8864,MergedCutProfiles.Batch221.profile8865,MergedCutProfiles.Batch221.profile8866,MergedCutProfiles.Batch221.profile8867,MergedCutProfiles.Batch221.profile8868,MergedCutProfiles.Batch221.profile8869,MergedCutProfiles.Batch221.profile8870,MergedCutProfiles.Batch221.profile8871,MergedCutProfiles.Batch221.profile8872,MergedCutProfiles.Batch221.profile8873,MergedCutProfiles.Batch221.profile8874,MergedCutProfiles.Batch221.profile8875,MergedCutProfiles.Batch221.profile8876,MergedCutProfiles.Batch221.profile8877,MergedCutProfiles.Batch221.profile8878,MergedCutProfiles.Batch221.profile8879]⟩
theorem profilesValid1364 : retention1364.ProfilesValid := by
  change ∀ j : Fin 16, (retention1364.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch221.valid8864
  · exact MergedCutProfiles.Batch221.valid8865
  · exact MergedCutProfiles.Batch221.valid8866
  · exact MergedCutProfiles.Batch221.valid8867
  · exact MergedCutProfiles.Batch221.valid8868
  · exact MergedCutProfiles.Batch221.valid8869
  · exact MergedCutProfiles.Batch221.valid8870
  · exact MergedCutProfiles.Batch221.valid8871
  · exact MergedCutProfiles.Batch221.valid8872
  · exact MergedCutProfiles.Batch221.valid8873
  · exact MergedCutProfiles.Batch221.valid8874
  · exact MergedCutProfiles.Batch221.valid8875
  · exact MergedCutProfiles.Batch221.valid8876
  · exact MergedCutProfiles.Batch221.valid8877
  · exact MergedCutProfiles.Batch221.valid8878
  · exact MergedCutProfiles.Batch221.valid8879
theorem numericValid1364 : retention1364.NumericValid := by decide +kernel
def certificate1364 : RatCutBinCertificate := ⟨⟨retention1364,(2309520674254567439/1000000000000000000),(90319036891105957/500000000000000000),(7858748083479551897/500000000000000000),(3970296207259030741/20000000000000000),(7235989165127817/3906250000000000)⟩,(990426110264388983/1000000000000000000),(70784918991113817/200000000000000000),(34807356588872277/125000000000000000),(147706789237442619/1000000000000000000)⟩
theorem valid1364 : certificate1364.Valid := by decide +kernel
theorem sound1364 : certificate1364.Sound := rat_cut_bin_certificate_sound certificate1364 profilesValid1364 numericValid1364 valid1364

def retention1365 : RatCutRetentionCertificate := ⟨(119/2000),(239/4000),(1226801152493853727/6305464103280704679),(4499246610675801/3906250000000000),(21/10),(65818739032542584019/40000000000000000000),true,MergedCutProfiles.Batch222.profile8880,![MergedCutProfiles.Batch222.profile8880,MergedCutProfiles.Batch222.profile8881,MergedCutProfiles.Batch222.profile8882,MergedCutProfiles.Batch222.profile8883,MergedCutProfiles.Batch222.profile8884,MergedCutProfiles.Batch222.profile8885,MergedCutProfiles.Batch222.profile8886,MergedCutProfiles.Batch222.profile8887,MergedCutProfiles.Batch222.profile8888,MergedCutProfiles.Batch222.profile8889,MergedCutProfiles.Batch222.profile8890,MergedCutProfiles.Batch222.profile8891,MergedCutProfiles.Batch222.profile8892,MergedCutProfiles.Batch222.profile8893,MergedCutProfiles.Batch222.profile8894,MergedCutProfiles.Batch222.profile8895]⟩
theorem profilesValid1365 : retention1365.ProfilesValid := by
  change ∀ j : Fin 16, (retention1365.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch222.valid8880
  · exact MergedCutProfiles.Batch222.valid8881
  · exact MergedCutProfiles.Batch222.valid8882
  · exact MergedCutProfiles.Batch222.valid8883
  · exact MergedCutProfiles.Batch222.valid8884
  · exact MergedCutProfiles.Batch222.valid8885
  · exact MergedCutProfiles.Batch222.valid8886
  · exact MergedCutProfiles.Batch222.valid8887
  · exact MergedCutProfiles.Batch222.valid8888
  · exact MergedCutProfiles.Batch222.valid8889
  · exact MergedCutProfiles.Batch222.valid8890
  · exact MergedCutProfiles.Batch222.valid8891
  · exact MergedCutProfiles.Batch222.valid8892
  · exact MergedCutProfiles.Batch222.valid8893
  · exact MergedCutProfiles.Batch222.valid8894
  · exact MergedCutProfiles.Batch222.valid8895
theorem numericValid1365 : retention1365.NumericValid := by decide +kernel
def certificate1365 : RatCutBinCertificate := ⟨⟨retention1365,(2309520674254567439/1000000000000000000),(90319036891105957/500000000000000000),(7858748083479551897/500000000000000000),(3970296207259030741/20000000000000000),(794853745859926079/500000000000000000)⟩,(990426110264388983/1000000000000000000),(373090518553974893/1000000000000000000),(129531891685200777/500000000000000000),(73828430121373049/500000000000000000)⟩
theorem valid1365 : certificate1365.Valid := by decide +kernel
theorem sound1365 : certificate1365.Sound := rat_cut_bin_certificate_sound certificate1365 profilesValid1365 numericValid1365 valid1365

def retention1366 : RatCutRetentionCertificate := ⟨(119/2000),(239/4000),(1657679072840802513/4203642735520469786),(1226801152493853727/500000000000000000),(5/4),(30409639024706298751/25600000000000000000),true,MergedCutProfiles.Batch222.profile8896,![MergedCutProfiles.Batch222.profile8896,MergedCutProfiles.Batch222.profile8897,MergedCutProfiles.Batch222.profile8898,MergedCutProfiles.Batch222.profile8899,MergedCutProfiles.Batch222.profile8900,MergedCutProfiles.Batch222.profile8901,MergedCutProfiles.Batch222.profile8902,MergedCutProfiles.Batch222.profile8903,MergedCutProfiles.Batch222.profile8904,MergedCutProfiles.Batch222.profile8905,MergedCutProfiles.Batch222.profile8906,MergedCutProfiles.Batch222.profile8907,MergedCutProfiles.Batch222.profile8908,MergedCutProfiles.Batch222.profile8909,MergedCutProfiles.Batch222.profile8910,MergedCutProfiles.Batch222.profile8911]⟩
theorem profilesValid1366 : retention1366.ProfilesValid := by
  change ∀ j : Fin 16, (retention1366.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch222.valid8896
  · exact MergedCutProfiles.Batch222.valid8897
  · exact MergedCutProfiles.Batch222.valid8898
  · exact MergedCutProfiles.Batch222.valid8899
  · exact MergedCutProfiles.Batch222.valid8900
  · exact MergedCutProfiles.Batch222.valid8901
  · exact MergedCutProfiles.Batch222.valid8902
  · exact MergedCutProfiles.Batch222.valid8903
  · exact MergedCutProfiles.Batch222.valid8904
  · exact MergedCutProfiles.Batch222.valid8905
  · exact MergedCutProfiles.Batch222.valid8906
  · exact MergedCutProfiles.Batch222.valid8907
  · exact MergedCutProfiles.Batch222.valid8908
  · exact MergedCutProfiles.Batch222.valid8909
  · exact MergedCutProfiles.Batch222.valid8910
  · exact MergedCutProfiles.Batch222.valid8911
theorem numericValid1366 : retention1366.NumericValid := by decide +kernel
def certificate1366 : RatCutBinCertificate := ⟨⟨retention1366,(2309520674254567439/1000000000000000000),(90319036891105957/500000000000000000),(7858748083479551897/500000000000000000),(3970296207259030741/20000000000000000),(1154688100444880787/1000000000000000000)⟩,(990426110264388983/1000000000000000000),(424252246707673567/1000000000000000000),(2119817522373061/10000000000000000),(5953090593527469/40000000000000000)⟩
theorem valid1366 : certificate1366.Valid := by decide +kernel
theorem sound1366 : certificate1366.Sound := rat_cut_bin_certificate_sound certificate1366 profilesValid1366 numericValid1366 valid1366

def retention1367 : RatCutRetentionCertificate := ⟨(119/2000),(239/4000),(6007970774585725039/12610928206561409358),(4973037218522407539/1000000000000000000),1,(256601449481039244099/256000000000000000000),true,MergedCutProfiles.Batch222.profile8912,![MergedCutProfiles.Batch222.profile8912,MergedCutProfiles.Batch222.profile8913,MergedCutProfiles.Batch222.profile8914,MergedCutProfiles.Batch222.profile8915,MergedCutProfiles.Batch222.profile8916,MergedCutProfiles.Batch222.profile8917,MergedCutProfiles.Batch222.profile8918,MergedCutProfiles.Batch222.profile8919,MergedCutProfiles.Batch223.profile8920,MergedCutProfiles.Batch223.profile8921,MergedCutProfiles.Batch223.profile8922,MergedCutProfiles.Batch223.profile8923,MergedCutProfiles.Batch223.profile8924,MergedCutProfiles.Batch223.profile8925,MergedCutProfiles.Batch223.profile8926,MergedCutProfiles.Batch223.profile8927]⟩
theorem profilesValid1367 : retention1367.ProfilesValid := by
  change ∀ j : Fin 16, (retention1367.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch222.valid8912
  · exact MergedCutProfiles.Batch222.valid8913
  · exact MergedCutProfiles.Batch222.valid8914
  · exact MergedCutProfiles.Batch222.valid8915
  · exact MergedCutProfiles.Batch222.valid8916
  · exact MergedCutProfiles.Batch222.valid8917
  · exact MergedCutProfiles.Batch222.valid8918
  · exact MergedCutProfiles.Batch222.valid8919
  · exact MergedCutProfiles.Batch223.valid8920
  · exact MergedCutProfiles.Batch223.valid8921
  · exact MergedCutProfiles.Batch223.valid8922
  · exact MergedCutProfiles.Batch223.valid8923
  · exact MergedCutProfiles.Batch223.valid8924
  · exact MergedCutProfiles.Batch223.valid8925
  · exact MergedCutProfiles.Batch223.valid8926
  · exact MergedCutProfiles.Batch223.valid8927
theorem numericValid1367 : retention1367.NumericValid := by decide +kernel
def certificate1367 : RatCutBinCertificate := ⟨⟨retention1367,(2309520674254567439/1000000000000000000),(90319036891105957/500000000000000000),(7858748083479551897/500000000000000000),(3970296207259030741/20000000000000000),(975801691145429747/1000000000000000000)⟩,(990426110264388983/1000000000000000000),(4546090256270567/10000000000000000),(46753619438575091/250000000000000000),(150942262871990949/1000000000000000000)⟩
theorem valid1367 : certificate1367.Valid := by decide +kernel
theorem sound1367 : certificate1367.Sound := rat_cut_bin_certificate_sound certificate1367 profilesValid1367 numericValid1367 valid1367

def certificates : List RatCutBinCertificate := [certificate1356,certificate1357,certificate1358,certificate1359,certificate1360,certificate1361,certificate1362,certificate1363,certificate1364,certificate1365,certificate1366,certificate1367]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1356,List.forall_mem_cons.mpr ⟨sound1357,List.forall_mem_cons.mpr ⟨sound1358,List.forall_mem_cons.mpr ⟨sound1359,List.forall_mem_cons.mpr ⟨sound1360,List.forall_mem_cons.mpr ⟨sound1361,List.forall_mem_cons.mpr ⟨sound1362,List.forall_mem_cons.mpr ⟨sound1363,List.forall_mem_cons.mpr ⟨sound1364,List.forall_mem_cons.mpr ⟨sound1365,List.forall_mem_cons.mpr ⟨sound1366,List.forall_mem_cons.mpr ⟨sound1367,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch113
