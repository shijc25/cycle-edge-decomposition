import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch350
import Cycle12.MergedCutProfiles.Batch351
import Cycle12.MergedCutProfiles.Batch352
import Cycle12.MergedCutProfiles.Batch353
import Cycle12.MergedCutProfiles.Batch472
import Cycle12.MergedCutProfiles.Batch473
import Cycle12.MergedCutProfiles.Batch474
import Cycle12.MergedCutProfiles.Batch475

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch256

def retention3072 : RatCutRetentionCertificate := ⟨(39/1000),(1/25),(175621307254067160/39386888540114143997),(695529929719077861/1000000000000000000),(39/10),(185874575291513865903/80000000000000000000),true,MergedCutProfiles.Batch472.profile18911,![MergedCutProfiles.Batch472.profile18911,MergedCutProfiles.Batch472.profile18912,MergedCutProfiles.Batch472.profile18913,MergedCutProfiles.Batch472.profile18914,MergedCutProfiles.Batch472.profile18915,MergedCutProfiles.Batch472.profile18916,MergedCutProfiles.Batch472.profile18917,MergedCutProfiles.Batch472.profile18918,MergedCutProfiles.Batch472.profile18919,MergedCutProfiles.Batch473.profile18920,MergedCutProfiles.Batch473.profile18921,MergedCutProfiles.Batch473.profile18922,MergedCutProfiles.Batch473.profile18923,MergedCutProfiles.Batch473.profile18924,MergedCutProfiles.Batch351.profile14072,MergedCutProfiles.Batch473.profile18925]⟩
theorem profilesValid3072 : retention3072.ProfilesValid := by
  change ∀ j : Fin 16, (retention3072.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch472.valid18911
  · exact MergedCutProfiles.Batch472.valid18912
  · exact MergedCutProfiles.Batch472.valid18913
  · exact MergedCutProfiles.Batch472.valid18914
  · exact MergedCutProfiles.Batch472.valid18915
  · exact MergedCutProfiles.Batch472.valid18916
  · exact MergedCutProfiles.Batch472.valid18917
  · exact MergedCutProfiles.Batch472.valid18918
  · exact MergedCutProfiles.Batch472.valid18919
  · exact MergedCutProfiles.Batch473.valid18920
  · exact MergedCutProfiles.Batch473.valid18921
  · exact MergedCutProfiles.Batch473.valid18922
  · exact MergedCutProfiles.Batch473.valid18923
  · exact MergedCutProfiles.Batch473.valid18924
  · exact MergedCutProfiles.Batch351.valid14072
  · exact MergedCutProfiles.Batch473.valid18925
theorem numericValid3072 : retention3072.NumericValid := by decide +kernel
def certificate3072 : RatCutBinCertificate := ⟨⟨retention3072,(99281800395224577/50000000000000000),(1140020255178431/15625000000000000),(11180552108126812303/1000000000000000000),(354187289948331892891/200000000000000000),(2272896276004160107/1000000000000000000)⟩,(499478049051391297/500000000000000000),(244905964390624559/500000000000000000),(10037042436942141/62500000000000000),(9618220516805403/125000000000000000)⟩
theorem valid3072 : certificate3072.Valid := by decide +kernel
theorem sound3072 : certificate3072.Sound := rat_cut_bin_certificate_sound certificate3072 profilesValid3072 numericValid3072 valid3072

def retention3073 : RatCutRetentionCertificate := ⟨(39/1000),(1/25),(975534272616118547/157547554160456575988),(4390532681351679/6250000000000000),(77/20),(7378492051950032613/3200000000000000000),true,MergedCutProfiles.Batch473.profile18926,![MergedCutProfiles.Batch473.profile18926,MergedCutProfiles.Batch350.profile14026,MergedCutProfiles.Batch352.profile14083,MergedCutProfiles.Batch473.profile18927,MergedCutProfiles.Batch472.profile18917,MergedCutProfiles.Batch352.profile14084,MergedCutProfiles.Batch473.profile18928,MergedCutProfiles.Batch473.profile18921,MergedCutProfiles.Batch473.profile18929,MergedCutProfiles.Batch473.profile18924,MergedCutProfiles.Batch473.profile18930,MergedCutProfiles.Batch352.profile14086,MergedCutProfiles.Batch473.profile18931,MergedCutProfiles.Batch473.profile18932,MergedCutProfiles.Batch352.profile14087,MergedCutProfiles.Batch351.profile14062]⟩
theorem profilesValid3073 : retention3073.ProfilesValid := by
  change ∀ j : Fin 16, (retention3073.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch473.valid18926
  · exact MergedCutProfiles.Batch350.valid14026
  · exact MergedCutProfiles.Batch352.valid14083
  · exact MergedCutProfiles.Batch473.valid18927
  · exact MergedCutProfiles.Batch472.valid18917
  · exact MergedCutProfiles.Batch352.valid14084
  · exact MergedCutProfiles.Batch473.valid18928
  · exact MergedCutProfiles.Batch473.valid18921
  · exact MergedCutProfiles.Batch473.valid18929
  · exact MergedCutProfiles.Batch473.valid18924
  · exact MergedCutProfiles.Batch473.valid18930
  · exact MergedCutProfiles.Batch352.valid14086
  · exact MergedCutProfiles.Batch473.valid18931
  · exact MergedCutProfiles.Batch473.valid18932
  · exact MergedCutProfiles.Batch352.valid14087
  · exact MergedCutProfiles.Batch351.valid14062
theorem numericValid3073 : retention3073.NumericValid := by decide +kernel
def certificate3073 : RatCutBinCertificate := ⟨⟨retention3073,(99281800395224577/50000000000000000),(1140020255178431/15625000000000000),(11180552108126812303/1000000000000000000),(354187289948331892891/200000000000000000),(451178149040341729/200000000000000000)⟩,(499478049051391297/500000000000000000),(24532741574620351/50000000000000000),(79995898905765357/500000000000000000),(1923958231168279/25000000000000000)⟩
theorem valid3073 : certificate3073.Valid := by decide +kernel
theorem sound3073 : certificate3073.Sound := rat_cut_bin_certificate_sound certificate3073 profilesValid3073 numericValid3073 valid3073

def retention3074 : RatCutRetentionCertificate := ⟨(39/1000),(1/25),(284262339750000000/39386888540114143997),(975534272616118547/1000000000000000000),(29/10),(2917759467652250734367/1280000000000000000000),true,MergedCutProfiles.Batch473.profile18933,![MergedCutProfiles.Batch473.profile18933,MergedCutProfiles.Batch473.profile18934,MergedCutProfiles.Batch473.profile18935,MergedCutProfiles.Batch473.profile18936,MergedCutProfiles.Batch350.profile14028,MergedCutProfiles.Batch473.profile18928,MergedCutProfiles.Batch473.profile18937,MergedCutProfiles.Batch473.profile18923,MergedCutProfiles.Batch473.profile18938,MergedCutProfiles.Batch473.profile18939,MergedCutProfiles.Batch473.profile18940,MergedCutProfiles.Batch473.profile18932,MergedCutProfiles.Batch352.profile14087,MergedCutProfiles.Batch351.profile14074,MergedCutProfiles.Batch473.profile18941,MergedCutProfiles.Batch473.profile18942]⟩
theorem profilesValid3074 : retention3074.ProfilesValid := by
  change ∀ j : Fin 16, (retention3074.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch473.valid18933
  · exact MergedCutProfiles.Batch473.valid18934
  · exact MergedCutProfiles.Batch473.valid18935
  · exact MergedCutProfiles.Batch473.valid18936
  · exact MergedCutProfiles.Batch350.valid14028
  · exact MergedCutProfiles.Batch473.valid18928
  · exact MergedCutProfiles.Batch473.valid18937
  · exact MergedCutProfiles.Batch473.valid18923
  · exact MergedCutProfiles.Batch473.valid18938
  · exact MergedCutProfiles.Batch473.valid18939
  · exact MergedCutProfiles.Batch473.valid18940
  · exact MergedCutProfiles.Batch473.valid18932
  · exact MergedCutProfiles.Batch352.valid14087
  · exact MergedCutProfiles.Batch351.valid14074
  · exact MergedCutProfiles.Batch473.valid18941
  · exact MergedCutProfiles.Batch473.valid18942
theorem numericValid3074 : retention3074.NumericValid := by decide +kernel
def certificate3074 : RatCutBinCertificate := ⟨⟨retention3074,(99281800395224577/50000000000000000),(1140020255178431/15625000000000000),(11180552108126812303/1000000000000000000),(354187289948331892891/200000000000000000),(1120960809710937223/500000000000000000)⟩,(499478049051391297/500000000000000000),(206730135034085921/500000000000000000),(55343317797380249/250000000000000000),(67123185062288847/500000000000000000)⟩
theorem valid3074 : certificate3074.Valid := by decide +kernel
theorem sound3074 : certificate3074.Sound := rat_cut_bin_certificate_sound certificate3074 profilesValid3074 numericValid3074 valid3074

def retention3075 : RatCutRetentionCertificate := ⟨(39/1000),(1/25),(370407898779462677/39386888540114143997),(1137049359/1000000000),(13/5),(7242661493705203709/3200000000000000000),true,MergedCutProfiles.Batch473.profile18943,![MergedCutProfiles.Batch473.profile18943,MergedCutProfiles.Batch473.profile18944,MergedCutProfiles.Batch473.profile18945,MergedCutProfiles.Batch473.profile18946,MergedCutProfiles.Batch473.profile18947,MergedCutProfiles.Batch352.profile14085,MergedCutProfiles.Batch351.profile14060,MergedCutProfiles.Batch473.profile18948,MergedCutProfiles.Batch351.profile14073,MergedCutProfiles.Batch473.profile18949,MergedCutProfiles.Batch351.profile14047,MergedCutProfiles.Batch352.profile14088,MergedCutProfiles.Batch473.profile18950,MergedCutProfiles.Batch352.profile14089,MergedCutProfiles.Batch473.profile18951,MergedCutProfiles.Batch351.profile14075]⟩
theorem profilesValid3075 : retention3075.ProfilesValid := by
  change ∀ j : Fin 16, (retention3075.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch473.valid18943
  · exact MergedCutProfiles.Batch473.valid18944
  · exact MergedCutProfiles.Batch473.valid18945
  · exact MergedCutProfiles.Batch473.valid18946
  · exact MergedCutProfiles.Batch473.valid18947
  · exact MergedCutProfiles.Batch352.valid14085
  · exact MergedCutProfiles.Batch351.valid14060
  · exact MergedCutProfiles.Batch473.valid18948
  · exact MergedCutProfiles.Batch351.valid14073
  · exact MergedCutProfiles.Batch473.valid18949
  · exact MergedCutProfiles.Batch351.valid14047
  · exact MergedCutProfiles.Batch352.valid14088
  · exact MergedCutProfiles.Batch473.valid18950
  · exact MergedCutProfiles.Batch352.valid14089
  · exact MergedCutProfiles.Batch473.valid18951
  · exact MergedCutProfiles.Batch351.valid14075
theorem numericValid3075 : retention3075.NumericValid := by decide +kernel
def certificate3075 : RatCutBinCertificate := ⟨⟨retention3075,(99281800395224577/50000000000000000),(1140020255178431/15625000000000000),(11180552108126812303/1000000000000000000),(354187289948331892891/200000000000000000),(2229641148881112077/1000000000000000000)⟩,(499478049051391297/500000000000000000),(96561958654668729/250000000000000000),(123160908795399407/500000000000000000),(163541205636556509/1000000000000000000)⟩
theorem valid3075 : certificate3075.Valid := by decide +kernel
theorem sound3075 : certificate3075.Sound := rat_cut_bin_certificate_sound certificate3075 profilesValid3075 numericValid3075 valid3075

def retention3076 : RatCutRetentionCertificate := ⟨(39/1000),(1/25),(12965811850686170413/157547554160456575988),(370407898779462677/250000000000000000),(43/20),(625940684883429271469/320000000000000000000),true,MergedCutProfiles.Batch473.profile18952,![MergedCutProfiles.Batch473.profile18952,MergedCutProfiles.Batch473.profile18953,MergedCutProfiles.Batch473.profile18954,MergedCutProfiles.Batch473.profile18955,MergedCutProfiles.Batch352.profile14101,MergedCutProfiles.Batch473.profile18956,MergedCutProfiles.Batch473.profile18957,MergedCutProfiles.Batch473.profile18958,MergedCutProfiles.Batch473.profile18959,MergedCutProfiles.Batch352.profile14109,MergedCutProfiles.Batch474.profile18960,MergedCutProfiles.Batch474.profile18961,MergedCutProfiles.Batch474.profile18962,MergedCutProfiles.Batch474.profile18963,MergedCutProfiles.Batch474.profile18964,MergedCutProfiles.Batch474.profile18965]⟩
theorem profilesValid3076 : retention3076.ProfilesValid := by
  change ∀ j : Fin 16, (retention3076.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch473.valid18952
  · exact MergedCutProfiles.Batch473.valid18953
  · exact MergedCutProfiles.Batch473.valid18954
  · exact MergedCutProfiles.Batch473.valid18955
  · exact MergedCutProfiles.Batch352.valid14101
  · exact MergedCutProfiles.Batch473.valid18956
  · exact MergedCutProfiles.Batch473.valid18957
  · exact MergedCutProfiles.Batch473.valid18958
  · exact MergedCutProfiles.Batch473.valid18959
  · exact MergedCutProfiles.Batch352.valid14109
  · exact MergedCutProfiles.Batch474.valid18960
  · exact MergedCutProfiles.Batch474.valid18961
  · exact MergedCutProfiles.Batch474.valid18962
  · exact MergedCutProfiles.Batch474.valid18963
  · exact MergedCutProfiles.Batch474.valid18964
  · exact MergedCutProfiles.Batch474.valid18965
theorem numericValid3076 : retention3076.NumericValid := by decide +kernel
def certificate3076 : RatCutBinCertificate := ⟨⟨retention3076,(99281800395224577/50000000000000000),(1140020255178431/15625000000000000),(11180552108126812303/1000000000000000000),(354187289948331892891/200000000000000000),(1928205160120072767/1000000000000000000)⟩,(499478049051391297/500000000000000000),(79746007660208639/200000000000000000),(117323991342764791/500000000000000000),(164014487551756151/1000000000000000000)⟩
theorem valid3076 : certificate3076.Valid := by decide +kernel
theorem sound3076 : certificate3076.Sound := rat_cut_bin_certificate_sound certificate3076 profilesValid3076 numericValid3076 valid3076

def retention3077 : RatCutRetentionCertificate := ⟨(39/1000),(1/25),(16000000000000000000/39386888540114143997),(12965811850686170413/1000000000000000000),(21/20),(3514795262976349076615454385455052570193/2963614137299696094400000000000000000000),false,MergedCutProfiles.Batch474.profile18966,(fun _ => MergedCutProfiles.Batch474.profile18966)⟩
theorem profilesValid3077 : retention3077.ProfilesValid := by
  exact MergedCutProfiles.Batch474.valid18966
theorem numericValid3077 : retention3077.NumericValid := by decide +kernel
def certificate3077 : RatCutBinCertificate := ⟨⟨retention3077,(99281800395224577/50000000000000000),(1140020255178431/15625000000000000),(11180552108126812303/1000000000000000000),(354187289948331892891/200000000000000000),(1172377098402285599/1000000000000000000)⟩,(499478049051391297/500000000000000000),(425536304095575087/1000000000000000000),(210882733057338669/1000000000000000000),(43475502433804577/200000000000000000)⟩
theorem valid3077 : certificate3077.Valid := by decide +kernel
theorem sound3077 : certificate3077.Sound := rat_cut_bin_certificate_sound certificate3077 profilesValid3077 numericValid3077 valid3077

def retention3078 : RatCutRetentionCertificate := ⟨(39/1000),(1/25),(1/2),64,1,(255383218571243657304565787478649566351/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch352.profile14113,(fun _ => MergedCutProfiles.Batch352.profile14113)⟩
theorem profilesValid3078 : retention3078.ProfilesValid := by
  exact MergedCutProfiles.Batch352.valid14113
theorem numericValid3078 : retention3078.NumericValid := by decide +kernel
def certificate3078 : RatCutBinCertificate := ⟨⟨retention3078,(99281800395224577/50000000000000000),(1140020255178431/15625000000000000),(11180552108126812303/1000000000000000000),(354187289948331892891/200000000000000000),(61539559940593341/62500000000000000)⟩,(499478049051391297/500000000000000000),(478470429366026551/1000000000000000000),(168819785753518339/1000000000000000000),(163534492231077627/1000000000000000000)⟩
theorem valid3078 : certificate3078.Valid := by decide +kernel
theorem sound3078 : certificate3078.Sound := rat_cut_bin_certificate_sound certificate3078 profilesValid3078 numericValid3078 valid3078

def retention3079 : RatCutRetentionCertificate := ⟨(39/1000),(1/25),(16000000000000000000/39386888540114143997),(4974961364710269939/500000000000000000),1,(319501687569817279730268014714535869/276386742483903885500000000000000000),false,MergedCutProfiles.Batch474.profile18966,(fun _ => MergedCutProfiles.Batch474.profile18966)⟩
theorem profilesValid3079 : retention3079.ProfilesValid := by
  exact MergedCutProfiles.Batch474.valid18966
theorem numericValid3079 : retention3079.NumericValid := by decide +kernel
def certificate3079 : RatCutBinCertificate := ⟨⟨retention3079,(106306485445224577/50000000000000000),(1140020255178431/15625000000000000),(11180552108126812303/1000000000000000000),(354187289948331892891/200000000000000000),(1142120370639872327/1000000000000000000)⟩,(199776446137558483/200000000000000000),(111818164821444599/1000000000000000000),(160169136027920823/250000000000000000),(327807893513761177/500000000000000000)⟩
theorem valid3079 : certificate3079.Valid := by decide +kernel
theorem sound3079 : certificate3079.Sound := rat_cut_bin_certificate_sound certificate3079 profilesValid3079 numericValid3079 valid3079

def retention3080 : RatCutRetentionCertificate := ⟨(39/1000),(1/25),(1/2),64,1,(255383218571243657304565787478649566351/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch352.profile14113,(fun _ => MergedCutProfiles.Batch352.profile14113)⟩
theorem profilesValid3080 : retention3080.ProfilesValid := by
  exact MergedCutProfiles.Batch352.valid14113
theorem numericValid3080 : retention3080.NumericValid := by decide +kernel
def certificate3080 : RatCutBinCertificate := ⟨⟨retention3080,(106306485445224577/50000000000000000),(1140020255178431/15625000000000000),(11180552108126812303/1000000000000000000),(354187289948331892891/200000000000000000),(983716134097475467/1000000000000000000)⟩,(199776446137558483/200000000000000000),(129823837816086891/1000000000000000000),(15087437906825593/25000000000000000),(73003042357361879/125000000000000000)⟩
theorem valid3080 : certificate3080.Valid := by decide +kernel
theorem sound3080 : certificate3080.Sound := rat_cut_bin_certificate_sound certificate3080 profilesValid3080 numericValid3080 valid3080

def retention3081 : RatCutRetentionCertificate := ⟨(1/25),(41/1000),(355708515188700351/74574689523806123209),(704373297403367031/1000000000000000000),(77/20),(2969684994297058060879/1280000000000000000000),true,MergedCutProfiles.Batch474.profile18967,![MergedCutProfiles.Batch474.profile18967,MergedCutProfiles.Batch474.profile18968,MergedCutProfiles.Batch474.profile18969,MergedCutProfiles.Batch474.profile18970,MergedCutProfiles.Batch474.profile18971,MergedCutProfiles.Batch474.profile18972,MergedCutProfiles.Batch474.profile18973,MergedCutProfiles.Batch352.profile14118,MergedCutProfiles.Batch474.profile18974,MergedCutProfiles.Batch474.profile18975,MergedCutProfiles.Batch353.profile14150,MergedCutProfiles.Batch474.profile18976,MergedCutProfiles.Batch474.profile18977,MergedCutProfiles.Batch474.profile18978,MergedCutProfiles.Batch353.profile14151,MergedCutProfiles.Batch474.profile18979]⟩
theorem profilesValid3081 : retention3081.ProfilesValid := by
  change ∀ j : Fin 16, (retention3081.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch474.valid18967
  · exact MergedCutProfiles.Batch474.valid18968
  · exact MergedCutProfiles.Batch474.valid18969
  · exact MergedCutProfiles.Batch474.valid18970
  · exact MergedCutProfiles.Batch474.valid18971
  · exact MergedCutProfiles.Batch474.valid18972
  · exact MergedCutProfiles.Batch474.valid18973
  · exact MergedCutProfiles.Batch352.valid14118
  · exact MergedCutProfiles.Batch474.valid18974
  · exact MergedCutProfiles.Batch474.valid18975
  · exact MergedCutProfiles.Batch353.valid14150
  · exact MergedCutProfiles.Batch474.valid18976
  · exact MergedCutProfiles.Batch474.valid18977
  · exact MergedCutProfiles.Batch474.valid18978
  · exact MergedCutProfiles.Batch353.valid14151
  · exact MergedCutProfiles.Batch474.valid18979
theorem numericValid3081 : retention3081.NumericValid := by decide +kernel
def certificate3081 : RatCutBinCertificate := ⟨⟨retention3081,(997483386825986613/500000000000000000),(77009395027439323/1000000000000000000),(2270527801094209419/200000000000000000),(1702396676814811822403/1000000000000000000),(1133982433061028707/500000000000000000)⟩,(998913549265470927/1000000000000000000),(3012338606514153/6250000000000000),(166249769722139097/1000000000000000000),(20088614974172783/250000000000000000)⟩
theorem valid3081 : certificate3081.Valid := by decide +kernel
theorem sound3081 : certificate3081.Sound := rat_cut_bin_certificate_sound certificate3081 profilesValid3081 numericValid3081 valid3081

def retention3082 : RatCutRetentionCertificate := ⟨(1/25),(41/1000),(484235749735485855/74574689523806123209),(355708515188700351/500000000000000000),(77/20),(1478008428434352696559/640000000000000000000),true,MergedCutProfiles.Batch474.profile18980,![MergedCutProfiles.Batch474.profile18980,MergedCutProfiles.Batch352.profile14116,MergedCutProfiles.Batch474.profile18981,MergedCutProfiles.Batch352.profile14117,MergedCutProfiles.Batch474.profile18982,MergedCutProfiles.Batch474.profile18983,MergedCutProfiles.Batch474.profile18984,MergedCutProfiles.Batch352.profile14119,MergedCutProfiles.Batch474.profile18985,MergedCutProfiles.Batch353.profile14120,MergedCutProfiles.Batch353.profile14151,MergedCutProfiles.Batch353.profile14121,MergedCutProfiles.Batch474.profile18986,MergedCutProfiles.Batch353.profile14122,MergedCutProfiles.Batch474.profile18987,MergedCutProfiles.Batch474.profile18988]⟩
theorem profilesValid3082 : retention3082.ProfilesValid := by
  change ∀ j : Fin 16, (retention3082.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch474.valid18980
  · exact MergedCutProfiles.Batch352.valid14116
  · exact MergedCutProfiles.Batch474.valid18981
  · exact MergedCutProfiles.Batch352.valid14117
  · exact MergedCutProfiles.Batch474.valid18982
  · exact MergedCutProfiles.Batch474.valid18983
  · exact MergedCutProfiles.Batch474.valid18984
  · exact MergedCutProfiles.Batch352.valid14119
  · exact MergedCutProfiles.Batch474.valid18985
  · exact MergedCutProfiles.Batch353.valid14120
  · exact MergedCutProfiles.Batch353.valid14151
  · exact MergedCutProfiles.Batch353.valid14121
  · exact MergedCutProfiles.Batch474.valid18986
  · exact MergedCutProfiles.Batch353.valid14122
  · exact MergedCutProfiles.Batch474.valid18987
  · exact MergedCutProfiles.Batch474.valid18988
theorem numericValid3082 : retention3082.NumericValid := by decide +kernel
def certificate3082 : RatCutBinCertificate := ⟨⟨retention3082,(997483386825986613/500000000000000000),(77009395027439323/1000000000000000000),(2270527801094209419/200000000000000000),(1702396676814811822403/1000000000000000000),(2257286642360966029/1000000000000000000)⟩,(998913549265470927/1000000000000000000),(96297249318784583/200000000000000000),(166606138398107331/1000000000000000000),(16071302026317259/200000000000000000)⟩
theorem valid3082 : certificate3082.Valid := by decide +kernel
theorem sound3082 : certificate3082.Sound := rat_cut_bin_certificate_sound certificate3082 profilesValid3082 numericValid3082 valid3082

def retention3083 : RatCutRetentionCertificate := ⟨(1/25),(41/1000),(562472970000000000/74574689523806123209),(96847149947097171/100000000000000000),(59/20),(292393094867746734707/128000000000000000000),true,MergedCutProfiles.Batch474.profile18989,![MergedCutProfiles.Batch474.profile18989,MergedCutProfiles.Batch474.profile18990,MergedCutProfiles.Batch474.profile18991,MergedCutProfiles.Batch474.profile18992,MergedCutProfiles.Batch474.profile18993,MergedCutProfiles.Batch474.profile18994,MergedCutProfiles.Batch353.profile14150,MergedCutProfiles.Batch474.profile18995,MergedCutProfiles.Batch474.profile18996,MergedCutProfiles.Batch474.profile18997,MergedCutProfiles.Batch474.profile18998,MergedCutProfiles.Batch353.profile14122,MergedCutProfiles.Batch474.profile18999,MergedCutProfiles.Batch353.profile14153,MergedCutProfiles.Batch475.profile19000,MergedCutProfiles.Batch475.profile19001]⟩
theorem profilesValid3083 : retention3083.ProfilesValid := by
  change ∀ j : Fin 16, (retention3083.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch474.valid18989
  · exact MergedCutProfiles.Batch474.valid18990
  · exact MergedCutProfiles.Batch474.valid18991
  · exact MergedCutProfiles.Batch474.valid18992
  · exact MergedCutProfiles.Batch474.valid18993
  · exact MergedCutProfiles.Batch474.valid18994
  · exact MergedCutProfiles.Batch353.valid14150
  · exact MergedCutProfiles.Batch474.valid18995
  · exact MergedCutProfiles.Batch474.valid18996
  · exact MergedCutProfiles.Batch474.valid18997
  · exact MergedCutProfiles.Batch474.valid18998
  · exact MergedCutProfiles.Batch353.valid14122
  · exact MergedCutProfiles.Batch474.valid18999
  · exact MergedCutProfiles.Batch353.valid14153
  · exact MergedCutProfiles.Batch475.valid19000
  · exact MergedCutProfiles.Batch475.valid19001
theorem numericValid3083 : retention3083.NumericValid := by decide +kernel
def certificate3083 : RatCutBinCertificate := ⟨⟨retention3083,(997483386825986613/500000000000000000),(77009395027439323/1000000000000000000),(2270527801094209419/200000000000000000),(1702396676814811822403/1000000000000000000),(448879826316513319/200000000000000000)⟩,(998913549265470927/1000000000000000000),(410361750958112929/1000000000000000000),(224121414423312441/1000000000000000000),(1344860144196537/10000000000000000)⟩
theorem valid3083 : certificate3083.Valid := by decide +kernel
theorem sound3083 : certificate3083.Sound := rat_cut_bin_certificate_sound certificate3083 profilesValid3083 numericValid3083 valid3083

def certificates : List RatCutBinCertificate := [certificate3072,certificate3073,certificate3074,certificate3075,certificate3076,certificate3077,certificate3078,certificate3079,certificate3080,certificate3081,certificate3082,certificate3083]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3072,List.forall_mem_cons.mpr ⟨sound3073,List.forall_mem_cons.mpr ⟨sound3074,List.forall_mem_cons.mpr ⟨sound3075,List.forall_mem_cons.mpr ⟨sound3076,List.forall_mem_cons.mpr ⟨sound3077,List.forall_mem_cons.mpr ⟨sound3078,List.forall_mem_cons.mpr ⟨sound3079,List.forall_mem_cons.mpr ⟨sound3080,List.forall_mem_cons.mpr ⟨sound3081,List.forall_mem_cons.mpr ⟨sound3082,List.forall_mem_cons.mpr ⟨sound3083,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch256
