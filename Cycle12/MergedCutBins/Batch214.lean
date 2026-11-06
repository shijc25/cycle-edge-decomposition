import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch226
import Cycle12.MergedCutProfiles.Batch400
import Cycle12.MergedCutProfiles.Batch401
import Cycle12.MergedCutProfiles.Batch402
import Cycle12.MergedCutProfiles.Batch403

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch214

def retention2568 : RatCutRetentionCertificate := ⟨(119/2000),(3/50),(1868077621870769084/24973922070982979467),(535017503429840451/500000000000000000),(12/5),(317009610094824656851/160000000000000000000),true,MergedCutProfiles.Batch401.profile16041,![MergedCutProfiles.Batch401.profile16041,MergedCutProfiles.Batch401.profile16042,MergedCutProfiles.Batch401.profile16043,MergedCutProfiles.Batch400.profile16032,MergedCutProfiles.Batch401.profile16044,MergedCutProfiles.Batch401.profile16045,MergedCutProfiles.Batch401.profile16046,MergedCutProfiles.Batch400.profile16038,MergedCutProfiles.Batch401.profile16047,MergedCutProfiles.Batch401.profile16048,MergedCutProfiles.Batch401.profile16049,MergedCutProfiles.Batch401.profile16050,MergedCutProfiles.Batch401.profile16051,MergedCutProfiles.Batch401.profile16052,MergedCutProfiles.Batch401.profile16053,MergedCutProfiles.Batch401.profile16054]⟩
theorem profilesValid2568 : retention2568.ProfilesValid := by
  change ∀ j : Fin 16, (retention2568.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch401.valid16041
  · exact MergedCutProfiles.Batch401.valid16042
  · exact MergedCutProfiles.Batch401.valid16043
  · exact MergedCutProfiles.Batch400.valid16032
  · exact MergedCutProfiles.Batch401.valid16044
  · exact MergedCutProfiles.Batch401.valid16045
  · exact MergedCutProfiles.Batch401.valid16046
  · exact MergedCutProfiles.Batch400.valid16038
  · exact MergedCutProfiles.Batch401.valid16047
  · exact MergedCutProfiles.Batch401.valid16048
  · exact MergedCutProfiles.Batch401.valid16049
  · exact MergedCutProfiles.Batch401.valid16050
  · exact MergedCutProfiles.Batch401.valid16051
  · exact MergedCutProfiles.Batch401.valid16052
  · exact MergedCutProfiles.Batch401.valid16053
  · exact MergedCutProfiles.Batch401.valid16054
theorem numericValid2568 : retention2568.NumericValid := by decide +kernel
def certificate2568 : RatCutBinCertificate := ⟨⟨retention2568,(2277826033255611433/1000000000000000000),(182428996879551849/1000000000000000000),(15722171334757975717/1000000000000000000),(393845047766373384873/1000000000000000000),(479466482593380117/250000000000000000)⟩,(124405732897495927/125000000000000000),(15269678460301971/50000000000000000),(166171367987875453/500000000000000000),(201407639728689659/1000000000000000000)⟩
theorem valid2568 : certificate2568.Valid := by decide +kernel
theorem sound2568 : certificate2568.Sound := rat_cut_bin_certificate_sound certificate2568 profilesValid2568 numericValid2568 valid2568

def retention2569 : RatCutRetentionCertificate := ⟨(119/2000),(3/50),(6544673939786898721/24973922070982979467),(467019405467692271/250000000000000000),(8/5),(476045421243177313363/320000000000000000000),true,MergedCutProfiles.Batch401.profile16055,![MergedCutProfiles.Batch401.profile16055,MergedCutProfiles.Batch401.profile16046,MergedCutProfiles.Batch401.profile16056,MergedCutProfiles.Batch401.profile16057,MergedCutProfiles.Batch401.profile16058,MergedCutProfiles.Batch401.profile16059,MergedCutProfiles.Batch401.profile16060,MergedCutProfiles.Batch401.profile16061,MergedCutProfiles.Batch401.profile16062,MergedCutProfiles.Batch401.profile16063,MergedCutProfiles.Batch401.profile16064,MergedCutProfiles.Batch401.profile16065,MergedCutProfiles.Batch401.profile16066,MergedCutProfiles.Batch401.profile16067,MergedCutProfiles.Batch401.profile16068,MergedCutProfiles.Batch401.profile16069]⟩
theorem profilesValid2569 : retention2569.ProfilesValid := by
  change ∀ j : Fin 16, (retention2569.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch401.valid16055
  · exact MergedCutProfiles.Batch401.valid16046
  · exact MergedCutProfiles.Batch401.valid16056
  · exact MergedCutProfiles.Batch401.valid16057
  · exact MergedCutProfiles.Batch401.valid16058
  · exact MergedCutProfiles.Batch401.valid16059
  · exact MergedCutProfiles.Batch401.valid16060
  · exact MergedCutProfiles.Batch401.valid16061
  · exact MergedCutProfiles.Batch401.valid16062
  · exact MergedCutProfiles.Batch401.valid16063
  · exact MergedCutProfiles.Batch401.valid16064
  · exact MergedCutProfiles.Batch401.valid16065
  · exact MergedCutProfiles.Batch401.valid16066
  · exact MergedCutProfiles.Batch401.valid16067
  · exact MergedCutProfiles.Batch401.valid16068
  · exact MergedCutProfiles.Batch401.valid16069
theorem numericValid2569 : retention2569.NumericValid := by decide +kernel
def certificate2569 : RatCutBinCertificate := ⟨⟨retention2569,(2277826033255611433/1000000000000000000),(182428996879551849/1000000000000000000),(15722171334757975717/1000000000000000000),(393845047766373384873/1000000000000000000),(1445346926853940477/1000000000000000000)⟩,(124405732897495927/125000000000000000),(34121856472499013/100000000000000000),(291884852582875241/1000000000000000000),(25169827843067653/125000000000000000)⟩
theorem valid2569 : certificate2569.Valid := by decide +kernel
theorem sound2569 : certificate2569.Sound := rat_cut_bin_certificate_sound certificate2569 profilesValid2569 numericValid2569 valid2569

def retention2570 : RatCutRetentionCertificate := ⟨(119/2000),(3/50),(11540013587863446343/24973922070982979467),(6544673939786898721/1000000000000000000),1,(264992572794272251201/256000000000000000000),true,MergedCutProfiles.Batch401.profile16070,![MergedCutProfiles.Batch401.profile16070,MergedCutProfiles.Batch401.profile16071,MergedCutProfiles.Batch401.profile16072,MergedCutProfiles.Batch401.profile16073,MergedCutProfiles.Batch401.profile16074,MergedCutProfiles.Batch401.profile16075,MergedCutProfiles.Batch401.profile16076,MergedCutProfiles.Batch401.profile16077,MergedCutProfiles.Batch401.profile16078,MergedCutProfiles.Batch401.profile16079,MergedCutProfiles.Batch402.profile16080,MergedCutProfiles.Batch402.profile16081,MergedCutProfiles.Batch402.profile16082,MergedCutProfiles.Batch402.profile16083,MergedCutProfiles.Batch402.profile16084,MergedCutProfiles.Batch402.profile16085]⟩
theorem profilesValid2570 : retention2570.ProfilesValid := by
  change ∀ j : Fin 16, (retention2570.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch401.valid16070
  · exact MergedCutProfiles.Batch401.valid16071
  · exact MergedCutProfiles.Batch401.valid16072
  · exact MergedCutProfiles.Batch401.valid16073
  · exact MergedCutProfiles.Batch401.valid16074
  · exact MergedCutProfiles.Batch401.valid16075
  · exact MergedCutProfiles.Batch401.valid16076
  · exact MergedCutProfiles.Batch401.valid16077
  · exact MergedCutProfiles.Batch401.valid16078
  · exact MergedCutProfiles.Batch401.valid16079
  · exact MergedCutProfiles.Batch402.valid16080
  · exact MergedCutProfiles.Batch402.valid16081
  · exact MergedCutProfiles.Batch402.valid16082
  · exact MergedCutProfiles.Batch402.valid16083
  · exact MergedCutProfiles.Batch402.valid16084
  · exact MergedCutProfiles.Batch402.valid16085
theorem numericValid2570 : retention2570.NumericValid := by decide +kernel
def certificate2570 : RatCutBinCertificate := ⟨⟨retention2570,(2277826033255611433/1000000000000000000),(182428996879551849/1000000000000000000),(15722171334757975717/1000000000000000000),(393845047766373384873/1000000000000000000),(1008695078747423627/1000000000000000000)⟩,(124405732897495927/125000000000000000),(50130445991546787/125000000000000000),(232527553426970527/1000000000000000000),(202180252001830319/1000000000000000000)⟩
theorem valid2570 : certificate2570.Valid := by decide +kernel
theorem sound2570 : certificate2570.Sound := rat_cut_bin_certificate_sound certificate2570 profilesValid2570 numericValid2570 valid2570

def retention2571 : RatCutRetentionCertificate := ⟨(119/2000),(3/50),(12372456531343655831/24973922070982979467),(11540013587863446343/1000000000000000000),(21/20),(18588064183857989847272534748427061419191/18464021740581514148800000000000000000000),false,MergedCutProfiles.Batch402.profile16086,(fun _ => MergedCutProfiles.Batch402.profile16086)⟩
theorem profilesValid2571 : retention2571.ProfilesValid := by
  exact MergedCutProfiles.Batch402.valid16086
theorem numericValid2571 : retention2571.NumericValid := by decide +kernel
def certificate2571 : RatCutBinCertificate := ⟨⟨retention2571,(2277826033255611433/1000000000000000000),(182428996879551849/1000000000000000000),(15722171334757975717/1000000000000000000),(393845047766373384873/1000000000000000000),(97896519861973899/100000000000000000)⟩,(124405732897495927/125000000000000000),(397565029359927581/1000000000000000000),(235720827834436417/1000000000000000000),(20305436058730317/100000000000000000)⟩
theorem valid2571 : certificate2571.Valid := by decide +kernel
theorem sound2571 : certificate2571.Sound := rat_cut_bin_certificate_sound certificate2571 profilesValid2571 numericValid2571 valid2571

def retention2572 : RatCutRetentionCertificate := ⟨(119/2000),(3/50),(1/2),(12372456531343655831/1000000000000000000),1,(1517687592096656416112560013007074067/1546557066417956978875000000000000000),false,MergedCutProfiles.Batch402.profile16087,(fun _ => MergedCutProfiles.Batch402.profile16087)⟩
theorem profilesValid2572 : retention2572.ProfilesValid := by
  exact MergedCutProfiles.Batch402.valid16087
theorem numericValid2572 : retention2572.NumericValid := by decide +kernel
def certificate2572 : RatCutBinCertificate := ⟨⟨retention2572,(2277826033255611433/1000000000000000000),(182428996879551849/1000000000000000000),(15722171334757975717/1000000000000000000),(393845047766373384873/1000000000000000000),(954901791201306407/1000000000000000000)⟩,(124405732897495927/125000000000000000),(50771076709203551/125000000000000000),(56969417920382981/250000000000000000),(25125488810476647/125000000000000000)⟩
theorem valid2572 : certificate2572.Valid := by decide +kernel
theorem sound2572 : certificate2572.Sound := rat_cut_bin_certificate_sound certificate2572 profilesValid2572 numericValid2572 valid2572

def retention2573 : RatCutRetentionCertificate := ⟨(119/2000),(3/50),(11273240853316192154/24973922070982979467),(1284104197680929531/250000000000000000),(21/20),(547084425208751113401495831001393349519/513641679072371812400000000000000000000),false,MergedCutProfiles.Batch402.profile16088,(fun _ => MergedCutProfiles.Batch402.profile16088)⟩
theorem profilesValid2573 : retention2573.ProfilesValid := by
  exact MergedCutProfiles.Batch402.valid16088
theorem numericValid2573 : retention2573.NumericValid := by decide +kernel
def certificate2573 : RatCutBinCertificate := ⟨⟨retention2573,(2522483005255611433/1000000000000000000),(182428996879551849/1000000000000000000),(15722171334757975717/1000000000000000000),(393845047766373384873/1000000000000000000),(517186943495858269/500000000000000000)⟩,(994734644797324579/1000000000000000000),(112330853335052233/500000000000000000),(439721525385387319/1000000000000000000),(72834770131784839/200000000000000000)⟩
theorem valid2573 : certificate2573.Valid := by decide +kernel
theorem sound2573 : certificate2573.Sound := rat_cut_bin_certificate_sound certificate2573 profilesValid2573 numericValid2573 valid2573

def retention2574 : RatCutRetentionCertificate := ⟨(119/2000),(3/50),(12329377496695596990/24973922070982979467),(5636620426658096077/500000000000000000),1,(349273994244837568225641298004098713/352288776666131004812500000000000000),false,MergedCutProfiles.Batch402.profile16089,(fun _ => MergedCutProfiles.Batch402.profile16089)⟩
theorem profilesValid2574 : retention2574.ProfilesValid := by
  exact MergedCutProfiles.Batch402.valid16089
theorem numericValid2574 : retention2574.NumericValid := by decide +kernel
def certificate2574 : RatCutBinCertificate := ⟨⟨retention2574,(2522483005255611433/1000000000000000000),(182428996879551849/1000000000000000000),(15722171334757975717/1000000000000000000),(393845047766373384873/1000000000000000000),(962171980008881393/1000000000000000000)⟩,(994734644797324579/1000000000000000000),(48304088585993487/200000000000000000),(415221717042336827/1000000000000000000),(91517289157306157/250000000000000000)⟩
theorem valid2574 : certificate2574.Valid := by decide +kernel
theorem sound2574 : certificate2574.Sound := rat_cut_bin_certificate_sound certificate2574 profilesValid2574 numericValid2574 valid2574

def retention2575 : RatCutRetentionCertificate := ⟨(119/2000),(3/50),(12452671271662552960/24973922070982979467),(1232937749669559699/100000000000000000),1,(48523563478369233700708739172849459839/49317509986782387960000000000000000000),false,MergedCutProfiles.Batch402.profile16090,(fun _ => MergedCutProfiles.Batch402.profile16090)⟩
theorem profilesValid2575 : retention2575.ProfilesValid := by
  exact MergedCutProfiles.Batch402.valid16090
theorem numericValid2575 : retention2575.NumericValid := by decide +kernel
def certificate2575 : RatCutBinCertificate := ⟨⟨retention2575,(2522483005255611433/1000000000000000000),(182428996879551849/1000000000000000000),(15722171334757975717/1000000000000000000),(393845047766373384873/1000000000000000000),(954631111324302881/1000000000000000000)⟩,(994734644797324579/1000000000000000000),(60857068251257819/250000000000000000),(412523559357858459/1000000000000000000),(363500492899078861/1000000000000000000)⟩
theorem valid2575 : certificate2575.Valid := by decide +kernel
theorem sound2575 : certificate2575.Sound := rat_cut_bin_certificate_sound certificate2575 profilesValid2575 numericValid2575 valid2575

def retention2576 : RatCutRetentionCertificate := ⟨(119/2000),(3/50),(1/2),(19457298861972739/1562500000000000),1,(3055461037796696560496126662957241311/3113167817915638240000000000000000000),false,MergedCutProfiles.Batch402.profile16087,(fun _ => MergedCutProfiles.Batch402.profile16087)⟩
theorem profilesValid2576 : retention2576.ProfilesValid := by
  exact MergedCutProfiles.Batch402.valid16087
theorem numericValid2576 : retention2576.NumericValid := by decide +kernel
def certificate2576 : RatCutBinCertificate := ⟨⟨retention2576,(2522483005255611433/1000000000000000000),(182428996879551849/1000000000000000000),(15722171334757975717/1000000000000000000),(393845047766373384873/1000000000000000000),(952193442259995159/1000000000000000000)⟩,(994734644797324579/1000000000000000000),(122025731575610141/500000000000000000),(411645405395937543/1000000000000000000),(362124657942825483/1000000000000000000)⟩
theorem valid2576 : certificate2576.Valid := by decide +kernel
theorem sound2576 : certificate2576.Sound := rat_cut_bin_certificate_sound certificate2576 profilesValid2576 numericValid2576 valid2576

def retention2577 : RatCutRetentionCertificate := ⟨(3/50),(121/2000),(924279873924552851/24487694854243433168),(915128588044111733/1000000000000000000),(27/10),(167803904276409115167/80000000000000000000),true,MergedCutProfiles.Batch402.profile16091,![MergedCutProfiles.Batch402.profile16091,MergedCutProfiles.Batch402.profile16092,MergedCutProfiles.Batch402.profile16093,MergedCutProfiles.Batch402.profile16094,MergedCutProfiles.Batch402.profile16095,MergedCutProfiles.Batch402.profile16096,MergedCutProfiles.Batch402.profile16097,MergedCutProfiles.Batch402.profile16098,MergedCutProfiles.Batch402.profile16099,MergedCutProfiles.Batch402.profile16100,MergedCutProfiles.Batch402.profile16101,MergedCutProfiles.Batch402.profile16102,MergedCutProfiles.Batch402.profile16103,MergedCutProfiles.Batch402.profile16104,MergedCutProfiles.Batch402.profile16105,MergedCutProfiles.Batch402.profile16106]⟩
theorem profilesValid2577 : retention2577.ProfilesValid := by
  change ∀ j : Fin 16, (retention2577.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch402.valid16091
  · exact MergedCutProfiles.Batch402.valid16092
  · exact MergedCutProfiles.Batch402.valid16093
  · exact MergedCutProfiles.Batch402.valid16094
  · exact MergedCutProfiles.Batch402.valid16095
  · exact MergedCutProfiles.Batch402.valid16096
  · exact MergedCutProfiles.Batch402.valid16097
  · exact MergedCutProfiles.Batch402.valid16098
  · exact MergedCutProfiles.Batch402.valid16099
  · exact MergedCutProfiles.Batch402.valid16100
  · exact MergedCutProfiles.Batch402.valid16101
  · exact MergedCutProfiles.Batch402.valid16102
  · exact MergedCutProfiles.Batch402.valid16103
  · exact MergedCutProfiles.Batch402.valid16104
  · exact MergedCutProfiles.Batch402.valid16105
  · exact MergedCutProfiles.Batch402.valid16106
theorem numericValid2577 : retention2577.NumericValid := by decide +kernel
def certificate2577 : RatCutBinCertificate := ⟨⟨retention2577,(284126762733315713/125000000000000000),(93024059904071007/500000000000000000),(15866339644806527893/1000000000000000000),(12178821694455002887/31250000000000000),(2025571042332000919/1000000000000000000)⟩,(995226413818562761/1000000000000000000),(76405329394090893/250000000000000000),(166036398955135017/500000000000000000),(190009085019759757/1000000000000000000)⟩
theorem valid2577 : certificate2577.Valid := by decide +kernel
theorem sound2577 : certificate2577.Sound := rat_cut_bin_certificate_sound certificate2577 profilesValid2577 numericValid2577 valid2577

def retention2578 : RatCutRetentionCertificate := ⟨(3/50),(121/2000),(61567443437500000/1530480928390214573),(924279873924552851/1000000000000000000),(27/10),(167513015249796951009/80000000000000000000),true,MergedCutProfiles.Batch402.profile16107,![MergedCutProfiles.Batch402.profile16107,MergedCutProfiles.Batch402.profile16108,MergedCutProfiles.Batch402.profile16109,MergedCutProfiles.Batch402.profile16110,MergedCutProfiles.Batch402.profile16111,MergedCutProfiles.Batch402.profile16112,MergedCutProfiles.Batch402.profile16113,MergedCutProfiles.Batch402.profile16114,MergedCutProfiles.Batch402.profile16115,MergedCutProfiles.Batch402.profile16116,MergedCutProfiles.Batch226.profile9063,MergedCutProfiles.Batch402.profile16117,MergedCutProfiles.Batch402.profile16118,MergedCutProfiles.Batch402.profile16119,MergedCutProfiles.Batch402.profile16106,MergedCutProfiles.Batch403.profile16120]⟩
theorem profilesValid2578 : retention2578.ProfilesValid := by
  change ∀ j : Fin 16, (retention2578.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch402.valid16107
  · exact MergedCutProfiles.Batch402.valid16108
  · exact MergedCutProfiles.Batch402.valid16109
  · exact MergedCutProfiles.Batch402.valid16110
  · exact MergedCutProfiles.Batch402.valid16111
  · exact MergedCutProfiles.Batch402.valid16112
  · exact MergedCutProfiles.Batch402.valid16113
  · exact MergedCutProfiles.Batch402.valid16114
  · exact MergedCutProfiles.Batch402.valid16115
  · exact MergedCutProfiles.Batch402.valid16116
  · exact MergedCutProfiles.Batch226.valid9063
  · exact MergedCutProfiles.Batch402.valid16117
  · exact MergedCutProfiles.Batch402.valid16118
  · exact MergedCutProfiles.Batch402.valid16119
  · exact MergedCutProfiles.Batch402.valid16106
  · exact MergedCutProfiles.Batch403.valid16120
theorem numericValid2578 : retention2578.NumericValid := by decide +kernel
def certificate2578 : RatCutBinCertificate := ⟨⟨retention2578,(284126762733315713/125000000000000000),(93024059904071007/500000000000000000),(15866339644806527893/1000000000000000000),(12178821694455002887/31250000000000000),(1010967533581170881/500000000000000000)⟩,(995226413818562761/1000000000000000000),(304940131120433689/1000000000000000000),(332880675776269853/1000000000000000000),(190649298951223787/1000000000000000000)⟩
theorem valid2578 : certificate2578.Valid := by decide +kernel
theorem sound2578 : certificate2578.Sound := rat_cut_bin_certificate_sound certificate2578 profilesValid2578 numericValid2578 valid2578

def retention2579 : RatCutRetentionCertificate := ⟨(3/50),(121/2000),(1105575038022842755/24487694854243433168),(197015819/200000000),(51/20),(8286766128186244917/4000000000000000000),true,MergedCutProfiles.Batch403.profile16121,![MergedCutProfiles.Batch403.profile16121,MergedCutProfiles.Batch403.profile16122,MergedCutProfiles.Batch403.profile16123,MergedCutProfiles.Batch403.profile16124,MergedCutProfiles.Batch402.profile16096,MergedCutProfiles.Batch403.profile16125,MergedCutProfiles.Batch403.profile16126,MergedCutProfiles.Batch403.profile16127,MergedCutProfiles.Batch226.profile9050,MergedCutProfiles.Batch402.profile16102,MergedCutProfiles.Batch403.profile16128,MergedCutProfiles.Batch403.profile16129,MergedCutProfiles.Batch226.profile9040,MergedCutProfiles.Batch403.profile16130,MergedCutProfiles.Batch403.profile16131,MergedCutProfiles.Batch403.profile16132]⟩
theorem profilesValid2579 : retention2579.ProfilesValid := by
  change ∀ j : Fin 16, (retention2579.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch403.valid16121
  · exact MergedCutProfiles.Batch403.valid16122
  · exact MergedCutProfiles.Batch403.valid16123
  · exact MergedCutProfiles.Batch403.valid16124
  · exact MergedCutProfiles.Batch402.valid16096
  · exact MergedCutProfiles.Batch403.valid16125
  · exact MergedCutProfiles.Batch403.valid16126
  · exact MergedCutProfiles.Batch403.valid16127
  · exact MergedCutProfiles.Batch226.valid9050
  · exact MergedCutProfiles.Batch402.valid16102
  · exact MergedCutProfiles.Batch403.valid16128
  · exact MergedCutProfiles.Batch403.valid16129
  · exact MergedCutProfiles.Batch226.valid9040
  · exact MergedCutProfiles.Batch403.valid16130
  · exact MergedCutProfiles.Batch403.valid16131
  · exact MergedCutProfiles.Batch403.valid16132
theorem numericValid2579 : retention2579.NumericValid := by decide +kernel
def certificate2579 : RatCutBinCertificate := ⟨⟨retention2579,(284126762733315713/125000000000000000),(93024059904071007/500000000000000000),(15866339644806527893/1000000000000000000),(12178821694455002887/31250000000000000),(1001856375154435491/500000000000000000)⟩,(995226413818562761/1000000000000000000),(300047899288222747/1000000000000000000),(169363756901779457/500000000000000000),(201587103876667431/1000000000000000000)⟩
theorem valid2579 : certificate2579.Valid := by decide +kernel
theorem sound2579 : certificate2579.Sound := rat_cut_bin_certificate_sound certificate2579 profilesValid2579 numericValid2579 valid2579

def certificates : List RatCutBinCertificate := [certificate2568,certificate2569,certificate2570,certificate2571,certificate2572,certificate2573,certificate2574,certificate2575,certificate2576,certificate2577,certificate2578,certificate2579]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2568,List.forall_mem_cons.mpr ⟨sound2569,List.forall_mem_cons.mpr ⟨sound2570,List.forall_mem_cons.mpr ⟨sound2571,List.forall_mem_cons.mpr ⟨sound2572,List.forall_mem_cons.mpr ⟨sound2573,List.forall_mem_cons.mpr ⟨sound2574,List.forall_mem_cons.mpr ⟨sound2575,List.forall_mem_cons.mpr ⟨sound2576,List.forall_mem_cons.mpr ⟨sound2577,List.forall_mem_cons.mpr ⟨sound2578,List.forall_mem_cons.mpr ⟨sound2579,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch214
