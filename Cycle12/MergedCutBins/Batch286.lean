import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch404
import Cycle12.MergedCutProfiles.Batch405
import Cycle12.MergedCutProfiles.Batch406
import Cycle12.MergedCutProfiles.Batch407
import Cycle12.MergedCutProfiles.Batch408
import Cycle12.MergedCutProfiles.Batch526
import Cycle12.MergedCutProfiles.Batch527
import Cycle12.MergedCutProfiles.Batch528
import Cycle12.MergedCutProfiles.Batch529

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch286

def retention3432 : RatCutRetentionCertificate := ⟨(121/2000),(61/1000),(700489711181546287/30017456134998216493),(221212413/200000000),(5/2),(8746780207566319071/4000000000000000000),true,MergedCutProfiles.Batch526.profile21079,![MergedCutProfiles.Batch526.profile21079,MergedCutProfiles.Batch527.profile21080,MergedCutProfiles.Batch527.profile21081,MergedCutProfiles.Batch527.profile21082,MergedCutProfiles.Batch404.profile16184,MergedCutProfiles.Batch527.profile21083,MergedCutProfiles.Batch527.profile21084,MergedCutProfiles.Batch527.profile21085,MergedCutProfiles.Batch527.profile21086,MergedCutProfiles.Batch404.profile16187,MergedCutProfiles.Batch527.profile21087,MergedCutProfiles.Batch527.profile21088,MergedCutProfiles.Batch527.profile21089,MergedCutProfiles.Batch527.profile21090,MergedCutProfiles.Batch404.profile16190,MergedCutProfiles.Batch527.profile21091]⟩
theorem profilesValid3432 : retention3432.ProfilesValid := by
  change ∀ j : Fin 16, (retention3432.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch526.valid21079
  · exact MergedCutProfiles.Batch527.valid21080
  · exact MergedCutProfiles.Batch527.valid21081
  · exact MergedCutProfiles.Batch527.valid21082
  · exact MergedCutProfiles.Batch404.valid16184
  · exact MergedCutProfiles.Batch527.valid21083
  · exact MergedCutProfiles.Batch527.valid21084
  · exact MergedCutProfiles.Batch527.valid21085
  · exact MergedCutProfiles.Batch527.valid21086
  · exact MergedCutProfiles.Batch404.valid16187
  · exact MergedCutProfiles.Batch527.valid21087
  · exact MergedCutProfiles.Batch527.valid21088
  · exact MergedCutProfiles.Batch527.valid21089
  · exact MergedCutProfiles.Batch527.valid21090
  · exact MergedCutProfiles.Batch404.valid16190
  · exact MergedCutProfiles.Batch527.valid21091
theorem numericValid3432 : retention3432.NumericValid := by decide +kernel
def certificate3432 : RatCutBinCertificate := ⟨⟨retention3432,(2217465728453509257/1000000000000000000),(9485872639178457/50000000000000000),(3202793912973537903/200000000000000000),(964357342583473521597/1000000000000000000),(2121014603575188169/1000000000000000000)⟩,(249531892927526829/250000000000000000),(303014881730171101/1000000000000000000),(83793049749598759/250000000000000000),(217116749055371057/1000000000000000000)⟩
theorem valid3432 : certificate3432.Valid := by decide +kernel
theorem sound3432 : certificate3432.Sound := rat_cut_bin_certificate_sound certificate3432 profilesValid3432 numericValid3432 valid3432

def retention3433 : RatCutRetentionCertificate := ⟨(121/2000),(61/1000),(2994486317281699126/30017456134998216493),(700489711181546287/500000000000000000),(21/10),(1224278927771030181291/640000000000000000000),true,MergedCutProfiles.Batch527.profile21092,![MergedCutProfiles.Batch527.profile21092,MergedCutProfiles.Batch527.profile21093,MergedCutProfiles.Batch527.profile21094,MergedCutProfiles.Batch406.profile16259,MergedCutProfiles.Batch405.profile16225,MergedCutProfiles.Batch527.profile21095,MergedCutProfiles.Batch527.profile21096,MergedCutProfiles.Batch406.profile16260,MergedCutProfiles.Batch527.profile21097,MergedCutProfiles.Batch527.profile21098,MergedCutProfiles.Batch527.profile21099,MergedCutProfiles.Batch527.profile21100,MergedCutProfiles.Batch406.profile16251,MergedCutProfiles.Batch527.profile21101,MergedCutProfiles.Batch527.profile21102,MergedCutProfiles.Batch406.profile16262]⟩
theorem profilesValid3433 : retention3433.ProfilesValid := by
  change ∀ j : Fin 16, (retention3433.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch527.valid21092
  · exact MergedCutProfiles.Batch527.valid21093
  · exact MergedCutProfiles.Batch527.valid21094
  · exact MergedCutProfiles.Batch406.valid16259
  · exact MergedCutProfiles.Batch405.valid16225
  · exact MergedCutProfiles.Batch527.valid21095
  · exact MergedCutProfiles.Batch527.valid21096
  · exact MergedCutProfiles.Batch406.valid16260
  · exact MergedCutProfiles.Batch527.valid21097
  · exact MergedCutProfiles.Batch527.valid21098
  · exact MergedCutProfiles.Batch527.valid21099
  · exact MergedCutProfiles.Batch527.valid21100
  · exact MergedCutProfiles.Batch406.valid16251
  · exact MergedCutProfiles.Batch527.valid21101
  · exact MergedCutProfiles.Batch527.valid21102
  · exact MergedCutProfiles.Batch406.valid16262
theorem numericValid3433 : retention3433.NumericValid := by decide +kernel
def certificate3433 : RatCutBinCertificate := ⟨⟨retention3433,(2217465728453509257/1000000000000000000),(9485872639178457/50000000000000000),(3202793912973537903/200000000000000000),(964357342583473521597/1000000000000000000),(928882242029062013/500000000000000000)⟩,(249531892927526829/250000000000000000),(78995678708016517/250000000000000000),(31996883731166887/100000000000000000),(217145472746294607/1000000000000000000)⟩
theorem valid3433 : certificate3433.Valid := by decide +kernel
theorem sound3433 : certificate3433.Sound := rat_cut_bin_certificate_sound certificate3433 profilesValid3433 numericValid3433 valid3433

def retention3434 : RatCutRetentionCertificate := ⟨(121/2000),(61/1000),(12674228466585258841/30017456134998216493),(1497243158640849563/250000000000000000),(21/20),(361208265537630213567/320000000000000000000),true,MergedCutProfiles.Batch527.profile21103,![MergedCutProfiles.Batch527.profile21103,MergedCutProfiles.Batch527.profile21104,MergedCutProfiles.Batch527.profile21105,MergedCutProfiles.Batch527.profile21106,MergedCutProfiles.Batch527.profile21107,MergedCutProfiles.Batch527.profile21108,MergedCutProfiles.Batch527.profile21109,MergedCutProfiles.Batch527.profile21110,MergedCutProfiles.Batch527.profile21111,MergedCutProfiles.Batch527.profile21112,MergedCutProfiles.Batch527.profile21113,MergedCutProfiles.Batch527.profile21114,MergedCutProfiles.Batch527.profile21115,MergedCutProfiles.Batch527.profile21116,MergedCutProfiles.Batch527.profile21117,MergedCutProfiles.Batch527.profile21118]⟩
theorem profilesValid3434 : retention3434.ProfilesValid := by
  change ∀ j : Fin 16, (retention3434.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch527.valid21103
  · exact MergedCutProfiles.Batch527.valid21104
  · exact MergedCutProfiles.Batch527.valid21105
  · exact MergedCutProfiles.Batch527.valid21106
  · exact MergedCutProfiles.Batch527.valid21107
  · exact MergedCutProfiles.Batch527.valid21108
  · exact MergedCutProfiles.Batch527.valid21109
  · exact MergedCutProfiles.Batch527.valid21110
  · exact MergedCutProfiles.Batch527.valid21111
  · exact MergedCutProfiles.Batch527.valid21112
  · exact MergedCutProfiles.Batch527.valid21113
  · exact MergedCutProfiles.Batch527.valid21114
  · exact MergedCutProfiles.Batch527.valid21115
  · exact MergedCutProfiles.Batch527.valid21116
  · exact MergedCutProfiles.Batch527.valid21117
  · exact MergedCutProfiles.Batch527.valid21118
theorem numericValid3434 : retention3434.NumericValid := by decide +kernel
def certificate3434 : RatCutBinCertificate := ⟨⟨retention3434,(2217465728453509257/1000000000000000000),(9485872639178457/50000000000000000),(3202793912973537903/200000000000000000),(964357342583473521597/1000000000000000000),(11011911410448017/10000000000000000)⟩,(249531892927526829/250000000000000000),(38781168404277921/100000000000000000),(244837418992689951/1000000000000000000),(54905632287140439/250000000000000000)⟩
theorem valid3434 : certificate3434.Valid := by decide +kernel
theorem sound3434 : certificate3434.Sound := rat_cut_bin_certificate_sound certificate3434 profilesValid3434 numericValid3434 valid3434

def retention3435 : RatCutRetentionCertificate := ⟨(121/2000),(61/1000),(29723059281603816419/60034912269996432986),(12674228466585258841/500000000000000000),1,(1269134969121890615692523815625692137/1267422846658525884100000000000000000),false,MergedCutProfiles.Batch527.profile21119,(fun _ => MergedCutProfiles.Batch527.profile21119)⟩
theorem profilesValid3435 : retention3435.ProfilesValid := by
  exact MergedCutProfiles.Batch527.valid21119
theorem numericValid3435 : retention3435.NumericValid := by decide +kernel
def certificate3435 : RatCutBinCertificate := ⟨⟨retention3435,(2217465728453509257/1000000000000000000),(9485872639178457/50000000000000000),(3202793912973537903/200000000000000000),(964357342583473521597/1000000000000000000),(975080354995416737/1000000000000000000)⟩,(249531892927526829/250000000000000000),(12490913263295209/31250000000000000),(14609305741836281/62500000000000000),(43811982858480487/200000000000000000)⟩
theorem valid3435 : certificate3435.Valid := by decide +kernel
theorem sound3435 : certificate3435.Sound := rat_cut_bin_certificate_sound certificate3435 profilesValid3435 numericValid3435 valid3435

def retention3436 : RatCutRetentionCertificate := ⟨(121/2000),(61/1000),(1/2),(29723059281603816419/1000000000000000000),1,(118080450367730169908889001177423103619/118892237126415265676000000000000000000),false,MergedCutProfiles.Batch406.profile16277,(fun _ => MergedCutProfiles.Batch406.profile16277)⟩
theorem profilesValid3436 : retention3436.ProfilesValid := by
  exact MergedCutProfiles.Batch406.valid16277
theorem numericValid3436 : retention3436.NumericValid := by decide +kernel
def certificate3436 : RatCutBinCertificate := ⟨⟨retention3436,(2217465728453509257/1000000000000000000),(9485872639178457/50000000000000000),(3202793912973537903/200000000000000000),(964357342583473521597/1000000000000000000),(483450797595428561/500000000000000000)⟩,(249531892927526829/250000000000000000),(401333538731049517/1000000000000000000),(232262727611061511/1000000000000000000),(13567741362935449/62500000000000000)⟩
theorem valid3436 : certificate3436.Valid := by decide +kernel
theorem sound3436 : certificate3436.Sound := rat_cut_bin_certificate_sound certificate3436 profilesValid3436 numericValid3436 valid3436

def retention3437 : RatCutRetentionCertificate := ⟨(121/2000),(61/1000),(27660622180972038039/60034912269996432986),(4628932340323177627/500000000000000000),1,(38852820990606815396027354435313978039/37031458722585421016000000000000000000),false,MergedCutProfiles.Batch528.profile21120,(fun _ => MergedCutProfiles.Batch528.profile21120)⟩
theorem profilesValid3437 : retention3437.ProfilesValid := by
  exact MergedCutProfiles.Batch528.valid21120
theorem numericValid3437 : retention3437.NumericValid := by decide +kernel
def certificate3437 : RatCutBinCertificate := ⟨⟨retention3437,(2284393507453509257/1000000000000000000),(9485872639178457/50000000000000000),(3202793912973537903/200000000000000000),(964357342583473521597/1000000000000000000),(25553010262060373/25000000000000000)⟩,(49903551648477537/50000000000000000),(23536315134455173/200000000000000000),(31415802191598499/50000000000000000),(23087015562438097/40000000000000000)⟩
theorem valid3437 : certificate3437.Valid := by decide +kernel
theorem sound3437 : certificate3437.Sound := rat_cut_bin_certificate_sound certificate3437 profilesValid3437 numericValid3437 valid3437

def retention3438 : RatCutRetentionCertificate := ⟨(121/2000),(61/1000),(14827965450747713444/30017456134998216493),(27660622180972038039/1000000000000000000),1,(77172876260365981059117441660674123/76835061613811216775000000000000000),false,MergedCutProfiles.Batch528.profile21121,(fun _ => MergedCutProfiles.Batch528.profile21121)⟩
theorem profilesValid3438 : retention3438.ProfilesValid := by
  exact MergedCutProfiles.Batch528.valid21121
theorem numericValid3438 : retention3438.NumericValid := by decide +kernel
def certificate3438 : RatCutBinCertificate := ⟨⟨retention3438,(2284393507453509257/1000000000000000000),(9485872639178457/50000000000000000),(3202793912973537903/200000000000000000),(964357342583473521597/1000000000000000000),(61083326563811113/62500000000000000)⟩,(49903551648477537/50000000000000000),(30768610273579451/250000000000000000),(617166181098283297/1000000000000000000),(581443381819502817/1000000000000000000)⟩
theorem valid3438 : certificate3438.Valid := by decide +kernel
theorem sound3438 : certificate3438.Sound := rat_cut_bin_certificate_sound certificate3438 profilesValid3438 numericValid3438 valid3438

def retention3439 : RatCutRetentionCertificate := ⟨(121/2000),(61/1000),(4278927172930054451/8576416038570918998),(3706991362686928361/125000000000000000),1,(118064343382093395281242746480077771151/118623723605981707552000000000000000000),false,MergedCutProfiles.Batch528.profile21122,(fun _ => MergedCutProfiles.Batch528.profile21122)⟩
theorem profilesValid3439 : retention3439.ProfilesValid := by
  exact MergedCutProfiles.Batch528.valid21122
theorem numericValid3439 : retention3439.NumericValid := by decide +kernel
def certificate3439 : RatCutBinCertificate := ⟨⟨retention3439,(2284393507453509257/1000000000000000000),(9485872639178457/50000000000000000),(3202793912973537903/200000000000000000),(964357342583473521597/1000000000000000000),(60513814511940827/62500000000000000)⟩,(49903551648477537/50000000000000000),(4969309132240743/40000000000000000),(3842488305760783/6250000000000000),(575305422589016657/1000000000000000000)⟩
theorem valid3439 : certificate3439.Valid := by decide +kernel
theorem sound3439 : certificate3439.Sound := rat_cut_bin_certificate_sound certificate3439 profilesValid3439 numericValid3439 valid3439

def retention3440 : RatCutRetentionCertificate := ⟨(121/2000),(61/1000),(1/2),(29952490210510381157/1000000000000000000),1,(23799930354063188306976207271521013359/23961992168408304925600000000000000000),false,MergedCutProfiles.Batch406.profile16277,(fun _ => MergedCutProfiles.Batch406.profile16277)⟩
theorem profilesValid3440 : retention3440.ProfilesValid := by
  exact MergedCutProfiles.Batch406.valid16277
theorem numericValid3440 : retention3440.NumericValid := by decide +kernel
def certificate3440 : RatCutBinCertificate := ⟨⟨retention3440,(2284393507453509257/1000000000000000000),(9485872639178457/50000000000000000),(3202793912973537903/200000000000000000),(964357342583473521597/1000000000000000000),(966173332392897761/1000000000000000000)⟩,(49903551648477537/50000000000000000),(12449602612655197/100000000000000000),(122852226819884881/200000000000000000),(286902547173372553/500000000000000000)⟩
theorem valid3440 : certificate3440.Valid := by decide +kernel
theorem sound3440 : certificate3440.Sound := rat_cut_bin_certificate_sound certificate3440 profilesValid3440 numericValid3440 valid3440

def retention3441 : RatCutRetentionCertificate := ⟨(61/1000),(123/2000),(75035267972438053/4906732924340583720),(891508134325996669/1000000000000000000),(59/20),(44585242229329469309/20000000000000000000),true,MergedCutProfiles.Batch528.profile21123,![MergedCutProfiles.Batch528.profile21123,MergedCutProfiles.Batch528.profile21124,MergedCutProfiles.Batch528.profile21125,MergedCutProfiles.Batch528.profile21126,MergedCutProfiles.Batch528.profile21127,MergedCutProfiles.Batch528.profile21128,MergedCutProfiles.Batch528.profile21129,MergedCutProfiles.Batch528.profile21130,MergedCutProfiles.Batch528.profile21131,MergedCutProfiles.Batch528.profile21132,MergedCutProfiles.Batch528.profile21133,MergedCutProfiles.Batch528.profile21134,MergedCutProfiles.Batch408.profile16331,MergedCutProfiles.Batch528.profile21135,MergedCutProfiles.Batch528.profile21136,MergedCutProfiles.Batch528.profile21137]⟩
theorem profilesValid3441 : retention3441.ProfilesValid := by
  change ∀ j : Fin 16, (retention3441.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch528.valid21123
  · exact MergedCutProfiles.Batch528.valid21124
  · exact MergedCutProfiles.Batch528.valid21125
  · exact MergedCutProfiles.Batch528.valid21126
  · exact MergedCutProfiles.Batch528.valid21127
  · exact MergedCutProfiles.Batch528.valid21128
  · exact MergedCutProfiles.Batch528.valid21129
  · exact MergedCutProfiles.Batch528.valid21130
  · exact MergedCutProfiles.Batch528.valid21131
  · exact MergedCutProfiles.Batch528.valid21132
  · exact MergedCutProfiles.Batch528.valid21133
  · exact MergedCutProfiles.Batch528.valid21134
  · exact MergedCutProfiles.Batch408.valid16331
  · exact MergedCutProfiles.Batch528.valid21135
  · exact MergedCutProfiles.Batch528.valid21136
  · exact MergedCutProfiles.Batch528.valid21137
theorem numericValid3441 : retention3441.NumericValid := by decide +kernel
def certificate3441 : RatCutBinCertificate := ⟨⟨retention3441,(2224789110314203867/1000000000000000000),(19343761517970331/100000000000000000),(16162259592362227201/1000000000000000000),(477293369344536448549/500000000000000000),(1075352710474204389/500000000000000000)⟩,(249527671863175091/250000000000000000),(4053882604998873/12500000000000000),(310486375935437037/1000000000000000000),(176829778530155593/1000000000000000000)⟩
theorem valid3441 : certificate3441.Valid := by decide +kernel
theorem sound3441 : certificate3441.Sound := rat_cut_bin_certificate_sound certificate3441 profilesValid3441 numericValid3441 valid3441

def retention3442 : RatCutRetentionCertificate := ⟨(61/1000),(123/2000),(53318760221408453/2944039754604350232),(225105803917314159/250000000000000000),(59/20),(44422369821461993961/20000000000000000000),true,MergedCutProfiles.Batch528.profile21138,![MergedCutProfiles.Batch528.profile21138,MergedCutProfiles.Batch528.profile21139,MergedCutProfiles.Batch528.profile21140,MergedCutProfiles.Batch528.profile21141,MergedCutProfiles.Batch528.profile21142,MergedCutProfiles.Batch528.profile21143,MergedCutProfiles.Batch528.profile21144,MergedCutProfiles.Batch528.profile21145,MergedCutProfiles.Batch528.profile21146,MergedCutProfiles.Batch528.profile21147,MergedCutProfiles.Batch408.profile16331,MergedCutProfiles.Batch528.profile21148,MergedCutProfiles.Batch528.profile21149,MergedCutProfiles.Batch407.profile16317,MergedCutProfiles.Batch528.profile21150,MergedCutProfiles.Batch407.profile16302]⟩
theorem profilesValid3442 : retention3442.ProfilesValid := by
  change ∀ j : Fin 16, (retention3442.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch528.valid21138
  · exact MergedCutProfiles.Batch528.valid21139
  · exact MergedCutProfiles.Batch528.valid21140
  · exact MergedCutProfiles.Batch528.valid21141
  · exact MergedCutProfiles.Batch528.valid21142
  · exact MergedCutProfiles.Batch528.valid21143
  · exact MergedCutProfiles.Batch528.valid21144
  · exact MergedCutProfiles.Batch528.valid21145
  · exact MergedCutProfiles.Batch528.valid21146
  · exact MergedCutProfiles.Batch528.valid21147
  · exact MergedCutProfiles.Batch408.valid16331
  · exact MergedCutProfiles.Batch528.valid21148
  · exact MergedCutProfiles.Batch528.valid21149
  · exact MergedCutProfiles.Batch407.valid16317
  · exact MergedCutProfiles.Batch528.valid21150
  · exact MergedCutProfiles.Batch407.valid16302
theorem numericValid3442 : retention3442.NumericValid := by decide +kernel
def certificate3442 : RatCutBinCertificate := ⟨⟨retention3442,(2224789110314203867/1000000000000000000),(19343761517970331/100000000000000000),(16162259592362227201/1000000000000000000),(477293369344536448549/500000000000000000),(535640465119957263/250000000000000000)⟩,(249527671863175091/250000000000000000),(40506314806179201/125000000000000000),(77694817525067421/250000000000000000),(176850802542758997/1000000000000000000)⟩
theorem valid3442 : certificate3442.Valid := by decide +kernel
theorem sound3442 : certificate3442.Sound := rat_cut_bin_certificate_sound certificate3442 profilesValid3442 numericValid3442 valid3442

def retention3443 : RatCutRetentionCertificate := ⟨(61/1000),(123/2000),(6950373687500000/368004969325543779),(53318760221408453/50000000000000000),(51/20),(1101240722189190921/500000000000000000),true,MergedCutProfiles.Batch528.profile21151,![MergedCutProfiles.Batch528.profile21151,MergedCutProfiles.Batch528.profile21152,MergedCutProfiles.Batch528.profile21153,MergedCutProfiles.Batch528.profile21154,MergedCutProfiles.Batch528.profile21155,MergedCutProfiles.Batch528.profile21156,MergedCutProfiles.Batch528.profile21157,MergedCutProfiles.Batch528.profile21158,MergedCutProfiles.Batch528.profile21159,MergedCutProfiles.Batch529.profile21160,MergedCutProfiles.Batch529.profile21161,MergedCutProfiles.Batch529.profile21162,MergedCutProfiles.Batch528.profile21137,MergedCutProfiles.Batch529.profile21163,MergedCutProfiles.Batch529.profile21164,MergedCutProfiles.Batch529.profile21165]⟩
theorem profilesValid3443 : retention3443.ProfilesValid := by
  change ∀ j : Fin 16, (retention3443.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch528.valid21151
  · exact MergedCutProfiles.Batch528.valid21152
  · exact MergedCutProfiles.Batch528.valid21153
  · exact MergedCutProfiles.Batch528.valid21154
  · exact MergedCutProfiles.Batch528.valid21155
  · exact MergedCutProfiles.Batch528.valid21156
  · exact MergedCutProfiles.Batch528.valid21157
  · exact MergedCutProfiles.Batch528.valid21158
  · exact MergedCutProfiles.Batch528.valid21159
  · exact MergedCutProfiles.Batch529.valid21160
  · exact MergedCutProfiles.Batch529.valid21161
  · exact MergedCutProfiles.Batch529.valid21162
  · exact MergedCutProfiles.Batch528.valid21137
  · exact MergedCutProfiles.Batch529.valid21163
  · exact MergedCutProfiles.Batch529.valid21164
  · exact MergedCutProfiles.Batch529.valid21165
theorem numericValid3443 : retention3443.NumericValid := by decide +kernel
def certificate3443 : RatCutBinCertificate := ⟨⟨retention3443,(2224789110314203867/1000000000000000000),(19343761517970331/100000000000000000),(16162259592362227201/1000000000000000000),(477293369344536448549/500000000000000000),(426915336066270879/200000000000000000)⟩,(249527671863175091/250000000000000000),(301945350800392901/1000000000000000000),(42056307802096357/125000000000000000),(3357258675378517/15625000000000000)⟩
theorem valid3443 : certificate3443.Valid := by decide +kernel
theorem sound3443 : certificate3443.Sound := rat_cut_bin_certificate_sound certificate3443 profilesValid3443 numericValid3443 valid3443

def certificates : List RatCutBinCertificate := [certificate3432,certificate3433,certificate3434,certificate3435,certificate3436,certificate3437,certificate3438,certificate3439,certificate3440,certificate3441,certificate3442,certificate3443]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3432,List.forall_mem_cons.mpr ⟨sound3433,List.forall_mem_cons.mpr ⟨sound3434,List.forall_mem_cons.mpr ⟨sound3435,List.forall_mem_cons.mpr ⟨sound3436,List.forall_mem_cons.mpr ⟨sound3437,List.forall_mem_cons.mpr ⟨sound3438,List.forall_mem_cons.mpr ⟨sound3439,List.forall_mem_cons.mpr ⟨sound3440,List.forall_mem_cons.mpr ⟨sound3441,List.forall_mem_cons.mpr ⟨sound3442,List.forall_mem_cons.mpr ⟨sound3443,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch286
