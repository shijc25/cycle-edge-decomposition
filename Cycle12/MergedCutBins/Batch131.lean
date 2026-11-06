import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch253
import Cycle12.MergedCutProfiles.Batch254
import Cycle12.MergedCutProfiles.Batch255

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch131

def retention1572 : RatCutRetentionCertificate := ⟨(101/1600),(253/4000),(1/2),(5475666701388136003/1000000000000000000),(11/10),(2173212807368533761020323597665585019231/2190266680555254401200000000000000000000),false,MergedCutProfiles.Batch253.profile10130,(fun _ => MergedCutProfiles.Batch253.profile10130)⟩
theorem profilesValid1572 : retention1572.ProfilesValid := by
  exact MergedCutProfiles.Batch253.valid10130
theorem numericValid1572 : retention1572.NumericValid := by decide +kernel
def certificate1572 : RatCutBinCertificate := ⟨⟨retention1572,(47074083761169197/20000000000000000),(206867685175350651/1000000000000000000),(1680838030226467533/100000000000000000),(92628182321493895023/500000000000000000),(960343072427537069/1000000000000000000)⟩,(494941483250681637/500000000000000000),(434853775838668493/1000000000000000000),(101511632572112133/500000000000000000),(30619290103551097/200000000000000000)⟩
theorem valid1572 : certificate1572.Valid := by decide +kernel
theorem sound1572 : certificate1572.Sound := rat_cut_bin_certificate_sound certificate1572 profilesValid1572 numericValid1572 valid1572

def retention1573 : RatCutRetentionCertificate := ⟨(101/1600),(253/4000),(1/2),64,1,(63853302987300977290672926981274249111/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch253.profile10130,(fun _ => MergedCutProfiles.Batch253.profile10130)⟩
theorem profilesValid1573 : retention1573.ProfilesValid := by
  exact MergedCutProfiles.Batch253.valid10130
theorem numericValid1573 : retention1573.NumericValid := by decide +kernel
def certificate1573 : RatCutBinCertificate := ⟨⟨retention1573,(47074083761169197/20000000000000000),(206867685175350651/1000000000000000000),(1680838030226467533/100000000000000000),(92628182321493895023/500000000000000000),(121092417907069051/125000000000000000)⟩,(494941483250681637/500000000000000000),(12407289725902933/31250000000000000),(9448466087570337/40000000000000000),(223112409463076467/1000000000000000000)⟩
theorem valid1573 : certificate1573.Valid := by decide +kernel
theorem sound1573 : certificate1573.Sound := rat_cut_bin_certificate_sound certificate1573 profilesValid1573 numericValid1573 valid1573

def retention1574 : RatCutRetentionCertificate := ⟨(101/1600),(253/4000),(5134973626309104996/11013057205697723371),(328153013736445709/100000000000000000),(6/5),(13868496878818837202492612225033414591/13126120549457828360000000000000000000),false,MergedCutProfiles.Batch253.profile10131,(fun _ => MergedCutProfiles.Batch253.profile10131)⟩
theorem profilesValid1574 : retention1574.ProfilesValid := by
  exact MergedCutProfiles.Batch253.valid10131
theorem numericValid1574 : retention1574.NumericValid := by decide +kernel
def certificate1574 : RatCutBinCertificate := ⟨⟨retention1574,(53503377681169197/20000000000000000),(206867685175350651/1000000000000000000),(1680838030226467533/100000000000000000),(92628182321493895023/500000000000000000),(254259170622556411/250000000000000000)⟩,(15445266904426131/15625000000000000),(98147092923842103/250000000000000000),(120171163193018123/500000000000000000),(41366324024015903/250000000000000000)⟩
theorem valid1574 : certificate1574.Valid := by decide +kernel
theorem sound1574 : certificate1574.Sound := rat_cut_bin_certificate_sound certificate1574 profilesValid1574 numericValid1574 valid1574

def retention1575 : RatCutRetentionCertificate := ⟨(101/1600),(253/4000),(5450877977131804234/11013057205697723371),(1283743406577276249/250000000000000000),(11/10),(16041501299900515449431754165588081973/16046792582215953112500000000000000000),false,MergedCutProfiles.Batch253.profile10132,(fun _ => MergedCutProfiles.Batch253.profile10132)⟩
theorem profilesValid1575 : retention1575.ProfilesValid := by
  exact MergedCutProfiles.Batch253.valid10132
theorem numericValid1575 : retention1575.NumericValid := by decide +kernel
def certificate1575 : RatCutBinCertificate := ⟨⟨retention1575,(53503377681169197/20000000000000000),(206867685175350651/1000000000000000000),(1680838030226467533/100000000000000000),(92628182321493895023/500000000000000000),(192689249815131963/200000000000000000)⟩,(15445266904426131/15625000000000000),(414425584734350581/1000000000000000000),(220521863387256443/1000000000000000000),(33025480255507283/200000000000000000)⟩
theorem valid1575 : certificate1575.Valid := by decide +kernel
theorem sound1575 : certificate1575.Sound := rat_cut_bin_certificate_sound certificate1575 profilesValid1575 numericValid1575 valid1575

def retention1576 : RatCutRetentionCertificate := ⟨(101/1600),(253/4000),(5505386756903122277/11013057205697723371),(2725438988565902117/500000000000000000),(11/10),(540872339143354384274560808391581523511/545087797713180423400000000000000000000),false,MergedCutProfiles.Batch253.profile10133,(fun _ => MergedCutProfiles.Batch253.profile10133)⟩
theorem profilesValid1576 : retention1576.ProfilesValid := by
  exact MergedCutProfiles.Batch253.valid10133
theorem numericValid1576 : retention1576.NumericValid := by decide +kernel
def certificate1576 : RatCutBinCertificate := ⟨⟨retention1576,(53503377681169197/20000000000000000),(206867685175350651/1000000000000000000),(1680838030226467533/100000000000000000),(92628182321493895023/500000000000000000),(47802143215287849/50000000000000000)⟩,(15445266904426131/15625000000000000),(104408701230994789/250000000000000000),(54426864854666141/250000000000000000),(163203714136022189/1000000000000000000)⟩
theorem valid1576 : certificate1576.Valid := by decide +kernel
theorem sound1576 : certificate1576.Sound := rat_cut_bin_certificate_sound certificate1576 profilesValid1576 numericValid1576 valid1576

def retention1577 : RatCutRetentionCertificate := ⟨(101/1600),(253/4000),(1/2),(5505386756903122277/1000000000000000000),(11/10),(2185389179936139108905437059339251707231/2202154702761248910800000000000000000000),false,MergedCutProfiles.Batch253.profile10130,(fun _ => MergedCutProfiles.Batch253.profile10130)⟩
theorem profilesValid1577 : retention1577.ProfilesValid := by
  exact MergedCutProfiles.Batch253.valid10130
theorem numericValid1577 : retention1577.NumericValid := by decide +kernel
def certificate1577 : RatCutBinCertificate := ⟨⟨retention1577,(53503377681169197/20000000000000000),(206867685175350651/1000000000000000000),(1680838030226467533/100000000000000000),(92628182321493895023/500000000000000000),(956163235893479987/1000000000000000000)⟩,(15445266904426131/15625000000000000),(52197778598990439/125000000000000000),(54438342046962801/250000000000000000),(20432794292566133/125000000000000000)⟩
theorem valid1577 : certificate1577.Valid := by decide +kernel
theorem sound1577 : certificate1577.Sound := rat_cut_bin_certificate_sound certificate1577 profilesValid1577 numericValid1577 valid1577

def retention1578 : RatCutRetentionCertificate := ⟨(253/4000),(127/2000),(229117932806411795/2727356343157655291),(683847784274293/800000000000000),(53/20),(7753898454967462493/4000000000000000000),true,MergedCutProfiles.Batch253.profile10134,![MergedCutProfiles.Batch253.profile10134,MergedCutProfiles.Batch253.profile10135,MergedCutProfiles.Batch253.profile10136,MergedCutProfiles.Batch253.profile10137,MergedCutProfiles.Batch253.profile10138,MergedCutProfiles.Batch253.profile10139,MergedCutProfiles.Batch253.profile10140,MergedCutProfiles.Batch253.profile10141,MergedCutProfiles.Batch253.profile10142,MergedCutProfiles.Batch253.profile10143,MergedCutProfiles.Batch253.profile10144,MergedCutProfiles.Batch253.profile10145,MergedCutProfiles.Batch253.profile10146,MergedCutProfiles.Batch253.profile10147,MergedCutProfiles.Batch253.profile10148,MergedCutProfiles.Batch253.profile10149]⟩
theorem profilesValid1578 : retention1578.ProfilesValid := by
  change ∀ j : Fin 16, (retention1578.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch253.valid10134
  · exact MergedCutProfiles.Batch253.valid10135
  · exact MergedCutProfiles.Batch253.valid10136
  · exact MergedCutProfiles.Batch253.valid10137
  · exact MergedCutProfiles.Batch253.valid10138
  · exact MergedCutProfiles.Batch253.valid10139
  · exact MergedCutProfiles.Batch253.valid10140
  · exact MergedCutProfiles.Batch253.valid10141
  · exact MergedCutProfiles.Batch253.valid10142
  · exact MergedCutProfiles.Batch253.valid10143
  · exact MergedCutProfiles.Batch253.valid10144
  · exact MergedCutProfiles.Batch253.valid10145
  · exact MergedCutProfiles.Batch253.valid10146
  · exact MergedCutProfiles.Batch253.valid10147
  · exact MergedCutProfiles.Batch253.valid10148
  · exact MergedCutProfiles.Batch253.valid10149
theorem numericValid1578 : retention1578.NumericValid := by decide +kernel
def certificate1578 : RatCutBinCertificate := ⟨⟨retention1578,(591057572332507563/250000000000000000),(2610492019033761/12500000000000000),(8423975412553280809/500000000000000000),(184089318713182580423/1000000000000000000),(372155017751022191/200000000000000000)⟩,(989785481598171047/1000000000000000000),(170931609830505071/500000000000000000),(291192440897640477/1000000000000000000),(77073767542808571/500000000000000000)⟩
theorem valid1578 : certificate1578.Valid := by decide +kernel
theorem sound1578 : certificate1578.Sound := rat_cut_bin_certificate_sound certificate1578 profilesValid1578 numericValid1578 valid1578

def retention1579 : RatCutRetentionCertificate := ⟨(253/4000),(127/2000),(1235265428865758805/10909425372630621164),(45823586561282359/50000000000000000),(5/2),(29777324264175625663/16000000000000000000),true,MergedCutProfiles.Batch253.profile10150,![MergedCutProfiles.Batch253.profile10150,MergedCutProfiles.Batch253.profile10151,MergedCutProfiles.Batch253.profile10152,MergedCutProfiles.Batch253.profile10153,MergedCutProfiles.Batch253.profile10154,MergedCutProfiles.Batch253.profile10155,MergedCutProfiles.Batch253.profile10156,MergedCutProfiles.Batch253.profile10157,MergedCutProfiles.Batch253.profile10158,MergedCutProfiles.Batch253.profile10159,MergedCutProfiles.Batch254.profile10160,MergedCutProfiles.Batch254.profile10161,MergedCutProfiles.Batch254.profile10162,MergedCutProfiles.Batch254.profile10163,MergedCutProfiles.Batch254.profile10164,MergedCutProfiles.Batch254.profile10165]⟩
theorem profilesValid1579 : retention1579.ProfilesValid := by
  change ∀ j : Fin 16, (retention1579.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch253.valid10150
  · exact MergedCutProfiles.Batch253.valid10151
  · exact MergedCutProfiles.Batch253.valid10152
  · exact MergedCutProfiles.Batch253.valid10153
  · exact MergedCutProfiles.Batch253.valid10154
  · exact MergedCutProfiles.Batch253.valid10155
  · exact MergedCutProfiles.Batch253.valid10156
  · exact MergedCutProfiles.Batch253.valid10157
  · exact MergedCutProfiles.Batch253.valid10158
  · exact MergedCutProfiles.Batch253.valid10159
  · exact MergedCutProfiles.Batch254.valid10160
  · exact MergedCutProfiles.Batch254.valid10161
  · exact MergedCutProfiles.Batch254.valid10162
  · exact MergedCutProfiles.Batch254.valid10163
  · exact MergedCutProfiles.Batch254.valid10164
  · exact MergedCutProfiles.Batch254.valid10165
theorem numericValid1579 : retention1579.NumericValid := by decide +kernel
def certificate1579 : RatCutBinCertificate := ⟨⟨retention1579,(591057572332507563/250000000000000000),(2610492019033761/12500000000000000),(8423975412553280809/500000000000000000),(184089318713182580423/1000000000000000000),(71511269725934541/40000000000000000)⟩,(989785481598171047/1000000000000000000),(69193447607231553/200000000000000000),(286812748216056481/1000000000000000000),(154378305153520929/1000000000000000000)⟩
theorem valid1579 : certificate1579.Valid := by decide +kernel
theorem sound1579 : certificate1579.Sound := rat_cut_bin_certificate_sound certificate1579 profilesValid1579 numericValid1579 valid1579

def retention1580 : RatCutRetentionCertificate := ⟨(253/4000),(127/2000),(619721353223254611/2727356343157655291),(247053085773151761/200000000000000000),(19/10),(400003382132495153757/256000000000000000000),true,MergedCutProfiles.Batch254.profile10166,![MergedCutProfiles.Batch254.profile10166,MergedCutProfiles.Batch254.profile10167,MergedCutProfiles.Batch253.profile10155,MergedCutProfiles.Batch254.profile10168,MergedCutProfiles.Batch254.profile10169,MergedCutProfiles.Batch254.profile10170,MergedCutProfiles.Batch254.profile10171,MergedCutProfiles.Batch254.profile10172,MergedCutProfiles.Batch254.profile10173,MergedCutProfiles.Batch254.profile10174,MergedCutProfiles.Batch254.profile10175,MergedCutProfiles.Batch254.profile10176,MergedCutProfiles.Batch254.profile10177,MergedCutProfiles.Batch254.profile10178,MergedCutProfiles.Batch254.profile10179,MergedCutProfiles.Batch254.profile10180]⟩
theorem profilesValid1580 : retention1580.ProfilesValid := by
  change ∀ j : Fin 16, (retention1580.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch254.valid10166
  · exact MergedCutProfiles.Batch254.valid10167
  · exact MergedCutProfiles.Batch253.valid10155
  · exact MergedCutProfiles.Batch254.valid10168
  · exact MergedCutProfiles.Batch254.valid10169
  · exact MergedCutProfiles.Batch254.valid10170
  · exact MergedCutProfiles.Batch254.valid10171
  · exact MergedCutProfiles.Batch254.valid10172
  · exact MergedCutProfiles.Batch254.valid10173
  · exact MergedCutProfiles.Batch254.valid10174
  · exact MergedCutProfiles.Batch254.valid10175
  · exact MergedCutProfiles.Batch254.valid10176
  · exact MergedCutProfiles.Batch254.valid10177
  · exact MergedCutProfiles.Batch254.valid10178
  · exact MergedCutProfiles.Batch254.valid10179
  · exact MergedCutProfiles.Batch254.valid10180
theorem numericValid1580 : retention1580.NumericValid := by decide +kernel
def certificate1580 : RatCutBinCertificate := ⟨⟨retention1580,(591057572332507563/250000000000000000),(2610492019033761/12500000000000000),(8423975412553280809/500000000000000000),(184089318713182580423/1000000000000000000),(1506805089464231613/1000000000000000000)⟩,(989785481598171047/1000000000000000000),(368652326778499529/1000000000000000000),(32933204879867197/125000000000000000),(154251548916550277/1000000000000000000)⟩
theorem valid1580 : certificate1580.Valid := by decide +kernel
theorem sound1580 : certificate1580.Sound := rat_cut_bin_certificate_sound certificate1580 profilesValid1580 numericValid1580 valid1580

def retention1581 : RatCutRetentionCertificate := ⟨(253/4000),(127/2000),(4414648510657218315/10909425372630621164),(619721353223254611/250000000000000000),(6/5),(371689554437960981031/320000000000000000000),true,MergedCutProfiles.Batch254.profile10181,![MergedCutProfiles.Batch254.profile10181,MergedCutProfiles.Batch254.profile10182,MergedCutProfiles.Batch254.profile10183,MergedCutProfiles.Batch254.profile10184,MergedCutProfiles.Batch254.profile10185,MergedCutProfiles.Batch254.profile10186,MergedCutProfiles.Batch254.profile10187,MergedCutProfiles.Batch254.profile10188,MergedCutProfiles.Batch254.profile10189,MergedCutProfiles.Batch254.profile10190,MergedCutProfiles.Batch254.profile10191,MergedCutProfiles.Batch254.profile10192,MergedCutProfiles.Batch254.profile10193,MergedCutProfiles.Batch254.profile10194,MergedCutProfiles.Batch254.profile10195,MergedCutProfiles.Batch254.profile10196]⟩
theorem profilesValid1581 : retention1581.ProfilesValid := by
  change ∀ j : Fin 16, (retention1581.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch254.valid10181
  · exact MergedCutProfiles.Batch254.valid10182
  · exact MergedCutProfiles.Batch254.valid10183
  · exact MergedCutProfiles.Batch254.valid10184
  · exact MergedCutProfiles.Batch254.valid10185
  · exact MergedCutProfiles.Batch254.valid10186
  · exact MergedCutProfiles.Batch254.valid10187
  · exact MergedCutProfiles.Batch254.valid10188
  · exact MergedCutProfiles.Batch254.valid10189
  · exact MergedCutProfiles.Batch254.valid10190
  · exact MergedCutProfiles.Batch254.valid10191
  · exact MergedCutProfiles.Batch254.valid10192
  · exact MergedCutProfiles.Batch254.valid10193
  · exact MergedCutProfiles.Batch254.valid10194
  · exact MergedCutProfiles.Batch254.valid10195
  · exact MergedCutProfiles.Batch254.valid10196
theorem numericValid1581 : retention1581.NumericValid := by decide +kernel
def certificate1581 : RatCutBinCertificate := ⟨⟨retention1581,(591057572332507563/250000000000000000),(2610492019033761/12500000000000000),(8423975412553280809/500000000000000000),(184089318713182580423/1000000000000000000),(1126349367243832307/1000000000000000000)⟩,(989785481598171047/1000000000000000000),(412471419195450319/1000000000000000000),(22224777403370789/100000000000000000),(78343328855366593/500000000000000000)⟩
theorem valid1581 : certificate1581.Valid := by decide +kernel
theorem sound1581 : certificate1581.Sound := rat_cut_bin_certificate_sound certificate1581 profilesValid1581 numericValid1581 valid1581

def retention1582 : RatCutRetentionCertificate := ⟨(253/4000),(127/2000),(2614143897062636779/5454712686315310582),(882929702131443663/200000000000000000),1,(50948681196878171199/51200000000000000000),true,MergedCutProfiles.Batch254.profile10197,![MergedCutProfiles.Batch254.profile10197,MergedCutProfiles.Batch254.profile10198,MergedCutProfiles.Batch254.profile10199,MergedCutProfiles.Batch255.profile10200,MergedCutProfiles.Batch255.profile10201,MergedCutProfiles.Batch255.profile10202,MergedCutProfiles.Batch255.profile10203,MergedCutProfiles.Batch255.profile10204,MergedCutProfiles.Batch255.profile10205,MergedCutProfiles.Batch255.profile10206,MergedCutProfiles.Batch255.profile10207,MergedCutProfiles.Batch255.profile10208,MergedCutProfiles.Batch255.profile10209,MergedCutProfiles.Batch255.profile10210,MergedCutProfiles.Batch255.profile10211,MergedCutProfiles.Batch255.profile10212]⟩
theorem profilesValid1582 : retention1582.ProfilesValid := by
  change ∀ j : Fin 16, (retention1582.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch254.valid10197
  · exact MergedCutProfiles.Batch254.valid10198
  · exact MergedCutProfiles.Batch254.valid10199
  · exact MergedCutProfiles.Batch255.valid10200
  · exact MergedCutProfiles.Batch255.valid10201
  · exact MergedCutProfiles.Batch255.valid10202
  · exact MergedCutProfiles.Batch255.valid10203
  · exact MergedCutProfiles.Batch255.valid10204
  · exact MergedCutProfiles.Batch255.valid10205
  · exact MergedCutProfiles.Batch255.valid10206
  · exact MergedCutProfiles.Batch255.valid10207
  · exact MergedCutProfiles.Batch255.valid10208
  · exact MergedCutProfiles.Batch255.valid10209
  · exact MergedCutProfiles.Batch255.valid10210
  · exact MergedCutProfiles.Batch255.valid10211
  · exact MergedCutProfiles.Batch255.valid10212
theorem numericValid1582 : retention1582.NumericValid := by decide +kernel
def certificate1582 : RatCutBinCertificate := ⟨⟨retention1582,(591057572332507563/250000000000000000),(2610492019033761/12500000000000000),(8423975412553280809/500000000000000000),(184089318713182580423/1000000000000000000),(965777999865875221/1000000000000000000)⟩,(989785481598171047/1000000000000000000),(440055744912997387/1000000000000000000),(198722410030539323/1000000000000000000),(31134394270373859/200000000000000000)⟩
theorem valid1582 : certificate1582.Valid := by decide +kernel
theorem sound1582 : certificate1582.Sound := rat_cut_bin_certificate_sound certificate1582 profilesValid1582 numericValid1582 valid1582

def retention1583 : RatCutRetentionCertificate := ⟨(253/4000),(127/2000),(5386710142575063473/10909425372630621164),(2614143897062636779/500000000000000000),(11/10),(524180025268740447288869472201147329639/522828779412527355800000000000000000000),false,MergedCutProfiles.Batch255.profile10213,(fun _ => MergedCutProfiles.Batch255.profile10213)⟩
theorem profilesValid1583 : retention1583.ProfilesValid := by
  exact MergedCutProfiles.Batch255.valid10213
theorem numericValid1583 : retention1583.NumericValid := by decide +kernel
def certificate1583 : RatCutBinCertificate := ⟨⟨retention1583,(591057572332507563/250000000000000000),(2610492019033761/12500000000000000),(8423975412553280809/500000000000000000),(184089318713182580423/1000000000000000000),(970341642511381699/1000000000000000000)⟩,(989785481598171047/1000000000000000000),(42985506951616849/100000000000000000),(41442935579694103/200000000000000000),(39176561273107891/250000000000000000)⟩
theorem valid1583 : certificate1583.Valid := by decide +kernel
theorem sound1583 : certificate1583.Sound := rat_cut_bin_certificate_sound certificate1583 profilesValid1583 numericValid1583 valid1583

def certificates : List RatCutBinCertificate := [certificate1572,certificate1573,certificate1574,certificate1575,certificate1576,certificate1577,certificate1578,certificate1579,certificate1580,certificate1581,certificate1582,certificate1583]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1572,List.forall_mem_cons.mpr ⟨sound1573,List.forall_mem_cons.mpr ⟨sound1574,List.forall_mem_cons.mpr ⟨sound1575,List.forall_mem_cons.mpr ⟨sound1576,List.forall_mem_cons.mpr ⟨sound1577,List.forall_mem_cons.mpr ⟨sound1578,List.forall_mem_cons.mpr ⟨sound1579,List.forall_mem_cons.mpr ⟨sound1580,List.forall_mem_cons.mpr ⟨sound1581,List.forall_mem_cons.mpr ⟨sound1582,List.forall_mem_cons.mpr ⟨sound1583,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch131
