import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch406
import Cycle12.MergedCutProfiles.Batch407
import Cycle12.MergedCutProfiles.Batch409
import Cycle12.MergedCutProfiles.Batch410
import Cycle12.MergedCutProfiles.Batch411
import Cycle12.MergedCutProfiles.Batch528
import Cycle12.MergedCutProfiles.Batch529
import Cycle12.MergedCutProfiles.Batch530
import Cycle12.MergedCutProfiles.Batch531
import Cycle12.MergedCutProfiles.Batch629
import Cycle12.MergedCutProfiles.Batch630
import Cycle12.MergedCutProfiles.Batch631

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch350

def retention4200 : RatCutRetentionCertificate := ⟨(121/2000),(61/1000),(1/2),64,1,(255408979415051621191349709308445271431/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch406.profile16277,(fun _ => MergedCutProfiles.Batch406.profile16277)⟩
theorem profilesValid4200 : retention4200.ProfilesValid := by
  exact MergedCutProfiles.Batch406.valid16277
theorem numericValid4200 : retention4200.NumericValid := by decide +kernel
def certificate4200 : RatCutBinCertificate := ⟨⟨retention4200,(383831653122675463/200000000000000000),(9485872639178457/50000000000000000),(1601422808435793077/100000000000000000),(1928745821128284453269/500000000000000000),(974955412780856173/1000000000000000000)⟩,(499797504750252751/500000000000000000),(10531594442174171/200000000000000000),(781275929011463773/1000000000000000000),(749972259362604961/1000000000000000000)⟩
theorem valid4200 : certificate4200.Valid := by decide +kernel
theorem sound4200 : certificate4200.Sound := rat_cut_bin_certificate_sound certificate4200 profilesValid4200 numericValid4200 valid4200

def retention4201 : RatCutRetentionCertificate := ⟨(61/1000),(123/2000),(386853393790241035/117761590184174009281),(9575579054213887/12500000000000000),(73/20),(379682432143429777/160000000000000000),true,MergedCutProfiles.Batch629.profile25178,![MergedCutProfiles.Batch629.profile25178,MergedCutProfiles.Batch629.profile25179,MergedCutProfiles.Batch629.profile25180,MergedCutProfiles.Batch629.profile25181,MergedCutProfiles.Batch629.profile25182,MergedCutProfiles.Batch629.profile25183,MergedCutProfiles.Batch629.profile25184,MergedCutProfiles.Batch629.profile25185,MergedCutProfiles.Batch629.profile25186,MergedCutProfiles.Batch629.profile25187,MergedCutProfiles.Batch528.profile21139,MergedCutProfiles.Batch407.profile16280,MergedCutProfiles.Batch407.profile16312,MergedCutProfiles.Batch528.profile21125,MergedCutProfiles.Batch529.profile21167,MergedCutProfiles.Batch629.profile25188]⟩
theorem profilesValid4201 : retention4201.ProfilesValid := by
  change ∀ j : Fin 16, (retention4201.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch629.valid25178
  · exact MergedCutProfiles.Batch629.valid25179
  · exact MergedCutProfiles.Batch629.valid25180
  · exact MergedCutProfiles.Batch629.valid25181
  · exact MergedCutProfiles.Batch629.valid25182
  · exact MergedCutProfiles.Batch629.valid25183
  · exact MergedCutProfiles.Batch629.valid25184
  · exact MergedCutProfiles.Batch629.valid25185
  · exact MergedCutProfiles.Batch629.valid25186
  · exact MergedCutProfiles.Batch629.valid25187
  · exact MergedCutProfiles.Batch528.valid21139
  · exact MergedCutProfiles.Batch407.valid16280
  · exact MergedCutProfiles.Batch407.valid16312
  · exact MergedCutProfiles.Batch528.valid21125
  · exact MergedCutProfiles.Batch529.valid21167
  · exact MergedCutProfiles.Batch629.valid25188
theorem numericValid4201 : retention4201.NumericValid := by decide +kernel
def certificate4201 : RatCutBinCertificate := ⟨⟨retention4201,(2084157149578550967/1000000000000000000),(19343761517970331/100000000000000000),(1616252833998960701/100000000000000000),(3818410446601521484933/1000000000000000000),(2281968791040367413/1000000000000000000)⟩,(499778843642324683/500000000000000000),(114586571347732377/250000000000000000),(184083678030252789/1000000000000000000),(94007250219776679/1000000000000000000)⟩
theorem valid4201 : certificate4201.Valid := by decide +kernel
theorem sound4201 : certificate4201.Sound := rat_cut_bin_certificate_sound certificate4201 profilesValid4201 numericValid4201 valid4201

def retention4202 : RatCutRetentionCertificate := ⟨(61/1000),(123/2000),(553841441500000000/117761590184174009281),(77370678758048207/100000000000000000),(73/20),(302457175367045465359/128000000000000000000),true,MergedCutProfiles.Batch629.profile25189,![MergedCutProfiles.Batch629.profile25189,MergedCutProfiles.Batch629.profile25190,MergedCutProfiles.Batch629.profile25191,MergedCutProfiles.Batch528.profile21151,MergedCutProfiles.Batch629.profile25192,MergedCutProfiles.Batch629.profile25193,MergedCutProfiles.Batch629.profile25187,MergedCutProfiles.Batch528.profile21152,MergedCutProfiles.Batch407.profile16312,MergedCutProfiles.Batch629.profile25194,MergedCutProfiles.Batch629.profile25195,MergedCutProfiles.Batch528.profile21153,MergedCutProfiles.Batch528.profile21126,MergedCutProfiles.Batch629.profile25196,MergedCutProfiles.Batch629.profile25197,MergedCutProfiles.Batch528.profile21154]⟩
theorem profilesValid4202 : retention4202.ProfilesValid := by
  change ∀ j : Fin 16, (retention4202.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch629.valid25189
  · exact MergedCutProfiles.Batch629.valid25190
  · exact MergedCutProfiles.Batch629.valid25191
  · exact MergedCutProfiles.Batch528.valid21151
  · exact MergedCutProfiles.Batch629.valid25192
  · exact MergedCutProfiles.Batch629.valid25193
  · exact MergedCutProfiles.Batch629.valid25187
  · exact MergedCutProfiles.Batch528.valid21152
  · exact MergedCutProfiles.Batch407.valid16312
  · exact MergedCutProfiles.Batch629.valid25194
  · exact MergedCutProfiles.Batch629.valid25195
  · exact MergedCutProfiles.Batch528.valid21153
  · exact MergedCutProfiles.Batch528.valid21126
  · exact MergedCutProfiles.Batch629.valid25196
  · exact MergedCutProfiles.Batch629.valid25197
  · exact MergedCutProfiles.Batch528.valid21154
theorem numericValid4202 : retention4202.NumericValid := by decide +kernel
def certificate4202 : RatCutBinCertificate := ⟨⟨retention4202,(2084157149578550967/1000000000000000000),(19343761517970331/100000000000000000),(1616252833998960701/100000000000000000),(3818410446601521484933/1000000000000000000),(1135950144515574137/500000000000000000)⟩,(499778843642324683/500000000000000000),(457801294594034679/1000000000000000000),(184509162138556731/1000000000000000000),(18810822920906793/200000000000000000)⟩
theorem valid4202 : certificate4202.Valid := by decide +kernel
theorem sound4202 : certificate4202.Sound := rat_cut_bin_certificate_sound certificate4202 profilesValid4202 numericValid4202 valid4202

def retention4203 : RatCutRetentionCertificate := ⟨(61/1000),(123/2000),(1405590566654089695/235523180368348018562),(1107682883/1000000000),(27/10),(37317090997490401859/16000000000000000000),true,MergedCutProfiles.Batch629.profile25198,![MergedCutProfiles.Batch629.profile25198,MergedCutProfiles.Batch629.profile25199,MergedCutProfiles.Batch528.profile21138,MergedCutProfiles.Batch630.profile25200,MergedCutProfiles.Batch629.profile25186,MergedCutProfiles.Batch630.profile25201,MergedCutProfiles.Batch630.profile25202,MergedCutProfiles.Batch629.profile25194,MergedCutProfiles.Batch630.profile25203,MergedCutProfiles.Batch630.profile25204,MergedCutProfiles.Batch629.profile25196,MergedCutProfiles.Batch528.profile21141,MergedCutProfiles.Batch630.profile25205,MergedCutProfiles.Batch407.profile16297,MergedCutProfiles.Batch630.profile25206,MergedCutProfiles.Batch630.profile25207]⟩
theorem profilesValid4203 : retention4203.ProfilesValid := by
  change ∀ j : Fin 16, (retention4203.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch629.valid25198
  · exact MergedCutProfiles.Batch629.valid25199
  · exact MergedCutProfiles.Batch528.valid21138
  · exact MergedCutProfiles.Batch630.valid25200
  · exact MergedCutProfiles.Batch629.valid25186
  · exact MergedCutProfiles.Batch630.valid25201
  · exact MergedCutProfiles.Batch630.valid25202
  · exact MergedCutProfiles.Batch629.valid25194
  · exact MergedCutProfiles.Batch630.valid25203
  · exact MergedCutProfiles.Batch630.valid25204
  · exact MergedCutProfiles.Batch629.valid25196
  · exact MergedCutProfiles.Batch528.valid21141
  · exact MergedCutProfiles.Batch630.valid25205
  · exact MergedCutProfiles.Batch407.valid16297
  · exact MergedCutProfiles.Batch630.valid25206
  · exact MergedCutProfiles.Batch630.valid25207
theorem numericValid4203 : retention4203.NumericValid := by decide +kernel
def certificate4203 : RatCutBinCertificate := ⟨⟨retention4203,(2084157149578550967/1000000000000000000),(19343761517970331/100000000000000000),(1616252833998960701/100000000000000000),(3818410446601521484933/1000000000000000000),(2264968867698249689/1000000000000000000)⟩,(499778843642324683/500000000000000000),(381287825156021597/1000000000000000000),(251071818764102663/1000000000000000000),(82198189148835551/500000000000000000)⟩
theorem valid4203 : certificate4203.Valid := by decide +kernel
theorem sound4203 : certificate4203.Sound := rat_cut_bin_certificate_sound certificate4203 profilesValid4203 numericValid4203 valid4203

def retention4204 : RatCutRetentionCertificate := ⟨(61/1000),(123/2000),(15932137166549552733/235523180368348018562),(281118113330817939/200000000000000000),(9/4),(103959593267534092623/51200000000000000000),true,MergedCutProfiles.Batch630.profile25208,![MergedCutProfiles.Batch630.profile25208,MergedCutProfiles.Batch630.profile25209,MergedCutProfiles.Batch630.profile25210,MergedCutProfiles.Batch528.profile21150,MergedCutProfiles.Batch407.profile16319,MergedCutProfiles.Batch630.profile25211,MergedCutProfiles.Batch630.profile25212,MergedCutProfiles.Batch630.profile25213,MergedCutProfiles.Batch630.profile25214,MergedCutProfiles.Batch630.profile25215,MergedCutProfiles.Batch630.profile25216,MergedCutProfiles.Batch630.profile25217,MergedCutProfiles.Batch630.profile25218,MergedCutProfiles.Batch630.profile25219,MergedCutProfiles.Batch630.profile25220,MergedCutProfiles.Batch630.profile25221]⟩
theorem profilesValid4204 : retention4204.ProfilesValid := by
  change ∀ j : Fin 16, (retention4204.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch630.valid25208
  · exact MergedCutProfiles.Batch630.valid25209
  · exact MergedCutProfiles.Batch630.valid25210
  · exact MergedCutProfiles.Batch528.valid21150
  · exact MergedCutProfiles.Batch407.valid16319
  · exact MergedCutProfiles.Batch630.valid25211
  · exact MergedCutProfiles.Batch630.valid25212
  · exact MergedCutProfiles.Batch630.valid25213
  · exact MergedCutProfiles.Batch630.valid25214
  · exact MergedCutProfiles.Batch630.valid25215
  · exact MergedCutProfiles.Batch630.valid25216
  · exact MergedCutProfiles.Batch630.valid25217
  · exact MergedCutProfiles.Batch630.valid25218
  · exact MergedCutProfiles.Batch630.valid25219
  · exact MergedCutProfiles.Batch630.valid25220
  · exact MergedCutProfiles.Batch630.valid25221
theorem numericValid4204 : retention4204.NumericValid := by decide +kernel
def certificate4204 : RatCutBinCertificate := ⟨⟨retention4204,(2084157149578550967/1000000000000000000),(19343761517970331/100000000000000000),(1616252833998960701/100000000000000000),(3818410446601521484933/1000000000000000000),(246792053077740089/125000000000000000)⟩,(499778843642324683/500000000000000000),(49190952790818147/125000000000000000),(59866325598597523/250000000000000000),(82201331989439081/500000000000000000)⟩
theorem valid4204 : certificate4204.Valid := by decide +kernel
theorem sound4204 : certificate4204.Sound := rat_cut_bin_certificate_sound certificate4204 profilesValid4204 numericValid4204 valid4204

def retention4205 : RatCutRetentionCertificate := ⟨(61/1000),(123/2000),(32000000000000000000/117761590184174009281),(15932137166549552733/1000000000000000000),1,(1538813400421278567269669546560434603/1062142477769970182200000000000000000),false,MergedCutProfiles.Batch630.profile25222,(fun _ => MergedCutProfiles.Batch630.profile25222)⟩
theorem profilesValid4205 : retention4205.ProfilesValid := by
  exact MergedCutProfiles.Batch630.valid25222
theorem numericValid4205 : retention4205.NumericValid := by decide +kernel
def certificate4205 : RatCutBinCertificate := ⟨⟨retention4205,(2084157149578550967/1000000000000000000),(19343761517970331/100000000000000000),(1616252833998960701/100000000000000000),(3818410446601521484933/1000000000000000000),(355959654710821033/250000000000000000)⟩,(499778843642324683/500000000000000000),(339364450312356677/1000000000000000000),(293883105689187079/1000000000000000000),(76787481846654149/200000000000000000)⟩
theorem valid4205 : certificate4205.Valid := by decide +kernel
theorem sound4205 : certificate4205.Sound := rat_cut_bin_certificate_sound certificate4205 profilesValid4205 numericValid4205 valid4205

def retention4206 : RatCutRetentionCertificate := ⟨(61/1000),(123/2000),(1/2),64,1,(255409760745005461774360843045007993799/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch409.profile16377,(fun _ => MergedCutProfiles.Batch409.profile16377)⟩
theorem profilesValid4206 : retention4206.ProfilesValid := by
  exact MergedCutProfiles.Batch409.valid16377
theorem numericValid4206 : retention4206.NumericValid := by decide +kernel
def certificate4206 : RatCutBinCertificate := ⟨⟨retention4206,(2084157149578550967/1000000000000000000),(19343761517970331/100000000000000000),(1616252833998960701/100000000000000000),(3818410446601521484933/1000000000000000000),(972750588218959433/1000000000000000000)⟩,(499778843642324683/500000000000000000),(474789936432350991/1000000000000000000),(171547078693434129/1000000000000000000),(164300665925052919/1000000000000000000)⟩
theorem valid4206 : certificate4206.Valid := by decide +kernel
theorem sound4206 : certificate4206.Sound := rat_cut_bin_certificate_sound certificate4206 profilesValid4206 numericValid4206 valid4206

def retention4207 : RatCutRetentionCertificate := ⟨(61/1000),(123/2000),(32000000000000000000/117761590184174009281),(24176869402093797779/1000000000000000000),1,(7062334045388962346279867795104395477/4835373880418759555800000000000000000),false,MergedCutProfiles.Batch630.profile25222,(fun _ => MergedCutProfiles.Batch630.profile25222)⟩
theorem profilesValid4207 : retention4207.ProfilesValid := by
  exact MergedCutProfiles.Batch630.valid25222
theorem numericValid4207 : retention4207.NumericValid := by decide +kernel
def certificate4207 : RatCutBinCertificate := ⟨⟨retention4207,(1923423214578550967/1000000000000000000),(19343761517970331/100000000000000000),(1616252833998960701/100000000000000000),(3818410446601521484933/1000000000000000000),(1437535830524681511/1000000000000000000)⟩,(999591802494275919/1000000000000000000),(7146071929397853/200000000000000000),(82777317735222863/100000000000000000),(140337331537968767/125000000000000000)⟩
theorem valid4207 : certificate4207.Valid := by decide +kernel
theorem sound4207 : certificate4207.Sound := rat_cut_bin_certificate_sound certificate4207 profilesValid4207 numericValid4207 valid4207

def retention4208 : RatCutRetentionCertificate := ⟨(61/1000),(123/2000),(1/2),64,1,(255409760745005461774360843045007993799/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch409.profile16377,(fun _ => MergedCutProfiles.Batch409.profile16377)⟩
theorem profilesValid4208 : retention4208.ProfilesValid := by
  exact MergedCutProfiles.Batch409.valid16377
theorem numericValid4208 : retention4208.NumericValid := by decide +kernel
def certificate4208 : RatCutBinCertificate := ⟨⟨retention4208,(1923423214578550967/1000000000000000000),(19343761517970331/100000000000000000),(1616252833998960701/100000000000000000),(3818410446601521484933/1000000000000000000),(487337148994485071/500000000000000000)⟩,(999591802494275919/1000000000000000000),(6587286688494059/125000000000000000),(390584458669238783/500000000000000000),(74965411151751653/100000000000000000)⟩
theorem valid4208 : certificate4208.Valid := by decide +kernel
theorem sound4208 : certificate4208.Sound := rat_cut_bin_certificate_sound certificate4208 profilesValid4208 numericValid4208 valid4208

def retention4209 : RatCutRetentionCertificate := ⟨(123/2000),(31/500),(394024002002240219/115511784528821437721),(386260172534300773/500000000000000000),(73/20),(1521244444734521702893/640000000000000000000),true,MergedCutProfiles.Batch630.profile25223,![MergedCutProfiles.Batch630.profile25223,MergedCutProfiles.Batch630.profile25224,MergedCutProfiles.Batch630.profile25225,MergedCutProfiles.Batch630.profile25226,MergedCutProfiles.Batch630.profile25227,MergedCutProfiles.Batch630.profile25228,MergedCutProfiles.Batch630.profile25229,MergedCutProfiles.Batch630.profile25230,MergedCutProfiles.Batch630.profile25231,MergedCutProfiles.Batch630.profile25232,MergedCutProfiles.Batch530.profile21205,MergedCutProfiles.Batch409.profile16381,MergedCutProfiles.Batch630.profile25233,MergedCutProfiles.Batch529.profile21192,MergedCutProfiles.Batch410.profile16429,MergedCutProfiles.Batch630.profile25234]⟩
theorem profilesValid4209 : retention4209.ProfilesValid := by
  change ∀ j : Fin 16, (retention4209.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch630.valid25223
  · exact MergedCutProfiles.Batch630.valid25224
  · exact MergedCutProfiles.Batch630.valid25225
  · exact MergedCutProfiles.Batch630.valid25226
  · exact MergedCutProfiles.Batch630.valid25227
  · exact MergedCutProfiles.Batch630.valid25228
  · exact MergedCutProfiles.Batch630.valid25229
  · exact MergedCutProfiles.Batch630.valid25230
  · exact MergedCutProfiles.Batch630.valid25231
  · exact MergedCutProfiles.Batch630.valid25232
  · exact MergedCutProfiles.Batch530.valid21205
  · exact MergedCutProfiles.Batch409.valid16381
  · exact MergedCutProfiles.Batch630.valid25233
  · exact MergedCutProfiles.Batch529.valid21192
  · exact MergedCutProfiles.Batch410.valid16429
  · exact MergedCutProfiles.Batch630.valid25234
theorem numericValid4209 : retention4209.NumericValid := by decide +kernel
def certificate4209 : RatCutBinCertificate := ⟨⟨retention4209,(2091512834683361927/1000000000000000000),(24651154762240763/125000000000000000),(3262583755059211207/200000000000000000),(3780351506350753384643/1000000000000000000),(1142326970768593/500000000000000)⟩,(999553714358143881/1000000000000000000),(450521266418882757/1000000000000000000),(190255329012016207/1000000000000000000),(1948024941242303/20000000000000000)⟩
theorem valid4209 : certificate4209.Valid := by decide +kernel
theorem sound4209 : certificate4209.Sound := rat_cut_bin_certificate_sound certificate4209 profilesValid4209 numericValid4209 valid4209

def retention4210 : RatCutRetentionCertificate := ⟨(123/2000),(31/500),(559279391500000000/115511784528821437721),(394024002002240219/500000000000000000),(18/5),(1512150979537196397991/640000000000000000000),true,MergedCutProfiles.Batch630.profile25235,![MergedCutProfiles.Batch630.profile25235,MergedCutProfiles.Batch630.profile25236,MergedCutProfiles.Batch630.profile25237,MergedCutProfiles.Batch630.profile25238,MergedCutProfiles.Batch630.profile25229,MergedCutProfiles.Batch630.profile25239,MergedCutProfiles.Batch630.profile25232,MergedCutProfiles.Batch530.profile21225,MergedCutProfiles.Batch410.profile16413,MergedCutProfiles.Batch631.profile25240,MergedCutProfiles.Batch631.profile25241,MergedCutProfiles.Batch631.profile25242,MergedCutProfiles.Batch529.profile21193,MergedCutProfiles.Batch530.profile21239,MergedCutProfiles.Batch631.profile25243,MergedCutProfiles.Batch531.profile21249]⟩
theorem profilesValid4210 : retention4210.ProfilesValid := by
  change ∀ j : Fin 16, (retention4210.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch630.valid25235
  · exact MergedCutProfiles.Batch630.valid25236
  · exact MergedCutProfiles.Batch630.valid25237
  · exact MergedCutProfiles.Batch630.valid25238
  · exact MergedCutProfiles.Batch630.valid25229
  · exact MergedCutProfiles.Batch630.valid25239
  · exact MergedCutProfiles.Batch630.valid25232
  · exact MergedCutProfiles.Batch530.valid21225
  · exact MergedCutProfiles.Batch410.valid16413
  · exact MergedCutProfiles.Batch631.valid25240
  · exact MergedCutProfiles.Batch631.valid25241
  · exact MergedCutProfiles.Batch631.valid25242
  · exact MergedCutProfiles.Batch529.valid21193
  · exact MergedCutProfiles.Batch530.valid21239
  · exact MergedCutProfiles.Batch631.valid25243
  · exact MergedCutProfiles.Batch531.valid21249
theorem numericValid4210 : retention4210.NumericValid := by decide +kernel
def certificate4210 : RatCutBinCertificate := ⟨⟨retention4210,(2091512834683361927/1000000000000000000),(24651154762240763/125000000000000000),(3262583755059211207/200000000000000000),(3780351506350753384643/1000000000000000000),(2271709665890682483/1000000000000000000)⟩,(999553714358143881/1000000000000000000),(448071548773851967/1000000000000000000),(192215260829855229/1000000000000000000),(991700039785399/10000000000000000)⟩
theorem valid4210 : certificate4210.Valid := by decide +kernel
theorem sound4210 : certificate4210.Sound := rat_cut_bin_certificate_sound certificate4210 profilesValid4210 numericValid4210 valid4210

def retention4211 : RatCutRetentionCertificate := ⟨(123/2000),(31/500),(1746878002356292423/231023569057642875442),(1118558783/1000000000),(53/20),(7403033147787175291/3200000000000000000),true,MergedCutProfiles.Batch631.profile25244,![MergedCutProfiles.Batch631.profile25244,MergedCutProfiles.Batch631.profile25245,MergedCutProfiles.Batch530.profile21237,MergedCutProfiles.Batch630.profile25231,MergedCutProfiles.Batch530.profile21205,MergedCutProfiles.Batch631.profile25246,MergedCutProfiles.Batch631.profile25247,MergedCutProfiles.Batch631.profile25248,MergedCutProfiles.Batch530.profile21239,MergedCutProfiles.Batch530.profile21207,MergedCutProfiles.Batch631.profile25249,MergedCutProfiles.Batch531.profile21240,MergedCutProfiles.Batch631.profile25250,MergedCutProfiles.Batch631.profile25251,MergedCutProfiles.Batch411.profile16445,MergedCutProfiles.Batch409.profile16383]⟩
theorem profilesValid4211 : retention4211.ProfilesValid := by
  change ∀ j : Fin 16, (retention4211.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch631.valid25244
  · exact MergedCutProfiles.Batch631.valid25245
  · exact MergedCutProfiles.Batch530.valid21237
  · exact MergedCutProfiles.Batch630.valid25231
  · exact MergedCutProfiles.Batch530.valid21205
  · exact MergedCutProfiles.Batch631.valid25246
  · exact MergedCutProfiles.Batch631.valid25247
  · exact MergedCutProfiles.Batch631.valid25248
  · exact MergedCutProfiles.Batch530.valid21239
  · exact MergedCutProfiles.Batch530.valid21207
  · exact MergedCutProfiles.Batch631.valid25249
  · exact MergedCutProfiles.Batch531.valid21240
  · exact MergedCutProfiles.Batch631.valid25250
  · exact MergedCutProfiles.Batch631.valid25251
  · exact MergedCutProfiles.Batch411.valid16445
  · exact MergedCutProfiles.Batch409.valid16383
theorem numericValid4211 : retention4211.NumericValid := by decide +kernel
def certificate4211 : RatCutBinCertificate := ⟨⟨retention4211,(2091512834683361927/1000000000000000000),(24651154762240763/125000000000000000),(3262583755059211207/200000000000000000),(3780351506350753384643/1000000000000000000),(1123221242579883829/500000000000000000)⟩,(999553714358143881/1000000000000000000),(378532515624426901/1000000000000000000),(63434567708229477/250000000000000000),(167174185566282063/1000000000000000000)⟩
theorem valid4211 : certificate4211.Valid := by decide +kernel
theorem sound4211 : certificate4211.Sound := rat_cut_bin_certificate_sound certificate4211 profilesValid4211 numericValid4211 valid4211

def certificates : List RatCutBinCertificate := [certificate4200,certificate4201,certificate4202,certificate4203,certificate4204,certificate4205,certificate4206,certificate4207,certificate4208,certificate4209,certificate4210,certificate4211]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4200,List.forall_mem_cons.mpr ⟨sound4201,List.forall_mem_cons.mpr ⟨sound4202,List.forall_mem_cons.mpr ⟨sound4203,List.forall_mem_cons.mpr ⟨sound4204,List.forall_mem_cons.mpr ⟨sound4205,List.forall_mem_cons.mpr ⟨sound4206,List.forall_mem_cons.mpr ⟨sound4207,List.forall_mem_cons.mpr ⟨sound4208,List.forall_mem_cons.mpr ⟨sound4209,List.forall_mem_cons.mpr ⟨sound4210,List.forall_mem_cons.mpr ⟨sound4211,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch350
