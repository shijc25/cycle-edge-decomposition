import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch203
import Cycle12.MergedCutProfiles.Batch204
import Cycle12.MergedCutProfiles.Batch205

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch103

def retention1236 : RatCutRetentionCertificate := ⟨(57/1000),(229/4000),(6926159471558550913/13945916804907706299),(6460153988903492317/1000000000000000000),(21/20),(10234333092260464516972146235229548990631/10336246382245587707200000000000000000000),false,MergedCutProfiles.Batch203.profile8145,(fun _ => MergedCutProfiles.Batch203.profile8145)⟩
theorem profilesValid1236 : retention1236.ProfilesValid := by
  exact MergedCutProfiles.Batch203.valid8145
theorem numericValid1236 : retention1236.NumericValid := by decide +kernel
def certificate1236 : RatCutBinCertificate := ⟨⟨retention1236,(652886521547612741/250000000000000000),(163394722365440633/1000000000000000000),(15026486207675484803/1000000000000000000),(52468180930640026063/250000000000000000),(240079882798906791/250000000000000000)⟩,(1979094719004583/2000000000000000),(51778032521637661/125000000000000000),(5517481150567911/25000000000000000),(87940048334530511/500000000000000000)⟩
theorem valid1236 : certificate1236.Valid := by decide +kernel
theorem sound1236 : certificate1236.Sound := rat_cut_bin_certificate_sound certificate1236 profilesValid1236 numericValid1236 valid1236

def retention1237 : RatCutRetentionCertificate := ⟨(57/1000),(229/4000),(1/2),(6926159471558550913/1000000000000000000),(21/20),(10927714290105261900208506006130662595751/11081855154493681460800000000000000000000),false,MergedCutProfiles.Batch203.profile8143,(fun _ => MergedCutProfiles.Batch203.profile8143)⟩
theorem profilesValid1237 : retention1237.ProfilesValid := by
  exact MergedCutProfiles.Batch203.valid8143
theorem numericValid1237 : retention1237.NumericValid := by decide +kernel
def certificate1237 : RatCutBinCertificate := ⟨⟨retention1237,(652886521547612741/250000000000000000),(163394722365440633/1000000000000000000),(15026486207675484803/1000000000000000000),(52468180930640026063/250000000000000000),(478135128430700969/500000000000000000)⟩,(1979094719004583/2000000000000000),(207989135124246527/500000000000000000),(109578553774513561/500000000000000000),(2740724123975947/15625000000000000)⟩
theorem valid1237 : certificate1237.Valid := by decide +kernel
theorem sound1237 : certificate1237.Sound := rat_cut_bin_certificate_sound certificate1237 profilesValid1237 numericValid1237 valid1237

def retention1238 : RatCutRetentionCertificate := ⟨(229/4000),(459/8000),(911474784539716238/13874792665248591837),(425074493975244737/500000000000000000),(14/5),(1282279415252626279229/640000000000000000000),true,MergedCutProfiles.Batch203.profile8146,![MergedCutProfiles.Batch203.profile8146,MergedCutProfiles.Batch203.profile8147,MergedCutProfiles.Batch203.profile8148,MergedCutProfiles.Batch203.profile8149,MergedCutProfiles.Batch203.profile8150,MergedCutProfiles.Batch203.profile8151,MergedCutProfiles.Batch203.profile8152,MergedCutProfiles.Batch203.profile8153,MergedCutProfiles.Batch203.profile8154,MergedCutProfiles.Batch203.profile8155,MergedCutProfiles.Batch203.profile8156,MergedCutProfiles.Batch203.profile8157,MergedCutProfiles.Batch203.profile8158,MergedCutProfiles.Batch203.profile8159,MergedCutProfiles.Batch204.profile8160,MergedCutProfiles.Batch204.profile8161]⟩
theorem profilesValid1238 : retention1238.ProfilesValid := by
  change ∀ j : Fin 16, (retention1238.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch203.valid8146
  · exact MergedCutProfiles.Batch203.valid8147
  · exact MergedCutProfiles.Batch203.valid8148
  · exact MergedCutProfiles.Batch203.valid8149
  · exact MergedCutProfiles.Batch203.valid8150
  · exact MergedCutProfiles.Batch203.valid8151
  · exact MergedCutProfiles.Batch203.valid8152
  · exact MergedCutProfiles.Batch203.valid8153
  · exact MergedCutProfiles.Batch203.valid8154
  · exact MergedCutProfiles.Batch203.valid8155
  · exact MergedCutProfiles.Batch203.valid8156
  · exact MergedCutProfiles.Batch203.valid8157
  · exact MergedCutProfiles.Batch203.valid8158
  · exact MergedCutProfiles.Batch203.valid8159
  · exact MergedCutProfiles.Batch204.valid8160
  · exact MergedCutProfiles.Batch204.valid8161
theorem numericValid1238 : retention1238.NumericValid := by decide +kernel
def certificate1238 : RatCutBinCertificate := ⟨⟨retention1238,(455981042612878479/200000000000000000),(16422872969426287/100000000000000000),(15093535518074265943/1000000000000000000),(41915401615407667629/200000000000000000),(483519752256304391/250000000000000000)⟩,(990882090553383841/1000000000000000000),(356807519382912521/1000000000000000000),(68869140466481401/250000000000000000),(145875530232495203/1000000000000000000)⟩
theorem valid1238 : certificate1238.Valid := by decide +kernel
theorem sound1238 : certificate1238.Sound := rat_cut_bin_certificate_sound certificate1238 profilesValid1238 numericValid1238 valid1238

def retention1239 : RatCutRetentionCertificate := ⟨(229/4000),(459/8000),(1317150765437790631/13874792665248591837),(455737392269858119/500000000000000000),(13/5),(306304602043438498191/160000000000000000000),true,MergedCutProfiles.Batch204.profile8162,![MergedCutProfiles.Batch204.profile8162,MergedCutProfiles.Batch204.profile8163,MergedCutProfiles.Batch204.profile8164,MergedCutProfiles.Batch204.profile8165,MergedCutProfiles.Batch204.profile8166,MergedCutProfiles.Batch204.profile8167,MergedCutProfiles.Batch204.profile8168,MergedCutProfiles.Batch204.profile8169,MergedCutProfiles.Batch203.profile8158,MergedCutProfiles.Batch204.profile8170,MergedCutProfiles.Batch204.profile8171,MergedCutProfiles.Batch204.profile8172,MergedCutProfiles.Batch204.profile8173,MergedCutProfiles.Batch204.profile8174,MergedCutProfiles.Batch204.profile8175,MergedCutProfiles.Batch204.profile8176]⟩
theorem profilesValid1239 : retention1239.ProfilesValid := by
  change ∀ j : Fin 16, (retention1239.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch204.valid8162
  · exact MergedCutProfiles.Batch204.valid8163
  · exact MergedCutProfiles.Batch204.valid8164
  · exact MergedCutProfiles.Batch204.valid8165
  · exact MergedCutProfiles.Batch204.valid8166
  · exact MergedCutProfiles.Batch204.valid8167
  · exact MergedCutProfiles.Batch204.valid8168
  · exact MergedCutProfiles.Batch204.valid8169
  · exact MergedCutProfiles.Batch203.valid8158
  · exact MergedCutProfiles.Batch204.valid8170
  · exact MergedCutProfiles.Batch204.valid8171
  · exact MergedCutProfiles.Batch204.valid8172
  · exact MergedCutProfiles.Batch204.valid8173
  · exact MergedCutProfiles.Batch204.valid8174
  · exact MergedCutProfiles.Batch204.valid8175
  · exact MergedCutProfiles.Batch204.valid8176
theorem numericValid1239 : retention1239.NumericValid := by decide +kernel
def certificate1239 : RatCutBinCertificate := ⟨⟨retention1239,(455981042612878479/200000000000000000),(16422872969426287/100000000000000000),(15093535518074265943/1000000000000000000),(41915401615407667629/200000000000000000),(1849884131884989323/1000000000000000000)⟩,(990882090553383841/1000000000000000000),(90700998048380679/250000000000000000),(269347709014776339/1000000000000000000),(145780030881172877/1000000000000000000)⟩
theorem valid1239 : certificate1239.Valid := by decide +kernel
theorem sound1239 : certificate1239.Sound := rat_cut_bin_certificate_sound certificate1239 profilesValid1239 numericValid1239 valid1239

def retention1240 : RatCutRetentionCertificate := ⟨(229/4000),(459/8000),(3161668857650455526/13874792665248591837),(1317150765437790631/1000000000000000000),(19/10),(2001869819689932004187/1280000000000000000000),true,MergedCutProfiles.Batch204.profile8177,![MergedCutProfiles.Batch204.profile8177,MergedCutProfiles.Batch204.profile8178,MergedCutProfiles.Batch204.profile8179,MergedCutProfiles.Batch204.profile8180,MergedCutProfiles.Batch204.profile8172,MergedCutProfiles.Batch204.profile8181,MergedCutProfiles.Batch204.profile8182,MergedCutProfiles.Batch204.profile8183,MergedCutProfiles.Batch204.profile8184,MergedCutProfiles.Batch204.profile8185,MergedCutProfiles.Batch204.profile8186,MergedCutProfiles.Batch204.profile8187,MergedCutProfiles.Batch204.profile8188,MergedCutProfiles.Batch204.profile8189,MergedCutProfiles.Batch204.profile8190,MergedCutProfiles.Batch204.profile8191]⟩
theorem profilesValid1240 : retention1240.ProfilesValid := by
  change ∀ j : Fin 16, (retention1240.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch204.valid8177
  · exact MergedCutProfiles.Batch204.valid8178
  · exact MergedCutProfiles.Batch204.valid8179
  · exact MergedCutProfiles.Batch204.valid8180
  · exact MergedCutProfiles.Batch204.valid8172
  · exact MergedCutProfiles.Batch204.valid8181
  · exact MergedCutProfiles.Batch204.valid8182
  · exact MergedCutProfiles.Batch204.valid8183
  · exact MergedCutProfiles.Batch204.valid8184
  · exact MergedCutProfiles.Batch204.valid8185
  · exact MergedCutProfiles.Batch204.valid8186
  · exact MergedCutProfiles.Batch204.valid8187
  · exact MergedCutProfiles.Batch204.valid8188
  · exact MergedCutProfiles.Batch204.valid8189
  · exact MergedCutProfiles.Batch204.valid8190
  · exact MergedCutProfiles.Batch204.valid8191
theorem numericValid1240 : retention1240.NumericValid := by decide +kernel
def certificate1240 : RatCutBinCertificate := ⟨⟨retention1240,(455981042612878479/200000000000000000),(16422872969426287/100000000000000000),(15093535518074265943/1000000000000000000),(41915401615407667629/200000000000000000),(379203165584658469/250000000000000000)⟩,(990882090553383841/1000000000000000000),(77826472136496309/200000000000000000),(6089718708644611/25000000000000000),(14584013765344523/100000000000000000)⟩
theorem valid1240 : certificate1240.Valid := by decide +kernel
theorem sound1240 : certificate1240.Sound := rat_cut_bin_certificate_sound certificate1240 profilesValid1240 numericValid1240 valid1240

def retention1241 : RatCutRetentionCertificate := ⟨(229/4000),(459/8000),(5917836058721945282/13874792665248591837),(1580834428825227763/500000000000000000),(23/20),(716787993263442883571/640000000000000000000),true,MergedCutProfiles.Batch204.profile8192,![MergedCutProfiles.Batch204.profile8192,MergedCutProfiles.Batch204.profile8193,MergedCutProfiles.Batch204.profile8194,MergedCutProfiles.Batch204.profile8195,MergedCutProfiles.Batch204.profile8196,MergedCutProfiles.Batch204.profile8197,MergedCutProfiles.Batch204.profile8198,MergedCutProfiles.Batch204.profile8199,MergedCutProfiles.Batch205.profile8200,MergedCutProfiles.Batch205.profile8201,MergedCutProfiles.Batch205.profile8202,MergedCutProfiles.Batch205.profile8203,MergedCutProfiles.Batch205.profile8204,MergedCutProfiles.Batch205.profile8205,MergedCutProfiles.Batch205.profile8206,MergedCutProfiles.Batch205.profile8207]⟩
theorem profilesValid1241 : retention1241.ProfilesValid := by
  change ∀ j : Fin 16, (retention1241.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch204.valid8192
  · exact MergedCutProfiles.Batch204.valid8193
  · exact MergedCutProfiles.Batch204.valid8194
  · exact MergedCutProfiles.Batch204.valid8195
  · exact MergedCutProfiles.Batch204.valid8196
  · exact MergedCutProfiles.Batch204.valid8197
  · exact MergedCutProfiles.Batch204.valid8198
  · exact MergedCutProfiles.Batch204.valid8199
  · exact MergedCutProfiles.Batch205.valid8200
  · exact MergedCutProfiles.Batch205.valid8201
  · exact MergedCutProfiles.Batch205.valid8202
  · exact MergedCutProfiles.Batch205.valid8203
  · exact MergedCutProfiles.Batch205.valid8204
  · exact MergedCutProfiles.Batch205.valid8205
  · exact MergedCutProfiles.Batch205.valid8206
  · exact MergedCutProfiles.Batch205.valid8207
theorem numericValid1241 : retention1241.NumericValid := by decide +kernel
def certificate1241 : RatCutBinCertificate := ⟨⟨retention1241,(455981042612878479/200000000000000000),(16422872969426287/100000000000000000),(15093535518074265943/1000000000000000000),(41915401615407667629/200000000000000000),(1091446995227406883/1000000000000000000)⟩,(990882090553383841/1000000000000000000),(221812162866364013/500000000000000000),(97903799542569613/500000000000000000),(72924063559735939/500000000000000000)⟩
theorem valid1241 : certificate1241.Valid := by decide +kernel
theorem sound1241 : certificate1241.Sound := rat_cut_bin_certificate_sound certificate1241 profilesValid1241 numericValid1241 valid1241

def retention1242 : RatCutRetentionCertificate := ⟨(229/4000),(459/8000),(6735049453137267062/13874792665248591837),(2958918029360972641/500000000000000000),(11/10),(605228953335535994407404560998896665239/591783605872194528200000000000000000000),false,MergedCutProfiles.Batch205.profile8208,(fun _ => MergedCutProfiles.Batch205.profile8208)⟩
theorem profilesValid1242 : retention1242.ProfilesValid := by
  exact MergedCutProfiles.Batch205.valid8208
theorem numericValid1242 : retention1242.NumericValid := by decide +kernel
def certificate1242 : RatCutBinCertificate := ⟨⟨retention1242,(455981042612878479/200000000000000000),(16422872969426287/100000000000000000),(15093535518074265943/1000000000000000000),(41915401615407667629/200000000000000000),(995429011758545529/1000000000000000000)⟩,(990882090553383841/1000000000000000000),(450984361963340647/1000000000000000000),(189886321834933679/1000000000000000000),(37343581270202867/250000000000000000)⟩
theorem valid1242 : certificate1242.Valid := by decide +kernel
theorem sound1242 : certificate1242.Sound := rat_cut_bin_certificate_sound certificate1242 profilesValid1242 numericValid1242 valid1242

def retention1243 : RatCutRetentionCertificate := ⟨(229/4000),(459/8000),(6870423947145326131/13874792665248591837),(3367524726568633531/500000000000000000),(21/20),(2678875589233198161413469897018367024239/2694019781254906824800000000000000000000),false,MergedCutProfiles.Batch205.profile8209,(fun _ => MergedCutProfiles.Batch205.profile8209)⟩
theorem profilesValid1243 : retention1243.ProfilesValid := by
  exact MergedCutProfiles.Batch205.valid8209
theorem numericValid1243 : retention1243.NumericValid := by decide +kernel
def certificate1243 : RatCutBinCertificate := ⟨⟨retention1243,(455981042612878479/200000000000000000),(16422872969426287/100000000000000000),(15093535518074265943/1000000000000000000),(41915401615407667629/200000000000000000),(121041038878710927/125000000000000000)⟩,(990882090553383841/1000000000000000000),(458536404250396171/1000000000000000000),(91967700651701261/500000000000000000),(148587217678846253/1000000000000000000)⟩
theorem valid1243 : certificate1243.Valid := by decide +kernel
theorem sound1243 : certificate1243.Sound := rat_cut_bin_certificate_sound certificate1243 profilesValid1243 numericValid1243 valid1243

def retention1244 : RatCutRetentionCertificate := ⟨(229/4000),(459/8000),(1/2),(6870423947145326131/1000000000000000000),(21/20),(10836946841645510226543993798448493456399/10992678315432521809600000000000000000000),false,MergedCutProfiles.Batch205.profile8210,(fun _ => MergedCutProfiles.Batch205.profile8210)⟩
theorem profilesValid1244 : retention1244.ProfilesValid := by
  exact MergedCutProfiles.Batch205.valid8210
theorem numericValid1244 : retention1244.NumericValid := by decide +kernel
def certificate1244 : RatCutBinCertificate := ⟨⟨retention1244,(455981042612878479/200000000000000000),(16422872969426287/100000000000000000),(15093535518074265943/1000000000000000000),(41915401615407667629/200000000000000000),(959782942485414939/1000000000000000000)⟩,(990882090553383841/1000000000000000000),(461889139987919511/1000000000000000000),(90666735359768497/500000000000000000),(2913415753134761/20000000000000000)⟩
theorem valid1244 : certificate1244.Valid := by decide +kernel
theorem sound1244 : certificate1244.Sound := rat_cut_bin_certificate_sound certificate1244 profilesValid1244 numericValid1244 valid1244

def retention1245 : RatCutRetentionCertificate := ⟨(229/4000),(459/8000),(1/2),64,1,(255404148382492260236675510576610915039/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch205.profile8210,(fun _ => MergedCutProfiles.Batch205.profile8210)⟩
theorem profilesValid1245 : retention1245.ProfilesValid := by
  exact MergedCutProfiles.Batch205.valid8210
theorem numericValid1245 : retention1245.NumericValid := by decide +kernel
def certificate1245 : RatCutBinCertificate := ⟨⟨retention1245,(455981042612878479/200000000000000000),(16422872969426287/100000000000000000),(15093535518074265943/1000000000000000000),(41915401615407667629/200000000000000000),(972865111037419929/1000000000000000000)⟩,(990882090553383841/1000000000000000000),(211851266244246833/500000000000000000),(106226718657730233/500000000000000000),(4034399464542669/20000000000000000)⟩
theorem valid1245 : certificate1245.Valid := by decide +kernel
theorem sound1245 : certificate1245.Sound := rat_cut_bin_certificate_sound certificate1245 profilesValid1245 numericValid1245 valid1245

def retention1246 : RatCutRetentionCertificate := ⟨(229/4000),(459/8000),(6408926202111205327/13874792665248591837),(3634686560602250633/1000000000000000000),(6/5),(97211732531780602558721475433688405709/90867164015056265825000000000000000000),false,MergedCutProfiles.Batch205.profile8211,(fun _ => MergedCutProfiles.Batch205.profile8211)⟩
theorem profilesValid1246 : retention1246.ProfilesValid := by
  exact MergedCutProfiles.Batch205.valid8211
theorem numericValid1246 : retention1246.NumericValid := by decide +kernel
def certificate1246 : RatCutBinCertificate := ⟨⟨retention1246,(522847955412878479/200000000000000000),(16422872969426287/100000000000000000),(15093535518074265943/1000000000000000000),(41915401615407667629/200000000000000000),(64730156812118913/62500000000000000)⟩,(197908454686327313/200000000000000000),(382261898178292681/1000000000000000000),(125066963351078093/500000000000000000),(35629038771757333/200000000000000000)⟩
theorem valid1246 : certificate1246.Valid := by decide +kernel
theorem sound1246 : certificate1246.Sound := rat_cut_bin_certificate_sound certificate1246 profilesValid1246 numericValid1246 valid1246

def retention1247 : RatCutRetentionCertificate := ⟨(229/4000),(459/8000),(6871236350328339463/13874792665248591837),(6408926202111205327/1000000000000000000),(21/20),(10177781444433945968603405030467793433671/10254281923377928523200000000000000000000),false,MergedCutProfiles.Batch205.profile8212,(fun _ => MergedCutProfiles.Batch205.profile8212)⟩
theorem profilesValid1247 : retention1247.ProfilesValid := by
  exact MergedCutProfiles.Batch205.valid8212
theorem numericValid1247 : retention1247.NumericValid := by decide +kernel
def certificate1247 : RatCutBinCertificate := ⟨⟨retention1247,(522847955412878479/200000000000000000),(16422872969426287/100000000000000000),(15093535518074265943/1000000000000000000),(41915401615407667629/200000000000000000),(481334545013554553/500000000000000000)⟩,(197908454686327313/200000000000000000),(411254465214954759/1000000000000000000),(27915907030706743/125000000000000000),(178186354410770927/1000000000000000000)⟩
theorem valid1247 : certificate1247.Valid := by decide +kernel
theorem sound1247 : certificate1247.Sound := rat_cut_bin_certificate_sound certificate1247 profilesValid1247 numericValid1247 valid1247

def certificates : List RatCutBinCertificate := [certificate1236,certificate1237,certificate1238,certificate1239,certificate1240,certificate1241,certificate1242,certificate1243,certificate1244,certificate1245,certificate1246,certificate1247]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1236,List.forall_mem_cons.mpr ⟨sound1237,List.forall_mem_cons.mpr ⟨sound1238,List.forall_mem_cons.mpr ⟨sound1239,List.forall_mem_cons.mpr ⟨sound1240,List.forall_mem_cons.mpr ⟨sound1241,List.forall_mem_cons.mpr ⟨sound1242,List.forall_mem_cons.mpr ⟨sound1243,List.forall_mem_cons.mpr ⟨sound1244,List.forall_mem_cons.mpr ⟨sound1245,List.forall_mem_cons.mpr ⟨sound1246,List.forall_mem_cons.mpr ⟨sound1247,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch103
