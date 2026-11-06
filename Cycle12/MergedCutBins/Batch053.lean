import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch105
import Cycle12.MergedCutProfiles.Batch106
import Cycle12.MergedCutProfiles.Batch107
import Cycle12.MergedCutProfiles.Batch108

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch053

def retention636 : RatCutRetentionCertificate := ⟨(11/250),(89/2000),(817291859688725325/24841894796692238297),(404599930538972933/500000000000000000),(31/10),(1359144976135126512417/640000000000000000000),true,MergedCutProfiles.Batch105.profile4229,![MergedCutProfiles.Batch105.profile4229,MergedCutProfiles.Batch105.profile4230,MergedCutProfiles.Batch105.profile4231,MergedCutProfiles.Batch105.profile4232,MergedCutProfiles.Batch105.profile4233,MergedCutProfiles.Batch105.profile4234,MergedCutProfiles.Batch105.profile4235,MergedCutProfiles.Batch105.profile4236,MergedCutProfiles.Batch105.profile4237,MergedCutProfiles.Batch105.profile4238,MergedCutProfiles.Batch105.profile4239,MergedCutProfiles.Batch106.profile4240,MergedCutProfiles.Batch106.profile4241,MergedCutProfiles.Batch106.profile4242,MergedCutProfiles.Batch106.profile4243,MergedCutProfiles.Batch106.profile4244]⟩
theorem profilesValid636 : retention636.ProfilesValid := by
  change ∀ j : Fin 16, (retention636.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch105.valid4229
  · exact MergedCutProfiles.Batch105.valid4230
  · exact MergedCutProfiles.Batch105.valid4231
  · exact MergedCutProfiles.Batch105.valid4232
  · exact MergedCutProfiles.Batch105.valid4233
  · exact MergedCutProfiles.Batch105.valid4234
  · exact MergedCutProfiles.Batch105.valid4235
  · exact MergedCutProfiles.Batch105.valid4236
  · exact MergedCutProfiles.Batch105.valid4237
  · exact MergedCutProfiles.Batch105.valid4238
  · exact MergedCutProfiles.Batch105.valid4239
  · exact MergedCutProfiles.Batch106.valid4240
  · exact MergedCutProfiles.Batch106.valid4241
  · exact MergedCutProfiles.Batch106.valid4242
  · exact MergedCutProfiles.Batch106.valid4243
  · exact MergedCutProfiles.Batch106.valid4244
theorem numericValid636 : retention636.NumericValid := by decide +kernel
def certificate636 : RatCutBinCertificate := ⟨⟨retention636,(262994737541455967/125000000000000000),(23060041821265367/250000000000000000),(12081787966095065807/1000000000000000000),(15048211230393984179/50000000000000000),(8295450905763137/4000000000000000)⟩,(7949072632627987/8000000000000000),(391554203493874509/1000000000000000000),(241310577490621913/1000000000000000000),(126489188737648147/1000000000000000000)⟩
theorem valid636 : certificate636.Valid := by decide +kernel
theorem sound636 : certificate636.Sound := rat_cut_bin_certificate_sound certificate636 profilesValid636 numericValid636 valid636

def retention637 : RatCutRetentionCertificate := ⟨(11/250),(89/2000),(892709745000000000/24841894796692238297),(32691674387549013/40000000000000000),(61/20),(21587855703154305049/10240000000000000000),true,MergedCutProfiles.Batch106.profile4245,![MergedCutProfiles.Batch106.profile4245,MergedCutProfiles.Batch106.profile4246,MergedCutProfiles.Batch106.profile4247,MergedCutProfiles.Batch106.profile4248,MergedCutProfiles.Batch106.profile4249,MergedCutProfiles.Batch106.profile4250,MergedCutProfiles.Batch106.profile4251,MergedCutProfiles.Batch106.profile4252,MergedCutProfiles.Batch106.profile4253,MergedCutProfiles.Batch106.profile4254,MergedCutProfiles.Batch106.profile4240,MergedCutProfiles.Batch106.profile4255,MergedCutProfiles.Batch106.profile4256,MergedCutProfiles.Batch106.profile4257,MergedCutProfiles.Batch106.profile4258,MergedCutProfiles.Batch106.profile4259]⟩
theorem profilesValid637 : retention637.ProfilesValid := by
  change ∀ j : Fin 16, (retention637.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch106.valid4245
  · exact MergedCutProfiles.Batch106.valid4246
  · exact MergedCutProfiles.Batch106.valid4247
  · exact MergedCutProfiles.Batch106.valid4248
  · exact MergedCutProfiles.Batch106.valid4249
  · exact MergedCutProfiles.Batch106.valid4250
  · exact MergedCutProfiles.Batch106.valid4251
  · exact MergedCutProfiles.Batch106.valid4252
  · exact MergedCutProfiles.Batch106.valid4253
  · exact MergedCutProfiles.Batch106.valid4254
  · exact MergedCutProfiles.Batch106.valid4240
  · exact MergedCutProfiles.Batch106.valid4255
  · exact MergedCutProfiles.Batch106.valid4256
  · exact MergedCutProfiles.Batch106.valid4257
  · exact MergedCutProfiles.Batch106.valid4258
  · exact MergedCutProfiles.Batch106.valid4259
theorem numericValid637 : retention637.NumericValid := by decide +kernel
def certificate637 : RatCutBinCertificate := ⟨⟨retention637,(262994737541455967/125000000000000000),(23060041821265367/250000000000000000),(12081787966095065807/1000000000000000000),(15048211230393984179/50000000000000000),(2059190943604974639/1000000000000000000)⟩,(7949072632627987/8000000000000000),(392630878110184827/1000000000000000000),(240302587600737399/1000000000000000000),(31675916958465357/250000000000000000)⟩
theorem valid637 : certificate637.Valid := by decide +kernel
theorem sound637 : certificate637.Sound := rat_cut_bin_certificate_sound certificate637 profilesValid637 numericValid637 valid637

def retention638 : RatCutRetentionCertificate := ⟨(11/250),(89/2000),(977601594865928693/24841894796692238297),(178541949/200000000),(57/20),(16754476917213399367/8000000000000000000),true,MergedCutProfiles.Batch106.profile4260,![MergedCutProfiles.Batch106.profile4260,MergedCutProfiles.Batch106.profile4261,MergedCutProfiles.Batch106.profile4262,MergedCutProfiles.Batch106.profile4263,MergedCutProfiles.Batch105.profile4234,MergedCutProfiles.Batch106.profile4264,MergedCutProfiles.Batch106.profile4265,MergedCutProfiles.Batch106.profile4266,MergedCutProfiles.Batch106.profile4267,MergedCutProfiles.Batch106.profile4240,MergedCutProfiles.Batch106.profile4255,MergedCutProfiles.Batch106.profile4268,MergedCutProfiles.Batch106.profile4269,MergedCutProfiles.Batch106.profile4270,MergedCutProfiles.Batch106.profile4271,MergedCutProfiles.Batch106.profile4272]⟩
theorem profilesValid638 : retention638.ProfilesValid := by
  change ∀ j : Fin 16, (retention638.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch106.valid4260
  · exact MergedCutProfiles.Batch106.valid4261
  · exact MergedCutProfiles.Batch106.valid4262
  · exact MergedCutProfiles.Batch106.valid4263
  · exact MergedCutProfiles.Batch105.valid4234
  · exact MergedCutProfiles.Batch106.valid4264
  · exact MergedCutProfiles.Batch106.valid4265
  · exact MergedCutProfiles.Batch106.valid4266
  · exact MergedCutProfiles.Batch106.valid4267
  · exact MergedCutProfiles.Batch106.valid4240
  · exact MergedCutProfiles.Batch106.valid4255
  · exact MergedCutProfiles.Batch106.valid4268
  · exact MergedCutProfiles.Batch106.valid4269
  · exact MergedCutProfiles.Batch106.valid4270
  · exact MergedCutProfiles.Batch106.valid4271
  · exact MergedCutProfiles.Batch106.valid4272
theorem numericValid638 : retention638.NumericValid := by decide +kernel
def certificate638 : RatCutBinCertificate := ⟨⟨retention638,(262994737541455967/125000000000000000),(23060041821265367/250000000000000000),(12081787966095065807/1000000000000000000),(15048211230393984179/50000000000000000),(1024262314071221431/500000000000000000)⟩,(7949072632627987/8000000000000000),(190063391091389633/500000000000000000),(63048246212453849/250000000000000000),(140283902607257801/1000000000000000000)⟩
theorem valid638 : certificate638.Valid := by decide +kernel
theorem sound638 : certificate638.Sound := rat_cut_bin_certificate_sound certificate638 profilesValid638 numericValid638 valid638

def retention639 : RatCutRetentionCertificate := ⟨(11/250),(89/2000),(1758421376142497022/24841894796692238297),(977601594865928693/1000000000000000000),(53/20),(2547130083414470215741/1280000000000000000000),true,MergedCutProfiles.Batch106.profile4273,![MergedCutProfiles.Batch106.profile4273,MergedCutProfiles.Batch106.profile4274,MergedCutProfiles.Batch106.profile4275,MergedCutProfiles.Batch106.profile4276,MergedCutProfiles.Batch106.profile4267,MergedCutProfiles.Batch106.profile4277,MergedCutProfiles.Batch106.profile4278,MergedCutProfiles.Batch106.profile4279,MergedCutProfiles.Batch107.profile4280,MergedCutProfiles.Batch107.profile4281,MergedCutProfiles.Batch107.profile4282,MergedCutProfiles.Batch107.profile4283,MergedCutProfiles.Batch107.profile4284,MergedCutProfiles.Batch107.profile4285,MergedCutProfiles.Batch107.profile4286,MergedCutProfiles.Batch107.profile4287]⟩
theorem profilesValid639 : retention639.ProfilesValid := by
  change ∀ j : Fin 16, (retention639.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch106.valid4273
  · exact MergedCutProfiles.Batch106.valid4274
  · exact MergedCutProfiles.Batch106.valid4275
  · exact MergedCutProfiles.Batch106.valid4276
  · exact MergedCutProfiles.Batch106.valid4267
  · exact MergedCutProfiles.Batch106.valid4277
  · exact MergedCutProfiles.Batch106.valid4278
  · exact MergedCutProfiles.Batch106.valid4279
  · exact MergedCutProfiles.Batch107.valid4280
  · exact MergedCutProfiles.Batch107.valid4281
  · exact MergedCutProfiles.Batch107.valid4282
  · exact MergedCutProfiles.Batch107.valid4283
  · exact MergedCutProfiles.Batch107.valid4284
  · exact MergedCutProfiles.Batch107.valid4285
  · exact MergedCutProfiles.Batch107.valid4286
  · exact MergedCutProfiles.Batch107.valid4287
theorem numericValid639 : retention639.NumericValid := by decide +kernel
def certificate639 : RatCutBinCertificate := ⟨⟨retention639,(262994737541455967/125000000000000000),(23060041821265367/250000000000000000),(12081787966095065807/1000000000000000000),(15048211230393984179/50000000000000000),(486843366137561499/250000000000000000)⟩,(7949072632627987/8000000000000000),(385469694536261773/1000000000000000000),(247062780496571041/1000000000000000000),(35095486212069077/250000000000000000)⟩
theorem valid639 : certificate639.Valid := by decide +kernel
theorem sound639 : certificate639.Sound := rat_cut_bin_certificate_sound certificate639 profilesValid639 numericValid639 valid639

def retention640 : RatCutRetentionCertificate := ⟨(11/250),(89/2000),(6539496232277305610/24841894796692238297),(879210688071248511/500000000000000000),(17/10),(952346274667501434771/640000000000000000000),true,MergedCutProfiles.Batch105.profile4236,![MergedCutProfiles.Batch105.profile4236,MergedCutProfiles.Batch106.profile4244,MergedCutProfiles.Batch107.profile4288,MergedCutProfiles.Batch107.profile4289,MergedCutProfiles.Batch107.profile4290,MergedCutProfiles.Batch107.profile4291,MergedCutProfiles.Batch107.profile4292,MergedCutProfiles.Batch107.profile4293,MergedCutProfiles.Batch107.profile4294,MergedCutProfiles.Batch107.profile4295,MergedCutProfiles.Batch107.profile4296,MergedCutProfiles.Batch107.profile4297,MergedCutProfiles.Batch107.profile4298,MergedCutProfiles.Batch107.profile4299,MergedCutProfiles.Batch107.profile4300,MergedCutProfiles.Batch107.profile4301]⟩
theorem profilesValid640 : retention640.ProfilesValid := by
  change ∀ j : Fin 16, (retention640.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch105.valid4236
  · exact MergedCutProfiles.Batch106.valid4244
  · exact MergedCutProfiles.Batch107.valid4288
  · exact MergedCutProfiles.Batch107.valid4289
  · exact MergedCutProfiles.Batch107.valid4290
  · exact MergedCutProfiles.Batch107.valid4291
  · exact MergedCutProfiles.Batch107.valid4292
  · exact MergedCutProfiles.Batch107.valid4293
  · exact MergedCutProfiles.Batch107.valid4294
  · exact MergedCutProfiles.Batch107.valid4295
  · exact MergedCutProfiles.Batch107.valid4296
  · exact MergedCutProfiles.Batch107.valid4297
  · exact MergedCutProfiles.Batch107.valid4298
  · exact MergedCutProfiles.Batch107.valid4299
  · exact MergedCutProfiles.Batch107.valid4300
  · exact MergedCutProfiles.Batch107.valid4301
theorem numericValid640 : retention640.NumericValid := by decide +kernel
def certificate640 : RatCutBinCertificate := ⟨⟨retention640,(262994737541455967/125000000000000000),(23060041821265367/250000000000000000),(12081787966095065807/1000000000000000000),(15048211230393984179/50000000000000000),(1460731201121629699/1000000000000000000)⟩,(7949072632627987/8000000000000000),(106058852690345507/250000000000000000),(26499523478900597/125000000000000000),(140454824730669149/1000000000000000000)⟩
theorem valid640 : certificate640.Valid := by decide +kernel
theorem sound640 : certificate640.Sound := rat_cut_bin_certificate_sound certificate640 profilesValid640 numericValid640 valid640

def retention641 : RatCutRetentionCertificate := ⟨(11/250),(89/2000),(11416716734976341601/24841894796692238297),(653949623227730561/100000000000000000),1,(26623853440279818689/25600000000000000000),true,MergedCutProfiles.Batch106.profile4242,![MergedCutProfiles.Batch106.profile4242,MergedCutProfiles.Batch107.profile4302,MergedCutProfiles.Batch107.profile4303,MergedCutProfiles.Batch107.profile4304,MergedCutProfiles.Batch107.profile4305,MergedCutProfiles.Batch107.profile4306,MergedCutProfiles.Batch107.profile4307,MergedCutProfiles.Batch107.profile4308,MergedCutProfiles.Batch107.profile4309,MergedCutProfiles.Batch107.profile4310,MergedCutProfiles.Batch107.profile4311,MergedCutProfiles.Batch107.profile4312,MergedCutProfiles.Batch107.profile4313,MergedCutProfiles.Batch107.profile4314,MergedCutProfiles.Batch107.profile4315,MergedCutProfiles.Batch107.profile4316]⟩
theorem profilesValid641 : retention641.ProfilesValid := by
  change ∀ j : Fin 16, (retention641.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch106.valid4242
  · exact MergedCutProfiles.Batch107.valid4302
  · exact MergedCutProfiles.Batch107.valid4303
  · exact MergedCutProfiles.Batch107.valid4304
  · exact MergedCutProfiles.Batch107.valid4305
  · exact MergedCutProfiles.Batch107.valid4306
  · exact MergedCutProfiles.Batch107.valid4307
  · exact MergedCutProfiles.Batch107.valid4308
  · exact MergedCutProfiles.Batch107.valid4309
  · exact MergedCutProfiles.Batch107.valid4310
  · exact MergedCutProfiles.Batch107.valid4311
  · exact MergedCutProfiles.Batch107.valid4312
  · exact MergedCutProfiles.Batch107.valid4313
  · exact MergedCutProfiles.Batch107.valid4314
  · exact MergedCutProfiles.Batch107.valid4315
  · exact MergedCutProfiles.Batch107.valid4316
theorem numericValid641 : retention641.NumericValid := by decide +kernel
def certificate641 : RatCutBinCertificate := ⟨⟨retention641,(262994737541455967/125000000000000000),(23060041821265367/250000000000000000),(12081787966095065807/1000000000000000000),(15048211230393984179/50000000000000000),(1023930549629127419/1000000000000000000)⟩,(7949072632627987/8000000000000000),(488137257374112067/1000000000000000000),(80895405148680631/500000000000000000),(71127404666385181/500000000000000000)⟩
theorem valid641 : certificate641.Valid := by decide +kernel
theorem sound641 : certificate641.Sound := rat_cut_bin_certificate_sound certificate641 profilesValid641 numericValid641 valid641

def retention642 : RatCutRetentionCertificate := ⟨(11/250),(89/2000),(12240265616559853577/24841894796692238297),(11416716734976341601/1000000000000000000),(21/20),(6160563725517214344061728831825996276213/6088915591987382187200000000000000000000),false,MergedCutProfiles.Batch107.profile4317,(fun _ => MergedCutProfiles.Batch107.profile4317)⟩
theorem profilesValid642 : retention642.ProfilesValid := by
  exact MergedCutProfiles.Batch107.valid4317
theorem numericValid642 : retention642.NumericValid := by decide +kernel
def certificate642 : RatCutBinCertificate := ⟨⟨retention642,(262994737541455967/125000000000000000),(23060041821265367/250000000000000000),(12081787966095065807/1000000000000000000),(15048211230393984179/50000000000000000),(198980085043183821/200000000000000000)⟩,(7949072632627987/8000000000000000),(48344936251326583/100000000000000000),(20646917982338163/125000000000000000),(144079098825351789/1000000000000000000)⟩
theorem valid642 : certificate642.Valid := by decide +kernel
theorem sound642 : certificate642.Sound := rat_cut_bin_certificate_sound certificate642 profilesValid642 numericValid642 valid642

def retention643 : RatCutRetentionCertificate := ⟨(11/250),(89/2000),(12362668272725452113/24841894796692238297),(12240265616559853577/1000000000000000000),(21/20),(19644231938175701031349340177884645363071/19584424986495765723200000000000000000000),false,MergedCutProfiles.Batch107.profile4318,(fun _ => MergedCutProfiles.Batch107.profile4318)⟩
theorem profilesValid643 : retention643.ProfilesValid := by
  exact MergedCutProfiles.Batch107.valid4318
theorem numericValid643 : retention643.NumericValid := by decide +kernel
def certificate643 : RatCutBinCertificate := ⟨⟨retention643,(262994737541455967/125000000000000000),(23060041821265367/250000000000000000),(12081787966095065807/1000000000000000000),(15048211230393984179/50000000000000000),(986187278373479229/1000000000000000000)⟩,(7949072632627987/8000000000000000),(24299889547087937/50000000000000000),(20416229577124277/125000000000000000),(14200892833763129/100000000000000000)⟩
theorem valid643 : certificate643.Valid := by decide +kernel
theorem sound643 : certificate643.Sound := rat_cut_bin_certificate_sound certificate643 profilesValid643 numericValid643 valid643

def retention644 : RatCutRetentionCertificate := ⟨(11/250),(89/2000),(1/2),(12362668272725452113/1000000000000000000),(21/20),(19751685384104320339942717630869717258911/19780269236360723380800000000000000000000),false,MergedCutProfiles.Batch107.profile4319,(fun _ => MergedCutProfiles.Batch107.profile4319)⟩
theorem profilesValid644 : retention644.ProfilesValid := by
  exact MergedCutProfiles.Batch107.valid4319
theorem numericValid644 : retention644.NumericValid := by decide +kernel
def certificate644 : RatCutBinCertificate := ⟨⟨retention644,(262994737541455967/125000000000000000),(23060041821265367/250000000000000000),(12081787966095065807/1000000000000000000),(15048211230393984179/50000000000000000),(981688411668403153/1000000000000000000)⟩,(7949072632627987/8000000000000000),(487987447633459333/1000000000000000000),(161898270235788017/1000000000000000000),(28052027238222377/200000000000000000)⟩
theorem valid644 : certificate644.Valid := by decide +kernel
theorem sound644 : certificate644.Sound := rat_cut_bin_certificate_sound certificate644 profilesValid644 numericValid644 valid644

def retention645 : RatCutRetentionCertificate := ⟨(11/250),(89/2000),(10982972219674038210/24841894796692238297),(1874914729348946183/500000000000000000),(6/5),(12999009273454496628611975494912250877/11718217058430913643750000000000000000),false,MergedCutProfiles.Batch108.profile4320,(fun _ => MergedCutProfiles.Batch108.profile4320)⟩
theorem profilesValid645 : retention645.ProfilesValid := by
  exact MergedCutProfiles.Batch108.valid4320
theorem numericValid645 : retention645.NumericValid := by decide +kernel
def certificate645 : RatCutBinCertificate := ⟨⟨retention645,(310702373916455967/125000000000000000),(23060041821265367/250000000000000000),(12081787966095065807/1000000000000000000),(15048211230393984179/50000000000000000),(2716313762659777/2500000000000000)⟩,(992478433061543411/1000000000000000000),(372513768153066403/1000000000000000000),(64908204141381269/250000000000000000),(19409938043246859/100000000000000000)⟩
theorem valid645 : certificate645.Valid := by decide +kernel
theorem sound645 : certificate645.Sound := rat_cut_bin_certificate_sound certificate645 profilesValid645 numericValid645 valid645

def retention646 : RatCutRetentionCertificate := ⟨(11/250),(89/2000),(12253354457794836116/24841894796692238297),(1098297221967403821/100000000000000000),(21/20),(3944538895896067200529550527946218819/3905056789217435808000000000000000000),false,MergedCutProfiles.Batch108.profile4321,(fun _ => MergedCutProfiles.Batch108.profile4321)⟩
theorem profilesValid646 : retention646.ProfilesValid := by
  exact MergedCutProfiles.Batch108.valid4321
theorem numericValid646 : retention646.NumericValid := by decide +kernel
def certificate646 : RatCutBinCertificate := ⟨⟨retention646,(310702373916455967/125000000000000000),(23060041821265367/250000000000000000),(12081787966095065807/1000000000000000000),(15048211230393984179/50000000000000000),(198036863495153411/200000000000000000)⟩,(992478433061543411/1000000000000000000),(204378974167946491/500000000000000000),(11277651802318847/50000000000000000),(195088912327120043/1000000000000000000)⟩
theorem valid646 : certificate646.Valid := by decide +kernel
theorem sound646 : certificate646.Sound := rat_cut_bin_certificate_sound certificate646 profilesValid646 numericValid646 valid646

def retention647 : RatCutRetentionCertificate := ⟨(11/250),(89/2000),(12375888002372784478/24841894796692238297),(3063338614448709029/250000000000000000),(21/20),(1227808618093778861675230247432344859639/1225335445779483611600000000000000000000),false,MergedCutProfiles.Batch108.profile4322,(fun _ => MergedCutProfiles.Batch108.profile4322)⟩
theorem profilesValid647 : retention647.ProfilesValid := by
  exact MergedCutProfiles.Batch108.valid4322
theorem numericValid647 : retention647.NumericValid := by decide +kernel
def certificate647 : RatCutBinCertificate := ⟨⟨retention647,(310702373916455967/125000000000000000),(23060041821265367/250000000000000000),(12081787966095065807/1000000000000000000),(15048211230393984179/50000000000000000),(491046114086182233/500000000000000000)⟩,(992478433061543411/1000000000000000000),(82425193576572153/200000000000000000),(222553836563856269/1000000000000000000),(192542651025139429/1000000000000000000)⟩
theorem valid647 : certificate647.Valid := by decide +kernel
theorem sound647 : certificate647.Sound := rat_cut_bin_certificate_sound certificate647 profilesValid647 numericValid647 valid647

def certificates : List RatCutBinCertificate := [certificate636,certificate637,certificate638,certificate639,certificate640,certificate641,certificate642,certificate643,certificate644,certificate645,certificate646,certificate647]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound636,List.forall_mem_cons.mpr ⟨sound637,List.forall_mem_cons.mpr ⟨sound638,List.forall_mem_cons.mpr ⟨sound639,List.forall_mem_cons.mpr ⟨sound640,List.forall_mem_cons.mpr ⟨sound641,List.forall_mem_cons.mpr ⟨sound642,List.forall_mem_cons.mpr ⟨sound643,List.forall_mem_cons.mpr ⟨sound644,List.forall_mem_cons.mpr ⟨sound645,List.forall_mem_cons.mpr ⟨sound646,List.forall_mem_cons.mpr ⟨sound647,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch053
