import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch419
import Cycle12.MergedCutProfiles.Batch544
import Cycle12.MergedCutProfiles.Batch545
import Cycle12.MergedCutProfiles.Batch632
import Cycle12.MergedCutProfiles.Batch633
import Cycle12.MergedCutProfiles.Batch634

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch352

def retention4224 : RatCutRetentionCertificate := ⟨(31/500),(63/1000),(12800000000000000000/44471963983586701429),(2987928939751716707/125000000000000000),1,(27255238680036712718981776541735720667/19122745214410986924800000000000000000),false,MergedCutProfiles.Batch632.profile25309,(fun _ => MergedCutProfiles.Batch632.profile25309)⟩
theorem profilesValid4224 : retention4224.ProfilesValid := by
  exact MergedCutProfiles.Batch632.valid25309
theorem numericValid4224 : retention4224.NumericValid := by decide +kernel
def certificate4224 : RatCutBinCertificate := ⟨⟨retention4224,(964732003685437663/500000000000000000),(204909449857824037/1000000000000000000),(16465437042510239339/1000000000000000000),(1842051788571481264403/500000000000000000),(280253332346620617/200000000000000000)⟩,(124947439169797339/125000000000000000),(4551073875142771/125000000000000000),(165169547006026801/200000000000000000),(1092676475530456823/1000000000000000000)⟩
theorem valid4224 : certificate4224.Valid := by decide +kernel
theorem sound4224 : certificate4224.Sound := rat_cut_bin_certificate_sound certificate4224 profilesValid4224 numericValid4224 valid4224

def retention4225 : RatCutRetentionCertificate := ⟨(31/500),(63/1000),(1/2),64,1,(255411314097293059585699365940977515079/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch632.profile25310,(fun _ => MergedCutProfiles.Batch632.profile25310)⟩
theorem profilesValid4225 : retention4225.ProfilesValid := by
  exact MergedCutProfiles.Batch632.valid25310
theorem numericValid4225 : retention4225.NumericValid := by decide +kernel
def certificate4225 : RatCutBinCertificate := ⟨⟨retention4225,(964732003685437663/500000000000000000),(204909449857824037/1000000000000000000),(16465437042510239339/1000000000000000000),(1842051788571481264403/500000000000000000),(19473771734787163/20000000000000000)⟩,(124947439169797339/125000000000000000),(26198389025706623/500000000000000000),(390984773654663993/500000000000000000),(187416377619964459/250000000000000000)⟩
theorem valid4225 : certificate4225.Valid := by decide +kernel
theorem sound4225 : certificate4225.Sound := rat_cut_bin_certificate_sound certificate4225 profilesValid4225 numericValid4225 valid4225

def retention4226 : RatCutRetentionCertificate := ⟨(63/1000),(127/2000),(801465800533037795/218188507452612423284),(793530495577265143/1000000000000000000),(71/20),(3037016814981414274631/1280000000000000000000),true,MergedCutProfiles.Batch632.profile25311,![MergedCutProfiles.Batch632.profile25311,MergedCutProfiles.Batch632.profile25312,MergedCutProfiles.Batch632.profile25313,MergedCutProfiles.Batch632.profile25314,MergedCutProfiles.Batch632.profile25315,MergedCutProfiles.Batch632.profile25316,MergedCutProfiles.Batch632.profile25317,MergedCutProfiles.Batch632.profile25318,MergedCutProfiles.Batch632.profile25319,MergedCutProfiles.Batch633.profile25320,MergedCutProfiles.Batch633.profile25321,MergedCutProfiles.Batch633.profile25322,MergedCutProfiles.Batch633.profile25323,MergedCutProfiles.Batch633.profile25324,MergedCutProfiles.Batch633.profile25325,MergedCutProfiles.Batch633.profile25326]⟩
theorem profilesValid4226 : retention4226.ProfilesValid := by
  change ∀ j : Fin 16, (retention4226.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch632.valid25311
  · exact MergedCutProfiles.Batch632.valid25312
  · exact MergedCutProfiles.Batch632.valid25313
  · exact MergedCutProfiles.Batch632.valid25314
  · exact MergedCutProfiles.Batch632.valid25315
  · exact MergedCutProfiles.Batch632.valid25316
  · exact MergedCutProfiles.Batch632.valid25317
  · exact MergedCutProfiles.Batch632.valid25318
  · exact MergedCutProfiles.Batch632.valid25319
  · exact MergedCutProfiles.Batch633.valid25320
  · exact MergedCutProfiles.Batch633.valid25321
  · exact MergedCutProfiles.Batch633.valid25322
  · exact MergedCutProfiles.Batch633.valid25323
  · exact MergedCutProfiles.Batch633.valid25324
  · exact MergedCutProfiles.Batch633.valid25325
  · exact MergedCutProfiles.Batch633.valid25326
theorem numericValid4226 : retention4226.NumericValid := by decide +kernel
def certificate4226 : RatCutBinCertificate := ⟨⟨retention4226,(2113714005816501513/1000000000000000000),(2610492019033761/12500000000000000),(16777018063336665559/1000000000000000000),(91800435768608139787/25000000000000000),(569815515651277833/250000000000000000)⟩,(999542269922698689/1000000000000000000),(107011875993402771/250000000000000000),(52186148220934413/250000000000000000),(109086866681029821/1000000000000000000)⟩
theorem valid4226 : certificate4226.Valid := by decide +kernel
theorem sound4226 : certificate4226.Sound := rat_cut_bin_certificate_sound certificate4226 profilesValid4226 numericValid4226 valid4226

def retention4227 : RatCutRetentionCertificate := ⟨(63/1000),(127/2000),(280196186000000000/54547126863153105821),(160293160106607559/200000000000000000),(7/2),(602823097728663570227/256000000000000000000),true,MergedCutProfiles.Batch633.profile25327,![MergedCutProfiles.Batch633.profile25327,MergedCutProfiles.Batch633.profile25328,MergedCutProfiles.Batch633.profile25329,MergedCutProfiles.Batch633.profile25330,MergedCutProfiles.Batch632.profile25317,MergedCutProfiles.Batch633.profile25331,MergedCutProfiles.Batch633.profile25332,MergedCutProfiles.Batch633.profile25333,MergedCutProfiles.Batch633.profile25334,MergedCutProfiles.Batch633.profile25324,MergedCutProfiles.Batch633.profile25335,MergedCutProfiles.Batch633.profile25336,MergedCutProfiles.Batch633.profile25337,MergedCutProfiles.Batch633.profile25338,MergedCutProfiles.Batch633.profile25339,MergedCutProfiles.Batch633.profile25340]⟩
theorem profilesValid4227 : retention4227.ProfilesValid := by
  change ∀ j : Fin 16, (retention4227.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch633.valid25327
  · exact MergedCutProfiles.Batch633.valid25328
  · exact MergedCutProfiles.Batch633.valid25329
  · exact MergedCutProfiles.Batch633.valid25330
  · exact MergedCutProfiles.Batch632.valid25317
  · exact MergedCutProfiles.Batch633.valid25331
  · exact MergedCutProfiles.Batch633.valid25332
  · exact MergedCutProfiles.Batch633.valid25333
  · exact MergedCutProfiles.Batch633.valid25334
  · exact MergedCutProfiles.Batch633.valid25324
  · exact MergedCutProfiles.Batch633.valid25335
  · exact MergedCutProfiles.Batch633.valid25336
  · exact MergedCutProfiles.Batch633.valid25337
  · exact MergedCutProfiles.Batch633.valid25338
  · exact MergedCutProfiles.Batch633.valid25339
  · exact MergedCutProfiles.Batch633.valid25340
theorem numericValid4227 : retention4227.NumericValid := by decide +kernel
def certificate4227 : RatCutBinCertificate := ⟨⟨retention4227,(2113714005816501513/1000000000000000000),(2610492019033761/12500000000000000),(16777018063336665559/1000000000000000000),(91800435768608139787/25000000000000000),(2262685989628411403/1000000000000000000)⟩,(999542269922698689/1000000000000000000),(85765800390253809/200000000000000000),(104041101049929053/500000000000000000),(109265227920371261/1000000000000000000)⟩
theorem valid4227 : certificate4227.Valid := by decide +kernel
theorem sound4227 : certificate4227.Sound := rat_cut_bin_certificate_sound certificate4227 profilesValid4227 numericValid4227 valid4227

def retention4228 : RatCutRetentionCertificate := ⟨(63/1000),(127/2000),(1608352209531381689/218188507452612423284),(140098093/125000000),(53/20),(37093722994083526661/16000000000000000000),true,MergedCutProfiles.Batch632.profile25312,![MergedCutProfiles.Batch632.profile25312,MergedCutProfiles.Batch632.profile25314,MergedCutProfiles.Batch632.profile25316,MergedCutProfiles.Batch632.profile25318,MergedCutProfiles.Batch633.profile25320,MergedCutProfiles.Batch633.profile25322,MergedCutProfiles.Batch633.profile25324,MergedCutProfiles.Batch633.profile25326,MergedCutProfiles.Batch633.profile25341,MergedCutProfiles.Batch633.profile25342,MergedCutProfiles.Batch633.profile25343,MergedCutProfiles.Batch633.profile25344,MergedCutProfiles.Batch633.profile25345,MergedCutProfiles.Batch633.profile25346,MergedCutProfiles.Batch633.profile25347,MergedCutProfiles.Batch633.profile25348]⟩
theorem profilesValid4228 : retention4228.ProfilesValid := by
  change ∀ j : Fin 16, (retention4228.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch632.valid25312
  · exact MergedCutProfiles.Batch632.valid25314
  · exact MergedCutProfiles.Batch632.valid25316
  · exact MergedCutProfiles.Batch632.valid25318
  · exact MergedCutProfiles.Batch633.valid25320
  · exact MergedCutProfiles.Batch633.valid25322
  · exact MergedCutProfiles.Batch633.valid25324
  · exact MergedCutProfiles.Batch633.valid25326
  · exact MergedCutProfiles.Batch633.valid25341
  · exact MergedCutProfiles.Batch633.valid25342
  · exact MergedCutProfiles.Batch633.valid25343
  · exact MergedCutProfiles.Batch633.valid25344
  · exact MergedCutProfiles.Batch633.valid25345
  · exact MergedCutProfiles.Batch633.valid25346
  · exact MergedCutProfiles.Batch633.valid25347
  · exact MergedCutProfiles.Batch633.valid25348
theorem numericValid4228 : retention4228.NumericValid := by decide +kernel
def certificate4228 : RatCutBinCertificate := ⟨⟨retention4228,(2113714005816501513/1000000000000000000),(2610492019033761/12500000000000000),(16777018063336665559/1000000000000000000),(91800435768608139787/25000000000000000),(449726233124297501/200000000000000000)⟩,(999542269922698689/1000000000000000000),(4550178592854093/12500000000000000),(13406137720087723/50000000000000000),(35372146477304067/200000000000000000)⟩
theorem valid4228 : certificate4228.Valid := by decide +kernel
theorem sound4228 : certificate4228.Sound := rat_cut_bin_certificate_sound certificate4228 profilesValid4228 numericValid4228 valid4228

def retention4229 : RatCutRetentionCertificate := ⟨(63/1000),(127/2000),(6082137181604363296/54547126863153105821),(1608352209531381689/1000000000000000000),2,(482834528656022089273/256000000000000000000),true,MergedCutProfiles.Batch633.profile25347,![MergedCutProfiles.Batch633.profile25347,MergedCutProfiles.Batch633.profile25349,MergedCutProfiles.Batch633.profile25350,MergedCutProfiles.Batch633.profile25351,MergedCutProfiles.Batch633.profile25352,MergedCutProfiles.Batch633.profile25353,MergedCutProfiles.Batch633.profile25354,MergedCutProfiles.Batch633.profile25355,MergedCutProfiles.Batch633.profile25356,MergedCutProfiles.Batch633.profile25357,MergedCutProfiles.Batch633.profile25358,MergedCutProfiles.Batch633.profile25359,MergedCutProfiles.Batch634.profile25360,MergedCutProfiles.Batch634.profile25361,MergedCutProfiles.Batch634.profile25362,MergedCutProfiles.Batch634.profile25363]⟩
theorem profilesValid4229 : retention4229.ProfilesValid := by
  change ∀ j : Fin 16, (retention4229.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch633.valid25347
  · exact MergedCutProfiles.Batch633.valid25349
  · exact MergedCutProfiles.Batch633.valid25350
  · exact MergedCutProfiles.Batch633.valid25351
  · exact MergedCutProfiles.Batch633.valid25352
  · exact MergedCutProfiles.Batch633.valid25353
  · exact MergedCutProfiles.Batch633.valid25354
  · exact MergedCutProfiles.Batch633.valid25355
  · exact MergedCutProfiles.Batch633.valid25356
  · exact MergedCutProfiles.Batch633.valid25357
  · exact MergedCutProfiles.Batch633.valid25358
  · exact MergedCutProfiles.Batch633.valid25359
  · exact MergedCutProfiles.Batch634.valid25360
  · exact MergedCutProfiles.Batch634.valid25361
  · exact MergedCutProfiles.Batch634.valid25362
  · exact MergedCutProfiles.Batch634.valid25363
theorem numericValid4229 : retention4229.NumericValid := by decide +kernel
def certificate4229 : RatCutBinCertificate := ⟨⟨retention4229,(2113714005816501513/1000000000000000000),(2610492019033761/12500000000000000),(16777018063336665559/1000000000000000000),(91800435768608139787/25000000000000000),(458362166250471033/250000000000000000)⟩,(999542269922698689/1000000000000000000),(191730097155577419/500000000000000000),(124491770927662487/500000000000000000),(11095750450732431/62500000000000000)⟩
theorem valid4229 : certificate4229.Valid := by decide +kernel
theorem sound4229 : certificate4229.Sound := rat_cut_bin_certificate_sound certificate4229 profilesValid4229 numericValid4229 valid4229

def retention4230 : RatCutRetentionCertificate := ⟨(63/1000),(127/2000),(16000000000000000000/54547126863153105821),(190066786925136353/7812500000000000),1,(6879751896299051695894636738857407907/4865709745283490636800000000000000000),false,MergedCutProfiles.Batch634.profile25364,(fun _ => MergedCutProfiles.Batch634.profile25364)⟩
theorem profilesValid4230 : retention4230.ProfilesValid := by
  exact MergedCutProfiles.Batch634.valid25364
theorem numericValid4230 : retention4230.NumericValid := by decide +kernel
def certificate4230 : RatCutBinCertificate := ⟨⟨retention4230,(2113714005816501513/1000000000000000000),(2610492019033761/12500000000000000),(16777018063336665559/1000000000000000000),(91800435768608139787/25000000000000000),(173451776782732467/125000000000000000)⟩,(999542269922698689/1000000000000000000),(164003915895065203/500000000000000000),(61269050342263293/200000000000000000),(401962492222388553/1000000000000000000)⟩
theorem valid4230 : certificate4230.Valid := by decide +kernel
theorem sound4230 : certificate4230.Sound := rat_cut_bin_certificate_sound certificate4230 profilesValid4230 numericValid4230 valid4230

def retention4231 : RatCutRetentionCertificate := ⟨(63/1000),(127/2000),(1/2),64,1,(255412978361873197152661673902210338999/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch419.profile16776,(fun _ => MergedCutProfiles.Batch419.profile16776)⟩
theorem profilesValid4231 : retention4231.ProfilesValid := by
  exact MergedCutProfiles.Batch419.valid16776
theorem numericValid4231 : retention4231.NumericValid := by decide +kernel
def certificate4231 : RatCutBinCertificate := ⟨⟨retention4231,(2113714005816501513/1000000000000000000),(2610492019033761/12500000000000000),(16777018063336665559/1000000000000000000),(91800435768608139787/25000000000000000),(38855821290595059/40000000000000000)⟩,(999542269922698689/1000000000000000000),(457352514377878099/1000000000000000000),(92430009963900213/500000000000000000),(176805527997899159/1000000000000000000)⟩
theorem valid4231 : certificate4231.Valid := by decide +kernel
theorem sound4231 : certificate4231.Sound := rat_cut_bin_certificate_sound certificate4231 profilesValid4231 numericValid4231 valid4231

def retention4232 : RatCutRetentionCertificate := ⟨(63/1000),(127/2000),(16000000000000000000/54547126863153105821),(23633873690209958823/1000000000000000000),1,(2226789271256705538587376879578274303/1575591579347330588200000000000000000),false,MergedCutProfiles.Batch634.profile25364,(fun _ => MergedCutProfiles.Batch634.profile25364)⟩
theorem profilesValid4232 : retention4232.ProfilesValid := by
  exact MergedCutProfiles.Batch634.valid25364
theorem numericValid4232 : retention4232.NumericValid := by decide +kernel
def certificate4232 : RatCutBinCertificate := ⟨⟨retention4232,(1937077951816501513/1000000000000000000),(2610492019033761/12500000000000000),(16777018063336665559/1000000000000000000),(91800435768608139787/25000000000000000),(1389190919111030417/1000000000000000000)⟩,(499790262519523071/500000000000000000),(9124698748179/250000000000000),(825592060101908511/1000000000000000000),(541382148358653719/500000000000000000)⟩
theorem valid4232 : certificate4232.Valid := by decide +kernel
theorem sound4232 : certificate4232.Sound := rat_cut_bin_certificate_sound certificate4232 profilesValid4232 numericValid4232 valid4232

def retention4233 : RatCutRetentionCertificate := ⟨(63/1000),(127/2000),(1/2),64,1,(255412978361873197152661673902210338999/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch419.profile16776,(fun _ => MergedCutProfiles.Batch419.profile16776)⟩
theorem profilesValid4233 : retention4233.ProfilesValid := by
  exact MergedCutProfiles.Batch419.valid16776
theorem numericValid4233 : retention4233.NumericValid := by decide +kernel
def certificate4233 : RatCutBinCertificate := ⟨⟨retention4233,(1937077951816501513/1000000000000000000),(2610492019033761/12500000000000000),(16777018063336665559/1000000000000000000),(91800435768608139787/25000000000000000),(194718857943744073/200000000000000000)⟩,(499790262519523071/500000000000000000),(52078976939177581/1000000000000000000),(782814461862314253/1000000000000000000),(187601166127150469/250000000000000000)⟩
theorem valid4233 : certificate4233.Valid := by decide +kernel
theorem sound4233 : certificate4233.Sound := rat_cut_bin_certificate_sound certificate4233 profilesValid4233 numericValid4233 valid4233

def retention4234 : RatCutRetentionCertificate := ⟨(127/2000),(8/125),(29145611281576179/7647131750087800898),(799997172712609559/1000000000000000000),(7/2),(37871594905754649469/16000000000000000000),true,MergedCutProfiles.Batch634.profile25365,![MergedCutProfiles.Batch634.profile25365,MergedCutProfiles.Batch634.profile25366,MergedCutProfiles.Batch634.profile25367,MergedCutProfiles.Batch634.profile25368,MergedCutProfiles.Batch634.profile25369,MergedCutProfiles.Batch634.profile25370,MergedCutProfiles.Batch634.profile25371,MergedCutProfiles.Batch634.profile25372,MergedCutProfiles.Batch634.profile25373,MergedCutProfiles.Batch634.profile25374,MergedCutProfiles.Batch545.profile21809,MergedCutProfiles.Batch419.profile16796,MergedCutProfiles.Batch634.profile25375,MergedCutProfiles.Batch634.profile25376,MergedCutProfiles.Batch634.profile25377,MergedCutProfiles.Batch544.profile21796]⟩
theorem profilesValid4234 : retention4234.ProfilesValid := by
  change ∀ j : Fin 16, (retention4234.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch634.valid25365
  · exact MergedCutProfiles.Batch634.valid25366
  · exact MergedCutProfiles.Batch634.valid25367
  · exact MergedCutProfiles.Batch634.valid25368
  · exact MergedCutProfiles.Batch634.valid25369
  · exact MergedCutProfiles.Batch634.valid25370
  · exact MergedCutProfiles.Batch634.valid25371
  · exact MergedCutProfiles.Batch634.valid25372
  · exact MergedCutProfiles.Batch634.valid25373
  · exact MergedCutProfiles.Batch634.valid25374
  · exact MergedCutProfiles.Batch545.valid21809
  · exact MergedCutProfiles.Batch419.valid16796
  · exact MergedCutProfiles.Batch634.valid25375
  · exact MergedCutProfiles.Batch634.valid25376
  · exact MergedCutProfiles.Batch634.valid25377
  · exact MergedCutProfiles.Batch544.valid21796
theorem numericValid4234 : retention4234.NumericValid := by decide +kernel
def certificate4234 : RatCutBinCertificate := ⟨⟨retention4234,(2120661058131922261/1000000000000000000),(106411689904918233/500000000000000000),(16936160295534147131/1000000000000000000),(3637762398317120126113/1000000000000000000),(2273702365666859751/1000000000000000000)⟩,(999538730619160109/1000000000000000000),(422293835610322269/1000000000000000000),(213665433783941947/1000000000000000000),(5630057145127219/50000000000000000)⟩
theorem valid4234 : certificate4234.Valid := by decide +kernel
theorem sound4234 : certificate4234.Sound := rat_cut_bin_certificate_sound certificate4234 profilesValid4234 numericValid4234 valid4234

def retention4235 : RatCutRetentionCertificate := ⟨(127/2000),(8/125),(141149655000000000/26764961125307303143),(204019278971033253/250000000000000000),(69/20),(753299800681769202329/320000000000000000000),true,MergedCutProfiles.Batch634.profile25378,![MergedCutProfiles.Batch634.profile25378,MergedCutProfiles.Batch634.profile25379,MergedCutProfiles.Batch634.profile25380,MergedCutProfiles.Batch634.profile25381,MergedCutProfiles.Batch634.profile25371,MergedCutProfiles.Batch634.profile25382,MergedCutProfiles.Batch634.profile25383,MergedCutProfiles.Batch634.profile25384,MergedCutProfiles.Batch634.profile25385,MergedCutProfiles.Batch634.profile25386,MergedCutProfiles.Batch634.profile25387,MergedCutProfiles.Batch634.profile25388,MergedCutProfiles.Batch544.profile21783,MergedCutProfiles.Batch634.profile25389,MergedCutProfiles.Batch634.profile25390,MergedCutProfiles.Batch634.profile25391]⟩
theorem profilesValid4235 : retention4235.ProfilesValid := by
  change ∀ j : Fin 16, (retention4235.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch634.valid25378
  · exact MergedCutProfiles.Batch634.valid25379
  · exact MergedCutProfiles.Batch634.valid25380
  · exact MergedCutProfiles.Batch634.valid25381
  · exact MergedCutProfiles.Batch634.valid25371
  · exact MergedCutProfiles.Batch634.valid25382
  · exact MergedCutProfiles.Batch634.valid25383
  · exact MergedCutProfiles.Batch634.valid25384
  · exact MergedCutProfiles.Batch634.valid25385
  · exact MergedCutProfiles.Batch634.valid25386
  · exact MergedCutProfiles.Batch634.valid25387
  · exact MergedCutProfiles.Batch634.valid25388
  · exact MergedCutProfiles.Batch544.valid21783
  · exact MergedCutProfiles.Batch634.valid25389
  · exact MergedCutProfiles.Batch634.valid25390
  · exact MergedCutProfiles.Batch634.valid25391
theorem numericValid4235 : retention4235.NumericValid := by decide +kernel
def certificate4235 : RatCutBinCertificate := ⟨⟨retention4235,(2120661058131922261/1000000000000000000),(106411689904918233/500000000000000000),(16936160295534147131/1000000000000000000),(3637762398317120126113/1000000000000000000),(2262122033403227373/1000000000000000000)⟩,(999538730619160109/1000000000000000000),(104967652439852829/250000000000000000),(215761297766584523/1000000000000000000),(28671132817214807/250000000000000000)⟩
theorem valid4235 : certificate4235.Valid := by decide +kernel
theorem sound4235 : certificate4235.Sound := rat_cut_bin_certificate_sound certificate4235 profilesValid4235 numericValid4235 valid4235

def certificates : List RatCutBinCertificate := [certificate4224,certificate4225,certificate4226,certificate4227,certificate4228,certificate4229,certificate4230,certificate4231,certificate4232,certificate4233,certificate4234,certificate4235]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4224,List.forall_mem_cons.mpr ⟨sound4225,List.forall_mem_cons.mpr ⟨sound4226,List.forall_mem_cons.mpr ⟨sound4227,List.forall_mem_cons.mpr ⟨sound4228,List.forall_mem_cons.mpr ⟨sound4229,List.forall_mem_cons.mpr ⟨sound4230,List.forall_mem_cons.mpr ⟨sound4231,List.forall_mem_cons.mpr ⟨sound4232,List.forall_mem_cons.mpr ⟨sound4233,List.forall_mem_cons.mpr ⟨sound4234,List.forall_mem_cons.mpr ⟨sound4235,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch352
