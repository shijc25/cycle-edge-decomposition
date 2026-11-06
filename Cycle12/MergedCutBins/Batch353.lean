import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch421
import Cycle12.MergedCutProfiles.Batch422
import Cycle12.MergedCutProfiles.Batch423
import Cycle12.MergedCutProfiles.Batch545
import Cycle12.MergedCutProfiles.Batch546
import Cycle12.MergedCutProfiles.Batch547
import Cycle12.MergedCutProfiles.Batch634
import Cycle12.MergedCutProfiles.Batch635
import Cycle12.MergedCutProfiles.Batch636

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch353

def retention4236 : RatCutRetentionCertificate := ⟨(127/2000),(8/125),(456775166699050547/53529922250614606286),(28229931/25000000),(53/20),(37021240718588109127/16000000000000000000),true,MergedCutProfiles.Batch634.profile25392,![MergedCutProfiles.Batch634.profile25392,MergedCutProfiles.Batch634.profile25393,MergedCutProfiles.Batch634.profile25394,MergedCutProfiles.Batch634.profile25373,MergedCutProfiles.Batch634.profile25384,MergedCutProfiles.Batch634.profile25395,MergedCutProfiles.Batch634.profile25396,MergedCutProfiles.Batch634.profile25397,MergedCutProfiles.Batch634.profile25398,MergedCutProfiles.Batch545.profile21831,MergedCutProfiles.Batch634.profile25399,MergedCutProfiles.Batch635.profile25400,MergedCutProfiles.Batch635.profile25401,MergedCutProfiles.Batch635.profile25402,MergedCutProfiles.Batch635.profile25403,MergedCutProfiles.Batch635.profile25404]⟩
theorem profilesValid4236 : retention4236.ProfilesValid := by
  change ∀ j : Fin 16, (retention4236.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch634.valid25392
  · exact MergedCutProfiles.Batch634.valid25393
  · exact MergedCutProfiles.Batch634.valid25394
  · exact MergedCutProfiles.Batch634.valid25373
  · exact MergedCutProfiles.Batch634.valid25384
  · exact MergedCutProfiles.Batch634.valid25395
  · exact MergedCutProfiles.Batch634.valid25396
  · exact MergedCutProfiles.Batch634.valid25397
  · exact MergedCutProfiles.Batch634.valid25398
  · exact MergedCutProfiles.Batch545.valid21831
  · exact MergedCutProfiles.Batch634.valid25399
  · exact MergedCutProfiles.Batch635.valid25400
  · exact MergedCutProfiles.Batch635.valid25401
  · exact MergedCutProfiles.Batch635.valid25402
  · exact MergedCutProfiles.Batch635.valid25403
  · exact MergedCutProfiles.Batch635.valid25404
theorem numericValid4236 : retention4236.NumericValid := by decide +kernel
def certificate4236 : RatCutBinCertificate := ⟨⟨retention4236,(2120661058131922261/1000000000000000000),(106411689904918233/500000000000000000),(16936160295534147131/1000000000000000000),(3637762398317120126113/1000000000000000000),(1121603585995098283/500000000000000000)⟩,(999538730619160109/1000000000000000000),(14384939639215137/40000000000000000),(13629299568209159/50000000000000000),(4494089146174489/25000000000000000)⟩
theorem valid4236 : certificate4236.Valid := by decide +kernel
theorem sound4236 : certificate4236.Sound := rat_cut_bin_certificate_sound certificate4236 profilesValid4236 numericValid4236 valid4236

def retention4237 : RatCutRetentionCertificate := ⟨(127/2000),(8/125),(4675874358207986023/30588527000351203592),(456775166699050547/250000000000000000),(37/20),(323697367261235457879881598981387486679/182710066679620218800000000000000000000),false,MergedCutProfiles.Batch635.profile25405,(fun _ => MergedCutProfiles.Batch635.profile25405)⟩
theorem profilesValid4237 : retention4237.ProfilesValid := by
  exact MergedCutProfiles.Batch635.valid25405
theorem numericValid4237 : retention4237.NumericValid := by decide +kernel
def certificate4237 : RatCutBinCertificate := ⟨⟨retention4237,(2120661058131922261/1000000000000000000),(106411689904918233/500000000000000000),(16936160295534147131/1000000000000000000),(3637762398317120126113/1000000000000000000),(861172023616945749/500000000000000000)⟩,(999538730619160109/1000000000000000000),(385672918818688203/1000000000000000000),(246869114333244389/1000000000000000000),(180104162580478587/1000000000000000000)⟩
theorem valid4237 : certificate4237.Valid := by decide +kernel
theorem sound4237 : certificate4237.Sound := rat_cut_bin_certificate_sound certificate4237 profilesValid4237 numericValid4237 valid4237

def retention4238 : RatCutRetentionCertificate := ⟨(127/2000),(8/125),(8000000000000000000/26764961125307303143),(32731120507455902161/1000000000000000000),1,(184249576233155709876840087040683679059/130924482029823608644000000000000000000),false,MergedCutProfiles.Batch635.profile25406,(fun _ => MergedCutProfiles.Batch635.profile25406)⟩
theorem profilesValid4238 : retention4238.ProfilesValid := by
  exact MergedCutProfiles.Batch635.valid25406
theorem numericValid4238 : retention4238.NumericValid := by decide +kernel
def certificate4238 : RatCutBinCertificate := ⟨⟨retention4238,(2120661058131922261/1000000000000000000),(106411689904918233/500000000000000000),(16936160295534147131/1000000000000000000),(3637762398317120126113/1000000000000000000),(1380647859364975787/1000000000000000000)⟩,(999538730619160109/1000000000000000000),(323505795836840913/1000000000000000000),(19462085709746813/62500000000000000),(412329404911182683/1000000000000000000)⟩
theorem valid4238 : certificate4238.Valid := by decide +kernel
theorem sound4238 : certificate4238.Sound := rat_cut_bin_certificate_sound certificate4238 profilesValid4238 numericValid4238 valid4238

def retention4239 : RatCutRetentionCertificate := ⟨(127/2000),(8/125),(1/2),64,1,(63853451544214774671362442957259811079/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch421.profile16877,(fun _ => MergedCutProfiles.Batch421.profile16877)⟩
theorem profilesValid4239 : retention4239.ProfilesValid := by
  exact MergedCutProfiles.Batch421.valid16877
theorem numericValid4239 : retention4239.NumericValid := by decide +kernel
def certificate4239 : RatCutBinCertificate := ⟨⟨retention4239,(2120661058131922261/1000000000000000000),(106411689904918233/500000000000000000),(16936160295534147131/1000000000000000000),(3637762398317120126113/1000000000000000000),(971061479697964069/1000000000000000000)⟩,(999538730619160109/1000000000000000000),(4534848810858707/10000000000000000),(187902042571968717/1000000000000000000),(44913370316942363/250000000000000000)⟩
theorem valid4239 : certificate4239.Valid := by decide +kernel
theorem sound4239 : certificate4239.Sound := rat_cut_bin_certificate_sound certificate4239 profilesValid4239 numericValid4239 valid4239

def retention4240 : RatCutRetentionCertificate := ⟨(127/2000),(8/125),(8000000000000000000/26764961125307303143),(23552680151868765813/1000000000000000000),1,(2933661983334849324539843032449911503/2093571569055001405600000000000000000),false,MergedCutProfiles.Batch635.profile25406,(fun _ => MergedCutProfiles.Batch635.profile25406)⟩
theorem profilesValid4240 : retention4240.ProfilesValid := by
  exact MergedCutProfiles.Batch635.valid25406
theorem numericValid4240 : retention4240.NumericValid := by decide +kernel
def certificate4240 : RatCutBinCertificate := ⟨⟨retention4240,(1939955255131922261/1000000000000000000),(106411689904918233/500000000000000000),(16936160295534147131/1000000000000000000),(3637762398317120126113/1000000000000000000),(344223364996768837/250000000000000000)⟩,(999578040690771933/1000000000000000000),(4582095066858209/125000000000000000),(206286137706340943/250000000000000000),(42916741958533/40000000000000)⟩
theorem valid4240 : certificate4240.Valid := by decide +kernel
theorem sound4240 : certificate4240.Sound := rat_cut_bin_certificate_sound certificate4240 profilesValid4240 numericValid4240 valid4240

def retention4241 : RatCutRetentionCertificate := ⟨(127/2000),(8/125),(1/2),64,1,(63853451544214774671362442957259811079/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch421.profile16877,(fun _ => MergedCutProfiles.Batch421.profile16877)⟩
theorem profilesValid4241 : retention4241.ProfilesValid := by
  exact MergedCutProfiles.Batch421.valid16877
theorem numericValid4241 : retention4241.NumericValid := by decide +kernel
def certificate4241 : RatCutBinCertificate := ⟨⟨retention4241,(1939955255131922261/1000000000000000000),(106411689904918233/500000000000000000),(16936160295534147131/1000000000000000000),(3637762398317120126113/1000000000000000000),(194666453838790421/200000000000000000)⟩,(999578040690771933/1000000000000000000),(25927658746260791/500000000000000000),(783409730169435203/1000000000000000000),(750774293187920233/1000000000000000000)⟩
theorem valid4241 : certificate4241.Valid := by decide +kernel
theorem sound4241 : certificate4241.Sound := rat_cut_bin_certificate_sound certificate4241 profilesValid4241 numericValid4241 valid4241

def retention4242 : RatCutRetentionCertificate := ⟨(8/125),(129/2000),(411984066682838311/105075060445203568366),(80773270597556771/100000000000000000),(7/2),(15327063145855541721912887184662489/6461861647804541680000000000000000),true,MergedCutProfiles.Batch635.profile25407,![MergedCutProfiles.Batch635.profile25407,MergedCutProfiles.Batch635.profile25408,MergedCutProfiles.Batch635.profile25409,MergedCutProfiles.Batch635.profile25410,MergedCutProfiles.Batch635.profile25411,MergedCutProfiles.Batch635.profile25412,MergedCutProfiles.Batch635.profile25413,MergedCutProfiles.Batch635.profile25414,MergedCutProfiles.Batch546.profile21867,MergedCutProfiles.Batch635.profile25415,MergedCutProfiles.Batch635.profile25416,MergedCutProfiles.Batch635.profile25417,MergedCutProfiles.Batch635.profile25418,MergedCutProfiles.Batch635.profile25419,MergedCutProfiles.Batch635.profile25420,MergedCutProfiles.Batch547.profile21883]⟩
theorem profilesValid4242 : retention4242.ProfilesValid := by
  change ∀ j : Fin 16, (retention4242.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch635.valid25407
  · exact MergedCutProfiles.Batch635.valid25408
  · exact MergedCutProfiles.Batch635.valid25409
  · exact MergedCutProfiles.Batch635.valid25410
  · exact MergedCutProfiles.Batch635.valid25411
  · exact MergedCutProfiles.Batch635.valid25412
  · exact MergedCutProfiles.Batch635.valid25413
  · exact MergedCutProfiles.Batch635.valid25414
  · exact MergedCutProfiles.Batch546.valid21867
  · exact MergedCutProfiles.Batch635.valid25415
  · exact MergedCutProfiles.Batch635.valid25416
  · exact MergedCutProfiles.Batch635.valid25417
  · exact MergedCutProfiles.Batch635.valid25418
  · exact MergedCutProfiles.Batch635.valid25419
  · exact MergedCutProfiles.Batch635.valid25420
  · exact MergedCutProfiles.Batch547.valid21883
theorem numericValid4242 : retention4242.NumericValid := by decide +kernel
def certificate4242 : RatCutBinCertificate := ⟨⟨retention4242,(66537780815368877/31250000000000000),(216862197802423917/1000000000000000000),(8548796245022962061/500000000000000000),(3604392558273399597219/1000000000000000000),(2277402332596420869/1000000000000000000)⟩,(15617733367844861/15625000000000000),(412738708695628523/1000000000000000000),(222011159688606419/1000000000000000000),(117365262304792583/1000000000000000000)⟩
theorem valid4242 : certificate4242.Valid := by decide +kernel
theorem sound4242 : certificate4242.Sound := rat_cut_bin_certificate_sound certificate4242 profilesValid4242 numericValid4242 valid4242

def retention4243 : RatCutRetentionCertificate := ⟨(8/125),(129/2000),(277902391000000000/52537530222601784183),(411984066682838311/500000000000000000),(69/20),(1509712703337126206143/640000000000000000000),true,MergedCutProfiles.Batch635.profile25421,![MergedCutProfiles.Batch635.profile25421,MergedCutProfiles.Batch635.profile25422,MergedCutProfiles.Batch635.profile25410,MergedCutProfiles.Batch547.profile21894,MergedCutProfiles.Batch635.profile25423,MergedCutProfiles.Batch635.profile25424,MergedCutProfiles.Batch635.profile25425,MergedCutProfiles.Batch635.profile25426,MergedCutProfiles.Batch635.profile25417,MergedCutProfiles.Batch547.profile21912,MergedCutProfiles.Batch635.profile25427,MergedCutProfiles.Batch547.profile21883,MergedCutProfiles.Batch423.profile16938,MergedCutProfiles.Batch635.profile25428,MergedCutProfiles.Batch635.profile25429,MergedCutProfiles.Batch547.profile21895]⟩
theorem profilesValid4243 : retention4243.ProfilesValid := by
  change ∀ j : Fin 16, (retention4243.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch635.valid25421
  · exact MergedCutProfiles.Batch635.valid25422
  · exact MergedCutProfiles.Batch635.valid25410
  · exact MergedCutProfiles.Batch547.valid21894
  · exact MergedCutProfiles.Batch635.valid25423
  · exact MergedCutProfiles.Batch635.valid25424
  · exact MergedCutProfiles.Batch635.valid25425
  · exact MergedCutProfiles.Batch635.valid25426
  · exact MergedCutProfiles.Batch635.valid25417
  · exact MergedCutProfiles.Batch547.valid21912
  · exact MergedCutProfiles.Batch635.valid25427
  · exact MergedCutProfiles.Batch547.valid21883
  · exact MergedCutProfiles.Batch423.valid16938
  · exact MergedCutProfiles.Batch635.valid25428
  · exact MergedCutProfiles.Batch635.valid25429
  · exact MergedCutProfiles.Batch547.valid21895
theorem numericValid4243 : retention4243.NumericValid := by decide +kernel
def certificate4243 : RatCutBinCertificate := ⟨⟨retention4243,(66537780815368877/31250000000000000),(216862197802423917/1000000000000000000),(8548796245022962061/500000000000000000),(3604392558273399597219/1000000000000000000),(1132875971168125533/500000000000000000)⟩,(15617733367844861/15625000000000000),(3206331196053491/7812500000000000),(224078092431861457/1000000000000000000),(59738039488127367/500000000000000000)⟩
theorem valid4243 : certificate4243.Valid := by decide +kernel
theorem sound4243 : certificate4243.Sound := rat_cut_bin_certificate_sound certificate4243 profilesValid4243 numericValid4243 valid4243

def retention4244 : RatCutRetentionCertificate := ⟨(8/125),(129/2000),(1155678741195798781/210150120890407136732),(277902391/250000000),(53/20),(4662532168909948157/2000000000000000000),true,MergedCutProfiles.Batch635.profile25421,![MergedCutProfiles.Batch635.profile25421,MergedCutProfiles.Batch635.profile25430,MergedCutProfiles.Batch635.profile25431,MergedCutProfiles.Batch635.profile25432,MergedCutProfiles.Batch635.profile25413,MergedCutProfiles.Batch635.profile25433,MergedCutProfiles.Batch635.profile25434,MergedCutProfiles.Batch635.profile25435,MergedCutProfiles.Batch423.profile16923,MergedCutProfiles.Batch635.profile25436,MergedCutProfiles.Batch635.profile25437,MergedCutProfiles.Batch635.profile25438,MergedCutProfiles.Batch546.profile21869,MergedCutProfiles.Batch635.profile25439,MergedCutProfiles.Batch547.profile21884,MergedCutProfiles.Batch636.profile25440]⟩
theorem profilesValid4244 : retention4244.ProfilesValid := by
  change ∀ j : Fin 16, (retention4244.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch635.valid25421
  · exact MergedCutProfiles.Batch635.valid25430
  · exact MergedCutProfiles.Batch635.valid25431
  · exact MergedCutProfiles.Batch635.valid25432
  · exact MergedCutProfiles.Batch635.valid25413
  · exact MergedCutProfiles.Batch635.valid25433
  · exact MergedCutProfiles.Batch635.valid25434
  · exact MergedCutProfiles.Batch635.valid25435
  · exact MergedCutProfiles.Batch423.valid16923
  · exact MergedCutProfiles.Batch635.valid25436
  · exact MergedCutProfiles.Batch635.valid25437
  · exact MergedCutProfiles.Batch635.valid25438
  · exact MergedCutProfiles.Batch546.valid21869
  · exact MergedCutProfiles.Batch635.valid25439
  · exact MergedCutProfiles.Batch547.valid21884
  · exact MergedCutProfiles.Batch636.valid25440
theorem numericValid4244 : retention4244.NumericValid := by decide +kernel
def certificate4244 : RatCutBinCertificate := ⟨⟨retention4244,(66537780815368877/31250000000000000),(216862197802423917/1000000000000000000),(8548796245022962061/500000000000000000),(3604392558273399597219/1000000000000000000),(564924395591457049/250000000000000000)⟩,(15617733367844861/15625000000000000),(7081217002117267/20000000000000000),(34789671842993331/125000000000000000),(183946815873776389/1000000000000000000)⟩
theorem valid4244 : certificate4244.Valid := by decide +kernel
theorem sound4244 : certificate4244.Sound := rat_cut_bin_certificate_sound certificate4244 profilesValid4244 numericValid4244 valid4244

def retention4245 : RatCutRetentionCertificate := ⟨(8/125),(129/2000),(1359706814453202529/105075060445203568366),(1155678741195798781/1000000000000000000),(13/5),(2923814688243376538169/1280000000000000000000),true,MergedCutProfiles.Batch636.profile25441,![MergedCutProfiles.Batch636.profile25441,MergedCutProfiles.Batch636.profile25442,MergedCutProfiles.Batch635.profile25434,MergedCutProfiles.Batch636.profile25443,MergedCutProfiles.Batch636.profile25444,MergedCutProfiles.Batch635.profile25439,MergedCutProfiles.Batch422.profile16881,MergedCutProfiles.Batch636.profile25445,MergedCutProfiles.Batch636.profile25446,MergedCutProfiles.Batch636.profile25447,MergedCutProfiles.Batch636.profile25448,MergedCutProfiles.Batch636.profile25449,MergedCutProfiles.Batch547.profile21887,MergedCutProfiles.Batch636.profile25450,MergedCutProfiles.Batch423.profile16952,MergedCutProfiles.Batch547.profile21906]⟩
theorem profilesValid4245 : retention4245.ProfilesValid := by
  change ∀ j : Fin 16, (retention4245.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch636.valid25441
  · exact MergedCutProfiles.Batch636.valid25442
  · exact MergedCutProfiles.Batch635.valid25434
  · exact MergedCutProfiles.Batch636.valid25443
  · exact MergedCutProfiles.Batch636.valid25444
  · exact MergedCutProfiles.Batch635.valid25439
  · exact MergedCutProfiles.Batch422.valid16881
  · exact MergedCutProfiles.Batch636.valid25445
  · exact MergedCutProfiles.Batch636.valid25446
  · exact MergedCutProfiles.Batch636.valid25447
  · exact MergedCutProfiles.Batch636.valid25448
  · exact MergedCutProfiles.Batch636.valid25449
  · exact MergedCutProfiles.Batch547.valid21887
  · exact MergedCutProfiles.Batch636.valid25450
  · exact MergedCutProfiles.Batch423.valid16952
  · exact MergedCutProfiles.Batch547.valid21906
theorem numericValid4245 : retention4245.NumericValid := by decide +kernel
def certificate4245 : RatCutBinCertificate := ⟨⟨retention4245,(66537780815368877/31250000000000000),(216862197802423917/1000000000000000000),(8548796245022962061/500000000000000000),(3604392558273399597219/1000000000000000000),(1107006050178458093/500000000000000000)⟩,(15617733367844861/15625000000000000),(44370239355145399/125000000000000000),(69345772076661581/250000000000000000),(45985969947641553/250000000000000000)⟩
theorem valid4245 : certificate4245.Valid := by decide +kernel
theorem sound4245 : certificate4245.Sound := rat_cut_bin_certificate_sound certificate4245 profilesValid4245 numericValid4245 valid4245

def retention4246 : RatCutRetentionCertificate := ⟨(8/125),(129/2000),(55443613313745916361/210150120890407136732),(1359706814453202529/500000000000000000),(3/2),(16321853760044310728712387059301443823/10877654515625620232000000000000000000),false,MergedCutProfiles.Batch636.profile25451,(fun _ => MergedCutProfiles.Batch636.profile25451)⟩
theorem profilesValid4246 : retention4246.ProfilesValid := by
  exact MergedCutProfiles.Batch636.valid25451
theorem numericValid4246 : retention4246.NumericValid := by decide +kernel
def certificate4246 : RatCutBinCertificate := ⟨⟨retention4246,(66537780815368877/31250000000000000),(216862197802423917/1000000000000000000),(8548796245022962061/500000000000000000),(3604392558273399597219/1000000000000000000),(729991806118941241/500000000000000000)⟩,(15617733367844861/15625000000000000),(6209489262888603/15625000000000000),(5896658235970417/25000000000000000),(185249369197648887/1000000000000000000)⟩
theorem valid4246 : certificate4246.Valid := by decide +kernel
theorem sound4246 : certificate4246.Sound := rat_cut_bin_certificate_sound certificate4246 profilesValid4246 numericValid4246 valid4246

def retention4247 : RatCutRetentionCertificate := ⟨(8/125),(129/2000),(16000000000000000000/52537530222601784183),(55443613313745916361/1000000000000000000),1,(310782590856990261982561794943591712523/221774453254983665444000000000000000000),false,MergedCutProfiles.Batch636.profile25452,(fun _ => MergedCutProfiles.Batch636.profile25452)⟩
theorem profilesValid4247 : retention4247.ProfilesValid := by
  exact MergedCutProfiles.Batch636.valid25452
theorem numericValid4247 : retention4247.NumericValid := by decide +kernel
def certificate4247 : RatCutBinCertificate := ⟨⟨retention4247,(66537780815368877/31250000000000000),(216862197802423917/1000000000000000000),(8548796245022962061/500000000000000000),(3604392558273399597219/1000000000000000000),(1374338854473090343/1000000000000000000)⟩,(15617733367844861/15625000000000000),(316992238003511729/1000000000000000000),(159403907292710971/500000000000000000),(85470082734019603/200000000000000000)⟩
theorem valid4247 : certificate4247.Valid := by decide +kernel
theorem sound4247 : certificate4247.Sound := rat_cut_bin_certificate_sound certificate4247 profilesValid4247 numericValid4247 valid4247

def certificates : List RatCutBinCertificate := [certificate4236,certificate4237,certificate4238,certificate4239,certificate4240,certificate4241,certificate4242,certificate4243,certificate4244,certificate4245,certificate4246,certificate4247]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4236,List.forall_mem_cons.mpr ⟨sound4237,List.forall_mem_cons.mpr ⟨sound4238,List.forall_mem_cons.mpr ⟨sound4239,List.forall_mem_cons.mpr ⟨sound4240,List.forall_mem_cons.mpr ⟨sound4241,List.forall_mem_cons.mpr ⟨sound4242,List.forall_mem_cons.mpr ⟨sound4243,List.forall_mem_cons.mpr ⟨sound4244,List.forall_mem_cons.mpr ⟨sound4245,List.forall_mem_cons.mpr ⟨sound4246,List.forall_mem_cons.mpr ⟨sound4247,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch353
