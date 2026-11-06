import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch431
import Cycle12.MergedCutProfiles.Batch432
import Cycle12.MergedCutProfiles.Batch433
import Cycle12.MergedCutProfiles.Batch434

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch227

def retention2724 : RatCutRetentionCertificate := ⟨(131/2000),(33/500),(9029970203196224619/19880633818081446644),(2388297365046084279/500000000000000000),(21/20),(2017224479090203983364222375157769773279/1910637892036867423200000000000000000000),false,MergedCutProfiles.Batch431.profile17279,(fun _ => MergedCutProfiles.Batch431.profile17279)⟩
theorem profilesValid2724 : retention2724.ProfilesValid := by
  exact MergedCutProfiles.Batch431.valid17279
theorem numericValid2724 : retention2724.NumericValid := by decide +kernel
def certificate2724 : RatCutBinCertificate := ⟨⟨retention2724,(1295365176092031847/500000000000000000),(229314578619222081/1000000000000000000),(4398392572121590119/250000000000000000),(175442977448303472037/500000000000000000),(1020325288879602843/1000000000000000000)⟩,(994268896255491479/1000000000000000000),(7027120963297937/31250000000000000),(439414612348192911/1000000000000000000),(355434086885022937/1000000000000000000)⟩
theorem valid2724 : certificate2724.Valid := by decide +kernel
theorem sound2724 : certificate2724.Sound := rat_cut_bin_certificate_sound certificate2724 profilesValid2724 numericValid2724 valid2724

def retention2725 : RatCutRetentionCertificate := ⟨(131/2000),(33/500),(9778163786152788853/19880633818081446644),(9029970203196224619/1000000000000000000),1,(62037845069384358395019310555652873/62708126411084893187500000000000000),false,MergedCutProfiles.Batch432.profile17280,(fun _ => MergedCutProfiles.Batch432.profile17280)⟩
theorem profilesValid2725 : retention2725.ProfilesValid := by
  exact MergedCutProfiles.Batch432.valid17280
theorem numericValid2725 : retention2725.NumericValid := by decide +kernel
def certificate2725 : RatCutBinCertificate := ⟨⟨retention2725,(1295365176092031847/500000000000000000),(229314578619222081/1000000000000000000),(4398392572121590119/250000000000000000),(175442977448303472037/500000000000000000),(477770535990424057/500000000000000000)⟩,(994268896255491479/1000000000000000000),(24011356705387417/100000000000000000),(208610446691611401/500000000000000000),(358329208784616481/1000000000000000000)⟩
theorem valid2725 : certificate2725.Valid := by decide +kernel
theorem sound2725 : certificate2725.Sound := rat_cut_bin_certificate_sound certificate2725 profilesValid2725 numericValid2725 valid2725

def retention2726 : RatCutRetentionCertificate := ⟨(131/2000),(33/500),(4937972712007158371/9940316909040723322),(9778163786152788853/1000000000000000000),1,(300112474063052877893633525604296987/305567618317274651656250000000000000),false,MergedCutProfiles.Batch432.profile17281,(fun _ => MergedCutProfiles.Batch432.profile17281)⟩
theorem profilesValid2726 : retention2726.ProfilesValid := by
  exact MergedCutProfiles.Batch432.valid17281
theorem numericValid2726 : retention2726.NumericValid := by decide +kernel
def certificate2726 : RatCutBinCertificate := ⟨⟨retention2726,(1295365176092031847/500000000000000000),(229314578619222081/1000000000000000000),(4398392572121590119/250000000000000000),(175442977448303472037/500000000000000000),(23709441788726587/25000000000000000)⟩,(994268896255491479/1000000000000000000),(24192722176286959/100000000000000000),(103661296936084513/250000000000000000),(89075222290524911/250000000000000000)⟩
theorem valid2726 : certificate2726.Valid := by decide +kernel
theorem sound2726 : certificate2726.Sound := rat_cut_bin_certificate_sound certificate2726 profilesValid2726 numericValid2726 valid2726

def retention2727 : RatCutRetentionCertificate := ⟨(131/2000),(33/500),(1/2),(4937972712007158371/500000000000000000),1,(7713076408335102288074452249244762027/7900756339211453393600000000000000000),false,MergedCutProfiles.Batch431.profile17278,(fun _ => MergedCutProfiles.Batch431.profile17278)⟩
theorem profilesValid2727 : retention2727.ProfilesValid := by
  exact MergedCutProfiles.Batch431.valid17278
theorem numericValid2727 : retention2727.NumericValid := by decide +kernel
def certificate2727 : RatCutBinCertificate := ⟨⟨retention2727,(1295365176092031847/500000000000000000),(229314578619222081/1000000000000000000),(4398392572121590119/250000000000000000),(175442977448303472037/500000000000000000),(188495101893166661/200000000000000000)⟩,(994268896255491479/1000000000000000000),(60860566920683947/250000000000000000),(1289074443285023/3125000000000000),(35275682949740521/100000000000000000)⟩
theorem valid2727 : certificate2727.Valid := by decide +kernel
theorem sound2727 : certificate2727.Sound := rat_cut_bin_certificate_sound certificate2727 profilesValid2727 numericValid2727 valid2727

def retention2728 : RatCutRetentionCertificate := ⟨(33/500),(133/2000),(971503190676953007/19520377059030781007),(961884347204903967/1000000000000000000),(5/2),(523049187345019385343/256000000000000000000),true,MergedCutProfiles.Batch432.profile17282,![MergedCutProfiles.Batch432.profile17282,MergedCutProfiles.Batch432.profile17283,MergedCutProfiles.Batch432.profile17284,MergedCutProfiles.Batch432.profile17285,MergedCutProfiles.Batch432.profile17286,MergedCutProfiles.Batch432.profile17287,MergedCutProfiles.Batch432.profile17288,MergedCutProfiles.Batch432.profile17289,MergedCutProfiles.Batch432.profile17290,MergedCutProfiles.Batch432.profile17291,MergedCutProfiles.Batch432.profile17292,MergedCutProfiles.Batch432.profile17293,MergedCutProfiles.Batch432.profile17294,MergedCutProfiles.Batch432.profile17295,MergedCutProfiles.Batch432.profile17296,MergedCutProfiles.Batch432.profile17297]⟩
theorem profilesValid2728 : retention2728.ProfilesValid := by
  change ∀ j : Fin 16, (retention2728.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch432.valid17282
  · exact MergedCutProfiles.Batch432.valid17283
  · exact MergedCutProfiles.Batch432.valid17284
  · exact MergedCutProfiles.Batch432.valid17285
  · exact MergedCutProfiles.Batch432.valid17286
  · exact MergedCutProfiles.Batch432.valid17287
  · exact MergedCutProfiles.Batch432.valid17288
  · exact MergedCutProfiles.Batch432.valid17289
  · exact MergedCutProfiles.Batch432.valid17290
  · exact MergedCutProfiles.Batch432.valid17291
  · exact MergedCutProfiles.Batch432.valid17292
  · exact MergedCutProfiles.Batch432.valid17293
  · exact MergedCutProfiles.Batch432.valid17294
  · exact MergedCutProfiles.Batch432.valid17295
  · exact MergedCutProfiles.Batch432.valid17296
  · exact MergedCutProfiles.Batch432.valid17297
theorem numericValid2728 : retention2728.NumericValid := by decide +kernel
def certificate2728 : RatCutBinCertificate := ⟨⟨retention2728,(236154990863854579/100000000000000000),(233579791654726571/1000000000000000000),(17764504729885923971/1000000000000000000),(347878757732324395133/1000000000000000000),(1965511051503519693/1000000000000000000)⟩,(497379936490464869/500000000000000000),(268817223046721253/1000000000000000000),(377978935090944631/1000000000000000000),(111263961395505969/500000000000000000)⟩
theorem valid2728 : certificate2728.Valid := by decide +kernel
theorem sound2728 : certificate2728.Sound := rat_cut_bin_certificate_sound certificate2728 profilesValid2728 numericValid2728 valid2728

def retention2729 : RatCutRetentionCertificate := ⟨(33/500),(133/2000),(985789096000000000/19520377059030781007),(971503190676953007/1000000000000000000),(5/2),(32742552472276203237/16000000000000000000),true,MergedCutProfiles.Batch432.profile17298,![MergedCutProfiles.Batch432.profile17298,MergedCutProfiles.Batch432.profile17299,MergedCutProfiles.Batch432.profile17300,MergedCutProfiles.Batch432.profile17301,MergedCutProfiles.Batch432.profile17302,MergedCutProfiles.Batch432.profile17303,MergedCutProfiles.Batch432.profile17304,MergedCutProfiles.Batch432.profile17305,MergedCutProfiles.Batch432.profile17306,MergedCutProfiles.Batch432.profile17307,MergedCutProfiles.Batch432.profile17308,MergedCutProfiles.Batch432.profile17309,MergedCutProfiles.Batch432.profile17310,MergedCutProfiles.Batch432.profile17311,MergedCutProfiles.Batch432.profile17312,MergedCutProfiles.Batch432.profile17313]⟩
theorem profilesValid2729 : retention2729.ProfilesValid := by
  change ∀ j : Fin 16, (retention2729.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch432.valid17298
  · exact MergedCutProfiles.Batch432.valid17299
  · exact MergedCutProfiles.Batch432.valid17300
  · exact MergedCutProfiles.Batch432.valid17301
  · exact MergedCutProfiles.Batch432.valid17302
  · exact MergedCutProfiles.Batch432.valid17303
  · exact MergedCutProfiles.Batch432.valid17304
  · exact MergedCutProfiles.Batch432.valid17305
  · exact MergedCutProfiles.Batch432.valid17306
  · exact MergedCutProfiles.Batch432.valid17307
  · exact MergedCutProfiles.Batch432.valid17308
  · exact MergedCutProfiles.Batch432.valid17309
  · exact MergedCutProfiles.Batch432.valid17310
  · exact MergedCutProfiles.Batch432.valid17311
  · exact MergedCutProfiles.Batch432.valid17312
  · exact MergedCutProfiles.Batch432.valid17313
theorem numericValid2729 : retention2729.NumericValid := by decide +kernel
def certificate2729 : RatCutBinCertificate := ⟨⟨retention2729,(236154990863854579/100000000000000000),(233579791654726571/1000000000000000000),(17764504729885923971/1000000000000000000),(347878757732324395133/1000000000000000000),(1968759907560575209/1000000000000000000)⟩,(497379936490464869/500000000000000000),(267371738587452951/1000000000000000000),(189939898868372529/500000000000000000),(224475751508389921/1000000000000000000)⟩
theorem valid2729 : certificate2729.Valid := by decide +kernel
theorem sound2729 : certificate2729.Sound := rat_cut_bin_certificate_sound certificate2729 profilesValid2729 numericValid2729 valid2729

def retention2730 : RatCutRetentionCertificate := ⟨(33/500),(133/2000),(1073143919329342518/19520377059030781007),(123223637/125000000),(49/20),(8111117971688728703/4000000000000000000),true,MergedCutProfiles.Batch432.profile17314,![MergedCutProfiles.Batch432.profile17314,MergedCutProfiles.Batch432.profile17315,MergedCutProfiles.Batch432.profile17316,MergedCutProfiles.Batch432.profile17317,MergedCutProfiles.Batch432.profile17318,MergedCutProfiles.Batch432.profile17319,MergedCutProfiles.Batch433.profile17320,MergedCutProfiles.Batch433.profile17321,MergedCutProfiles.Batch433.profile17322,MergedCutProfiles.Batch433.profile17323,MergedCutProfiles.Batch432.profile17309,MergedCutProfiles.Batch433.profile17324,MergedCutProfiles.Batch433.profile17325,MergedCutProfiles.Batch433.profile17326,MergedCutProfiles.Batch433.profile17327,MergedCutProfiles.Batch433.profile17328]⟩
theorem profilesValid2730 : retention2730.ProfilesValid := by
  change ∀ j : Fin 16, (retention2730.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch432.valid17314
  · exact MergedCutProfiles.Batch432.valid17315
  · exact MergedCutProfiles.Batch432.valid17316
  · exact MergedCutProfiles.Batch432.valid17317
  · exact MergedCutProfiles.Batch432.valid17318
  · exact MergedCutProfiles.Batch432.valid17319
  · exact MergedCutProfiles.Batch433.valid17320
  · exact MergedCutProfiles.Batch433.valid17321
  · exact MergedCutProfiles.Batch433.valid17322
  · exact MergedCutProfiles.Batch433.valid17323
  · exact MergedCutProfiles.Batch432.valid17309
  · exact MergedCutProfiles.Batch433.valid17324
  · exact MergedCutProfiles.Batch433.valid17325
  · exact MergedCutProfiles.Batch433.valid17326
  · exact MergedCutProfiles.Batch433.valid17327
  · exact MergedCutProfiles.Batch433.valid17328
theorem numericValid2730 : retention2730.NumericValid := by decide +kernel
def certificate2730 : RatCutBinCertificate := ⟨⟨retention2730,(236154990863854579/100000000000000000),(233579791654726571/1000000000000000000),(17764504729885923971/1000000000000000000),(347878757732324395133/1000000000000000000),(975841372598110601/500000000000000000)⟩,(497379936490464869/500000000000000000),(134123308913429843/500000000000000000),(378728378677518767/1000000000000000000),(225429700879891323/1000000000000000000)⟩
theorem valid2730 : certificate2730.Valid := by decide +kernel
theorem sound2730 : certificate2730.Sound := rat_cut_bin_certificate_sound certificate2730 profilesValid2730 numericValid2730 valid2730

def retention2731 : RatCutRetentionCertificate := ⟨(33/500),(133/2000),(1764926639147300447/19520377059030781007),(536571959664671259/500000000000000000),(23/10),(1235541796824466390543/640000000000000000000),true,MergedCutProfiles.Batch433.profile17329,![MergedCutProfiles.Batch433.profile17329,MergedCutProfiles.Batch433.profile17330,MergedCutProfiles.Batch433.profile17331,MergedCutProfiles.Batch433.profile17332,MergedCutProfiles.Batch433.profile17333,MergedCutProfiles.Batch433.profile17334,MergedCutProfiles.Batch433.profile17335,MergedCutProfiles.Batch433.profile17336,MergedCutProfiles.Batch433.profile17337,MergedCutProfiles.Batch433.profile17338,MergedCutProfiles.Batch433.profile17339,MergedCutProfiles.Batch433.profile17340,MergedCutProfiles.Batch433.profile17341,MergedCutProfiles.Batch433.profile17342,MergedCutProfiles.Batch433.profile17343,MergedCutProfiles.Batch433.profile17344]⟩
theorem profilesValid2731 : retention2731.ProfilesValid := by
  change ∀ j : Fin 16, (retention2731.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch433.valid17329
  · exact MergedCutProfiles.Batch433.valid17330
  · exact MergedCutProfiles.Batch433.valid17331
  · exact MergedCutProfiles.Batch433.valid17332
  · exact MergedCutProfiles.Batch433.valid17333
  · exact MergedCutProfiles.Batch433.valid17334
  · exact MergedCutProfiles.Batch433.valid17335
  · exact MergedCutProfiles.Batch433.valid17336
  · exact MergedCutProfiles.Batch433.valid17337
  · exact MergedCutProfiles.Batch433.valid17338
  · exact MergedCutProfiles.Batch433.valid17339
  · exact MergedCutProfiles.Batch433.valid17340
  · exact MergedCutProfiles.Batch433.valid17341
  · exact MergedCutProfiles.Batch433.valid17342
  · exact MergedCutProfiles.Batch433.valid17343
  · exact MergedCutProfiles.Batch433.valid17344
theorem numericValid2731 : retention2731.NumericValid := by decide +kernel
def certificate2731 : RatCutBinCertificate := ⟨⟨retention2731,(236154990863854579/100000000000000000),(233579791654726571/1000000000000000000),(17764504729885923971/1000000000000000000),(347878757732324395133/1000000000000000000),(929548360544630327/500000000000000000)⟩,(497379936490464869/500000000000000000),(273094429231010783/1000000000000000000),(46549902749863231/125000000000000000),(112660207875442207/500000000000000000)⟩
theorem valid2731 : certificate2731.Valid := by decide +kernel
theorem sound2731 : certificate2731.Sound := rat_cut_bin_certificate_sound certificate2731 profilesValid2731 numericValid2731 valid2731

def retention2732 : RatCutRetentionCertificate := ⟨(33/500),(133/2000),(5118157579761872450/19520377059030781007),(1764926639147300447/1000000000000000000),(8/5),(1901278990272627828091/1280000000000000000000),true,MergedCutProfiles.Batch433.profile17345,![MergedCutProfiles.Batch433.profile17345,MergedCutProfiles.Batch433.profile17346,MergedCutProfiles.Batch433.profile17347,MergedCutProfiles.Batch433.profile17348,MergedCutProfiles.Batch433.profile17349,MergedCutProfiles.Batch433.profile17350,MergedCutProfiles.Batch433.profile17351,MergedCutProfiles.Batch433.profile17352,MergedCutProfiles.Batch433.profile17353,MergedCutProfiles.Batch433.profile17354,MergedCutProfiles.Batch433.profile17355,MergedCutProfiles.Batch433.profile17356,MergedCutProfiles.Batch433.profile17357,MergedCutProfiles.Batch433.profile17358,MergedCutProfiles.Batch433.profile17359,MergedCutProfiles.Batch434.profile17360]⟩
theorem profilesValid2732 : retention2732.ProfilesValid := by
  change ∀ j : Fin 16, (retention2732.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch433.valid17345
  · exact MergedCutProfiles.Batch433.valid17346
  · exact MergedCutProfiles.Batch433.valid17347
  · exact MergedCutProfiles.Batch433.valid17348
  · exact MergedCutProfiles.Batch433.valid17349
  · exact MergedCutProfiles.Batch433.valid17350
  · exact MergedCutProfiles.Batch433.valid17351
  · exact MergedCutProfiles.Batch433.valid17352
  · exact MergedCutProfiles.Batch433.valid17353
  · exact MergedCutProfiles.Batch433.valid17354
  · exact MergedCutProfiles.Batch433.valid17355
  · exact MergedCutProfiles.Batch433.valid17356
  · exact MergedCutProfiles.Batch433.valid17357
  · exact MergedCutProfiles.Batch433.valid17358
  · exact MergedCutProfiles.Batch433.valid17359
  · exact MergedCutProfiles.Batch434.valid17360
theorem numericValid2732 : retention2732.NumericValid := by decide +kernel
def certificate2732 : RatCutBinCertificate := ⟨⟨retention2732,(236154990863854579/100000000000000000),(233579791654726571/1000000000000000000),(17764504729885923971/1000000000000000000),(347878757732324395133/1000000000000000000),(1435680374905643439/1000000000000000000)⟩,(497379936490464869/500000000000000000),(304885822552090717/1000000000000000000),(6658903003410421/20000000000000000),(112654604701147091/500000000000000000)⟩
theorem valid2732 : certificate2732.Valid := by decide +kernel
theorem sound2732 : certificate2732.Sound := rat_cut_bin_certificate_sound certificate2732 profilesValid2732 numericValid2732 valid2732

def retention2733 : RatCutRetentionCertificate := ⟨(33/500),(133/2000),(8846861147521360145/19520377059030781007),(102363151595237449/20000000000000000),1,(5361968600996512249/5120000000000000000),true,MergedCutProfiles.Batch433.profile17333,![MergedCutProfiles.Batch433.profile17333,MergedCutProfiles.Batch434.profile17361,MergedCutProfiles.Batch434.profile17362,MergedCutProfiles.Batch434.profile17363,MergedCutProfiles.Batch434.profile17364,MergedCutProfiles.Batch434.profile17365,MergedCutProfiles.Batch434.profile17366,MergedCutProfiles.Batch434.profile17367,MergedCutProfiles.Batch434.profile17368,MergedCutProfiles.Batch434.profile17369,MergedCutProfiles.Batch434.profile17370,MergedCutProfiles.Batch434.profile17371,MergedCutProfiles.Batch434.profile17372,MergedCutProfiles.Batch434.profile17373,MergedCutProfiles.Batch434.profile17374,MergedCutProfiles.Batch434.profile17375]⟩
theorem profilesValid2733 : retention2733.ProfilesValid := by
  change ∀ j : Fin 16, (retention2733.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch433.valid17333
  · exact MergedCutProfiles.Batch434.valid17361
  · exact MergedCutProfiles.Batch434.valid17362
  · exact MergedCutProfiles.Batch434.valid17363
  · exact MergedCutProfiles.Batch434.valid17364
  · exact MergedCutProfiles.Batch434.valid17365
  · exact MergedCutProfiles.Batch434.valid17366
  · exact MergedCutProfiles.Batch434.valid17367
  · exact MergedCutProfiles.Batch434.valid17368
  · exact MergedCutProfiles.Batch434.valid17369
  · exact MergedCutProfiles.Batch434.valid17370
  · exact MergedCutProfiles.Batch434.valid17371
  · exact MergedCutProfiles.Batch434.valid17372
  · exact MergedCutProfiles.Batch434.valid17373
  · exact MergedCutProfiles.Batch434.valid17374
  · exact MergedCutProfiles.Batch434.valid17375
theorem numericValid2733 : retention2733.NumericValid := by decide +kernel
def certificate2733 : RatCutBinCertificate := ⟨⟨retention2733,(236154990863854579/100000000000000000),(233579791654726571/1000000000000000000),(17764504729885923971/1000000000000000000),(347878757732324395133/1000000000000000000),(203240830860196613/200000000000000000)⟩,(497379936490464869/500000000000000000),(180369631975681411/500000000000000000),(271446761324714187/1000000000000000000),(228810586352117963/1000000000000000000)⟩
theorem valid2733 : certificate2733.Valid := by decide +kernel
theorem sound2733 : certificate2733.Sound := rat_cut_bin_certificate_sound certificate2733 profilesValid2733 numericValid2733 valid2733

def retention2734 : RatCutRetentionCertificate := ⟨(33/500),(133/2000),(9675681746527576768/19520377059030781007),(1769372229504272029/200000000000000000),(21/20),(566883103673315339069587002197128644311/566199113441367049280000000000000000000),false,MergedCutProfiles.Batch434.profile17376,(fun _ => MergedCutProfiles.Batch434.profile17376)⟩
theorem profilesValid2734 : retention2734.ProfilesValid := by
  exact MergedCutProfiles.Batch434.valid17376
theorem numericValid2734 : retention2734.NumericValid := by decide +kernel
def certificate2734 : RatCutBinCertificate := ⟨⟨retention2734,(236154990863854579/100000000000000000),(233579791654726571/1000000000000000000),(17764504729885923971/1000000000000000000),(347878757732324395133/1000000000000000000),(968601853909869631/1000000000000000000)⟩,(497379936490464869/500000000000000000),(14487054488090243/40000000000000000),(33748066009641871/125000000000000000),(225290524903720743/1000000000000000000)⟩
theorem valid2734 : certificate2734.Valid := by decide +kernel
theorem sound2734 : certificate2734.Sound := rat_cut_bin_certificate_sound certificate2734 profilesValid2734 numericValid2734 valid2734

def retention2735 : RatCutRetentionCertificate := ⟨(33/500),(133/2000),(1/2),(151182527289493387/15625000000000000),(21/20),(240614074317323424873404966867421197639/241892043663189419200000000000000000000),false,MergedCutProfiles.Batch434.profile17377,(fun _ => MergedCutProfiles.Batch434.profile17377)⟩
theorem profilesValid2735 : retention2735.ProfilesValid := by
  exact MergedCutProfiles.Batch434.valid17377
theorem numericValid2735 : retention2735.NumericValid := by decide +kernel
def certificate2735 : RatCutBinCertificate := ⟨⟨retention2735,(236154990863854579/100000000000000000),(233579791654726571/1000000000000000000),(17764504729885923971/1000000000000000000),(347878757732324395133/1000000000000000000),(96211079553728851/100000000000000000)⟩,(497379936490464869/500000000000000000),(362691359983230003/1000000000000000000),(5389238207221521/20000000000000000),(225221103809392089/1000000000000000000)⟩
theorem valid2735 : certificate2735.Valid := by decide +kernel
theorem sound2735 : certificate2735.Sound := rat_cut_bin_certificate_sound certificate2735 profilesValid2735 numericValid2735 valid2735

def certificates : List RatCutBinCertificate := [certificate2724,certificate2725,certificate2726,certificate2727,certificate2728,certificate2729,certificate2730,certificate2731,certificate2732,certificate2733,certificate2734,certificate2735]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2724,List.forall_mem_cons.mpr ⟨sound2725,List.forall_mem_cons.mpr ⟨sound2726,List.forall_mem_cons.mpr ⟨sound2727,List.forall_mem_cons.mpr ⟨sound2728,List.forall_mem_cons.mpr ⟨sound2729,List.forall_mem_cons.mpr ⟨sound2730,List.forall_mem_cons.mpr ⟨sound2731,List.forall_mem_cons.mpr ⟨sound2732,List.forall_mem_cons.mpr ⟨sound2733,List.forall_mem_cons.mpr ⟨sound2734,List.forall_mem_cons.mpr ⟨sound2735,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch227
