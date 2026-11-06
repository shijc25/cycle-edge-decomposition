import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch304
import Cycle12.MergedCutProfiles.Batch305
import Cycle12.MergedCutProfiles.Batch436
import Cycle12.MergedCutProfiles.Batch437
import Cycle12.MergedCutProfiles.Batch438
import Cycle12.MergedCutProfiles.Batch557
import Cycle12.MergedCutProfiles.Batch558
import Cycle12.MergedCutProfiles.Batch559

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch302

def retention3624 : RatCutRetentionCertificate := ⟨(133/2000),(67/1000),(22128216487561174992/47921503563055897243),(8428943732599404107/1000000000000000000),1,(8801711887992404308967622579657130549/8428943732599404107000000000000000000),false,MergedCutProfiles.Batch557.profile22287,(fun _ => MergedCutProfiles.Batch557.profile22287)⟩
theorem profilesValid3624 : retention3624.ProfilesValid := by
  exact MergedCutProfiles.Batch557.valid22287
theorem numericValid3624 : retention3624.NumericValid := by decide +kernel
def certificate3624 : RatCutBinCertificate := ⟨⟨retention3624,(2347251154774205273/1000000000000000000),(11895173549139047/50000000000000000),(8970110022628371949/500000000000000000),(431240624310649139377/500000000000000000),(202619418890114227/200000000000000000)⟩,(997912837819772849/1000000000000000000),(14559383713097887/125000000000000000),(315419481417765401/500000000000000000),(142312600451371961/250000000000000000)⟩
theorem valid3624 : certificate3624.Valid := by decide +kernel
theorem sound3624 : certificate3624.Sound := rat_cut_bin_certificate_sound certificate3624 profilesValid3624 numericValid3624 valid3624

def retention3625 : RatCutRetentionCertificate := ⟨(133/2000),(67/1000),(23724443175391544422/47921503563055897243),(1383013530472573437/62500000000000000),1,(22127678106758847057526881971649699839/22128216487561174992000000000000000000),false,MergedCutProfiles.Batch557.profile22288,(fun _ => MergedCutProfiles.Batch557.profile22288)⟩
theorem profilesValid3625 : retention3625.ProfilesValid := by
  exact MergedCutProfiles.Batch557.valid22288
theorem numericValid3625 : retention3625.NumericValid := by decide +kernel
def certificate3625 : RatCutBinCertificate := ⟨⟨retention3625,(2347251154774205273/1000000000000000000),(11895173549139047/50000000000000000),(8970110022628371949/500000000000000000),(431240624310649139377/500000000000000000),(96884861818431079/100000000000000000)⟩,(997912837819772849/1000000000000000000),(121794625578333057/1000000000000000000),(9684275033027271/15625000000000000),(114812242379196137/200000000000000000)⟩
theorem valid3625 : certificate3625.Valid := by decide +kernel
theorem sound3625 : certificate3625.Sound := rat_cut_bin_certificate_sound certificate3625 profilesValid3625 numericValid3625 valid3625

def retention3626 : RatCutRetentionCertificate := ⟨(133/2000),(67/1000),(1/2),(11862221587695772211/500000000000000000),1,(5532412155002389774608035940951030431/5582221923621539864000000000000000000),false,MergedCutProfiles.Batch436.profile17478,(fun _ => MergedCutProfiles.Batch436.profile17478)⟩
theorem profilesValid3626 : retention3626.ProfilesValid := by
  exact MergedCutProfiles.Batch436.valid17478
theorem numericValid3626 : retention3626.NumericValid := by decide +kernel
def certificate3626 : RatCutBinCertificate := ⟨⟨retention3626,(2347251154774205273/1000000000000000000),(11895173549139047/50000000000000000),(8970110022628371949/500000000000000000),(431240624310649139377/500000000000000000),(959950045575642709/1000000000000000000)⟩,(997912837819772849/1000000000000000000),(307309102274909/2500000000000000),(308737586196839713/500000000000000000),(35529495320863961/62500000000000000)⟩
theorem valid3626 : certificate3626.Valid := by decide +kernel
theorem sound3626 : certificate3626.Sound := rat_cut_bin_certificate_sound certificate3626 profilesValid3626 numericValid3626 valid3626

def retention3627 : RatCutRetentionCertificate := ⟨(67/1000),(27/400),(965840614147642731/47062625165987385095),(478138917894872639/500000000000000000),(11/4),(8812843085458346597/4000000000000000000),true,MergedCutProfiles.Batch557.profile22289,![MergedCutProfiles.Batch557.profile22289,MergedCutProfiles.Batch557.profile22290,MergedCutProfiles.Batch557.profile22291,MergedCutProfiles.Batch557.profile22292,MergedCutProfiles.Batch557.profile22293,MergedCutProfiles.Batch437.profile17499,MergedCutProfiles.Batch557.profile22294,MergedCutProfiles.Batch557.profile22295,MergedCutProfiles.Batch557.profile22296,MergedCutProfiles.Batch557.profile22297,MergedCutProfiles.Batch557.profile22298,MergedCutProfiles.Batch557.profile22299,MergedCutProfiles.Batch557.profile22300,MergedCutProfiles.Batch557.profile22301,MergedCutProfiles.Batch557.profile22302,MergedCutProfiles.Batch557.profile22303]⟩
theorem profilesValid3627 : retention3627.ProfilesValid := by
  change ∀ j : Fin 16, (retention3627.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch557.valid22289
  · exact MergedCutProfiles.Batch557.valid22290
  · exact MergedCutProfiles.Batch557.valid22291
  · exact MergedCutProfiles.Batch557.valid22292
  · exact MergedCutProfiles.Batch557.valid22293
  · exact MergedCutProfiles.Batch437.valid17499
  · exact MergedCutProfiles.Batch557.valid22294
  · exact MergedCutProfiles.Batch557.valid22295
  · exact MergedCutProfiles.Batch557.valid22296
  · exact MergedCutProfiles.Batch557.valid22297
  · exact MergedCutProfiles.Batch557.valid22298
  · exact MergedCutProfiles.Batch557.valid22299
  · exact MergedCutProfiles.Batch557.valid22300
  · exact MergedCutProfiles.Batch557.valid22301
  · exact MergedCutProfiles.Batch557.valid22302
  · exact MergedCutProfiles.Batch557.valid22303
theorem numericValid3627 : retention3627.NumericValid := by decide +kernel
def certificate3627 : RatCutBinCertificate := ⟨⟨retention3627,(2311588734462153949/1000000000000000000),(121143195939341811/500000000000000000),(452907603621399993/25000000000000000),(213836632946619844371/250000000000000000),(211818521954031287/100000000000000000)⟩,(997939080072713513/1000000000000000000),(270341958347288799/1000000000000000000),(75196440148907267/200000000000000000),(223435897174660871/1000000000000000000)⟩
theorem valid3627 : certificate3627.Valid := by decide +kernel
theorem sound3627 : certificate3627.Sound := rat_cut_bin_certificate_sound certificate3627 profilesValid3627 numericValid3627 valid3627

def retention3628 : RatCutRetentionCertificate := ⟨(67/1000),(27/400),(221651197400000000/9412525033197477019),(965840614147642731/1000000000000000000),(27/10),(174657659879831718489/80000000000000000000),true,MergedCutProfiles.Batch557.profile22304,![MergedCutProfiles.Batch557.profile22304,MergedCutProfiles.Batch557.profile22305,MergedCutProfiles.Batch557.profile22306,MergedCutProfiles.Batch557.profile22307,MergedCutProfiles.Batch557.profile22308,MergedCutProfiles.Batch557.profile22309,MergedCutProfiles.Batch557.profile22295,MergedCutProfiles.Batch557.profile22310,MergedCutProfiles.Batch437.profile17485,MergedCutProfiles.Batch557.profile22311,MergedCutProfiles.Batch557.profile22312,MergedCutProfiles.Batch557.profile22313,MergedCutProfiles.Batch437.profile17502,MergedCutProfiles.Batch557.profile22303,MergedCutProfiles.Batch557.profile22314,MergedCutProfiles.Batch557.profile22315]⟩
theorem profilesValid3628 : retention3628.ProfilesValid := by
  change ∀ j : Fin 16, (retention3628.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch557.valid22304
  · exact MergedCutProfiles.Batch557.valid22305
  · exact MergedCutProfiles.Batch557.valid22306
  · exact MergedCutProfiles.Batch557.valid22307
  · exact MergedCutProfiles.Batch557.valid22308
  · exact MergedCutProfiles.Batch557.valid22309
  · exact MergedCutProfiles.Batch557.valid22295
  · exact MergedCutProfiles.Batch557.valid22310
  · exact MergedCutProfiles.Batch437.valid17485
  · exact MergedCutProfiles.Batch557.valid22311
  · exact MergedCutProfiles.Batch557.valid22312
  · exact MergedCutProfiles.Batch557.valid22313
  · exact MergedCutProfiles.Batch437.valid17502
  · exact MergedCutProfiles.Batch557.valid22303
  · exact MergedCutProfiles.Batch557.valid22314
  · exact MergedCutProfiles.Batch557.valid22315
theorem numericValid3628 : retention3628.NumericValid := by decide +kernel
def certificate3628 : RatCutBinCertificate := ⟨⟨retention3628,(2311588734462153949/1000000000000000000),(121143195939341811/500000000000000000),(452907603621399993/25000000000000000),(213836632946619844371/250000000000000000),(1049870519983367009/500000000000000000)⟩,(997939080072713513/1000000000000000000),(271566366627031409/1000000000000000000),(23399058484114629/62500000000000000),(6991018218626043/31250000000000000)⟩
theorem valid3628 : certificate3628.Valid := by decide +kernel
theorem sound3628 : certificate3628.Sound := rat_cut_bin_certificate_sound certificate3628 profilesValid3628 numericValid3628 valid3628

def retention3629 : RatCutRetentionCertificate := ⟨(67/1000),(27/400),(1143849319335010841/47062625165987385095),(1108255987/1000000000),(12/5),(433369286703444951/200000000000000000),true,MergedCutProfiles.Batch557.profile22316,![MergedCutProfiles.Batch557.profile22316,MergedCutProfiles.Batch557.profile22317,MergedCutProfiles.Batch557.profile22318,MergedCutProfiles.Batch557.profile22319,MergedCutProfiles.Batch437.profile17511,MergedCutProfiles.Batch558.profile22320,MergedCutProfiles.Batch558.profile22321,MergedCutProfiles.Batch558.profile22322,MergedCutProfiles.Batch558.profile22323,MergedCutProfiles.Batch437.profile17512,MergedCutProfiles.Batch557.profile22300,MergedCutProfiles.Batch558.profile22324,MergedCutProfiles.Batch558.profile22325,MergedCutProfiles.Batch558.profile22326,MergedCutProfiles.Batch437.profile17513,MergedCutProfiles.Batch558.profile22327]⟩
theorem profilesValid3629 : retention3629.ProfilesValid := by
  change ∀ j : Fin 16, (retention3629.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch557.valid22316
  · exact MergedCutProfiles.Batch557.valid22317
  · exact MergedCutProfiles.Batch557.valid22318
  · exact MergedCutProfiles.Batch557.valid22319
  · exact MergedCutProfiles.Batch437.valid17511
  · exact MergedCutProfiles.Batch558.valid22320
  · exact MergedCutProfiles.Batch558.valid22321
  · exact MergedCutProfiles.Batch558.valid22322
  · exact MergedCutProfiles.Batch558.valid22323
  · exact MergedCutProfiles.Batch437.valid17512
  · exact MergedCutProfiles.Batch557.valid22300
  · exact MergedCutProfiles.Batch558.valid22324
  · exact MergedCutProfiles.Batch558.valid22325
  · exact MergedCutProfiles.Batch558.valid22326
  · exact MergedCutProfiles.Batch437.valid17513
  · exact MergedCutProfiles.Batch558.valid22327
theorem numericValid3629 : retention3629.NumericValid := by decide +kernel
def certificate3629 : RatCutBinCertificate := ⟨⟨retention3629,(2311588734462153949/1000000000000000000),(121143195939341811/500000000000000000),(452907603621399993/25000000000000000),(213836632946619844371/250000000000000000),(2092642405853469121/1000000000000000000)⟩,(997939080072713513/1000000000000000000),(257655833977185243/1000000000000000000),(392859435551693713/1000000000000000000),(257340224115969677/1000000000000000000)⟩
theorem valid3629 : certificate3629.Valid := by decide +kernel
theorem sound3629 : certificate3629.Sound := rat_cut_bin_certificate_sound certificate3629 profilesValid3629 numericValid3629 valid3629

def retention3630 : RatCutRetentionCertificate := ⟨(67/1000),(27/400),(1652949738229380919/47062625165987385095),(1143849319335010841/1000000000000000000),(47/20),(42559312231157210683/20000000000000000000),true,MergedCutProfiles.Batch558.profile22328,![MergedCutProfiles.Batch558.profile22328,MergedCutProfiles.Batch558.profile22329,MergedCutProfiles.Batch437.profile17483,MergedCutProfiles.Batch558.profile22330,MergedCutProfiles.Batch558.profile22331,MergedCutProfiles.Batch437.profile17485,MergedCutProfiles.Batch437.profile17501,MergedCutProfiles.Batch558.profile22332,MergedCutProfiles.Batch558.profile22325,MergedCutProfiles.Batch558.profile22333,MergedCutProfiles.Batch558.profile22334,MergedCutProfiles.Batch437.profile17489,MergedCutProfiles.Batch558.profile22335,MergedCutProfiles.Batch558.profile22336,MergedCutProfiles.Batch437.profile17491,MergedCutProfiles.Batch558.profile22337]⟩
theorem profilesValid3630 : retention3630.ProfilesValid := by
  change ∀ j : Fin 16, (retention3630.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch558.valid22328
  · exact MergedCutProfiles.Batch558.valid22329
  · exact MergedCutProfiles.Batch437.valid17483
  · exact MergedCutProfiles.Batch558.valid22330
  · exact MergedCutProfiles.Batch558.valid22331
  · exact MergedCutProfiles.Batch437.valid17485
  · exact MergedCutProfiles.Batch437.valid17501
  · exact MergedCutProfiles.Batch558.valid22332
  · exact MergedCutProfiles.Batch558.valid22325
  · exact MergedCutProfiles.Batch558.valid22333
  · exact MergedCutProfiles.Batch558.valid22334
  · exact MergedCutProfiles.Batch437.valid17489
  · exact MergedCutProfiles.Batch558.valid22335
  · exact MergedCutProfiles.Batch558.valid22336
  · exact MergedCutProfiles.Batch437.valid17491
  · exact MergedCutProfiles.Batch558.valid22337
theorem numericValid3630 : retention3630.NumericValid := by decide +kernel
def certificate3630 : RatCutBinCertificate := ⟨⟨retention3630,(2311588734462153949/1000000000000000000),(121143195939341811/500000000000000000),(452907603621399993/25000000000000000),(213836632946619844371/250000000000000000),(1027653791198024957/500000000000000000)⟩,(997939080072713513/1000000000000000000),(259149344421489567/1000000000000000000),(195420494227633367/500000000000000000),(257276391566370529/1000000000000000000)⟩
theorem valid3630 : certificate3630.Valid := by decide +kernel
theorem sound3630 : certificate3630.Sound := rat_cut_bin_certificate_sound certificate3630 profilesValid3630 numericValid3630 valid3630

def retention3631 : RatCutRetentionCertificate := ⟨(67/1000),(27/400),(7651581537272472909/47062625165987385095),(1652949738229380919/1000000000000000000),(9/5),(2219792280219700304211/1280000000000000000000),true,MergedCutProfiles.Batch558.profile22338,![MergedCutProfiles.Batch558.profile22338,MergedCutProfiles.Batch558.profile22339,MergedCutProfiles.Batch437.profile17514,MergedCutProfiles.Batch558.profile22340,MergedCutProfiles.Batch558.profile22341,MergedCutProfiles.Batch437.profile17518,MergedCutProfiles.Batch558.profile22342,MergedCutProfiles.Batch558.profile22343,MergedCutProfiles.Batch558.profile22344,MergedCutProfiles.Batch558.profile22345,MergedCutProfiles.Batch558.profile22346,MergedCutProfiles.Batch558.profile22347,MergedCutProfiles.Batch558.profile22348,MergedCutProfiles.Batch558.profile22349,MergedCutProfiles.Batch558.profile22350,MergedCutProfiles.Batch558.profile22351]⟩
theorem profilesValid3631 : retention3631.ProfilesValid := by
  change ∀ j : Fin 16, (retention3631.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch558.valid22338
  · exact MergedCutProfiles.Batch558.valid22339
  · exact MergedCutProfiles.Batch437.valid17514
  · exact MergedCutProfiles.Batch558.valid22340
  · exact MergedCutProfiles.Batch558.valid22341
  · exact MergedCutProfiles.Batch437.valid17518
  · exact MergedCutProfiles.Batch558.valid22342
  · exact MergedCutProfiles.Batch558.valid22343
  · exact MergedCutProfiles.Batch558.valid22344
  · exact MergedCutProfiles.Batch558.valid22345
  · exact MergedCutProfiles.Batch558.valid22346
  · exact MergedCutProfiles.Batch558.valid22347
  · exact MergedCutProfiles.Batch558.valid22348
  · exact MergedCutProfiles.Batch558.valid22349
  · exact MergedCutProfiles.Batch558.valid22350
  · exact MergedCutProfiles.Batch558.valid22351
theorem numericValid3631 : retention3631.NumericValid := by decide +kernel
def certificate3631 : RatCutBinCertificate := ⟨⟨retention3631,(2311588734462153949/1000000000000000000),(121143195939341811/500000000000000000),(452907603621399993/25000000000000000),(213836632946619844371/250000000000000000),(67142413063095413/40000000000000000)⟩,(997939080072713513/1000000000000000000),(69973422788549911/250000000000000000),(45458221374429181/125000000000000000),(257575350605224781/1000000000000000000)⟩
theorem valid3631 : certificate3631.Valid := by decide +kernel
theorem sound3631 : certificate3631.Sound := rat_cut_bin_certificate_sound certificate3631 profilesValid3631 numericValid3631 valid3631

def retention3632 : RatCutRetentionCertificate := ⟨(67/1000),(27/400),(21112095240496121224/47062625165987385095),(7651581537272472909/1000000000000000000),1,(272881808375599980669/256000000000000000000),true,MergedCutProfiles.Batch558.profile22352,![MergedCutProfiles.Batch558.profile22352,MergedCutProfiles.Batch558.profile22353,MergedCutProfiles.Batch304.profile12182,MergedCutProfiles.Batch304.profile12174,MergedCutProfiles.Batch558.profile22354,MergedCutProfiles.Batch438.profile17533,MergedCutProfiles.Batch558.profile22355,MergedCutProfiles.Batch558.profile22356,MergedCutProfiles.Batch558.profile22357,MergedCutProfiles.Batch558.profile22358,MergedCutProfiles.Batch558.profile22359,MergedCutProfiles.Batch559.profile22360,MergedCutProfiles.Batch559.profile22361,MergedCutProfiles.Batch559.profile22362,MergedCutProfiles.Batch559.profile22363,MergedCutProfiles.Batch559.profile22364]⟩
theorem profilesValid3632 : retention3632.ProfilesValid := by
  change ∀ j : Fin 16, (retention3632.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch558.valid22352
  · exact MergedCutProfiles.Batch558.valid22353
  · exact MergedCutProfiles.Batch304.valid12182
  · exact MergedCutProfiles.Batch304.valid12174
  · exact MergedCutProfiles.Batch558.valid22354
  · exact MergedCutProfiles.Batch438.valid17533
  · exact MergedCutProfiles.Batch558.valid22355
  · exact MergedCutProfiles.Batch558.valid22356
  · exact MergedCutProfiles.Batch558.valid22357
  · exact MergedCutProfiles.Batch558.valid22358
  · exact MergedCutProfiles.Batch558.valid22359
  · exact MergedCutProfiles.Batch559.valid22360
  · exact MergedCutProfiles.Batch559.valid22361
  · exact MergedCutProfiles.Batch559.valid22362
  · exact MergedCutProfiles.Batch559.valid22363
  · exact MergedCutProfiles.Batch559.valid22364
theorem numericValid3632 : retention3632.NumericValid := by decide +kernel
def certificate3632 : RatCutBinCertificate := ⟨⟨retention3632,(2311588734462153949/1000000000000000000),(121143195939341811/500000000000000000),(452907603621399993/25000000000000000),(213836632946619844371/250000000000000000),(64689272936297583/62500000000000000)⟩,(997939080072713513/1000000000000000000),(86755400482619313/250000000000000000),(142847715254712283/500000000000000000),(51977781254995069/200000000000000000)⟩
theorem valid3632 : certificate3632.Valid := by decide +kernel
theorem sound3632 : certificate3632.Sound := rat_cut_bin_certificate_sound certificate3632 profilesValid3632 numericValid3632 valid3632

def retention3633 : RatCutRetentionCertificate := ⟨(67/1000),(27/400),(23320887516440600264/47062625165987385095),(2639011905062015153/125000000000000000),1,(84323571791762190556808999292561281479/84448380961984484896000000000000000000),false,MergedCutProfiles.Batch559.profile22365,(fun _ => MergedCutProfiles.Batch559.profile22365)⟩
theorem profilesValid3633 : retention3633.ProfilesValid := by
  exact MergedCutProfiles.Batch559.valid22365
theorem numericValid3633 : retention3633.NumericValid := by decide +kernel
def certificate3633 : RatCutBinCertificate := ⟨⟨retention3633,(2311588734462153949/1000000000000000000),(121143195939341811/500000000000000000),(452907603621399993/25000000000000000),(213836632946619844371/250000000000000000),(967606598264330327/1000000000000000000)⟩,(997939080072713513/1000000000000000000),(87778199014069751/250000000000000000),(281390154221552353/1000000000000000000),(8118415760977001/31250000000000000)⟩
theorem valid3633 : certificate3633.Valid := by decide +kernel
theorem sound3633 : certificate3633.Sound := rat_cut_bin_certificate_sound certificate3633 profilesValid3633 numericValid3633 valid3633

def retention3634 : RatCutRetentionCertificate := ⟨(67/1000),(27/400),(1/2),(2915110939555075033/125000000000000000),1,(18486888651768094511190447078959594403/18656710013152480211200000000000000000),false,MergedCutProfiles.Batch305.profile12226,(fun _ => MergedCutProfiles.Batch305.profile12226)⟩
theorem profilesValid3634 : retention3634.ProfilesValid := by
  exact MergedCutProfiles.Batch305.valid12226
theorem numericValid3634 : retention3634.NumericValid := by decide +kernel
def certificate3634 : RatCutBinCertificate := ⟨⟨retention3634,(2311588734462153949/1000000000000000000),(121143195939341811/500000000000000000),(452907603621399993/25000000000000000),(213836632946619844371/250000000000000000),(959982143890308623/1000000000000000000)⟩,(997939080072713513/1000000000000000000),(70562254593787109/200000000000000000),(279616813959393383/1000000000000000000),(257267712344594483/1000000000000000000)⟩
theorem valid3634 : certificate3634.Valid := by decide +kernel
theorem sound3634 : certificate3634.Sound := rat_cut_bin_certificate_sound certificate3634 profilesValid3634 numericValid3634 valid3634

def retention3635 : RatCutRetentionCertificate := ⟨(67/1000),(27/400),(21680512024897593708/47062625165987385095),(4170495489663091047/500000000000000000),1,(1744817354404201760493182112787675303/1668198195865236418800000000000000000),false,MergedCutProfiles.Batch559.profile22366,(fun _ => MergedCutProfiles.Batch559.profile22366)⟩
theorem profilesValid3635 : retention3635.ProfilesValid := by
  exact MergedCutProfiles.Batch559.valid22366
theorem numericValid3635 : retention3635.NumericValid := by decide +kernel
def certificate3635 : RatCutBinCertificate := ⟨⟨retention3635,(2353563829462153949/1000000000000000000),(121143195939341811/500000000000000000),(452907603621399993/25000000000000000),(213836632946619844371/250000000000000000),(1014451795972815347/1000000000000000000)⟩,(249475408061513141/250000000000000000),(116409835977729261/1000000000000000000),(630975672709638199/1000000000000000000),(142350024636064469/250000000000000000)⟩
theorem valid3635 : certificate3635.Valid := by decide +kernel
theorem sound3635 : certificate3635.Sound := rat_cut_bin_certificate_sound certificate3635 profilesValid3635 numericValid3635 valid3635

def certificates : List RatCutBinCertificate := [certificate3624,certificate3625,certificate3626,certificate3627,certificate3628,certificate3629,certificate3630,certificate3631,certificate3632,certificate3633,certificate3634,certificate3635]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3624,List.forall_mem_cons.mpr ⟨sound3625,List.forall_mem_cons.mpr ⟨sound3626,List.forall_mem_cons.mpr ⟨sound3627,List.forall_mem_cons.mpr ⟨sound3628,List.forall_mem_cons.mpr ⟨sound3629,List.forall_mem_cons.mpr ⟨sound3630,List.forall_mem_cons.mpr ⟨sound3631,List.forall_mem_cons.mpr ⟨sound3632,List.forall_mem_cons.mpr ⟨sound3633,List.forall_mem_cons.mpr ⟨sound3634,List.forall_mem_cons.mpr ⟨sound3635,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch302
