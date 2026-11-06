import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch512
import Cycle12.MergedCutProfiles.Batch513
import Cycle12.MergedCutProfiles.Batch514

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch278

def retention3336 : RatCutRetentionCertificate := ⟨(113/2000),(57/1000),(3053492109862961003/6404380869922312314),(3185051428818128617/200000000000000000),1,(65675713980488881715934232962851886579/63701028576362572340000000000000000000),false,MergedCutProfiles.Batch512.profile20492,(fun _ => MergedCutProfiles.Batch512.profile20492)⟩
theorem profilesValid3336 : retention3336.ProfilesValid := by
  exact MergedCutProfiles.Batch512.valid20492
theorem numericValid3336 : retention3336.NumericValid := by decide +kernel
def certificate3336 : RatCutBinCertificate := ⟨⟨retention3336,(2156782234939053039/1000000000000000000),(161735409484216873/1000000000000000000),(14898547127280195749/1000000000000000000),(1052721501435622198073/1000000000000000000),(503792741182763913/500000000000000000)⟩,(199655059546259973/200000000000000000),(422289120448130377/1000000000000000000),(53417374608605173/250000000000000000),(25264633697803039/125000000000000000)⟩
theorem valid3336 : certificate3336.Valid := by decide +kernel
theorem sound3336 : certificate3336.Sound := rat_cut_bin_certificate_sound certificate3336 profilesValid3336 numericValid3336 valid3336

def retention3337 : RatCutRetentionCertificate := ⟨(113/2000),(57/1000),(34952237474294335475/70448189569145435454),(33588413208492571033/1000000000000000000),1,(134587240796669282544590998572597273331/134353652833970284132000000000000000000),false,MergedCutProfiles.Batch512.profile20493,(fun _ => MergedCutProfiles.Batch512.profile20493)⟩
theorem profilesValid3337 : retention3337.ProfilesValid := by
  exact MergedCutProfiles.Batch512.valid20493
theorem numericValid3337 : retention3337.NumericValid := by decide +kernel
def certificate3337 : RatCutBinCertificate := ⟨⟨retention3337,(2156782234939053039/1000000000000000000),(161735409484216873/1000000000000000000),(14898547127280195749/1000000000000000000),(1052721501435622198073/1000000000000000000),(978324936057772317/1000000000000000000)⟩,(199655059546259973/200000000000000000),(423836582505937273/1000000000000000000),(212338349315750943/1000000000000000000),(201501872803161089/1000000000000000000)⟩
theorem valid3337 : certificate3337.Valid := by decide +kernel
theorem sound3337 : certificate3337.Sound := rat_cut_bin_certificate_sound certificate3337 profilesValid3337 numericValid3337 valid3337

def retention3338 : RatCutRetentionCertificate := ⟨(113/2000),(57/1000),(1/2),(1398089498971773419/40000000000000000),1,(139027626094944729687869665213498528419/139808949897177341900000000000000000000),false,MergedCutProfiles.Batch512.profile20494,(fun _ => MergedCutProfiles.Batch512.profile20494)⟩
theorem profilesValid3338 : retention3338.ProfilesValid := by
  exact MergedCutProfiles.Batch512.valid20494
theorem numericValid3338 : retention3338.NumericValid := by decide +kernel
def certificate3338 : RatCutBinCertificate := ⟨⟨retention3338,(2156782234939053039/1000000000000000000),(161735409484216873/1000000000000000000),(14898547127280195749/1000000000000000000),(1052721501435622198073/1000000000000000000),(3792960251506151/3906250000000000)⟩,(199655059546259973/200000000000000000),(213320999926659957/500000000000000000),(209939477221008497/1000000000000000000),(197992560129019671/1000000000000000000)⟩
theorem valid3338 : certificate3338.Valid := by decide +kernel
theorem sound3338 : certificate3338.Sound := rat_cut_bin_certificate_sound certificate3338 profilesValid3338 numericValid3338 valid3338

def retention3339 : RatCutRetentionCertificate := ⟨(113/2000),(57/1000),(16171012426834682389/35224094784572717727),(9606376526945960059/1000000000000000000),1,(40479158418251852952894375009808036083/38425506107783840236000000000000000000),false,MergedCutProfiles.Batch512.profile20495,(fun _ => MergedCutProfiles.Batch512.profile20495)⟩
theorem profilesValid3339 : retention3339.ProfilesValid := by
  exact MergedCutProfiles.Batch512.valid20495
theorem numericValid3339 : retention3339.NumericValid := by decide +kernel
def certificate3339 : RatCutBinCertificate := ⟨⟨retention3339,(2249643230939053039/1000000000000000000),(161735409484216873/1000000000000000000),(14898547127280195749/1000000000000000000),(1052721501435622198073/1000000000000000000),(514511499007461541/500000000000000000)⟩,(249550253733380181/250000000000000000),(11891175268161623/100000000000000000),(625754414685656403/1000000000000000000),(290253643273576871/500000000000000000)⟩
theorem valid3339 : certificate3339.Valid := by decide +kernel
theorem sound3339 : certificate3339.Sound := rat_cut_bin_certificate_sound certificate3339 profilesValid3339 numericValid3339 valid3339

def retention3340 : RatCutRetentionCertificate := ⟨(113/2000),(57/1000),(69213000961236952/139225671085267659),(16171012426834682389/500000000000000000),1,(6465158234016636744123447750991177599/6468404970733872955600000000000000000),false,MergedCutProfiles.Batch512.profile20496,(fun _ => MergedCutProfiles.Batch512.profile20496)⟩
theorem profilesValid3340 : retention3340.ProfilesValid := by
  exact MergedCutProfiles.Batch512.valid20496
theorem numericValid3340 : retention3340.NumericValid := by decide +kernel
def certificate3340 : RatCutBinCertificate := ⟨⟨retention3340,(2249643230939053039/1000000000000000000),(161735409484216873/1000000000000000000),(14898547127280195749/1000000000000000000),(1052721501435622198073/1000000000000000000),(243769076310249681/250000000000000000)⟩,(249550253733380181/250000000000000000),(125490618104398223/1000000000000000000),(153059250738886829/250000000000000000),(144611151769859921/250000000000000000)⟩
theorem valid3340 : certificate3340.Valid := by decide +kernel
theorem sound3340 : certificate3340.Sound := rat_cut_bin_certificate_sound certificate3340 profilesValid3340 numericValid3340 valid3340

def retention3341 : RatCutRetentionCertificate := ⟨(113/2000),(57/1000),(1/2),(2188861155399118607/62500000000000000),1,(12664202867366843884796922113142871317/12735192176867599168000000000000000000),false,MergedCutProfiles.Batch512.profile20494,(fun _ => MergedCutProfiles.Batch512.profile20494)⟩
theorem profilesValid3341 : retention3341.ProfilesValid := by
  exact MergedCutProfiles.Batch512.valid20494
theorem numericValid3341 : retention3341.NumericValid := by decide +kernel
def certificate3341 : RatCutBinCertificate := ⟨⟨retention3341,(2249643230939053039/1000000000000000000),(161735409484216873/1000000000000000000),(14898547127280195749/1000000000000000000),(1052721501435622198073/1000000000000000000),(970003988962519833/1000000000000000000)⟩,(249550253733380181/250000000000000000),(31536707486770399/250000000000000000),(3818157891993423/6250000000000000),(287777544762208403/500000000000000000)⟩
theorem valid3341 : certificate3341.Valid := by decide +kernel
theorem sound3341 : certificate3341.Sound := rat_cut_bin_certificate_sound certificate3341 profilesValid3341 numericValid3341 valid3341

def retention3342 : RatCutRetentionCertificate := ⟨(57/1000),(23/400),(214209983762515115/17255192072792048192),(212089092834173381/250000000000000000),(31/10),(44921525938396794367/20000000000000000000),true,MergedCutProfiles.Batch512.profile20497,![MergedCutProfiles.Batch512.profile20497,MergedCutProfiles.Batch512.profile20498,MergedCutProfiles.Batch512.profile20499,MergedCutProfiles.Batch512.profile20500,MergedCutProfiles.Batch512.profile20501,MergedCutProfiles.Batch512.profile20502,MergedCutProfiles.Batch512.profile20503,MergedCutProfiles.Batch512.profile20504,MergedCutProfiles.Batch512.profile20505,MergedCutProfiles.Batch512.profile20506,MergedCutProfiles.Batch512.profile20507,MergedCutProfiles.Batch512.profile20508,MergedCutProfiles.Batch512.profile20509,MergedCutProfiles.Batch512.profile20510,MergedCutProfiles.Batch512.profile20511,MergedCutProfiles.Batch512.profile20512]⟩
theorem profilesValid3342 : retention3342.ProfilesValid := by
  change ∀ j : Fin 16, (retention3342.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch512.valid20497
  · exact MergedCutProfiles.Batch512.valid20498
  · exact MergedCutProfiles.Batch512.valid20499
  · exact MergedCutProfiles.Batch512.valid20500
  · exact MergedCutProfiles.Batch512.valid20501
  · exact MergedCutProfiles.Batch512.valid20502
  · exact MergedCutProfiles.Batch512.valid20503
  · exact MergedCutProfiles.Batch512.valid20504
  · exact MergedCutProfiles.Batch512.valid20505
  · exact MergedCutProfiles.Batch512.valid20506
  · exact MergedCutProfiles.Batch512.valid20507
  · exact MergedCutProfiles.Batch512.valid20508
  · exact MergedCutProfiles.Batch512.valid20509
  · exact MergedCutProfiles.Batch512.valid20510
  · exact MergedCutProfiles.Batch512.valid20511
  · exact MergedCutProfiles.Batch512.valid20512
theorem numericValid3342 : retention3342.NumericValid := by decide +kernel
def certificate3342 : RatCutBinCertificate := ⟨⟨retention3342,(542436147691451017/250000000000000000),(165065648943161283/1000000000000000000),(15031403837523526189/1000000000000000000),(260149748406860929449/250000000000000000),(543052188076883701/250000000000000000)⟩,(49912577346804737/50000000000000000),(361872213120241449/1000000000000000000),(3378669010590373/12500000000000000),(37309944905347933/250000000000000000)⟩
theorem valid3342 : certificate3342.Valid := by decide +kernel
theorem sound3342 : certificate3342.Sound := rat_cut_bin_certificate_sound certificate3342 profilesValid3342 numericValid3342 valid3342

def retention3343 : RatCutRetentionCertificate := ⟨(57/1000),(23/400),(1035155994631432257/69020768291168192768),(42841996752503023/50000000000000000),(31/10),(4475108912304010249/2000000000000000000),true,MergedCutProfiles.Batch512.profile20513,![MergedCutProfiles.Batch512.profile20513,MergedCutProfiles.Batch512.profile20514,MergedCutProfiles.Batch512.profile20515,MergedCutProfiles.Batch512.profile20516,MergedCutProfiles.Batch512.profile20517,MergedCutProfiles.Batch512.profile20518,MergedCutProfiles.Batch512.profile20519,MergedCutProfiles.Batch513.profile20520,MergedCutProfiles.Batch513.profile20521,MergedCutProfiles.Batch513.profile20522,MergedCutProfiles.Batch513.profile20523,MergedCutProfiles.Batch513.profile20524,MergedCutProfiles.Batch513.profile20525,MergedCutProfiles.Batch513.profile20526,MergedCutProfiles.Batch513.profile20527,MergedCutProfiles.Batch513.profile20528]⟩
theorem profilesValid3343 : retention3343.ProfilesValid := by
  change ∀ j : Fin 16, (retention3343.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch512.valid20513
  · exact MergedCutProfiles.Batch512.valid20514
  · exact MergedCutProfiles.Batch512.valid20515
  · exact MergedCutProfiles.Batch512.valid20516
  · exact MergedCutProfiles.Batch512.valid20517
  · exact MergedCutProfiles.Batch512.valid20518
  · exact MergedCutProfiles.Batch512.valid20519
  · exact MergedCutProfiles.Batch513.valid20520
  · exact MergedCutProfiles.Batch513.valid20521
  · exact MergedCutProfiles.Batch513.valid20522
  · exact MergedCutProfiles.Batch513.valid20523
  · exact MergedCutProfiles.Batch513.valid20524
  · exact MergedCutProfiles.Batch513.valid20525
  · exact MergedCutProfiles.Batch513.valid20526
  · exact MergedCutProfiles.Batch513.valid20527
  · exact MergedCutProfiles.Batch513.valid20528
theorem numericValid3343 : retention3343.NumericValid := by decide +kernel
def certificate3343 : RatCutBinCertificate := ⟨⟨retention3343,(542436147691451017/250000000000000000),(165065648943161283/1000000000000000000),(15031403837523526189/1000000000000000000),(260149748406860929449/250000000000000000),(2163686955649935829/1000000000000000000)⟩,(49912577346804737/50000000000000000),(361541489557191499/1000000000000000000),(135314900541417661/500000000000000000),(29854503129728241/200000000000000000)⟩
theorem valid3343 : certificate3343.Valid := by decide +kernel
theorem sound3343 : certificate3343.Sound := rat_cut_bin_certificate_sound certificate3343 profilesValid3343 numericValid3343 valid3343

def retention3344 : RatCutRetentionCertificate := ⟨(57/1000),(23/400),(4236627414062500/269612376137375753),(1035155994631432257/1000000000000000000),(27/10),(2861085846893981522181/1280000000000000000000),true,MergedCutProfiles.Batch513.profile20529,![MergedCutProfiles.Batch513.profile20529,MergedCutProfiles.Batch513.profile20530,MergedCutProfiles.Batch513.profile20531,MergedCutProfiles.Batch513.profile20532,MergedCutProfiles.Batch513.profile20533,MergedCutProfiles.Batch513.profile20534,MergedCutProfiles.Batch513.profile20535,MergedCutProfiles.Batch513.profile20536,MergedCutProfiles.Batch513.profile20537,MergedCutProfiles.Batch513.profile20538,MergedCutProfiles.Batch513.profile20539,MergedCutProfiles.Batch513.profile20540,MergedCutProfiles.Batch513.profile20541,MergedCutProfiles.Batch513.profile20542,MergedCutProfiles.Batch513.profile20543,MergedCutProfiles.Batch513.profile20544]⟩
theorem profilesValid3344 : retention3344.ProfilesValid := by
  change ∀ j : Fin 16, (retention3344.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch513.valid20529
  · exact MergedCutProfiles.Batch513.valid20530
  · exact MergedCutProfiles.Batch513.valid20531
  · exact MergedCutProfiles.Batch513.valid20532
  · exact MergedCutProfiles.Batch513.valid20533
  · exact MergedCutProfiles.Batch513.valid20534
  · exact MergedCutProfiles.Batch513.valid20535
  · exact MergedCutProfiles.Batch513.valid20536
  · exact MergedCutProfiles.Batch513.valid20537
  · exact MergedCutProfiles.Batch513.valid20538
  · exact MergedCutProfiles.Batch513.valid20539
  · exact MergedCutProfiles.Batch513.valid20540
  · exact MergedCutProfiles.Batch513.valid20541
  · exact MergedCutProfiles.Batch513.valid20542
  · exact MergedCutProfiles.Batch513.valid20543
  · exact MergedCutProfiles.Batch513.valid20544
theorem numericValid3344 : retention3344.NumericValid := by decide +kernel
def certificate3344 : RatCutBinCertificate := ⟨⟨retention3344,(542436147691451017/250000000000000000),(165065648943161283/1000000000000000000),(15031403837523526189/1000000000000000000),(260149748406860929449/250000000000000000),(2170887298450180507/1000000000000000000)⟩,(49912577346804737/50000000000000000),(165097098757421953/500000000000000000),(151957985899341219/500000000000000000),(189376056848831341/1000000000000000000)⟩
theorem valid3344 : certificate3344.Valid := by decide +kernel
theorem sound3344 : certificate3344.Sound := rat_cut_bin_certificate_sound certificate3344 profilesValid3344 numericValid3344 valid3344

def retention3345 : RatCutRetentionCertificate := ⟨(57/1000),(23/400),(1109827336789852779/69020768291168192768),(542288309/500000000),(13/5),(4461225886617093499/2000000000000000000),true,MergedCutProfiles.Batch513.profile20529,![MergedCutProfiles.Batch513.profile20529,MergedCutProfiles.Batch513.profile20545,MergedCutProfiles.Batch513.profile20546,MergedCutProfiles.Batch513.profile20547,MergedCutProfiles.Batch513.profile20548,MergedCutProfiles.Batch513.profile20549,MergedCutProfiles.Batch512.profile20505,MergedCutProfiles.Batch513.profile20550,MergedCutProfiles.Batch513.profile20551,MergedCutProfiles.Batch512.profile20509,MergedCutProfiles.Batch513.profile20552,MergedCutProfiles.Batch513.profile20553,MergedCutProfiles.Batch513.profile20526,MergedCutProfiles.Batch513.profile20527,MergedCutProfiles.Batch513.profile20554,MergedCutProfiles.Batch513.profile20555]⟩
theorem profilesValid3345 : retention3345.ProfilesValid := by
  change ∀ j : Fin 16, (retention3345.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch513.valid20529
  · exact MergedCutProfiles.Batch513.valid20545
  · exact MergedCutProfiles.Batch513.valid20546
  · exact MergedCutProfiles.Batch513.valid20547
  · exact MergedCutProfiles.Batch513.valid20548
  · exact MergedCutProfiles.Batch513.valid20549
  · exact MergedCutProfiles.Batch512.valid20505
  · exact MergedCutProfiles.Batch513.valid20550
  · exact MergedCutProfiles.Batch513.valid20551
  · exact MergedCutProfiles.Batch512.valid20509
  · exact MergedCutProfiles.Batch513.valid20552
  · exact MergedCutProfiles.Batch513.valid20553
  · exact MergedCutProfiles.Batch513.valid20526
  · exact MergedCutProfiles.Batch513.valid20527
  · exact MergedCutProfiles.Batch513.valid20554
  · exact MergedCutProfiles.Batch513.valid20555
theorem numericValid3345 : retention3345.NumericValid := by decide +kernel
def certificate3345 : RatCutBinCertificate := ⟨⟨retention3345,(542436147691451017/250000000000000000),(165065648943161283/1000000000000000000),(15031403837523526189/1000000000000000000),(260149748406860929449/250000000000000000),(8674639082203813/4000000000000000)⟩,(49912577346804737/50000000000000000),(32392545257589549/100000000000000000),(1943251151189853/6250000000000000),(199727966398800777/1000000000000000000)⟩
theorem valid3345 : certificate3345.Valid := by decide +kernel
theorem sound3345 : certificate3345.Sound := rat_cut_bin_certificate_sound certificate3345 profilesValid3345 numericValid3345 valid3345

def retention3346 : RatCutRetentionCertificate := ⟨(57/1000),(23/400),(381486687874550143/17255192072792048192),(1109827336789852779/1000000000000000000),(51/20),(2815229025479195340763/1280000000000000000000),true,MergedCutProfiles.Batch513.profile20556,![MergedCutProfiles.Batch513.profile20556,MergedCutProfiles.Batch513.profile20557,MergedCutProfiles.Batch513.profile20558,MergedCutProfiles.Batch513.profile20559,MergedCutProfiles.Batch514.profile20560,MergedCutProfiles.Batch514.profile20561,MergedCutProfiles.Batch514.profile20562,MergedCutProfiles.Batch513.profile20552,MergedCutProfiles.Batch512.profile20512,MergedCutProfiles.Batch513.profile20542,MergedCutProfiles.Batch514.profile20563,MergedCutProfiles.Batch514.profile20564,MergedCutProfiles.Batch514.profile20565,MergedCutProfiles.Batch514.profile20566,MergedCutProfiles.Batch514.profile20567,MergedCutProfiles.Batch514.profile20568]⟩
theorem profilesValid3346 : retention3346.ProfilesValid := by
  change ∀ j : Fin 16, (retention3346.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch513.valid20556
  · exact MergedCutProfiles.Batch513.valid20557
  · exact MergedCutProfiles.Batch513.valid20558
  · exact MergedCutProfiles.Batch513.valid20559
  · exact MergedCutProfiles.Batch514.valid20560
  · exact MergedCutProfiles.Batch514.valid20561
  · exact MergedCutProfiles.Batch514.valid20562
  · exact MergedCutProfiles.Batch513.valid20552
  · exact MergedCutProfiles.Batch512.valid20512
  · exact MergedCutProfiles.Batch513.valid20542
  · exact MergedCutProfiles.Batch514.valid20563
  · exact MergedCutProfiles.Batch514.valid20564
  · exact MergedCutProfiles.Batch514.valid20565
  · exact MergedCutProfiles.Batch514.valid20566
  · exact MergedCutProfiles.Batch514.valid20567
  · exact MergedCutProfiles.Batch514.valid20568
theorem numericValid3346 : retention3346.NumericValid := by decide +kernel
def certificate3346 : RatCutBinCertificate := ⟨⟨retention3346,(542436147691451017/250000000000000000),(165065648943161283/1000000000000000000),(15031403837523526189/1000000000000000000),(260149748406860929449/250000000000000000),(2138635922837027327/1000000000000000000)⟩,(49912577346804737/50000000000000000),(162639856735572559/500000000000000000),(154698435607298309/500000000000000000),(199755377761829851/1000000000000000000)⟩
theorem valid3346 : certificate3346.Valid := by decide +kernel
theorem sound3346 : certificate3346.Sound := rat_cut_bin_certificate_sound certificate3346 profilesValid3346 numericValid3346 valid3346

def retention3347 : RatCutRetentionCertificate := ⟨(57/1000),(23/400),(4266846778692942289/34510384145584096384),(381486687874550143/250000000000000000),2,(117768218620431165731/64000000000000000000),true,MergedCutProfiles.Batch512.profile20506,![MergedCutProfiles.Batch512.profile20506,MergedCutProfiles.Batch514.profile20569,MergedCutProfiles.Batch514.profile20570,MergedCutProfiles.Batch514.profile20571,MergedCutProfiles.Batch514.profile20572,MergedCutProfiles.Batch514.profile20573,MergedCutProfiles.Batch514.profile20574,MergedCutProfiles.Batch514.profile20575,MergedCutProfiles.Batch514.profile20576,MergedCutProfiles.Batch514.profile20577,MergedCutProfiles.Batch514.profile20578,MergedCutProfiles.Batch514.profile20579,MergedCutProfiles.Batch514.profile20580,MergedCutProfiles.Batch514.profile20581,MergedCutProfiles.Batch514.profile20582,MergedCutProfiles.Batch514.profile20583]⟩
theorem profilesValid3347 : retention3347.ProfilesValid := by
  change ∀ j : Fin 16, (retention3347.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch512.valid20506
  · exact MergedCutProfiles.Batch514.valid20569
  · exact MergedCutProfiles.Batch514.valid20570
  · exact MergedCutProfiles.Batch514.valid20571
  · exact MergedCutProfiles.Batch514.valid20572
  · exact MergedCutProfiles.Batch514.valid20573
  · exact MergedCutProfiles.Batch514.valid20574
  · exact MergedCutProfiles.Batch514.valid20575
  · exact MergedCutProfiles.Batch514.valid20576
  · exact MergedCutProfiles.Batch514.valid20577
  · exact MergedCutProfiles.Batch514.valid20578
  · exact MergedCutProfiles.Batch514.valid20579
  · exact MergedCutProfiles.Batch514.valid20580
  · exact MergedCutProfiles.Batch514.valid20581
  · exact MergedCutProfiles.Batch514.valid20582
  · exact MergedCutProfiles.Batch514.valid20583
theorem numericValid3347 : retention3347.NumericValid := by decide +kernel
def certificate3347 : RatCutBinCertificate := ⟨⟨retention3347,(542436147691451017/250000000000000000),(165065648943161283/1000000000000000000),(15031403837523526189/1000000000000000000),(260149748406860929449/250000000000000000),(89623616648955811/50000000000000000)⟩,(49912577346804737/50000000000000000),(17173621225905523/50000000000000000),(289469314129108591/1000000000000000000),(200133426598553593/1000000000000000000)⟩
theorem valid3347 : certificate3347.Valid := by decide +kernel
theorem sound3347 : certificate3347.Sound := rat_cut_bin_certificate_sound certificate3347 profilesValid3347 numericValid3347 valid3347

def certificates : List RatCutBinCertificate := [certificate3336,certificate3337,certificate3338,certificate3339,certificate3340,certificate3341,certificate3342,certificate3343,certificate3344,certificate3345,certificate3346,certificate3347]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3336,List.forall_mem_cons.mpr ⟨sound3337,List.forall_mem_cons.mpr ⟨sound3338,List.forall_mem_cons.mpr ⟨sound3339,List.forall_mem_cons.mpr ⟨sound3340,List.forall_mem_cons.mpr ⟨sound3341,List.forall_mem_cons.mpr ⟨sound3342,List.forall_mem_cons.mpr ⟨sound3343,List.forall_mem_cons.mpr ⟨sound3344,List.forall_mem_cons.mpr ⟨sound3345,List.forall_mem_cons.mpr ⟨sound3346,List.forall_mem_cons.mpr ⟨sound3347,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch278
