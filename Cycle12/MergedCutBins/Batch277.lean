import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch510
import Cycle12.MergedCutProfiles.Batch511
import Cycle12.MergedCutProfiles.Batch512

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch277

def retention3324 : RatCutRetentionCertificate := ⟨(7/125),(113/2000),(35737374837202782671/71915481072141101315),(31090192738247238247/1000000000000000000),1,(485569996444662655287791302653923731/485784261535113097609375000000000000),false,MergedCutProfiles.Batch510.profile20408,(fun _ => MergedCutProfiles.Batch510.profile20408)⟩
theorem profilesValid3324 : retention3324.ProfilesValid := by
  exact MergedCutProfiles.Batch510.valid20408
theorem numericValid3324 : retention3324.NumericValid := by decide +kernel
def certificate3324 : RatCutBinCertificate := ⟨⟨retention3324,(2157109970855523329/1000000000000000000),(39612838789917267/250000000000000000),(7383734865585826093/500000000000000000),(266295555735450815613/250000000000000000),(976413553941501291/1000000000000000000)⟩,(998288672261469089/1000000000000000000),(428954007597450319/1000000000000000000),(103988190290399651/500000000000000000),(196543923871352967/1000000000000000000)⟩
theorem valid3324 : certificate3324.Valid := by decide +kernel
theorem sound3324 : certificate3324.Sound := rat_cut_bin_certificate_sound certificate3324 profilesValid3324 numericValid3324 valid3324

def retention3325 : RatCutRetentionCertificate := ⟨(7/125),(113/2000),(1/2),(35737374837202782671/1000000000000000000),1,(142172769688578659890669068055793437083/142949499348811130684000000000000000000),false,MergedCutProfiles.Batch510.profile20409,(fun _ => MergedCutProfiles.Batch510.profile20409)⟩
theorem profilesValid3325 : retention3325.ProfilesValid := by
  exact MergedCutProfiles.Batch510.valid20409
theorem numericValid3325 : retention3325.NumericValid := by decide +kernel
def certificate3325 : RatCutBinCertificate := ⟨⟨retention3325,(2157109970855523329/1000000000000000000),(39612838789917267/250000000000000000),(7383734865585826093/500000000000000000),(266295555735450815613/250000000000000000),(971421043980340407/1000000000000000000)⟩,(998288672261469089/1000000000000000000),(429722440956717789/1000000000000000000),(51831668840398903/250000000000000000),(97865239011406253/500000000000000000)⟩
theorem valid3325 : certificate3325.Valid := by decide +kernel
theorem sound3325 : certificate3325.Sound := rat_cut_bin_certificate_sound certificate3325 profilesValid3325 numericValid3325 valid3325

def retention3326 : RatCutRetentionCertificate := ⟨(7/125),(113/2000),(6605603640871014073/14383096214428220263),(9713003383763258499/1000000000000000000),1,(40928481851198195590188175898665737443/38852013535053033996000000000000000000),false,MergedCutProfiles.Batch510.profile20410,(fun _ => MergedCutProfiles.Batch510.profile20410)⟩
theorem profilesValid3326 : retention3326.ProfilesValid := by
  exact MergedCutProfiles.Batch510.valid20410
theorem numericValid3326 : retention3326.NumericValid := by decide +kernel
def certificate3326 : RatCutBinCertificate := ⟨⟨retention3326,(2243659312855523329/1000000000000000000),(39612838789917267/250000000000000000),(7383734865585826093/500000000000000000),(266295555735450815613/250000000000000000),(1029371290990491819/1000000000000000000)⟩,(249554996626425959/250000000000000000),(118432808675419253/1000000000000000000),(626750441733851409/1000000000000000000),(1819500561517251/3125000000000000)⟩
theorem valid3326 : certificate3326.Valid := by decide +kernel
theorem sound3326 : certificate3326.Sound := rat_cut_bin_certificate_sound certificate3326 profilesValid3326 numericValid3326 valid3326

def retention3327 : RatCutRetentionCertificate := ⟨(7/125),(113/2000),(7152922197238437825/14383096214428220263),(6605603640871014073/200000000000000000),1,(132018323248896756532676312400263265939/132112072817420281460000000000000000000),false,MergedCutProfiles.Batch510.profile20411,(fun _ => MergedCutProfiles.Batch510.profile20411)⟩
theorem profilesValid3327 : retention3327.ProfilesValid := by
  exact MergedCutProfiles.Batch510.valid20411
theorem numericValid3327 : retention3327.NumericValid := by decide +kernel
def certificate3327 : RatCutBinCertificate := ⟨⟨retention3327,(2243659312855523329/1000000000000000000),(39612838789917267/250000000000000000),(7383734865585826093/500000000000000000),(266295555735450815613/250000000000000000),(975216351842925849/1000000000000000000)⟩,(249554996626425959/250000000000000000),(31252381312993509/250000000000000000),(153303809522118003/250000000000000000),(579813798413180931/1000000000000000000)⟩
theorem valid3327 : certificate3327.Valid := by decide +kernel
theorem sound3327 : certificate3327.Sound := rat_cut_bin_certificate_sound certificate3327 profilesValid3327 numericValid3327 valid3327

def retention3328 : RatCutRetentionCertificate := ⟨(7/125),(113/2000),(1/2),(286116887889537513/8000000000000000),1,(142281886859610602522136606679413556211/143058443944768756500000000000000000000),false,MergedCutProfiles.Batch510.profile20409,(fun _ => MergedCutProfiles.Batch510.profile20409)⟩
theorem profilesValid3328 : retention3328.ProfilesValid := by
  exact MergedCutProfiles.Batch510.valid20409
theorem numericValid3328 : retention3328.NumericValid := by decide +kernel
def certificate3328 : RatCutBinCertificate := ⟨⟨retention3328,(2243659312855523329/1000000000000000000),(39612838789917267/250000000000000000),(7383734865585826093/500000000000000000),(266295555735450815613/250000000000000000),(194099546208389171/200000000000000000)⟩,(249554996626425959/250000000000000000),(125617329399585283/1000000000000000000),(305989809599088131/500000000000000000),(144296916997046023/250000000000000000)⟩
theorem valid3328 : certificate3328.Valid := by decide +kernel
theorem sound3328 : certificate3328.Sound := rat_cut_bin_certificate_sound certificate3328 profilesValid3328 numericValid3328 valid3328

def retention3329 : RatCutRetentionCertificate := ⟨(113/2000),(57/1000),(854284568505552001/70448189569145435454),(169165261090208317/200000000000000000),(63/20),(1804563062433190053/800000000000000000),true,MergedCutProfiles.Batch510.profile20412,![MergedCutProfiles.Batch510.profile20412,MergedCutProfiles.Batch510.profile20413,MergedCutProfiles.Batch510.profile20414,MergedCutProfiles.Batch510.profile20415,MergedCutProfiles.Batch510.profile20416,MergedCutProfiles.Batch510.profile20417,MergedCutProfiles.Batch510.profile20418,MergedCutProfiles.Batch510.profile20419,MergedCutProfiles.Batch510.profile20420,MergedCutProfiles.Batch510.profile20421,MergedCutProfiles.Batch510.profile20422,MergedCutProfiles.Batch510.profile20423,MergedCutProfiles.Batch510.profile20424,MergedCutProfiles.Batch510.profile20425,MergedCutProfiles.Batch510.profile20426,MergedCutProfiles.Batch510.profile20427]⟩
theorem profilesValid3329 : retention3329.ProfilesValid := by
  change ∀ j : Fin 16, (retention3329.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch510.valid20412
  · exact MergedCutProfiles.Batch510.valid20413
  · exact MergedCutProfiles.Batch510.valid20414
  · exact MergedCutProfiles.Batch510.valid20415
  · exact MergedCutProfiles.Batch510.valid20416
  · exact MergedCutProfiles.Batch510.valid20417
  · exact MergedCutProfiles.Batch510.valid20418
  · exact MergedCutProfiles.Batch510.valid20419
  · exact MergedCutProfiles.Batch510.valid20420
  · exact MergedCutProfiles.Batch510.valid20421
  · exact MergedCutProfiles.Batch510.valid20422
  · exact MergedCutProfiles.Batch510.valid20423
  · exact MergedCutProfiles.Batch510.valid20424
  · exact MergedCutProfiles.Batch510.valid20425
  · exact MergedCutProfiles.Batch510.valid20426
  · exact MergedCutProfiles.Batch510.valid20427
theorem numericValid3329 : retention3329.NumericValid := by decide +kernel
def certificate3329 : RatCutBinCertificate := ⟨⟨retention3329,(2156782234939053039/1000000000000000000),(161735409484216873/1000000000000000000),(14898547127280195749/1000000000000000000),(1052721501435622198073/1000000000000000000),(545486713672001299/250000000000000000)⟩,(199655059546259973/200000000000000000),(181735442083478383/500000000000000000),(268672241488054891/1000000000000000000),(18425095449863257/125000000000000000)⟩
theorem valid3329 : certificate3329.Valid := by decide +kernel
theorem sound3329 : certificate3329.Sound := rat_cut_bin_certificate_sound certificate3329 profilesValid3329 numericValid3329 valid3329

def retention3330 : RatCutRetentionCertificate := ⟨(113/2000),(57/1000),(173731586961953518/11741364928190905909),(854284568505552001/1000000000000000000),(63/20),(44945855944688359737/20000000000000000000),true,MergedCutProfiles.Batch510.profile20428,![MergedCutProfiles.Batch510.profile20428,MergedCutProfiles.Batch510.profile20429,MergedCutProfiles.Batch510.profile20430,MergedCutProfiles.Batch510.profile20431,MergedCutProfiles.Batch510.profile20432,MergedCutProfiles.Batch510.profile20433,MergedCutProfiles.Batch510.profile20434,MergedCutProfiles.Batch510.profile20435,MergedCutProfiles.Batch510.profile20422,MergedCutProfiles.Batch510.profile20436,MergedCutProfiles.Batch510.profile20437,MergedCutProfiles.Batch510.profile20438,MergedCutProfiles.Batch510.profile20439,MergedCutProfiles.Batch511.profile20440,MergedCutProfiles.Batch511.profile20441,MergedCutProfiles.Batch511.profile20442]⟩
theorem profilesValid3330 : retention3330.ProfilesValid := by
  change ∀ j : Fin 16, (retention3330.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch510.valid20428
  · exact MergedCutProfiles.Batch510.valid20429
  · exact MergedCutProfiles.Batch510.valid20430
  · exact MergedCutProfiles.Batch510.valid20431
  · exact MergedCutProfiles.Batch510.valid20432
  · exact MergedCutProfiles.Batch510.valid20433
  · exact MergedCutProfiles.Batch510.valid20434
  · exact MergedCutProfiles.Batch510.valid20435
  · exact MergedCutProfiles.Batch510.valid20422
  · exact MergedCutProfiles.Batch510.valid20436
  · exact MergedCutProfiles.Batch510.valid20437
  · exact MergedCutProfiles.Batch510.valid20438
  · exact MergedCutProfiles.Batch510.valid20439
  · exact MergedCutProfiles.Batch511.valid20440
  · exact MergedCutProfiles.Batch511.valid20441
  · exact MergedCutProfiles.Batch511.valid20442
theorem numericValid3330 : retention3330.NumericValid := by decide +kernel
def certificate3330 : RatCutBinCertificate := ⟨⟨retention3330,(2156782234939053039/1000000000000000000),(161735409484216873/1000000000000000000),(14898547127280195749/1000000000000000000),(1052721501435622198073/1000000000000000000),(2173535865988153603/1000000000000000000)⟩,(199655059546259973/200000000000000000),(363109070834442499/1000000000000000000),(269038555560185557/1000000000000000000),(147450452462675961/1000000000000000000)⟩
theorem valid3330 : certificate3330.Valid := by decide +kernel
theorem sound3330 : certificate3330.Sound := rat_cut_bin_certificate_sound certificate3330 profilesValid3330 numericValid3330 valid3330

def retention3331 : RatCutRetentionCertificate := ⟨(113/2000),(57/1000),(540762796000000000/35224094784572717727),(260597380442930277/250000000000000000),(53/20),(1392049970177382153/625000000000000000),true,MergedCutProfiles.Batch511.profile20443,![MergedCutProfiles.Batch511.profile20443,MergedCutProfiles.Batch511.profile20444,MergedCutProfiles.Batch511.profile20445,MergedCutProfiles.Batch510.profile20416,MergedCutProfiles.Batch511.profile20446,MergedCutProfiles.Batch511.profile20447,MergedCutProfiles.Batch511.profile20448,MergedCutProfiles.Batch511.profile20449,MergedCutProfiles.Batch511.profile20450,MergedCutProfiles.Batch511.profile20451,MergedCutProfiles.Batch510.profile20425,MergedCutProfiles.Batch511.profile20452,MergedCutProfiles.Batch511.profile20453,MergedCutProfiles.Batch511.profile20454,MergedCutProfiles.Batch511.profile20455,MergedCutProfiles.Batch511.profile20456]⟩
theorem profilesValid3331 : retention3331.ProfilesValid := by
  change ∀ j : Fin 16, (retention3331.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch511.valid20443
  · exact MergedCutProfiles.Batch511.valid20444
  · exact MergedCutProfiles.Batch511.valid20445
  · exact MergedCutProfiles.Batch510.valid20416
  · exact MergedCutProfiles.Batch511.valid20446
  · exact MergedCutProfiles.Batch511.valid20447
  · exact MergedCutProfiles.Batch511.valid20448
  · exact MergedCutProfiles.Batch511.valid20449
  · exact MergedCutProfiles.Batch511.valid20450
  · exact MergedCutProfiles.Batch511.valid20451
  · exact MergedCutProfiles.Batch510.valid20425
  · exact MergedCutProfiles.Batch511.valid20452
  · exact MergedCutProfiles.Batch511.valid20453
  · exact MergedCutProfiles.Batch511.valid20454
  · exact MergedCutProfiles.Batch511.valid20455
  · exact MergedCutProfiles.Batch511.valid20456
theorem numericValid3331 : retention3331.NumericValid := by decide +kernel
def certificate3331 : RatCutBinCertificate := ⟨⟨retention3331,(2156782234939053039/1000000000000000000),(161735409484216873/1000000000000000000),(14898547127280195749/1000000000000000000),(1052721501435622198073/1000000000000000000),(1082615280960604489/500000000000000000)⟩,(199655059546259973/200000000000000000),(66493736794025493/200000000000000000),(150702052806251117/500000000000000000),(189665928326750997/1000000000000000000)⟩
theorem valid3331 : certificate3331.Valid := by decide +kernel
theorem sound3331 : certificate3331.Sound := rat_cut_bin_certificate_sound certificate3331 profilesValid3331 numericValid3331 valid3331

def retention3332 : RatCutRetentionCertificate := ⟨(113/2000),(57/1000),(1084714716337635293/70448189569145435454),(135190699/125000000),(13/5),(8926823247392464789/4000000000000000000),true,MergedCutProfiles.Batch511.profile20443,![MergedCutProfiles.Batch511.profile20443,MergedCutProfiles.Batch511.profile20444,MergedCutProfiles.Batch511.profile20457,MergedCutProfiles.Batch511.profile20458,MergedCutProfiles.Batch511.profile20459,MergedCutProfiles.Batch511.profile20447,MergedCutProfiles.Batch511.profile20460,MergedCutProfiles.Batch511.profile20449,MergedCutProfiles.Batch511.profile20450,MergedCutProfiles.Batch511.profile20451,MergedCutProfiles.Batch510.profile20425,MergedCutProfiles.Batch511.profile20461,MergedCutProfiles.Batch511.profile20462,MergedCutProfiles.Batch511.profile20454,MergedCutProfiles.Batch511.profile20463,MergedCutProfiles.Batch511.profile20464]⟩
theorem profilesValid3332 : retention3332.ProfilesValid := by
  change ∀ j : Fin 16, (retention3332.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch511.valid20443
  · exact MergedCutProfiles.Batch511.valid20444
  · exact MergedCutProfiles.Batch511.valid20457
  · exact MergedCutProfiles.Batch511.valid20458
  · exact MergedCutProfiles.Batch511.valid20459
  · exact MergedCutProfiles.Batch511.valid20447
  · exact MergedCutProfiles.Batch511.valid20460
  · exact MergedCutProfiles.Batch511.valid20449
  · exact MergedCutProfiles.Batch511.valid20450
  · exact MergedCutProfiles.Batch511.valid20451
  · exact MergedCutProfiles.Batch510.valid20425
  · exact MergedCutProfiles.Batch511.valid20461
  · exact MergedCutProfiles.Batch511.valid20462
  · exact MergedCutProfiles.Batch511.valid20454
  · exact MergedCutProfiles.Batch511.valid20463
  · exact MergedCutProfiles.Batch511.valid20464
theorem numericValid3332 : retention3332.NumericValid := by decide +kernel
def certificate3332 : RatCutBinCertificate := ⟨⟨retention3332,(2156782234939053039/1000000000000000000),(161735409484216873/1000000000000000000),(14898547127280195749/1000000000000000000),(1052721501435622198073/1000000000000000000),(2170827224462347419/1000000000000000000)⟩,(199655059546259973/200000000000000000),(81590195798203109/250000000000000000),(308184888775663623/1000000000000000000),(198001402387848901/1000000000000000000)⟩
theorem valid3332 : certificate3332.Valid := by decide +kernel
theorem sound3332 : certificate3332.Sound := rat_cut_bin_certificate_sound certificate3332 profilesValid3332 numericValid3332 valid3332

def retention3333 : RatCutRetentionCertificate := ⟨(113/2000),(57/1000),(570023034181112680/35224094784572717727),(1084714716337635293/1000000000000000000),(13/5),(2853815652214847157097/1280000000000000000000),true,MergedCutProfiles.Batch511.profile20465,![MergedCutProfiles.Batch511.profile20465,MergedCutProfiles.Batch511.profile20466,MergedCutProfiles.Batch510.profile20415,MergedCutProfiles.Batch511.profile20467,MergedCutProfiles.Batch511.profile20468,MergedCutProfiles.Batch510.profile20419,MergedCutProfiles.Batch511.profile20469,MergedCutProfiles.Batch511.profile20470,MergedCutProfiles.Batch510.profile20423,MergedCutProfiles.Batch511.profile20471,MergedCutProfiles.Batch511.profile20472,MergedCutProfiles.Batch510.profile20427,MergedCutProfiles.Batch511.profile20473,MergedCutProfiles.Batch511.profile20474,MergedCutProfiles.Batch511.profile20475,MergedCutProfiles.Batch511.profile20476]⟩
theorem profilesValid3333 : retention3333.ProfilesValid := by
  change ∀ j : Fin 16, (retention3333.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch511.valid20465
  · exact MergedCutProfiles.Batch511.valid20466
  · exact MergedCutProfiles.Batch510.valid20415
  · exact MergedCutProfiles.Batch511.valid20467
  · exact MergedCutProfiles.Batch511.valid20468
  · exact MergedCutProfiles.Batch510.valid20419
  · exact MergedCutProfiles.Batch511.valid20469
  · exact MergedCutProfiles.Batch511.valid20470
  · exact MergedCutProfiles.Batch510.valid20423
  · exact MergedCutProfiles.Batch511.valid20471
  · exact MergedCutProfiles.Batch511.valid20472
  · exact MergedCutProfiles.Batch510.valid20427
  · exact MergedCutProfiles.Batch511.valid20473
  · exact MergedCutProfiles.Batch511.valid20474
  · exact MergedCutProfiles.Batch511.valid20475
  · exact MergedCutProfiles.Batch511.valid20476
theorem numericValid3333 : retention3333.NumericValid := by decide +kernel
def certificate3333 : RatCutBinCertificate := ⟨⟨retention3333,(2156782234939053039/1000000000000000000),(161735409484216873/1000000000000000000),(14898547127280195749/1000000000000000000),(1052721501435622198073/1000000000000000000),(542166225171428853/250000000000000000)⟩,(199655059546259973/200000000000000000),(163137300561064843/500000000000000000),(308281375947681511/1000000000000000000),(39608912728345041/200000000000000000)⟩
theorem valid3333 : certificate3333.Valid := by decide +kernel
theorem sound3333 : certificate3333.Sound := rat_cut_bin_certificate_sound certificate3333 profilesValid3333 numericValid3333 valid3333

def retention3334 : RatCutRetentionCertificate := ⟨(113/2000),(57/1000),(1056373699484789497/35224094784572717727),(14250575854527817/12500000000000000),(5/2),(1082136007855326337/500000000000000000),true,MergedCutProfiles.Batch510.profile20429,![MergedCutProfiles.Batch510.profile20429,MergedCutProfiles.Batch511.profile20477,MergedCutProfiles.Batch511.profile20478,MergedCutProfiles.Batch511.profile20479,MergedCutProfiles.Batch512.profile20480,MergedCutProfiles.Batch512.profile20481,MergedCutProfiles.Batch511.profile20473,MergedCutProfiles.Batch512.profile20482,MergedCutProfiles.Batch512.profile20483,MergedCutProfiles.Batch512.profile20484,MergedCutProfiles.Batch512.profile20485,MergedCutProfiles.Batch512.profile20486,MergedCutProfiles.Batch512.profile20487,MergedCutProfiles.Batch512.profile20488,MergedCutProfiles.Batch512.profile20489,MergedCutProfiles.Batch512.profile20490]⟩
theorem profilesValid3334 : retention3334.ProfilesValid := by
  change ∀ j : Fin 16, (retention3334.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch510.valid20429
  · exact MergedCutProfiles.Batch511.valid20477
  · exact MergedCutProfiles.Batch511.valid20478
  · exact MergedCutProfiles.Batch511.valid20479
  · exact MergedCutProfiles.Batch512.valid20480
  · exact MergedCutProfiles.Batch512.valid20481
  · exact MergedCutProfiles.Batch511.valid20473
  · exact MergedCutProfiles.Batch512.valid20482
  · exact MergedCutProfiles.Batch512.valid20483
  · exact MergedCutProfiles.Batch512.valid20484
  · exact MergedCutProfiles.Batch512.valid20485
  · exact MergedCutProfiles.Batch512.valid20486
  · exact MergedCutProfiles.Batch512.valid20487
  · exact MergedCutProfiles.Batch512.valid20488
  · exact MergedCutProfiles.Batch512.valid20489
  · exact MergedCutProfiles.Batch512.valid20490
theorem numericValid3334 : retention3334.NumericValid := by decide +kernel
def certificate3334 : RatCutBinCertificate := ⟨⟨retention3334,(2156782234939053039/1000000000000000000),(161735409484216873/1000000000000000000),(14898547127280195749/1000000000000000000),(1052721501435622198073/1000000000000000000),(2105734955261192389/1000000000000000000)⟩,(199655059546259973/200000000000000000),(329048365333610109/1000000000000000000),(76296825916282627/250000000000000000),(99008643053387593/500000000000000000)⟩
theorem valid3334 : certificate3334.Valid := by decide +kernel
theorem sound3334 : certificate3334.Sound := rat_cut_bin_certificate_sound certificate3334 profilesValid3334 numericValid3334 valid3334

def retention3335 : RatCutRetentionCertificate := ⟨(113/2000),(57/1000),(1447750649462785735/6404380869922312314),(1056373699484789497/500000000000000000),(33/20),(1337517490286993260663412114513788603799/845098959587831597600000000000000000000),false,MergedCutProfiles.Batch512.profile20491,(fun _ => MergedCutProfiles.Batch512.profile20491)⟩
theorem profilesValid3335 : retention3335.ProfilesValid := by
  exact MergedCutProfiles.Batch512.valid20491
theorem numericValid3335 : retention3335.NumericValid := by decide +kernel
def certificate3335 : RatCutBinCertificate := ⟨⟨retention3335,(2156782234939053039/1000000000000000000),(161735409484216873/1000000000000000000),(14898547127280195749/1000000000000000000),(1052721501435622198073/1000000000000000000),(772020752516094341/500000000000000000)⟩,(199655059546259973/200000000000000000),(362870966192191821/1000000000000000000),(67319954631711631/250000000000000000),(198267477483305727/1000000000000000000)⟩
theorem valid3335 : certificate3335.Valid := by decide +kernel
theorem sound3335 : certificate3335.Sound := rat_cut_bin_certificate_sound certificate3335 profilesValid3335 numericValid3335 valid3335

def certificates : List RatCutBinCertificate := [certificate3324,certificate3325,certificate3326,certificate3327,certificate3328,certificate3329,certificate3330,certificate3331,certificate3332,certificate3333,certificate3334,certificate3335]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3324,List.forall_mem_cons.mpr ⟨sound3325,List.forall_mem_cons.mpr ⟨sound3326,List.forall_mem_cons.mpr ⟨sound3327,List.forall_mem_cons.mpr ⟨sound3328,List.forall_mem_cons.mpr ⟨sound3329,List.forall_mem_cons.mpr ⟨sound3330,List.forall_mem_cons.mpr ⟨sound3331,List.forall_mem_cons.mpr ⟨sound3332,List.forall_mem_cons.mpr ⟨sound3333,List.forall_mem_cons.mpr ⟨sound3334,List.forall_mem_cons.mpr ⟨sound3335,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch277
