import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch134
import Cycle12.MergedCutProfiles.Batch135
import Cycle12.MergedCutProfiles.Batch136
import Cycle12.MergedCutProfiles.Batch137
import Cycle12.MergedCutProfiles.Batch138

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch067

def retention804 : RatCutRetentionCertificate := ⟨(191/4000),(6/125),(9686323949095427509/20937402213582854438),(1487139409965013323/250000000000000000),1,(66091795287710731383/64000000000000000000),true,MergedCutProfiles.Batch134.profile5375,![MergedCutProfiles.Batch134.profile5375,MergedCutProfiles.Batch135.profile5413,MergedCutProfiles.Batch135.profile5414,MergedCutProfiles.Batch135.profile5415,MergedCutProfiles.Batch135.profile5416,MergedCutProfiles.Batch135.profile5417,MergedCutProfiles.Batch135.profile5418,MergedCutProfiles.Batch135.profile5419,MergedCutProfiles.Batch135.profile5420,MergedCutProfiles.Batch135.profile5421,MergedCutProfiles.Batch135.profile5422,MergedCutProfiles.Batch135.profile5423,MergedCutProfiles.Batch135.profile5424,MergedCutProfiles.Batch135.profile5425,MergedCutProfiles.Batch135.profile5426,MergedCutProfiles.Batch135.profile5427]⟩
theorem profilesValid804 : retention804.ProfilesValid := by
  change ∀ j : Fin 16, (retention804.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch134.valid5375
  · exact MergedCutProfiles.Batch135.valid5413
  · exact MergedCutProfiles.Batch135.valid5414
  · exact MergedCutProfiles.Batch135.valid5415
  · exact MergedCutProfiles.Batch135.valid5416
  · exact MergedCutProfiles.Batch135.valid5417
  · exact MergedCutProfiles.Batch135.valid5418
  · exact MergedCutProfiles.Batch135.valid5419
  · exact MergedCutProfiles.Batch135.valid5420
  · exact MergedCutProfiles.Batch135.valid5421
  · exact MergedCutProfiles.Batch135.valid5422
  · exact MergedCutProfiles.Batch135.valid5423
  · exact MergedCutProfiles.Batch135.valid5424
  · exact MergedCutProfiles.Batch135.valid5425
  · exact MergedCutProfiles.Batch135.valid5426
  · exact MergedCutProfiles.Batch135.valid5427
theorem numericValid804 : retention804.NumericValid := by decide +kernel
def certificate804 : RatCutBinCertificate := ⟨⟨retention804,(2142735331094584143/1000000000000000000),(13651068898300767/125000000000000000),(12833819923278311389/1000000000000000000),(134543316774886799319/500000000000000000),(202889918244080561/200000000000000000)⟩,(992890240178094193/1000000000000000000),(243073098919616027/500000000000000000),(32644555305097383/200000000000000000),(70184081416984037/500000000000000000)⟩
theorem valid804 : certificate804.Valid := by decide +kernel
theorem sound804 : certificate804.Sound := rat_cut_bin_certificate_sound certificate804 profilesValid804 numericValid804 valid804

def retention805 : RatCutRetentionCertificate := ⟨(191/4000),(6/125),(5192525168892994892/10468701106791427219),(9686323949095427509/1000000000000000000),(21/20),(15535777921069293878093579454243398281679/15498118318552684014400000000000000000000),false,MergedCutProfiles.Batch135.profile5428,(fun _ => MergedCutProfiles.Batch135.profile5428)⟩
theorem profilesValid805 : retention805.ProfilesValid := by
  exact MergedCutProfiles.Batch135.valid5428
theorem numericValid805 : retention805.NumericValid := by decide +kernel
def certificate805 : RatCutBinCertificate := ⟨⟨retention805,(2142735331094584143/1000000000000000000),(13651068898300767/125000000000000000),(12833819923278311389/1000000000000000000),(134543316774886799319/500000000000000000),(491642021674067757/500000000000000000)⟩,(992890240178094193/1000000000000000000),(96745480774683397/200000000000000000),(164973341784675133/1000000000000000000),(70203713387911759/500000000000000000)⟩
theorem valid805 : certificate805.Valid := by decide +kernel
theorem sound805 : certificate805.Sound := rat_cut_bin_certificate_sound certificate805 profilesValid805 numericValid805 valid805

def retention806 : RatCutRetentionCertificate := ⟨(191/4000),(6/125),(1/2),(1298131292223248723/125000000000000000),(21/20),(1034292620055295476605094206135989760159/1038505033778598978400000000000000000000),false,MergedCutProfiles.Batch135.profile5429,(fun _ => MergedCutProfiles.Batch135.profile5429)⟩
theorem profilesValid806 : retention806.ProfilesValid := by
  exact MergedCutProfiles.Batch135.valid5429
theorem numericValid806 : retention806.NumericValid := by decide +kernel
def certificate806 : RatCutBinCertificate := ⟨⟨retention806,(2142735331094584143/1000000000000000000),(13651068898300767/125000000000000000),(12833819923278311389/1000000000000000000),(134543316774886799319/500000000000000000),(488398959736921183/500000000000000000)⟩,(992890240178094193/1000000000000000000),(485017860116749311/1000000000000000000),(164037892605414877/1000000000000000000),(13955758440977623/100000000000000000)⟩
theorem valid806 : certificate806.Valid := by decide +kernel
theorem sound806 : certificate806.Sound := rat_cut_bin_certificate_sound certificate806 profilesValid806 numericValid806 valid806

def retention807 : RatCutRetentionCertificate := ⟨(191/4000),(6/125),(9415920419965395587/20937402213582854438),(3769609743751020941/1000000000000000000),(6/5),(103179989911874502437437591726404543741/94240243593775523525000000000000000000),false,MergedCutProfiles.Batch135.profile5430,(fun _ => MergedCutProfiles.Batch135.profile5430)⟩
theorem profilesValid807 : retention807.ProfilesValid := by
  exact MergedCutProfiles.Batch135.valid5430
theorem numericValid807 : retention807.NumericValid := by decide +kernel
def certificate807 : RatCutBinCertificate := ⟨⟨retention807,(2518719165094584143/1000000000000000000),(13651068898300767/125000000000000000),(12833819923278311389/1000000000000000000),(134543316774886799319/500000000000000000),(1069139480778255589/1000000000000000000)⟩,(991641435582924757/1000000000000000000),(373796674616650163/1000000000000000000),(258368288876094887/1000000000000000000),(47640330662978741/250000000000000000)⟩
theorem valid807 : certificate807.Valid := by decide +kernel
theorem sound807 : certificate807.Sound := rat_cut_bin_certificate_sound certificate807 profilesValid807 numericValid807 valid807

def retention808 : RatCutRetentionCertificate := ⟨(191/4000),(6/125),(10401034027004936647/20937402213582854438),(9415920419965395587/1000000000000000000),(21/20),(15070847193370265165187980590370667430671/15065472671944632939200000000000000000000),false,MergedCutProfiles.Batch135.profile5431,(fun _ => MergedCutProfiles.Batch135.profile5431)⟩
theorem profilesValid808 : retention808.ProfilesValid := by
  exact MergedCutProfiles.Batch135.valid5431
theorem numericValid808 : retention808.NumericValid := by decide +kernel
def certificate808 : RatCutBinCertificate := ⟨⟨retention808,(2518719165094584143/1000000000000000000),(13651068898300767/125000000000000000),(12833819923278311389/1000000000000000000),(134543316774886799319/500000000000000000),(488925650349348619/500000000000000000)⟩,(991641435582924757/1000000000000000000),(408692796471949649/1000000000000000000),(112805663064714437/500000000000000000),(190343187188885717/1000000000000000000)⟩
theorem valid808 : certificate808.Valid := by decide +kernel
theorem sound808 : certificate808.Sound := rat_cut_bin_certificate_sound certificate808 profilesValid808 numericValid808 valid808

def retention809 : RatCutRetentionCertificate := ⟨(191/4000),(6/125),(1/2),(10401034027004936647/1000000000000000000),(21/20),(16574603387062549196959935199337403625991/16641654443207898635200000000000000000000),false,MergedCutProfiles.Batch135.profile5429,(fun _ => MergedCutProfiles.Batch135.profile5429)⟩
theorem profilesValid809 : retention809.ProfilesValid := by
  exact MergedCutProfiles.Batch135.valid5429
theorem numericValid809 : retention809.NumericValid := by decide +kernel
def certificate809 : RatCutBinCertificate := ⟨⟨retention809,(2518719165094584143/1000000000000000000),(13651068898300767/125000000000000000),(12833819923278311389/1000000000000000000),(134543316774886799319/500000000000000000),(24336638347797041/25000000000000000)⟩,(991641435582924757/1000000000000000000),(410534085382892967/1000000000000000000),(223967954721666807/1000000000000000000),(23716097141707281/125000000000000000)⟩
theorem valid809 : certificate809.Valid := by decide +kernel
theorem sound809 : certificate809.Sound := rat_cut_bin_certificate_sound certificate809 profilesValid809 numericValid809 valid809

def retention810 : RatCutRetentionCertificate := ⟨(6/125),(193/4000),(843510475557998602/20691704506769099945),(208789721672771931/250000000000000000),(59/20),(1304406876593497887/625000000000000000),true,MergedCutProfiles.Batch135.profile5432,![MergedCutProfiles.Batch135.profile5432,MergedCutProfiles.Batch135.profile5433,MergedCutProfiles.Batch135.profile5434,MergedCutProfiles.Batch135.profile5435,MergedCutProfiles.Batch135.profile5436,MergedCutProfiles.Batch135.profile5437,MergedCutProfiles.Batch135.profile5438,MergedCutProfiles.Batch135.profile5439,MergedCutProfiles.Batch136.profile5440,MergedCutProfiles.Batch136.profile5441,MergedCutProfiles.Batch136.profile5442,MergedCutProfiles.Batch136.profile5443,MergedCutProfiles.Batch136.profile5444,MergedCutProfiles.Batch136.profile5445,MergedCutProfiles.Batch136.profile5446,MergedCutProfiles.Batch136.profile5447]⟩
theorem profilesValid810 : retention810.ProfilesValid := by
  change ∀ j : Fin 16, (retention810.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch135.valid5432
  · exact MergedCutProfiles.Batch135.valid5433
  · exact MergedCutProfiles.Batch135.valid5434
  · exact MergedCutProfiles.Batch135.valid5435
  · exact MergedCutProfiles.Batch135.valid5436
  · exact MergedCutProfiles.Batch135.valid5437
  · exact MergedCutProfiles.Batch135.valid5438
  · exact MergedCutProfiles.Batch135.valid5439
  · exact MergedCutProfiles.Batch136.valid5440
  · exact MergedCutProfiles.Batch136.valid5441
  · exact MergedCutProfiles.Batch136.valid5442
  · exact MergedCutProfiles.Batch136.valid5443
  · exact MergedCutProfiles.Batch136.valid5444
  · exact MergedCutProfiles.Batch136.valid5445
  · exact MergedCutProfiles.Batch136.valid5446
  · exact MergedCutProfiles.Batch136.valid5447
theorem numericValid810 : retention810.NumericValid := by decide +kernel
def certificate810 : RatCutBinCertificate := ⟨⟨retention810,(1073900229667366643/500000000000000000),(55245122099781037/500000000000000000),(6443241446912746207/500000000000000000),(66755191438671498179/250000000000000000),(2032716159903429207/1000000000000000000)⟩,(992828398507769541/1000000000000000000),(376990978448084587/1000000000000000000),(12761941360107203/50000000000000000),(136269158381973583/1000000000000000000)⟩
theorem valid810 : certificate810.Valid := by decide +kernel
theorem sound810 : certificate810.Sound := rat_cut_bin_certificate_sound certificate810 profilesValid810 numericValid810 valid810

def retention811 : RatCutRetentionCertificate := ⟨(6/125),(193/4000),(171200876000000000/4138340901353819989),(421755237778999301/500000000000000000),(59/20),(1337123049593371756413/640000000000000000000),true,MergedCutProfiles.Batch136.profile5448,![MergedCutProfiles.Batch136.profile5448,MergedCutProfiles.Batch136.profile5449,MergedCutProfiles.Batch136.profile5450,MergedCutProfiles.Batch136.profile5451,MergedCutProfiles.Batch136.profile5452,MergedCutProfiles.Batch136.profile5453,MergedCutProfiles.Batch136.profile5454,MergedCutProfiles.Batch136.profile5455,MergedCutProfiles.Batch136.profile5456,MergedCutProfiles.Batch136.profile5457,MergedCutProfiles.Batch136.profile5458,MergedCutProfiles.Batch136.profile5459,MergedCutProfiles.Batch136.profile5460,MergedCutProfiles.Batch136.profile5461,MergedCutProfiles.Batch136.profile5462,MergedCutProfiles.Batch136.profile5463]⟩
theorem profilesValid811 : retention811.ProfilesValid := by
  change ∀ j : Fin 16, (retention811.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch136.valid5448
  · exact MergedCutProfiles.Batch136.valid5449
  · exact MergedCutProfiles.Batch136.valid5450
  · exact MergedCutProfiles.Batch136.valid5451
  · exact MergedCutProfiles.Batch136.valid5452
  · exact MergedCutProfiles.Batch136.valid5453
  · exact MergedCutProfiles.Batch136.valid5454
  · exact MergedCutProfiles.Batch136.valid5455
  · exact MergedCutProfiles.Batch136.valid5456
  · exact MergedCutProfiles.Batch136.valid5457
  · exact MergedCutProfiles.Batch136.valid5458
  · exact MergedCutProfiles.Batch136.valid5459
  · exact MergedCutProfiles.Batch136.valid5460
  · exact MergedCutProfiles.Batch136.valid5461
  · exact MergedCutProfiles.Batch136.valid5462
  · exact MergedCutProfiles.Batch136.valid5463
theorem numericValid811 : retention811.NumericValid := by decide +kernel
def certificate811 : RatCutBinCertificate := ⟨⟨retention811,(1073900229667366643/500000000000000000),(55245122099781037/500000000000000000),(6443241446912746207/500000000000000000),(66755191438671498179/250000000000000000),(1017460006340884341/500000000000000000)⟩,(992828398507769541/1000000000000000000),(375030169519864043/1000000000000000000),(51431322662428033/200000000000000000),(17213629159784263/125000000000000000)⟩
theorem valid811 : certificate811.Valid := by decide +kernel
theorem sound811 : certificate811.Sound := rat_cut_bin_certificate_sound certificate811 profilesValid811 numericValid811 valid811

def retention812 : RatCutRetentionCertificate := ⟨(6/125),(193/4000),(886537987176086939/20691704506769099945),(42800219/50000000),(29/10),(16649686861397559283/8000000000000000000),true,MergedCutProfiles.Batch136.profile5464,![MergedCutProfiles.Batch136.profile5464,MergedCutProfiles.Batch136.profile5465,MergedCutProfiles.Batch136.profile5466,MergedCutProfiles.Batch136.profile5467,MergedCutProfiles.Batch136.profile5468,MergedCutProfiles.Batch136.profile5469,MergedCutProfiles.Batch136.profile5470,MergedCutProfiles.Batch136.profile5471,MergedCutProfiles.Batch136.profile5472,MergedCutProfiles.Batch136.profile5473,MergedCutProfiles.Batch136.profile5474,MergedCutProfiles.Batch136.profile5475,MergedCutProfiles.Batch136.profile5476,MergedCutProfiles.Batch136.profile5477,MergedCutProfiles.Batch136.profile5478,MergedCutProfiles.Batch136.profile5479]⟩
theorem profilesValid812 : retention812.ProfilesValid := by
  change ∀ j : Fin 16, (retention812.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch136.valid5464
  · exact MergedCutProfiles.Batch136.valid5465
  · exact MergedCutProfiles.Batch136.valid5466
  · exact MergedCutProfiles.Batch136.valid5467
  · exact MergedCutProfiles.Batch136.valid5468
  · exact MergedCutProfiles.Batch136.valid5469
  · exact MergedCutProfiles.Batch136.valid5470
  · exact MergedCutProfiles.Batch136.valid5471
  · exact MergedCutProfiles.Batch136.valid5472
  · exact MergedCutProfiles.Batch136.valid5473
  · exact MergedCutProfiles.Batch136.valid5474
  · exact MergedCutProfiles.Batch136.valid5475
  · exact MergedCutProfiles.Batch136.valid5476
  · exact MergedCutProfiles.Batch136.valid5477
  · exact MergedCutProfiles.Batch136.valid5478
  · exact MergedCutProfiles.Batch136.valid5479
theorem numericValid812 : retention812.NumericValid := by decide +kernel
def certificate812 : RatCutBinCertificate := ⟨⟨retention812,(1073900229667366643/500000000000000000),(55245122099781037/500000000000000000),(6443241446912746207/500000000000000000),(66755191438671498179/250000000000000000),(1013898506055259773/500000000000000000)⟩,(992828398507769541/1000000000000000000),(187036785611300647/500000000000000000),(2016374506131027/7812500000000000),(27922995510690847/200000000000000000)⟩
theorem valid812 : certificate812.Valid := by decide +kernel
theorem sound812 : certificate812.Sound := rat_cut_bin_certificate_sound certificate812 profilesValid812 numericValid812 valid812

def retention813 : RatCutRetentionCertificate := ⟨(6/125),(193/4000),(1148293926348319776/20691704506769099945),(886537987176086939/1000000000000000000),(14/5),(2606960442125098977183/1280000000000000000000),true,MergedCutProfiles.Batch137.profile5480,![MergedCutProfiles.Batch137.profile5480,MergedCutProfiles.Batch137.profile5481,MergedCutProfiles.Batch136.profile5451,MergedCutProfiles.Batch137.profile5482,MergedCutProfiles.Batch137.profile5483,MergedCutProfiles.Batch137.profile5484,MergedCutProfiles.Batch137.profile5485,MergedCutProfiles.Batch137.profile5486,MergedCutProfiles.Batch137.profile5487,MergedCutProfiles.Batch137.profile5488,MergedCutProfiles.Batch136.profile5446,MergedCutProfiles.Batch137.profile5489,MergedCutProfiles.Batch137.profile5490,MergedCutProfiles.Batch137.profile5491,MergedCutProfiles.Batch137.profile5492,MergedCutProfiles.Batch137.profile5493]⟩
theorem profilesValid813 : retention813.ProfilesValid := by
  change ∀ j : Fin 16, (retention813.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch137.valid5480
  · exact MergedCutProfiles.Batch137.valid5481
  · exact MergedCutProfiles.Batch136.valid5451
  · exact MergedCutProfiles.Batch137.valid5482
  · exact MergedCutProfiles.Batch137.valid5483
  · exact MergedCutProfiles.Batch137.valid5484
  · exact MergedCutProfiles.Batch137.valid5485
  · exact MergedCutProfiles.Batch137.valid5486
  · exact MergedCutProfiles.Batch137.valid5487
  · exact MergedCutProfiles.Batch137.valid5488
  · exact MergedCutProfiles.Batch136.valid5446
  · exact MergedCutProfiles.Batch137.valid5489
  · exact MergedCutProfiles.Batch137.valid5490
  · exact MergedCutProfiles.Batch137.valid5491
  · exact MergedCutProfiles.Batch137.valid5492
  · exact MergedCutProfiles.Batch137.valid5493
theorem numericValid813 : retention813.NumericValid := by decide +kernel
def certificate813 : RatCutBinCertificate := ⟨⟨retention813,(1073900229667366643/500000000000000000),(55245122099781037/500000000000000000),(6443241446912746207/500000000000000000),(66755191438671498179/250000000000000000),(248139482027681801/125000000000000000)⟩,(992828398507769541/1000000000000000000),(376715122063930529/1000000000000000000),(15969250859516759/62500000000000000),(27942048262149593/200000000000000000)⟩
theorem valid813 : certificate813.Valid := by decide +kernel
theorem sound813 : certificate813.Sound := rat_cut_bin_certificate_sound certificate813 profilesValid813 numericValid813 valid813

def retention814 : RatCutRetentionCertificate := ⟨(6/125),(193/4000),(3044722372539632138/20691704506769099945),(35884185198384993/31250000000000000),(9/4),(28241493900580779711/16000000000000000000),true,MergedCutProfiles.Batch137.profile5494,![MergedCutProfiles.Batch137.profile5494,MergedCutProfiles.Batch137.profile5495,MergedCutProfiles.Batch137.profile5496,MergedCutProfiles.Batch137.profile5497,MergedCutProfiles.Batch137.profile5498,MergedCutProfiles.Batch137.profile5499,MergedCutProfiles.Batch137.profile5500,MergedCutProfiles.Batch137.profile5501,MergedCutProfiles.Batch137.profile5502,MergedCutProfiles.Batch137.profile5503,MergedCutProfiles.Batch137.profile5504,MergedCutProfiles.Batch137.profile5505,MergedCutProfiles.Batch137.profile5506,MergedCutProfiles.Batch137.profile5507,MergedCutProfiles.Batch137.profile5508,MergedCutProfiles.Batch137.profile5509]⟩
theorem profilesValid814 : retention814.ProfilesValid := by
  change ∀ j : Fin 16, (retention814.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch137.valid5494
  · exact MergedCutProfiles.Batch137.valid5495
  · exact MergedCutProfiles.Batch137.valid5496
  · exact MergedCutProfiles.Batch137.valid5497
  · exact MergedCutProfiles.Batch137.valid5498
  · exact MergedCutProfiles.Batch137.valid5499
  · exact MergedCutProfiles.Batch137.valid5500
  · exact MergedCutProfiles.Batch137.valid5501
  · exact MergedCutProfiles.Batch137.valid5502
  · exact MergedCutProfiles.Batch137.valid5503
  · exact MergedCutProfiles.Batch137.valid5504
  · exact MergedCutProfiles.Batch137.valid5505
  · exact MergedCutProfiles.Batch137.valid5506
  · exact MergedCutProfiles.Batch137.valid5507
  · exact MergedCutProfiles.Batch137.valid5508
  · exact MergedCutProfiles.Batch137.valid5509
theorem numericValid814 : retention814.NumericValid := by decide +kernel
def certificate814 : RatCutBinCertificate := ⟨⟨retention814,(1073900229667366643/500000000000000000),(55245122099781037/500000000000000000),(6443241446912746207/500000000000000000),(66755191438671498179/250000000000000000),(430912965678929711/250000000000000000)⟩,(992828398507769541/1000000000000000000),(394106558732451643/1000000000000000000),(238925837777434207/1000000000000000000),(27997413556857857/200000000000000000)⟩
theorem valid814 : certificate814.Valid := by decide +kernel
theorem sound814 : certificate814.Sound := rat_cut_bin_certificate_sound certificate814 profilesValid814 numericValid814 valid814

def retention815 : RatCutRetentionCertificate := ⟨(6/125),(193/4000),(8153868495043878086/20691704506769099945),(1522361186269816069/500000000000000000),(5/4),(30722114796467118901/25600000000000000000),true,MergedCutProfiles.Batch137.profile5510,![MergedCutProfiles.Batch137.profile5510,MergedCutProfiles.Batch137.profile5511,MergedCutProfiles.Batch137.profile5512,MergedCutProfiles.Batch137.profile5513,MergedCutProfiles.Batch137.profile5514,MergedCutProfiles.Batch137.profile5515,MergedCutProfiles.Batch137.profile5516,MergedCutProfiles.Batch137.profile5517,MergedCutProfiles.Batch137.profile5518,MergedCutProfiles.Batch137.profile5519,MergedCutProfiles.Batch138.profile5520,MergedCutProfiles.Batch138.profile5521,MergedCutProfiles.Batch138.profile5522,MergedCutProfiles.Batch138.profile5523,MergedCutProfiles.Batch138.profile5524,MergedCutProfiles.Batch138.profile5525]⟩
theorem profilesValid815 : retention815.ProfilesValid := by
  change ∀ j : Fin 16, (retention815.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch137.valid5510
  · exact MergedCutProfiles.Batch137.valid5511
  · exact MergedCutProfiles.Batch137.valid5512
  · exact MergedCutProfiles.Batch137.valid5513
  · exact MergedCutProfiles.Batch137.valid5514
  · exact MergedCutProfiles.Batch137.valid5515
  · exact MergedCutProfiles.Batch137.valid5516
  · exact MergedCutProfiles.Batch137.valid5517
  · exact MergedCutProfiles.Batch137.valid5518
  · exact MergedCutProfiles.Batch137.valid5519
  · exact MergedCutProfiles.Batch138.valid5520
  · exact MergedCutProfiles.Batch138.valid5521
  · exact MergedCutProfiles.Batch138.valid5522
  · exact MergedCutProfiles.Batch138.valid5523
  · exact MergedCutProfiles.Batch138.valid5524
  · exact MergedCutProfiles.Batch138.valid5525
theorem numericValid815 : retention815.NumericValid := by decide +kernel
def certificate815 : RatCutBinCertificate := ⟨⟨retention815,(1073900229667366643/500000000000000000),(55245122099781037/500000000000000000),(6443241446912746207/500000000000000000),(66755191438671498179/250000000000000000),(588530367133245171/500000000000000000)⟩,(992828398507769541/1000000000000000000),(454313715112378801/1000000000000000000),(46811842449622169/250000000000000000),(70105817572347113/500000000000000000)⟩
theorem valid815 : certificate815.Valid := by decide +kernel
theorem sound815 : certificate815.Sound := rat_cut_bin_certificate_sound certificate815 profilesValid815 numericValid815 valid815

def certificates : List RatCutBinCertificate := [certificate804,certificate805,certificate806,certificate807,certificate808,certificate809,certificate810,certificate811,certificate812,certificate813,certificate814,certificate815]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound804,List.forall_mem_cons.mpr ⟨sound805,List.forall_mem_cons.mpr ⟨sound806,List.forall_mem_cons.mpr ⟨sound807,List.forall_mem_cons.mpr ⟨sound808,List.forall_mem_cons.mpr ⟨sound809,List.forall_mem_cons.mpr ⟨sound810,List.forall_mem_cons.mpr ⟨sound811,List.forall_mem_cons.mpr ⟨sound812,List.forall_mem_cons.mpr ⟨sound813,List.forall_mem_cons.mpr ⟨sound814,List.forall_mem_cons.mpr ⟨sound815,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch067
