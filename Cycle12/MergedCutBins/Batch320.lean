import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch028
import Cycle12.MergedCutProfiles.Batch584
import Cycle12.MergedCutProfiles.Batch585
import Cycle12.MergedCutProfiles.Batch586
import Cycle12.MergedCutProfiles.Batch587

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch320

def retention3840 : RatCutRetentionCertificate := ⟨(21/1000),(11/500),(1/2),64,1,(15960748357185807596877500066049185271/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch028.profile1132,(fun _ => MergedCutProfiles.Batch028.profile1132)⟩
theorem profilesValid3840 : retention3840.ProfilesValid := by
  exact MergedCutProfiles.Batch028.valid1132
theorem numericValid3840 : retention3840.NumericValid := by decide +kernel
def certificate3840 : RatCutBinCertificate := ⟨⟨retention3840,(35754562252895587/20000000000000000),(10247703429141591/500000000000000000),(541228170089349791/62500000000000000),(19868486828763672939793/1000000000000000000),(496657814946202387/500000000000000000)⟩,(199982339179804043/200000000000000000),(8475596939114207/125000000000000000),(742246698375841047/1000000000000000000),(725952373775111513/1000000000000000000)⟩
theorem valid3840 : certificate3840.Valid := by decide +kernel
theorem sound3840 : certificate3840.Sound := rat_cut_bin_certificate_sound certificate3840 profilesValid3840 numericValid3840 valid3840

def retention3841 : RatCutRetentionCertificate := ⟨(11/500),(9/400),(604592806495560803/2177731345554534727063),(558331313232145533/1000000000000000000),4,(971212543609943222909506955710674643/446665050585716426400000000000000000),true,MergedCutProfiles.Batch584.profile23370,![MergedCutProfiles.Batch584.profile23370,MergedCutProfiles.Batch584.profile23371,MergedCutProfiles.Batch584.profile23372,MergedCutProfiles.Batch584.profile23373,MergedCutProfiles.Batch584.profile23374,MergedCutProfiles.Batch584.profile23375,MergedCutProfiles.Batch584.profile23376,MergedCutProfiles.Batch584.profile23377,MergedCutProfiles.Batch584.profile23378,MergedCutProfiles.Batch584.profile23379,MergedCutProfiles.Batch584.profile23380,MergedCutProfiles.Batch584.profile23381,MergedCutProfiles.Batch584.profile23382,MergedCutProfiles.Batch584.profile23383,MergedCutProfiles.Batch584.profile23384,MergedCutProfiles.Batch584.profile23385]⟩
theorem profilesValid3841 : retention3841.ProfilesValid := by
  change ∀ j : Fin 16, (retention3841.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch584.valid23370
  · exact MergedCutProfiles.Batch584.valid23371
  · exact MergedCutProfiles.Batch584.valid23372
  · exact MergedCutProfiles.Batch584.valid23373
  · exact MergedCutProfiles.Batch584.valid23374
  · exact MergedCutProfiles.Batch584.valid23375
  · exact MergedCutProfiles.Batch584.valid23376
  · exact MergedCutProfiles.Batch584.valid23377
  · exact MergedCutProfiles.Batch584.valid23378
  · exact MergedCutProfiles.Batch584.valid23379
  · exact MergedCutProfiles.Batch584.valid23380
  · exact MergedCutProfiles.Batch584.valid23381
  · exact MergedCutProfiles.Batch584.valid23382
  · exact MergedCutProfiles.Batch584.valid23383
  · exact MergedCutProfiles.Batch584.valid23384
  · exact MergedCutProfiles.Batch584.valid23385
theorem numericValid3841 : retention3841.NumericValid := by decide +kernel
def certificate3841 : RatCutBinCertificate := ⟨⟨retention3841,(909404250231947981/500000000000000000),(21477458192571457/1000000000000000000),(8775705111999829607/1000000000000000000),(3831476627723406824789/200000000000000000),(2156559059208320763/1000000000000000000)⟩,(62494187832391977/62500000000000000),(177264668313496681/250000000000000000),(47154900219300111/1000000000000000000),(2047695399886931/100000000000000000)⟩
theorem valid3841 : certificate3841.Valid := by decide +kernel
theorem sound3841 : certificate3841.Sound := rat_cut_bin_certificate_sound certificate3841 profilesValid3841 numericValid3841 valid3841

def retention3842 : RatCutRetentionCertificate := ⟨(11/500),(9/400),(1225542385000000000/2177731345554534727063),(604592806495560803/1000000000000000000),4,(1370034889758568097542189012867529307/604592806495560803000000000000000000),true,MergedCutProfiles.Batch584.profile23371,![MergedCutProfiles.Batch584.profile23371,MergedCutProfiles.Batch584.profile23373,MergedCutProfiles.Batch584.profile23386,MergedCutProfiles.Batch584.profile23377,MergedCutProfiles.Batch584.profile23387,MergedCutProfiles.Batch584.profile23381,MergedCutProfiles.Batch584.profile23388,MergedCutProfiles.Batch584.profile23385,MergedCutProfiles.Batch584.profile23389,MergedCutProfiles.Batch584.profile23390,MergedCutProfiles.Batch584.profile23391,MergedCutProfiles.Batch584.profile23392,MergedCutProfiles.Batch584.profile23393,MergedCutProfiles.Batch584.profile23394,MergedCutProfiles.Batch584.profile23395,MergedCutProfiles.Batch584.profile23396]⟩
theorem profilesValid3842 : retention3842.ProfilesValid := by
  change ∀ j : Fin 16, (retention3842.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch584.valid23371
  · exact MergedCutProfiles.Batch584.valid23373
  · exact MergedCutProfiles.Batch584.valid23386
  · exact MergedCutProfiles.Batch584.valid23377
  · exact MergedCutProfiles.Batch584.valid23387
  · exact MergedCutProfiles.Batch584.valid23381
  · exact MergedCutProfiles.Batch584.valid23388
  · exact MergedCutProfiles.Batch584.valid23385
  · exact MergedCutProfiles.Batch584.valid23389
  · exact MergedCutProfiles.Batch584.valid23390
  · exact MergedCutProfiles.Batch584.valid23391
  · exact MergedCutProfiles.Batch584.valid23392
  · exact MergedCutProfiles.Batch584.valid23393
  · exact MergedCutProfiles.Batch584.valid23394
  · exact MergedCutProfiles.Batch584.valid23395
  · exact MergedCutProfiles.Batch584.valid23396
theorem numericValid3842 : retention3842.NumericValid := by decide +kernel
def certificate3842 : RatCutBinCertificate := ⟨⟨retention3842,(909404250231947981/500000000000000000),(21477458192571457/1000000000000000000),(8775705111999829607/1000000000000000000),(3831476627723406824789/200000000000000000),(2248240386341012021/1000000000000000000)⟩,(62494187832391977/62500000000000000),(644271691410821899/1000000000000000000),(18121019384441369/250000000000000000),(33053774412671897/1000000000000000000)⟩
theorem valid3842 : certificate3842.Valid := by decide +kernel
theorem sound3842 : certificate3842.Sound := rat_cut_bin_certificate_sound certificate3842 profilesValid3842 numericValid3842 valid3842

def retention3843 : RatCutRetentionCertificate := ⟨(11/500),(9/400),(2970864066081703418/2177731345554534727063),(245108477/200000000),(13/5),(180115553590652355254415731650212079/76596399062500000000000000000000000),true,MergedCutProfiles.Batch584.profile23397,![MergedCutProfiles.Batch584.profile23397,MergedCutProfiles.Batch584.profile23379,MergedCutProfiles.Batch584.profile23388,MergedCutProfiles.Batch584.profile23398,MergedCutProfiles.Batch584.profile23392,MergedCutProfiles.Batch584.profile23399,MergedCutProfiles.Batch585.profile23400,MergedCutProfiles.Batch585.profile23401,MergedCutProfiles.Batch585.profile23402,MergedCutProfiles.Batch585.profile23403,MergedCutProfiles.Batch585.profile23404,MergedCutProfiles.Batch585.profile23405,MergedCutProfiles.Batch585.profile23406,MergedCutProfiles.Batch585.profile23407,MergedCutProfiles.Batch585.profile23408,MergedCutProfiles.Batch585.profile23409]⟩
theorem profilesValid3843 : retention3843.ProfilesValid := by
  change ∀ j : Fin 16, (retention3843.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch584.valid23397
  · exact MergedCutProfiles.Batch584.valid23379
  · exact MergedCutProfiles.Batch584.valid23388
  · exact MergedCutProfiles.Batch584.valid23398
  · exact MergedCutProfiles.Batch584.valid23392
  · exact MergedCutProfiles.Batch584.valid23399
  · exact MergedCutProfiles.Batch585.valid23400
  · exact MergedCutProfiles.Batch585.valid23401
  · exact MergedCutProfiles.Batch585.valid23402
  · exact MergedCutProfiles.Batch585.valid23403
  · exact MergedCutProfiles.Batch585.valid23404
  · exact MergedCutProfiles.Batch585.valid23405
  · exact MergedCutProfiles.Batch585.valid23406
  · exact MergedCutProfiles.Batch585.valid23407
  · exact MergedCutProfiles.Batch585.valid23408
  · exact MergedCutProfiles.Batch585.valid23409
theorem numericValid3843 : retention3843.NumericValid := by decide +kernel
def certificate3843 : RatCutBinCertificate := ⟨⟨retention3843,(909404250231947981/500000000000000000),(21477458192571457/1000000000000000000),(8775705111999829607/1000000000000000000),(3831476627723406824789/200000000000000000),(2339915116857392337/1000000000000000000)⟩,(62494187832391977/62500000000000000),(102065983802940103/250000000000000000),(112997639492366953/500000000000000000),(79289059038267111/500000000000000000)⟩
theorem valid3843 : certificate3843.Valid := by decide +kernel
theorem sound3843 : certificate3843.Sound := rat_cut_bin_certificate_sound certificate3843 profilesValid3843 numericValid3843 valid3843

def retention3844 : RatCutRetentionCertificate := ⟨(11/500),(9/400),(64000000000000000000/2177731345554534727063),(1485432033040851709/500000000000000000),(3/2),(272485219255328705541/128000000000000000000),true,MergedCutProfiles.Batch585.profile23410,![MergedCutProfiles.Batch585.profile23410,MergedCutProfiles.Batch585.profile23411,MergedCutProfiles.Batch585.profile23412,MergedCutProfiles.Batch585.profile23413,MergedCutProfiles.Batch585.profile23414,MergedCutProfiles.Batch585.profile23415,MergedCutProfiles.Batch585.profile23416,MergedCutProfiles.Batch585.profile23417,MergedCutProfiles.Batch585.profile23418,MergedCutProfiles.Batch585.profile23419,MergedCutProfiles.Batch585.profile23420,MergedCutProfiles.Batch585.profile23421,MergedCutProfiles.Batch585.profile23422,MergedCutProfiles.Batch585.profile23423,MergedCutProfiles.Batch585.profile23424,MergedCutProfiles.Batch585.profile23425]⟩
theorem profilesValid3844 : retention3844.ProfilesValid := by
  change ∀ j : Fin 16, (retention3844.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch585.valid23410
  · exact MergedCutProfiles.Batch585.valid23411
  · exact MergedCutProfiles.Batch585.valid23412
  · exact MergedCutProfiles.Batch585.valid23413
  · exact MergedCutProfiles.Batch585.valid23414
  · exact MergedCutProfiles.Batch585.valid23415
  · exact MergedCutProfiles.Batch585.valid23416
  · exact MergedCutProfiles.Batch585.valid23417
  · exact MergedCutProfiles.Batch585.valid23418
  · exact MergedCutProfiles.Batch585.valid23419
  · exact MergedCutProfiles.Batch585.valid23420
  · exact MergedCutProfiles.Batch585.valid23421
  · exact MergedCutProfiles.Batch585.valid23422
  · exact MergedCutProfiles.Batch585.valid23423
  · exact MergedCutProfiles.Batch585.valid23424
  · exact MergedCutProfiles.Batch585.valid23425
theorem numericValid3844 : retention3844.NumericValid := by decide +kernel
def certificate3844 : RatCutBinCertificate := ⟨⟨retention3844,(909404250231947981/500000000000000000),(21477458192571457/1000000000000000000),(8775705111999829607/1000000000000000000),(3831476627723406824789/200000000000000000),(2122113808819667349/1000000000000000000)⟩,(62494187832391977/62500000000000000),(79308291612536051/250000000000000000),(318531203922402099/1000000000000000000),(342014219993506779/1000000000000000000)⟩
theorem valid3844 : certificate3844.Valid := by decide +kernel
theorem sound3844 : certificate3844.Sound := rat_cut_bin_certificate_sound certificate3844 profilesValid3844 numericValid3844 valid3844

def retention3845 : RatCutRetentionCertificate := ⟨(11/500),(9/400),(1/2),64,1,(255372426995979456506987099665889518839/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch585.profile23426,(fun _ => MergedCutProfiles.Batch585.profile23426)⟩
theorem profilesValid3845 : retention3845.ProfilesValid := by
  exact MergedCutProfiles.Batch585.valid23426
theorem numericValid3845 : retention3845.NumericValid := by decide +kernel
def certificate3845 : RatCutBinCertificate := ⟨⟨retention3845,(909404250231947981/500000000000000000),(21477458192571457/1000000000000000000),(8775705111999829607/1000000000000000000),(3831476627723406824789/200000000000000000),(993097232919862773/1000000000000000000)⟩,(62494187832391977/62500000000000000),(487680686368739083/1000000000000000000),(162118456496348489/1000000000000000000),(79262219889870823/500000000000000000)⟩
theorem valid3845 : certificate3845.Valid := by decide +kernel
theorem sound3845 : certificate3845.Sound := rat_cut_bin_certificate_sound certificate3845 profilesValid3845 numericValid3845 valid3845

def retention3846 : RatCutRetentionCertificate := ⟨(11/500),(9/400),(64000000000000000000/2177731345554534727063),(19475255917991226231/1000000000000000000),1,(18178395165932033807587498619087752691/8655669296884989436000000000000000000),false,MergedCutProfiles.Batch585.profile23427,(fun _ => MergedCutProfiles.Batch585.profile23427)⟩
theorem profilesValid3846 : retention3846.ProfilesValid := by
  exact MergedCutProfiles.Batch585.valid23427
theorem numericValid3846 : retention3846.NumericValid := by decide +kernel
def certificate3846 : RatCutBinCertificate := ⟨⟨retention3846,(894820549231947981/500000000000000000),(21477458192571457/1000000000000000000),(8775705111999829607/1000000000000000000),(3831476627723406824789/200000000000000000),(2095792173625798577/1000000000000000000)⟩,(31247140519825137/31250000000000000),(15955739655161581/500000000000000000),(209679110579094431/250000000000000000),(793422454217341729/500000000000000000)⟩
theorem valid3846 : certificate3846.Valid := by decide +kernel
theorem sound3846 : certificate3846.Sound := rat_cut_bin_certificate_sound certificate3846 profilesValid3846 numericValid3846 valid3846

def retention3847 : RatCutRetentionCertificate := ⟨(11/500),(9/400),(1/2),64,1,(255372426995979456506987099665889518839/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch585.profile23426,(fun _ => MergedCutProfiles.Batch585.profile23426)⟩
theorem profilesValid3847 : retention3847.ProfilesValid := by
  exact MergedCutProfiles.Batch585.valid23426
theorem numericValid3847 : retention3847.NumericValid := by decide +kernel
def certificate3847 : RatCutBinCertificate := ⟨⟨retention3847,(894820549231947981/500000000000000000),(21477458192571457/1000000000000000000),(8775705111999829607/1000000000000000000),(3831476627723406824789/200000000000000000),(993168616547733073/1000000000000000000)⟩,(31247140519825137/31250000000000000),(33669926472239943/500000000000000000),(14868216437297523/20000000000000000),(181745656678125037/250000000000000000)⟩
theorem valid3847 : certificate3847.Valid := by decide +kernel
theorem sound3847 : certificate3847.Sound := rat_cut_bin_certificate_sound certificate3847 profilesValid3847 numericValid3847 valid3847

def retention3848 : RatCutRetentionCertificate := ⟨(9/400),(23/1000),(581189502967152880/2079029921420965684411),(558511688771171349/1000000000000000000),4,(242951416650387759245099147682257791/111702337754234269800000000000000000),true,MergedCutProfiles.Batch585.profile23428,![MergedCutProfiles.Batch585.profile23428,MergedCutProfiles.Batch585.profile23429,MergedCutProfiles.Batch585.profile23430,MergedCutProfiles.Batch585.profile23431,MergedCutProfiles.Batch585.profile23432,MergedCutProfiles.Batch585.profile23433,MergedCutProfiles.Batch585.profile23434,MergedCutProfiles.Batch585.profile23435,MergedCutProfiles.Batch585.profile23436,MergedCutProfiles.Batch585.profile23437,MergedCutProfiles.Batch585.profile23438,MergedCutProfiles.Batch585.profile23439,MergedCutProfiles.Batch586.profile23440,MergedCutProfiles.Batch586.profile23441,MergedCutProfiles.Batch586.profile23442,MergedCutProfiles.Batch586.profile23443]⟩
theorem profilesValid3848 : retention3848.ProfilesValid := by
  change ∀ j : Fin 16, (retention3848.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch585.valid23428
  · exact MergedCutProfiles.Batch585.valid23429
  · exact MergedCutProfiles.Batch585.valid23430
  · exact MergedCutProfiles.Batch585.valid23431
  · exact MergedCutProfiles.Batch585.valid23432
  · exact MergedCutProfiles.Batch585.valid23433
  · exact MergedCutProfiles.Batch585.valid23434
  · exact MergedCutProfiles.Batch585.valid23435
  · exact MergedCutProfiles.Batch585.valid23436
  · exact MergedCutProfiles.Batch585.valid23437
  · exact MergedCutProfiles.Batch585.valid23438
  · exact MergedCutProfiles.Batch585.valid23439
  · exact MergedCutProfiles.Batch586.valid23440
  · exact MergedCutProfiles.Batch586.valid23441
  · exact MergedCutProfiles.Batch586.valid23442
  · exact MergedCutProfiles.Batch586.valid23443
theorem numericValid3848 : retention3848.NumericValid := by decide +kernel
def certificate3848 : RatCutBinCertificate := ⟨⟨retention3848,(1820174895558436391/1000000000000000000),(702642711920787/31250000000000000),(552164427511759861/62500000000000000),(4603011735212441710691/250000000000000000),(1078229898976575581/500000000000000000)⟩,(499951632592679551/500000000000000000),(88830509106755913/125000000000000000),(46611583978956087/1000000000000000000),(20241448557999441/1000000000000000000)⟩
theorem valid3848 : certificate3848.Valid := by decide +kernel
theorem sound3848 : certificate3848.Sound := rat_cut_bin_certificate_sound certificate3848 profilesValid3848 numericValid3848 valid3848

def retention3849 : RatCutRetentionCertificate := ⟨(9/400),(23/1000),(1225872656000000000/2079029921420965684411),(7264868787089411/12500000000000000),4,(35555928053296581269/16000000000000000000),true,MergedCutProfiles.Batch585.profile23429,![MergedCutProfiles.Batch585.profile23429,MergedCutProfiles.Batch585.profile23431,MergedCutProfiles.Batch586.profile23444,MergedCutProfiles.Batch585.profile23435,MergedCutProfiles.Batch585.profile23437,MergedCutProfiles.Batch586.profile23440,MergedCutProfiles.Batch586.profile23441,MergedCutProfiles.Batch586.profile23445,MergedCutProfiles.Batch586.profile23446,MergedCutProfiles.Batch586.profile23447,MergedCutProfiles.Batch586.profile23448,MergedCutProfiles.Batch586.profile23449,MergedCutProfiles.Batch586.profile23450,MergedCutProfiles.Batch586.profile23451,MergedCutProfiles.Batch586.profile23452,MergedCutProfiles.Batch586.profile23453]⟩
theorem profilesValid3849 : retention3849.ProfilesValid := by
  change ∀ j : Fin 16, (retention3849.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch585.valid23429
  · exact MergedCutProfiles.Batch585.valid23431
  · exact MergedCutProfiles.Batch586.valid23444
  · exact MergedCutProfiles.Batch585.valid23435
  · exact MergedCutProfiles.Batch585.valid23437
  · exact MergedCutProfiles.Batch586.valid23440
  · exact MergedCutProfiles.Batch586.valid23441
  · exact MergedCutProfiles.Batch586.valid23445
  · exact MergedCutProfiles.Batch586.valid23446
  · exact MergedCutProfiles.Batch586.valid23447
  · exact MergedCutProfiles.Batch586.valid23448
  · exact MergedCutProfiles.Batch586.valid23449
  · exact MergedCutProfiles.Batch586.valid23450
  · exact MergedCutProfiles.Batch586.valid23451
  · exact MergedCutProfiles.Batch586.valid23452
  · exact MergedCutProfiles.Batch586.valid23453
theorem numericValid3849 : retention3849.NumericValid := by decide +kernel
def certificate3849 : RatCutBinCertificate := ⟨⟨retention3849,(1820174895558436391/1000000000000000000),(702642711920787/31250000000000000),(552164427511759861/62500000000000000),(4603011735212441710691/250000000000000000),(275464469716000809/125000000000000000)⟩,(499951632592679551/500000000000000000),(338356465185612591/500000000000000000),(59025170009698993/1000000000000000000),(26285641341126171/1000000000000000000)⟩
theorem valid3849 : certificate3849.Valid := by decide +kernel
theorem sound3849 : certificate3849.Sound := rat_cut_bin_certificate_sound certificate3849 profilesValid3849 numericValid3849 valid3849

def retention3850 : RatCutRetentionCertificate := ⟨(9/400),(23/1000),(3348725486793698459/2079029921420965684411),(76617041/62500000),(13/5),(719606382754886229136374312655181671/306468164000000000000000000000000000),true,MergedCutProfiles.Batch585.profile23433,![MergedCutProfiles.Batch585.profile23433,MergedCutProfiles.Batch585.profile23439,MergedCutProfiles.Batch586.profile23445,MergedCutProfiles.Batch586.profile23448,MergedCutProfiles.Batch586.profile23454,MergedCutProfiles.Batch586.profile23455,MergedCutProfiles.Batch586.profile23456,MergedCutProfiles.Batch586.profile23457,MergedCutProfiles.Batch586.profile23458,MergedCutProfiles.Batch586.profile23459,MergedCutProfiles.Batch586.profile23460,MergedCutProfiles.Batch586.profile23461,MergedCutProfiles.Batch586.profile23462,MergedCutProfiles.Batch586.profile23463,MergedCutProfiles.Batch586.profile23464,MergedCutProfiles.Batch586.profile23465]⟩
theorem profilesValid3850 : retention3850.ProfilesValid := by
  change ∀ j : Fin 16, (retention3850.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch585.valid23433
  · exact MergedCutProfiles.Batch585.valid23439
  · exact MergedCutProfiles.Batch586.valid23445
  · exact MergedCutProfiles.Batch586.valid23448
  · exact MergedCutProfiles.Batch586.valid23454
  · exact MergedCutProfiles.Batch586.valid23455
  · exact MergedCutProfiles.Batch586.valid23456
  · exact MergedCutProfiles.Batch586.valid23457
  · exact MergedCutProfiles.Batch586.valid23458
  · exact MergedCutProfiles.Batch586.valid23459
  · exact MergedCutProfiles.Batch586.valid23460
  · exact MergedCutProfiles.Batch586.valid23461
  · exact MergedCutProfiles.Batch586.valid23462
  · exact MergedCutProfiles.Batch586.valid23463
  · exact MergedCutProfiles.Batch586.valid23464
  · exact MergedCutProfiles.Batch586.valid23465
theorem numericValid3850 : retention3850.NumericValid := by decide +kernel
def certificate3850 : RatCutBinCertificate := ⟨⟨retention3850,(1820174895558436391/1000000000000000000),(702642711920787/31250000000000000),(552164427511759861/62500000000000000),(4603011735212441710691/250000000000000000),(2336018099926585819/1000000000000000000)⟩,(499951632592679551/500000000000000000),(409998769231680311/1000000000000000000),(224444877712705959/1000000000000000000),(19661783296015549/125000000000000000)⟩
theorem valid3850 : certificate3850.Valid := by decide +kernel
theorem sound3850 : certificate3850.Sound := rat_cut_bin_certificate_sound certificate3850 profilesValid3850 numericValid3850 valid3850

def retention3851 : RatCutRetentionCertificate := ⟨(9/400),(23/1000),(64000000000000000000/2079029921420965684411),(3348725486793698459/1000000000000000000),(7/5),(707400910828873303547270493211715073251/334872548679369845900000000000000000000),true,MergedCutProfiles.Batch586.profile23466,![MergedCutProfiles.Batch586.profile23466,MergedCutProfiles.Batch586.profile23467,MergedCutProfiles.Batch586.profile23468,MergedCutProfiles.Batch586.profile23469,MergedCutProfiles.Batch586.profile23470,MergedCutProfiles.Batch586.profile23471,MergedCutProfiles.Batch586.profile23472,MergedCutProfiles.Batch586.profile23473,MergedCutProfiles.Batch586.profile23474,MergedCutProfiles.Batch586.profile23475,MergedCutProfiles.Batch586.profile23476,MergedCutProfiles.Batch586.profile23477,MergedCutProfiles.Batch586.profile23478,MergedCutProfiles.Batch586.profile23479,MergedCutProfiles.Batch587.profile23480,MergedCutProfiles.Batch587.profile23481]⟩
theorem profilesValid3851 : retention3851.ProfilesValid := by
  change ∀ j : Fin 16, (retention3851.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch586.valid23466
  · exact MergedCutProfiles.Batch586.valid23467
  · exact MergedCutProfiles.Batch586.valid23468
  · exact MergedCutProfiles.Batch586.valid23469
  · exact MergedCutProfiles.Batch586.valid23470
  · exact MergedCutProfiles.Batch586.valid23471
  · exact MergedCutProfiles.Batch586.valid23472
  · exact MergedCutProfiles.Batch586.valid23473
  · exact MergedCutProfiles.Batch586.valid23474
  · exact MergedCutProfiles.Batch586.valid23475
  · exact MergedCutProfiles.Batch586.valid23476
  · exact MergedCutProfiles.Batch586.valid23477
  · exact MergedCutProfiles.Batch586.valid23478
  · exact MergedCutProfiles.Batch586.valid23479
  · exact MergedCutProfiles.Batch587.valid23480
  · exact MergedCutProfiles.Batch587.valid23481
theorem numericValid3851 : retention3851.NumericValid := by decide +kernel
def certificate3851 : RatCutBinCertificate := ⟨⟨retention3851,(1820174895558436391/1000000000000000000),(702642711920787/31250000000000000),(552164427511759861/62500000000000000),(4603011735212441710691/250000000000000000),(1052981392603592303/500000000000000000)⟩,(499951632592679551/500000000000000000),(19375398955315829/62500000000000000),(326908220967588563/1000000000000000000),(186129807896590697/500000000000000000)⟩
theorem valid3851 : certificate3851.Valid := by decide +kernel
theorem sound3851 : certificate3851.Sound := rat_cut_bin_certificate_sound certificate3851 profilesValid3851 numericValid3851 valid3851

def certificates : List RatCutBinCertificate := [certificate3840,certificate3841,certificate3842,certificate3843,certificate3844,certificate3845,certificate3846,certificate3847,certificate3848,certificate3849,certificate3850,certificate3851]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3840,List.forall_mem_cons.mpr ⟨sound3841,List.forall_mem_cons.mpr ⟨sound3842,List.forall_mem_cons.mpr ⟨sound3843,List.forall_mem_cons.mpr ⟨sound3844,List.forall_mem_cons.mpr ⟨sound3845,List.forall_mem_cons.mpr ⟨sound3846,List.forall_mem_cons.mpr ⟨sound3847,List.forall_mem_cons.mpr ⟨sound3848,List.forall_mem_cons.mpr ⟨sound3849,List.forall_mem_cons.mpr ⟨sound3850,List.forall_mem_cons.mpr ⟨sound3851,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch320
