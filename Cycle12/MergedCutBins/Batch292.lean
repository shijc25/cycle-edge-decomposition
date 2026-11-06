import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch250
import Cycle12.MergedCutProfiles.Batch537
import Cycle12.MergedCutProfiles.Batch538
import Cycle12.MergedCutProfiles.Batch539
import Cycle12.MergedCutProfiles.Batch540

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch292

def retention3504 : RatCutRetentionCertificate := ⟨(1/16),(251/4000),(28007382779968616190/56121240256844669053),(6932520490091241631/250000000000000000),1,(27576019335262974616163585793358228551/27730081960364966524000000000000000000),false,MergedCutProfiles.Batch537.profile21519,(fun _ => MergedCutProfiles.Batch537.profile21519)⟩
theorem profilesValid3504 : retention3504.ProfilesValid := by
  exact MergedCutProfiles.Batch537.valid21519
theorem numericValid3504 : retention3504.NumericValid := by decide +kernel
def certificate3504 : RatCutBinCertificate := ⟨⟨retention3504,(2304280583580935069/1000000000000000000),(202964570941253559/1000000000000000000),(32460600985645383/1953125000000000),(23354465164861497557/25000000000000000),(483151831217029359/500000000000000000)⟩,(998028250267914257/1000000000000000000),(31032393087721157/250000000000000000),(615008646371370583/1000000000000000000),(286557724182126951/500000000000000000)⟩
theorem valid3504 : certificate3504.Valid := by decide +kernel
theorem sound3504 : certificate3504.Sound := rat_cut_bin_certificate_sound certificate3504 profilesValid3504 numericValid3504 valid3504

def retention3505 : RatCutRetentionCertificate := ⟨(1/16),(251/4000),(1/2),(2800738277996861619/100000000000000000),1,(111208080003797459716705575028466357471/112029531119874464760000000000000000000),false,MergedCutProfiles.Batch537.profile21516,(fun _ => MergedCutProfiles.Batch537.profile21516)⟩
theorem profilesValid3505 : retention3505.ProfilesValid := by
  exact MergedCutProfiles.Batch537.valid21516
theorem numericValid3505 : retention3505.NumericValid := by decide +kernel
def certificate3505 : RatCutBinCertificate := ⟨⟨retention3505,(2304280583580935069/1000000000000000000),(202964570941253559/1000000000000000000),(32460600985645383/1953125000000000),(23354465164861497557/25000000000000000),(482263503540751831/500000000000000000)⟩,(998028250267914257/1000000000000000000),(62179109293150999/500000000000000000),(122908426393446863/200000000000000000),(142963432489286241/250000000000000000)⟩
theorem valid3505 : certificate3505.Valid := by decide +kernel
theorem sound3505 : certificate3505.Sound := rat_cut_bin_certificate_sound certificate3505 profilesValid3505 numericValid3505 valid3505

def retention3506 : RatCutRetentionCertificate := ⟨(251/4000),(63/1000),(917561354461142031/55589954979483376786),(908476588575388149/1000000000000000000),(29/10),(177932373250807147227/80000000000000000000),true,MergedCutProfiles.Batch538.profile21520,![MergedCutProfiles.Batch538.profile21520,MergedCutProfiles.Batch538.profile21521,MergedCutProfiles.Batch538.profile21522,MergedCutProfiles.Batch538.profile21523,MergedCutProfiles.Batch538.profile21524,MergedCutProfiles.Batch538.profile21525,MergedCutProfiles.Batch538.profile21526,MergedCutProfiles.Batch538.profile21527,MergedCutProfiles.Batch538.profile21528,MergedCutProfiles.Batch538.profile21529,MergedCutProfiles.Batch538.profile21530,MergedCutProfiles.Batch538.profile21531,MergedCutProfiles.Batch538.profile21532,MergedCutProfiles.Batch538.profile21533,MergedCutProfiles.Batch538.profile21534,MergedCutProfiles.Batch538.profile21535]⟩
theorem profilesValid3506 : retention3506.ProfilesValid := by
  change ∀ j : Fin 16, (retention3506.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch538.valid21520
  · exact MergedCutProfiles.Batch538.valid21521
  · exact MergedCutProfiles.Batch538.valid21522
  · exact MergedCutProfiles.Batch538.valid21523
  · exact MergedCutProfiles.Batch538.valid21524
  · exact MergedCutProfiles.Batch538.valid21525
  · exact MergedCutProfiles.Batch538.valid21526
  · exact MergedCutProfiles.Batch538.valid21527
  · exact MergedCutProfiles.Batch538.valid21528
  · exact MergedCutProfiles.Batch538.valid21529
  · exact MergedCutProfiles.Batch538.valid21530
  · exact MergedCutProfiles.Batch538.valid21531
  · exact MergedCutProfiles.Batch538.valid21532
  · exact MergedCutProfiles.Batch538.valid21533
  · exact MergedCutProfiles.Batch538.valid21534
  · exact MergedCutProfiles.Batch538.valid21535
theorem numericValid3506 : retention3506.NumericValid := by decide +kernel
def certificate3506 : RatCutBinCertificate := ⟨⟨retention3506,(281055244310437663/125000000000000000),(204909449857824037/1000000000000000000),(16697990517973297567/1000000000000000000),(929689298073764836353/1000000000000000000),(2144131857658248547/1000000000000000000)⟩,(249517855907753279/250000000000000000),(309994534714629757/1000000000000000000),(65384418431983863/200000000000000000),(37661443982331491/200000000000000000)⟩
theorem valid3506 : certificate3506.Valid := by decide +kernel
theorem sound3506 : certificate3506.Sound := rat_cut_bin_certificate_sound certificate3506 profilesValid3506 numericValid3506 valid3506

def retention3507 : RatCutRetentionCertificate := ⟨(251/4000),(63/1000),(543335989072441671/27794977489741688393),(917561354461142031/1000000000000000000),(57/20),(88151175129182143731/40000000000000000000),true,MergedCutProfiles.Batch538.profile21536,![MergedCutProfiles.Batch538.profile21536,MergedCutProfiles.Batch538.profile21537,MergedCutProfiles.Batch538.profile21538,MergedCutProfiles.Batch538.profile21539,MergedCutProfiles.Batch538.profile21540,MergedCutProfiles.Batch538.profile21541,MergedCutProfiles.Batch538.profile21542,MergedCutProfiles.Batch538.profile21543,MergedCutProfiles.Batch538.profile21544,MergedCutProfiles.Batch538.profile21545,MergedCutProfiles.Batch538.profile21532,MergedCutProfiles.Batch538.profile21546,MergedCutProfiles.Batch538.profile21547,MergedCutProfiles.Batch538.profile21548,MergedCutProfiles.Batch538.profile21549,MergedCutProfiles.Batch538.profile21550]⟩
theorem profilesValid3507 : retention3507.ProfilesValid := by
  change ∀ j : Fin 16, (retention3507.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch538.valid21536
  · exact MergedCutProfiles.Batch538.valid21537
  · exact MergedCutProfiles.Batch538.valid21538
  · exact MergedCutProfiles.Batch538.valid21539
  · exact MergedCutProfiles.Batch538.valid21540
  · exact MergedCutProfiles.Batch538.valid21541
  · exact MergedCutProfiles.Batch538.valid21542
  · exact MergedCutProfiles.Batch538.valid21543
  · exact MergedCutProfiles.Batch538.valid21544
  · exact MergedCutProfiles.Batch538.valid21545
  · exact MergedCutProfiles.Batch538.valid21532
  · exact MergedCutProfiles.Batch538.valid21546
  · exact MergedCutProfiles.Batch538.valid21547
  · exact MergedCutProfiles.Batch538.valid21548
  · exact MergedCutProfiles.Batch538.valid21549
  · exact MergedCutProfiles.Batch538.valid21550
theorem numericValid3507 : retention3507.NumericValid := by decide +kernel
def certificate3507 : RatCutBinCertificate := ⟨⟨retention3507,(281055244310437663/125000000000000000),(204909449857824037/1000000000000000000),(16697990517973297567/1000000000000000000),(929689298073764836353/1000000000000000000),(1062568112350741883/500000000000000000)⟩,(249517855907753279/250000000000000000),(311360786555399453/1000000000000000000),(81331395476426881/250000000000000000),(188322733233753943/1000000000000000000)⟩
theorem valid3507 : certificate3507.Valid := by decide +kernel
theorem sound3507 : certificate3507.Sound := rat_cut_bin_certificate_sound certificate3507 profilesValid3507 numericValid3507 valid3507

def retention3508 : RatCutRetentionCertificate := ⟨(251/4000),(63/1000),(553011555500000000/27794977489741688393),(543335989072441671/500000000000000000),(5/2),(17569288933713660297/8000000000000000000),true,MergedCutProfiles.Batch538.profile21551,![MergedCutProfiles.Batch538.profile21551,MergedCutProfiles.Batch538.profile21552,MergedCutProfiles.Batch538.profile21553,MergedCutProfiles.Batch538.profile21554,MergedCutProfiles.Batch538.profile21525,MergedCutProfiles.Batch538.profile21555,MergedCutProfiles.Batch538.profile21556,MergedCutProfiles.Batch538.profile21557,MergedCutProfiles.Batch538.profile21558,MergedCutProfiles.Batch538.profile21559,MergedCutProfiles.Batch539.profile21560,MergedCutProfiles.Batch539.profile21561,MergedCutProfiles.Batch539.profile21562,MergedCutProfiles.Batch539.profile21563,MergedCutProfiles.Batch539.profile21564,MergedCutProfiles.Batch539.profile21565]⟩
theorem profilesValid3508 : retention3508.ProfilesValid := by
  change ∀ j : Fin 16, (retention3508.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch538.valid21551
  · exact MergedCutProfiles.Batch538.valid21552
  · exact MergedCutProfiles.Batch538.valid21553
  · exact MergedCutProfiles.Batch538.valid21554
  · exact MergedCutProfiles.Batch538.valid21525
  · exact MergedCutProfiles.Batch538.valid21555
  · exact MergedCutProfiles.Batch538.valid21556
  · exact MergedCutProfiles.Batch538.valid21557
  · exact MergedCutProfiles.Batch538.valid21558
  · exact MergedCutProfiles.Batch538.valid21559
  · exact MergedCutProfiles.Batch539.valid21560
  · exact MergedCutProfiles.Batch539.valid21561
  · exact MergedCutProfiles.Batch539.valid21562
  · exact MergedCutProfiles.Batch539.valid21563
  · exact MergedCutProfiles.Batch539.valid21564
  · exact MergedCutProfiles.Batch539.valid21565
theorem numericValid3508 : retention3508.NumericValid := by decide +kernel
def certificate3508 : RatCutBinCertificate := ⟨⟨retention3508,(281055244310437663/125000000000000000),(204909449857824037/1000000000000000000),(16697990517973297567/1000000000000000000),(929689298073764836353/1000000000000000000),(425435222363050807/200000000000000000)⟩,(249517855907753279/250000000000000000),(72305914894252203/250000000000000000),(175973919638552667/500000000000000000),(14219808395797253/62500000000000000)⟩
theorem valid3508 : certificate3508.Valid := by decide +kernel
theorem sound3508 : certificate3508.Sound := rat_cut_bin_certificate_sound certificate3508 profilesValid3508 numericValid3508 valid3508

def retention3509 : RatCutRetentionCertificate := ⟨(251/4000),(63/1000),(656409071496505617/27794977489741688393),(1106023111/1000000000),(49/20),(8702382582320889809/4000000000000000000),true,MergedCutProfiles.Batch539.profile21566,![MergedCutProfiles.Batch539.profile21566,MergedCutProfiles.Batch539.profile21567,MergedCutProfiles.Batch539.profile21568,MergedCutProfiles.Batch539.profile21569,MergedCutProfiles.Batch538.profile21541,MergedCutProfiles.Batch539.profile21570,MergedCutProfiles.Batch538.profile21529,MergedCutProfiles.Batch539.profile21571,MergedCutProfiles.Batch539.profile21572,MergedCutProfiles.Batch539.profile21573,MergedCutProfiles.Batch539.profile21562,MergedCutProfiles.Batch539.profile21574,MergedCutProfiles.Batch539.profile21575,MergedCutProfiles.Batch539.profile21576,MergedCutProfiles.Batch539.profile21577,MergedCutProfiles.Batch539.profile21578]⟩
theorem profilesValid3509 : retention3509.ProfilesValid := by
  change ∀ j : Fin 16, (retention3509.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch539.valid21566
  · exact MergedCutProfiles.Batch539.valid21567
  · exact MergedCutProfiles.Batch539.valid21568
  · exact MergedCutProfiles.Batch539.valid21569
  · exact MergedCutProfiles.Batch538.valid21541
  · exact MergedCutProfiles.Batch539.valid21570
  · exact MergedCutProfiles.Batch538.valid21529
  · exact MergedCutProfiles.Batch539.valid21571
  · exact MergedCutProfiles.Batch539.valid21572
  · exact MergedCutProfiles.Batch539.valid21573
  · exact MergedCutProfiles.Batch539.valid21562
  · exact MergedCutProfiles.Batch539.valid21574
  · exact MergedCutProfiles.Batch539.valid21575
  · exact MergedCutProfiles.Batch539.valid21576
  · exact MergedCutProfiles.Batch539.valid21577
  · exact MergedCutProfiles.Batch539.valid21578
theorem numericValid3509 : retention3509.NumericValid := by decide +kernel
def certificate3509 : RatCutBinCertificate := ⟨⟨retention3509,(281055244310437663/125000000000000000),(204909449857824037/1000000000000000000),(16697990517973297567/1000000000000000000),(929689298073764836353/1000000000000000000),(210799032676675033/100000000000000000)⟩,(249517855907753279/250000000000000000),(57952800193794601/200000000000000000),(351278455740210371/1000000000000000000),(9155040718591721/40000000000000000)⟩
theorem valid3509 : certificate3509.Valid := by decide +kernel
theorem sound3509 : certificate3509.Sound := rat_cut_bin_certificate_sound certificate3509 profilesValid3509 numericValid3509 valid3509

def retention3510 : RatCutRetentionCertificate := ⟨(251/4000),(63/1000),(4376135872033596907/55589954979483376786),(656409071496505617/500000000000000000),(11/5),(1269309602153688517317/640000000000000000000),true,MergedCutProfiles.Batch538.profile21539,![MergedCutProfiles.Batch538.profile21539,MergedCutProfiles.Batch539.profile21579,MergedCutProfiles.Batch539.profile21573,MergedCutProfiles.Batch539.profile21580,MergedCutProfiles.Batch539.profile21581,MergedCutProfiles.Batch539.profile21582,MergedCutProfiles.Batch539.profile21583,MergedCutProfiles.Batch539.profile21584,MergedCutProfiles.Batch539.profile21585,MergedCutProfiles.Batch539.profile21586,MergedCutProfiles.Batch539.profile21587,MergedCutProfiles.Batch539.profile21588,MergedCutProfiles.Batch539.profile21589,MergedCutProfiles.Batch539.profile21590,MergedCutProfiles.Batch539.profile21591,MergedCutProfiles.Batch539.profile21592]⟩
theorem profilesValid3510 : retention3510.ProfilesValid := by
  change ∀ j : Fin 16, (retention3510.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch538.valid21539
  · exact MergedCutProfiles.Batch539.valid21579
  · exact MergedCutProfiles.Batch539.valid21573
  · exact MergedCutProfiles.Batch539.valid21580
  · exact MergedCutProfiles.Batch539.valid21581
  · exact MergedCutProfiles.Batch539.valid21582
  · exact MergedCutProfiles.Batch539.valid21583
  · exact MergedCutProfiles.Batch539.valid21584
  · exact MergedCutProfiles.Batch539.valid21585
  · exact MergedCutProfiles.Batch539.valid21586
  · exact MergedCutProfiles.Batch539.valid21587
  · exact MergedCutProfiles.Batch539.valid21588
  · exact MergedCutProfiles.Batch539.valid21589
  · exact MergedCutProfiles.Batch539.valid21590
  · exact MergedCutProfiles.Batch539.valid21591
  · exact MergedCutProfiles.Batch539.valid21592
theorem numericValid3510 : retention3510.NumericValid := by decide +kernel
def certificate3510 : RatCutBinCertificate := ⟨⟨retention3510,(281055244310437663/125000000000000000),(204909449857824037/1000000000000000000),(16697990517973297567/1000000000000000000),(929689298073764836353/1000000000000000000),(1922589741519972437/1000000000000000000)⟩,(249517855907753279/250000000000000000),(148708544078543729/500000000000000000),(341904412549468363/1000000000000000000),(11443183389720313/50000000000000000)⟩
theorem valid3510 : certificate3510.Valid := by decide +kernel
theorem sound3510 : certificate3510.Sound := rat_cut_bin_certificate_sound certificate3510 profilesValid3510 numericValid3510 valid3510

def retention3511 : RatCutRetentionCertificate := ⟨(251/4000),(63/1000),(10859303747535823887/27794977489741688393),(4376135872033596907/1000000000000000000),(11/10),(1525462940680726461391/1280000000000000000000),true,MergedCutProfiles.Batch539.profile21593,![MergedCutProfiles.Batch539.profile21593,MergedCutProfiles.Batch539.profile21594,MergedCutProfiles.Batch539.profile21595,MergedCutProfiles.Batch539.profile21596,MergedCutProfiles.Batch539.profile21597,MergedCutProfiles.Batch539.profile21598,MergedCutProfiles.Batch539.profile21599,MergedCutProfiles.Batch540.profile21600,MergedCutProfiles.Batch540.profile21601,MergedCutProfiles.Batch540.profile21602,MergedCutProfiles.Batch540.profile21603,MergedCutProfiles.Batch540.profile21604,MergedCutProfiles.Batch250.profile10002,MergedCutProfiles.Batch540.profile21605,MergedCutProfiles.Batch540.profile21606,MergedCutProfiles.Batch540.profile21607]⟩
theorem profilesValid3511 : retention3511.ProfilesValid := by
  change ∀ j : Fin 16, (retention3511.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch539.valid21593
  · exact MergedCutProfiles.Batch539.valid21594
  · exact MergedCutProfiles.Batch539.valid21595
  · exact MergedCutProfiles.Batch539.valid21596
  · exact MergedCutProfiles.Batch539.valid21597
  · exact MergedCutProfiles.Batch539.valid21598
  · exact MergedCutProfiles.Batch539.valid21599
  · exact MergedCutProfiles.Batch540.valid21600
  · exact MergedCutProfiles.Batch540.valid21601
  · exact MergedCutProfiles.Batch540.valid21602
  · exact MergedCutProfiles.Batch540.valid21603
  · exact MergedCutProfiles.Batch540.valid21604
  · exact MergedCutProfiles.Batch250.valid10002
  · exact MergedCutProfiles.Batch540.valid21605
  · exact MergedCutProfiles.Batch540.valid21606
  · exact MergedCutProfiles.Batch540.valid21607
theorem numericValid3511 : retention3511.NumericValid := by decide +kernel
def certificate3511 : RatCutBinCertificate := ⟨⟨retention3511,(281055244310437663/125000000000000000),(204909449857824037/1000000000000000000),(16697990517973297567/1000000000000000000),(929689298073764836353/1000000000000000000),(1161415592973223663/1000000000000000000)⟩,(249517855907753279/250000000000000000),(183296194341838209/500000000000000000),(265526810432073747/1000000000000000000),(22942738323272747/100000000000000000)⟩
theorem valid3511 : certificate3511.Valid := by decide +kernel
theorem sound3511 : certificate3511.Sound := rat_cut_bin_certificate_sound certificate3511 profilesValid3511 numericValid3511 valid3511

def retention3512 : RatCutRetentionCertificate := ⟨(251/4000),(63/1000),(27303830152829110897/55589954979483376786),(10859303747535823887/500000000000000000),1,(87516085178080637805938665185788309783/86874429980286591096000000000000000000),false,MergedCutProfiles.Batch540.profile21608,(fun _ => MergedCutProfiles.Batch540.profile21608)⟩
theorem profilesValid3512 : retention3512.ProfilesValid := by
  exact MergedCutProfiles.Batch540.valid21608
theorem numericValid3512 : retention3512.NumericValid := by decide +kernel
def certificate3512 : RatCutBinCertificate := ⟨⟨retention3512,(281055244310437663/125000000000000000),(204909449857824037/1000000000000000000),(16697990517973297567/1000000000000000000),(929689298073764836353/1000000000000000000),(979793964146762219/1000000000000000000)⟩,(249517855907753279/250000000000000000),(383537997730777017/1000000000000000000),(124454489365328721/500000000000000000),(116444455783866143/500000000000000000)⟩
theorem valid3512 : certificate3512.Valid := by decide +kernel
theorem sound3512 : certificate3512.Sound := rat_cut_bin_certificate_sound certificate3512 profilesValid3512 numericValid3512 valid3512

def retention3513 : RatCutRetentionCertificate := ⟨(251/4000),(63/1000),(13788434227178701003/27794977489741688393),(27303830152829110897/1000000000000000000),1,(27308141103221917113056276206685242273/27303830152829110897000000000000000000),false,MergedCutProfiles.Batch540.profile21609,(fun _ => MergedCutProfiles.Batch540.profile21609)⟩
theorem profilesValid3513 : retention3513.ProfilesValid := by
  exact MergedCutProfiles.Batch540.valid21609
theorem numericValid3513 : retention3513.NumericValid := by decide +kernel
def certificate3513 : RatCutBinCertificate := ⟨⟨retention3513,(281055244310437663/125000000000000000),(204909449857824037/1000000000000000000),(16697990517973297567/1000000000000000000),(929689298073764836353/1000000000000000000),(972565901970480357/1000000000000000000)⟩,(249517855907753279/250000000000000000),(383735931488287159/1000000000000000000),(124359679726811563/500000000000000000),(233114791755381759/1000000000000000000)⟩
theorem valid3513 : certificate3513.Valid := by decide +kernel
theorem sound3513 : certificate3513.Sound := rat_cut_bin_certificate_sound certificate3513 profilesValid3513 numericValid3513 valid3513

def retention3514 : RatCutRetentionCertificate := ⟨(251/4000),(63/1000),(1/2),(13788434227178701003/500000000000000000),1,(10948340218077668543515615690121929/11030747381742960802400000000000000),false,MergedCutProfiles.Batch250.profile10024,(fun _ => MergedCutProfiles.Batch250.profile10024)⟩
theorem profilesValid3514 : retention3514.ProfilesValid := by
  exact MergedCutProfiles.Batch250.valid10024
theorem numericValid3514 : retention3514.NumericValid := by decide +kernel
def certificate3514 : RatCutBinCertificate := ⟨⟨retention3514,(281055244310437663/125000000000000000),(204909449857824037/1000000000000000000),(16697990517973297567/1000000000000000000),(929689298073764836353/1000000000000000000),(241234334471567007/250000000000000000)⟩,(249517855907753279/250000000000000000),(96666681300387153/250000000000000000),(24592358920016653/100000000000000000),(45765126391384941/200000000000000000)⟩
theorem valid3514 : certificate3514.Valid := by decide +kernel
theorem sound3514 : certificate3514.Sound := rat_cut_bin_certificate_sound certificate3514 profilesValid3514 numericValid3514 valid3514

def retention3515 : RatCutRetentionCertificate := ⟨(251/4000),(63/1000),(12798562070051343659/27794977489741688393),(562764825433633173/62500000000000000),1,(3148047785481384191323641223874262021/3001412402312710256000000000000000000),false,MergedCutProfiles.Batch540.profile21610,(fun _ => MergedCutProfiles.Batch540.profile21610)⟩
theorem profilesValid3515 : retention3515.ProfilesValid := by
  exact MergedCutProfiles.Batch540.valid21610
theorem numericValid3515 : retention3515.NumericValid := by decide +kernel
def certificate3515 : RatCutBinCertificate := ⟨⟨retention3515,(288214371685437663/125000000000000000),(204909449857824037/1000000000000000000),(16697990517973297567/1000000000000000000),(929689298073764836353/1000000000000000000),(255140044449276497/250000000000000000)⟩,(998022273588358479/1000000000000000000),(117052519793236761/1000000000000000000),(629630147903481147/1000000000000000000),(287971467371443697/500000000000000000)⟩
theorem valid3515 : certificate3515.Valid := by decide +kernel
theorem sound3515 : certificate3515.Sound := rat_cut_bin_certificate_sound certificate3515 profilesValid3515 numericValid3515 valid3515

def certificates : List RatCutBinCertificate := [certificate3504,certificate3505,certificate3506,certificate3507,certificate3508,certificate3509,certificate3510,certificate3511,certificate3512,certificate3513,certificate3514,certificate3515]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3504,List.forall_mem_cons.mpr ⟨sound3505,List.forall_mem_cons.mpr ⟨sound3506,List.forall_mem_cons.mpr ⟨sound3507,List.forall_mem_cons.mpr ⟨sound3508,List.forall_mem_cons.mpr ⟨sound3509,List.forall_mem_cons.mpr ⟨sound3510,List.forall_mem_cons.mpr ⟨sound3511,List.forall_mem_cons.mpr ⟨sound3512,List.forall_mem_cons.mpr ⟨sound3513,List.forall_mem_cons.mpr ⟨sound3514,List.forall_mem_cons.mpr ⟨sound3515,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch292
