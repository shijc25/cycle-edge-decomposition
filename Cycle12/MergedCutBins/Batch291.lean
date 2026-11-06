import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch535
import Cycle12.MergedCutProfiles.Batch536
import Cycle12.MergedCutProfiles.Batch537

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch291

def retention3492 : RatCutRetentionCertificate := ⟨(249/4000),(1/16),(1/2),(28299608005620414199/1000000000000000000),1,(112378700168134554254635595799021809643/113198432022481656796000000000000000000),false,MergedCutProfiles.Batch535.profile21435,(fun _ => MergedCutProfiles.Batch535.profile21435)⟩
theorem profilesValid3492 : retention3492.ProfilesValid := by
  exact MergedCutProfiles.Batch535.valid21435
theorem numericValid3492 : retention3492.NumericValid := by decide +kernel
def certificate3492 : RatCutBinCertificate := ⟨⟨retention3492,(71954379926178137/31250000000000000),(50258241146397749/250000000000000000),(16542216660907816767/1000000000000000000),(938727443778951818319/1000000000000000000),(192955221889118759/200000000000000000)⟩,(998034593965110883/1000000000000000000),(124818790264940061/1000000000000000000),(306801757100292669/500000000000000000),(35707710467073989/62500000000000000)⟩
theorem valid3492 : certificate3492.Valid := by decide +kernel
theorem sound3492 : certificate3492.Sound := rat_cut_bin_certificate_sound certificate3492 profilesValid3492 numericValid3492 valid3492

def retention3493 : RatCutRetentionCertificate := ⟨(1/16),(251/4000),(914270313068465921/56121240256844669053),(905218131750956357/1000000000000000000),(29/10),(569161247404415611301/256000000000000000000),true,MergedCutProfiles.Batch535.profile21439,![MergedCutProfiles.Batch535.profile21439,MergedCutProfiles.Batch536.profile21440,MergedCutProfiles.Batch536.profile21441,MergedCutProfiles.Batch536.profile21442,MergedCutProfiles.Batch536.profile21443,MergedCutProfiles.Batch536.profile21444,MergedCutProfiles.Batch536.profile21445,MergedCutProfiles.Batch536.profile21446,MergedCutProfiles.Batch536.profile21447,MergedCutProfiles.Batch536.profile21448,MergedCutProfiles.Batch536.profile21449,MergedCutProfiles.Batch536.profile21450,MergedCutProfiles.Batch536.profile21451,MergedCutProfiles.Batch536.profile21452,MergedCutProfiles.Batch536.profile21453,MergedCutProfiles.Batch536.profile21454]⟩
theorem profilesValid3493 : retention3493.ProfilesValid := by
  change ∀ j : Fin 16, (retention3493.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch535.valid21439
  · exact MergedCutProfiles.Batch536.valid21440
  · exact MergedCutProfiles.Batch536.valid21441
  · exact MergedCutProfiles.Batch536.valid21442
  · exact MergedCutProfiles.Batch536.valid21443
  · exact MergedCutProfiles.Batch536.valid21444
  · exact MergedCutProfiles.Batch536.valid21445
  · exact MergedCutProfiles.Batch536.valid21446
  · exact MergedCutProfiles.Batch536.valid21447
  · exact MergedCutProfiles.Batch536.valid21448
  · exact MergedCutProfiles.Batch536.valid21449
  · exact MergedCutProfiles.Batch536.valid21450
  · exact MergedCutProfiles.Batch536.valid21451
  · exact MergedCutProfiles.Batch536.valid21452
  · exact MergedCutProfiles.Batch536.valid21453
  · exact MergedCutProfiles.Batch536.valid21454
theorem numericValid3493 : retention3493.NumericValid := by decide +kernel
def certificate3493 : RatCutBinCertificate := ⟨⟨retention3493,(2244807023580935069/1000000000000000000),(202964570941253559/1000000000000000000),(32460600985645383/1953125000000000),(23354465164861497557/25000000000000000),(2143778883993317343/1000000000000000000)⟩,(998079165791011503/1000000000000000000),(156349726456224083/500000000000000000),(161883549776546897/500000000000000000),(186320719637684867/1000000000000000000)⟩
theorem valid3493 : certificate3493.Valid := by decide +kernel
theorem sound3493 : certificate3493.Sound := rat_cut_bin_certificate_sound certificate3493 profilesValid3493 numericValid3493 valid3493

def retention3494 : RatCutRetentionCertificate := ⟨(1/16),(251/4000),(1061439450288898409/56121240256844669053),(914270313068465921/1000000000000000000),(29/10),(177309906999074567543/80000000000000000000),true,MergedCutProfiles.Batch536.profile21455,![MergedCutProfiles.Batch536.profile21455,MergedCutProfiles.Batch536.profile21456,MergedCutProfiles.Batch536.profile21457,MergedCutProfiles.Batch536.profile21458,MergedCutProfiles.Batch536.profile21459,MergedCutProfiles.Batch536.profile21445,MergedCutProfiles.Batch536.profile21460,MergedCutProfiles.Batch536.profile21461,MergedCutProfiles.Batch536.profile21462,MergedCutProfiles.Batch536.profile21463,MergedCutProfiles.Batch536.profile21464,MergedCutProfiles.Batch536.profile21465,MergedCutProfiles.Batch536.profile21453,MergedCutProfiles.Batch536.profile21466,MergedCutProfiles.Batch536.profile21467,MergedCutProfiles.Batch536.profile21468]⟩
theorem profilesValid3494 : retention3494.ProfilesValid := by
  change ∀ j : Fin 16, (retention3494.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch536.valid21455
  · exact MergedCutProfiles.Batch536.valid21456
  · exact MergedCutProfiles.Batch536.valid21457
  · exact MergedCutProfiles.Batch536.valid21458
  · exact MergedCutProfiles.Batch536.valid21459
  · exact MergedCutProfiles.Batch536.valid21445
  · exact MergedCutProfiles.Batch536.valid21460
  · exact MergedCutProfiles.Batch536.valid21461
  · exact MergedCutProfiles.Batch536.valid21462
  · exact MergedCutProfiles.Batch536.valid21463
  · exact MergedCutProfiles.Batch536.valid21464
  · exact MergedCutProfiles.Batch536.valid21465
  · exact MergedCutProfiles.Batch536.valid21453
  · exact MergedCutProfiles.Batch536.valid21466
  · exact MergedCutProfiles.Batch536.valid21467
  · exact MergedCutProfiles.Batch536.valid21468
theorem numericValid3494 : retention3494.NumericValid := by decide +kernel
def certificate3494 : RatCutBinCertificate := ⟨⟨retention3494,(2244807023580935069/1000000000000000000),(202964570941253559/1000000000000000000),(32460600985645383/1953125000000000),(23354465164861497557/25000000000000000),(2136866663954352183/1000000000000000000)⟩,(998079165791011503/1000000000000000000),(39036982811818843/125000000000000000),(324236359272234721/1000000000000000000),(18652626714024051/100000000000000000)⟩
theorem valid3494 : certificate3494.Valid := by decide +kernel
theorem sound3494 : certificate3494.Sound := rat_cut_bin_certificate_sound certificate3494 profilesValid3494 numericValid3494 valid3494

def retention3495 : RatCutRetentionCertificate := ⟨(1/16),(251/4000),(1102239239000000000/56121240256844669053),(1061439450288898409/1000000000000000000),(51/20),(43986252104772167331/20000000000000000000),true,MergedCutProfiles.Batch536.profile21469,![MergedCutProfiles.Batch536.profile21469,MergedCutProfiles.Batch536.profile21470,MergedCutProfiles.Batch536.profile21471,MergedCutProfiles.Batch536.profile21472,MergedCutProfiles.Batch536.profile21444,MergedCutProfiles.Batch536.profile21473,MergedCutProfiles.Batch536.profile21474,MergedCutProfiles.Batch536.profile21475,MergedCutProfiles.Batch536.profile21476,MergedCutProfiles.Batch536.profile21450,MergedCutProfiles.Batch536.profile21477,MergedCutProfiles.Batch536.profile21478,MergedCutProfiles.Batch536.profile21479,MergedCutProfiles.Batch537.profile21480,MergedCutProfiles.Batch537.profile21481,MergedCutProfiles.Batch537.profile21482]⟩
theorem profilesValid3495 : retention3495.ProfilesValid := by
  change ∀ j : Fin 16, (retention3495.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch536.valid21469
  · exact MergedCutProfiles.Batch536.valid21470
  · exact MergedCutProfiles.Batch536.valid21471
  · exact MergedCutProfiles.Batch536.valid21472
  · exact MergedCutProfiles.Batch536.valid21444
  · exact MergedCutProfiles.Batch536.valid21473
  · exact MergedCutProfiles.Batch536.valid21474
  · exact MergedCutProfiles.Batch536.valid21475
  · exact MergedCutProfiles.Batch536.valid21476
  · exact MergedCutProfiles.Batch536.valid21450
  · exact MergedCutProfiles.Batch536.valid21477
  · exact MergedCutProfiles.Batch536.valid21478
  · exact MergedCutProfiles.Batch536.valid21479
  · exact MergedCutProfiles.Batch537.valid21480
  · exact MergedCutProfiles.Batch537.valid21481
  · exact MergedCutProfiles.Batch537.valid21482
theorem numericValid3495 : retention3495.NumericValid := by decide +kernel
def certificate3495 : RatCutBinCertificate := ⟨⟨retention3495,(2244807023580935069/1000000000000000000),(202964570941253559/1000000000000000000),(32460600985645383/1953125000000000),(23354465164861497557/25000000000000000),(2129401242070155333/1000000000000000000)⟩,(998079165791011503/1000000000000000000),(146850800113854967/500000000000000000),(346430627503675161/1000000000000000000),(220577104890805653/1000000000000000000)⟩
theorem valid3495 : certificate3495.Valid := by decide +kernel
theorem sound3495 : certificate3495.Sound := rat_cut_bin_certificate_sound certificate3495 profilesValid3495 numericValid3495 valid3495

def retention3496 : RatCutRetentionCertificate := ⟨(1/16),(251/4000),(1244621232288311963/56121240256844669053),(1102239239/1000000000),(49/20),(8718244169742735127/4000000000000000000),true,MergedCutProfiles.Batch537.profile21483,![MergedCutProfiles.Batch537.profile21483,MergedCutProfiles.Batch537.profile21484,MergedCutProfiles.Batch537.profile21485,MergedCutProfiles.Batch537.profile21486,MergedCutProfiles.Batch537.profile21487,MergedCutProfiles.Batch536.profile21460,MergedCutProfiles.Batch537.profile21488,MergedCutProfiles.Batch536.profile21476,MergedCutProfiles.Batch537.profile21489,MergedCutProfiles.Batch537.profile21490,MergedCutProfiles.Batch537.profile21491,MergedCutProfiles.Batch537.profile21492,MergedCutProfiles.Batch537.profile21493,MergedCutProfiles.Batch537.profile21494,MergedCutProfiles.Batch537.profile21495,MergedCutProfiles.Batch537.profile21496]⟩
theorem profilesValid3496 : retention3496.ProfilesValid := by
  change ∀ j : Fin 16, (retention3496.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch537.valid21483
  · exact MergedCutProfiles.Batch537.valid21484
  · exact MergedCutProfiles.Batch537.valid21485
  · exact MergedCutProfiles.Batch537.valid21486
  · exact MergedCutProfiles.Batch537.valid21487
  · exact MergedCutProfiles.Batch536.valid21460
  · exact MergedCutProfiles.Batch537.valid21488
  · exact MergedCutProfiles.Batch536.valid21476
  · exact MergedCutProfiles.Batch537.valid21489
  · exact MergedCutProfiles.Batch537.valid21490
  · exact MergedCutProfiles.Batch537.valid21491
  · exact MergedCutProfiles.Batch537.valid21492
  · exact MergedCutProfiles.Batch537.valid21493
  · exact MergedCutProfiles.Batch537.valid21494
  · exact MergedCutProfiles.Batch537.valid21495
  · exact MergedCutProfiles.Batch537.valid21496
theorem numericValid3496 : retention3496.NumericValid := by decide +kernel
def certificate3496 : RatCutBinCertificate := ⟨⟨retention3496,(2244807023580935069/1000000000000000000),(202964570941253559/1000000000000000000),(32460600985645383/1953125000000000),(23354465164861497557/25000000000000000),(2112391289005487017/1000000000000000000)⟩,(998079165791011503/1000000000000000000),(58300515847693683/200000000000000000),(69826292924968547/200000000000000000),(7114090937528363/31250000000000000)⟩
theorem valid3496 : certificate3496.Valid := by decide +kernel
theorem sound3496 : certificate3496.Sound := rat_cut_bin_certificate_sound certificate3496 profilesValid3496 numericValid3496 valid3496

def retention3497 : RatCutRetentionCertificate := ⟨(1/16),(251/4000),(3366468721485087926/56121240256844669053),(1244621232288311963/1000000000000000000),(23/10),(656003984108036444931/320000000000000000000),true,MergedCutProfiles.Batch537.profile21497,![MergedCutProfiles.Batch537.profile21497,MergedCutProfiles.Batch537.profile21498,MergedCutProfiles.Batch537.profile21499,MergedCutProfiles.Batch537.profile21500,MergedCutProfiles.Batch537.profile21501,MergedCutProfiles.Batch537.profile21502,MergedCutProfiles.Batch537.profile21503,MergedCutProfiles.Batch537.profile21504,MergedCutProfiles.Batch537.profile21505,MergedCutProfiles.Batch537.profile21506,MergedCutProfiles.Batch537.profile21507,MergedCutProfiles.Batch537.profile21508,MergedCutProfiles.Batch537.profile21509,MergedCutProfiles.Batch537.profile21510,MergedCutProfiles.Batch537.profile21511,MergedCutProfiles.Batch537.profile21512]⟩
theorem profilesValid3497 : retention3497.ProfilesValid := by
  change ∀ j : Fin 16, (retention3497.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch537.valid21497
  · exact MergedCutProfiles.Batch537.valid21498
  · exact MergedCutProfiles.Batch537.valid21499
  · exact MergedCutProfiles.Batch537.valid21500
  · exact MergedCutProfiles.Batch537.valid21501
  · exact MergedCutProfiles.Batch537.valid21502
  · exact MergedCutProfiles.Batch537.valid21503
  · exact MergedCutProfiles.Batch537.valid21504
  · exact MergedCutProfiles.Batch537.valid21505
  · exact MergedCutProfiles.Batch537.valid21506
  · exact MergedCutProfiles.Batch537.valid21507
  · exact MergedCutProfiles.Batch537.valid21508
  · exact MergedCutProfiles.Batch537.valid21509
  · exact MergedCutProfiles.Batch537.valid21510
  · exact MergedCutProfiles.Batch537.valid21511
  · exact MergedCutProfiles.Batch537.valid21512
theorem numericValid3497 : retention3497.NumericValid := by decide +kernel
def certificate3497 : RatCutBinCertificate := ⟨⟨retention3497,(2244807023580935069/1000000000000000000),(202964570941253559/1000000000000000000),(32460600985645383/1953125000000000),(23354465164861497557/25000000000000000),(993477709060553447/500000000000000000)⟩,(998079165791011503/1000000000000000000),(295464251154181819/1000000000000000000),(86069392294121601/250000000000000000),(227952842333006117/1000000000000000000)⟩
theorem valid3497 : certificate3497.Valid := by decide +kernel
theorem sound3497 : certificate3497.Sound := rat_cut_bin_certificate_sound certificate3497 profilesValid3497 numericValid3497 valid3497

def retention3498 : RatCutRetentionCertificate := ⟨(1/16),(251/4000),(19397080557334237250/56121240256844669053),(1683234360742543963/500000000000000000),(5/4),(14041049263389173203617896882251866659/10772699908752281363200000000000000000),false,MergedCutProfiles.Batch537.profile21513,(fun _ => MergedCutProfiles.Batch537.profile21513)⟩
theorem profilesValid3498 : retention3498.ProfilesValid := by
  exact MergedCutProfiles.Batch537.valid21513
theorem numericValid3498 : retention3498.NumericValid := by decide +kernel
def certificate3498 : RatCutBinCertificate := ⟨⟨retention3498,(2244807023580935069/1000000000000000000),(202964570941253559/1000000000000000000),(32460600985645383/1953125000000000),(23354465164861497557/25000000000000000),(1269122555338578107/1000000000000000000)⟩,(998079165791011503/1000000000000000000),(176133727192699613/500000000000000000),(140091855925791933/500000000000000000),(2286792957194579/10000000000000000)⟩
theorem valid3498 : certificate3498.Valid := by decide +kernel
theorem sound3498 : certificate3498.Sound := rat_cut_bin_certificate_sound certificate3498 profilesValid3498 numericValid3498 valid3498

def retention3499 : RatCutRetentionCertificate := ⟨(1/16),(251/4000),(27477957776480201059/56121240256844669053),(77588322229336949/4000000000000000),1,(78284989322117203216057811035283365911/77588322229336949000000000000000000000),false,MergedCutProfiles.Batch537.profile21514,(fun _ => MergedCutProfiles.Batch537.profile21514)⟩
theorem profilesValid3499 : retention3499.ProfilesValid := by
  exact MergedCutProfiles.Batch537.valid21514
theorem numericValid3499 : retention3499.NumericValid := by decide +kernel
def certificate3499 : RatCutBinCertificate := ⟨⟨retention3499,(2244807023580935069/1000000000000000000),(202964570941253559/1000000000000000000),(32460600985645383/1953125000000000),(23354465164861497557/25000000000000000),(981564692563760019/1000000000000000000)⟩,(998079165791011503/1000000000000000000),(386322784970815219/1000000000000000000),(246250530904717047/1000000000000000000),(229612045732530861/1000000000000000000)⟩
theorem valid3499 : certificate3499.Valid := by decide +kernel
theorem sound3499 : certificate3499.Sound := rat_cut_bin_certificate_sound certificate3499 profilesValid3499 numericValid3499 valid3499

def retention3500 : RatCutRetentionCertificate := ⟨(1/16),(251/4000),(28030264727787453101/56121240256844669053),(27477957776480201059/1000000000000000000),1,(3412621068344833987864176612509645807/3434744722060025132375000000000000000),false,MergedCutProfiles.Batch537.profile21515,(fun _ => MergedCutProfiles.Batch537.profile21515)⟩
theorem profilesValid3500 : retention3500.ProfilesValid := by
  exact MergedCutProfiles.Batch537.valid21515
theorem numericValid3500 : retention3500.NumericValid := by decide +kernel
def certificate3500 : RatCutBinCertificate := ⟨⟨retention3500,(2244807023580935069/1000000000000000000),(202964570941253559/1000000000000000000),(32460600985645383/1953125000000000),(23354465164861497557/25000000000000000),(96614462813423997/100000000000000000)⟩,(998079165791011503/1000000000000000000),(77630044692427799/200000000000000000),(24451690963659683/100000000000000000),(28470727900858021/125000000000000000)⟩
theorem valid3500 : certificate3500.Valid := by decide +kernel
theorem sound3500 : certificate3500.Sound := rat_cut_bin_certificate_sound certificate3500 profilesValid3500 numericValid3500 valid3500

def retention3501 : RatCutRetentionCertificate := ⟨(1/16),(251/4000),(1/2),(28030264727787453101/1000000000000000000),1,(111299756322707511572120351860534424779/112121058911149812404000000000000000000),false,MergedCutProfiles.Batch537.profile21516,(fun _ => MergedCutProfiles.Batch537.profile21516)⟩
theorem profilesValid3501 : retention3501.ProfilesValid := by
  exact MergedCutProfiles.Batch537.valid21516
theorem numericValid3501 : retention3501.NumericValid := by decide +kernel
def certificate3501 : RatCutBinCertificate := ⟨⟨retention3501,(2244807023580935069/1000000000000000000),(202964570941253559/1000000000000000000),(32460600985645383/1953125000000000),(23354465164861497557/25000000000000000),(482630312994451289/500000000000000000)⟩,(998079165791011503/1000000000000000000),(388300316484717443/1000000000000000000),(244374904756012991/1000000000000000000),(113792356360941989/500000000000000000)⟩
theorem valid3501 : certificate3501.Valid := by decide +kernel
theorem sound3501 : certificate3501.Sound := rat_cut_bin_certificate_sound certificate3501 profilesValid3501 numericValid3501 valid3501

def retention3502 : RatCutRetentionCertificate := ⟨(1/16),(251/4000),(25864348102941038577/56121240256844669053),(563009772343157197/62500000000000000),1,(9441438692916732958306273565072630943/9008156357490515152000000000000000000),false,MergedCutProfiles.Batch537.profile21517,(fun _ => MergedCutProfiles.Batch537.profile21517)⟩
theorem profilesValid3502 : retention3502.ProfilesValid := by
  exact MergedCutProfiles.Batch537.valid21517
theorem numericValid3502 : retention3502.NumericValid := by decide +kernel
def certificate3502 : RatCutBinCertificate := ⟨⟨retention3502,(2304280583580935069/1000000000000000000),(202964570941253559/1000000000000000000),(32460600985645383/1953125000000000),(23354465164861497557/25000000000000000),(63747368112537551/62500000000000000)⟩,(998028250267914257/1000000000000000000),(117599816206610839/1000000000000000000),(62848667892196473/100000000000000000),(574621590279319833/1000000000000000000)⟩
theorem valid3502 : certificate3502.Valid := by decide +kernel
theorem sound3502 : certificate3502.Sound := rat_cut_bin_certificate_sound certificate3502 profilesValid3502 numericValid3502 valid3502

def retention3503 : RatCutRetentionCertificate := ⟨(1/16),(251/4000),(27730081960364966524/56121240256844669053),(25864348102941038577/1000000000000000000),1,(270364418670350678718830032435430853/269420292738969151843750000000000000),false,MergedCutProfiles.Batch537.profile21518,(fun _ => MergedCutProfiles.Batch537.profile21518)⟩
theorem profilesValid3503 : retention3503.ProfilesValid := by
  exact MergedCutProfiles.Batch537.valid21518
theorem numericValid3503 : retention3503.NumericValid := by decide +kernel
def certificate3503 : RatCutBinCertificate := ⟨⟨retention3503,(2304280583580935069/1000000000000000000),(202964570941253559/1000000000000000000),(32460600985645383/1953125000000000),(23354465164861497557/25000000000000000),(975363727242654891/1000000000000000000)⟩,(998028250267914257/1000000000000000000),(61488272030641359/500000000000000000),(123473351023975101/200000000000000000),(11582051395505137/20000000000000000)⟩
theorem valid3503 : certificate3503.Valid := by decide +kernel
theorem sound3503 : certificate3503.Sound := rat_cut_bin_certificate_sound certificate3503 profilesValid3503 numericValid3503 valid3503

def certificates : List RatCutBinCertificate := [certificate3492,certificate3493,certificate3494,certificate3495,certificate3496,certificate3497,certificate3498,certificate3499,certificate3500,certificate3501,certificate3502,certificate3503]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3492,List.forall_mem_cons.mpr ⟨sound3493,List.forall_mem_cons.mpr ⟨sound3494,List.forall_mem_cons.mpr ⟨sound3495,List.forall_mem_cons.mpr ⟨sound3496,List.forall_mem_cons.mpr ⟨sound3497,List.forall_mem_cons.mpr ⟨sound3498,List.forall_mem_cons.mpr ⟨sound3499,List.forall_mem_cons.mpr ⟨sound3500,List.forall_mem_cons.mpr ⟨sound3501,List.forall_mem_cons.mpr ⟨sound3502,List.forall_mem_cons.mpr ⟨sound3503,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch291
