import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch587
import Cycle12.MergedCutProfiles.Batch588
import Cycle12.MergedCutProfiles.Batch589

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch321

def retention3852 : RatCutRetentionCertificate := ⟨(9/400),(23/1000),(1/2),64,1,(10214905530471709567396075374053018199/10240000000000000000000000000000000000),false,MergedCutProfiles.Batch587.profile23482,(fun _ => MergedCutProfiles.Batch587.profile23482)⟩
theorem profilesValid3852 : retention3852.ProfilesValid := by
  exact MergedCutProfiles.Batch587.valid23482
theorem numericValid3852 : retention3852.NumericValid := by decide +kernel
def certificate3852 : RatCutBinCertificate := ⟨⟨retention3852,(1820174895558436391/1000000000000000000),(702642711920787/31250000000000000),(552164427511759861/62500000000000000),(4603011735212441710691/250000000000000000),(496458467077190547/500000000000000000)⟩,(499951632592679551/500000000000000000),(489471023840389861/1000000000000000000),(16083611215331891/100000000000000000),(157241813745739281/1000000000000000000)⟩
theorem valid3852 : certificate3852.Valid := by decide +kernel
theorem sound3852 : certificate3852.Sound := rat_cut_bin_certificate_sound certificate3852 profilesValid3852 numericValid3852 valid3852

def retention3853 : RatCutRetentionCertificate := ⟨(9/400),(23/1000),(64000000000000000000/2079029921420965684411),(4881906208393732827/250000000000000000),1,(2044730122545327628943603405433517399/976381241678746565400000000000000000),false,MergedCutProfiles.Batch587.profile23483,(fun _ => MergedCutProfiles.Batch587.profile23483)⟩
theorem profilesValid3853 : retention3853.ProfilesValid := by
  exact MergedCutProfiles.Batch587.valid23483
theorem numericValid3853 : retention3853.NumericValid := by decide +kernel
def certificate3853 : RatCutBinCertificate := ⟨⟨retention3853,(1791692766558436391/1000000000000000000),(702642711920787/31250000000000000),(552164427511759861/62500000000000000),(4603011735212441710691/250000000000000000),(2089632399586505239/1000000000000000000)⟩,(499952389448307683/500000000000000000),(8000971655618439/250000000000000000),(838449582165358677/1000000000000000000),(1582534572727634933/1000000000000000000)⟩
theorem valid3853 : certificate3853.Valid := by decide +kernel
theorem sound3853 : certificate3853.Sound := rat_cut_bin_certificate_sound certificate3853 profilesValid3853 numericValid3853 valid3853

def retention3854 : RatCutRetentionCertificate := ⟨(9/400),(23/1000),(1/2),64,1,(10214905530471709567396075374053018199/10240000000000000000000000000000000000),false,MergedCutProfiles.Batch587.profile23482,(fun _ => MergedCutProfiles.Batch587.profile23482)⟩
theorem profilesValid3854 : retention3854.ProfilesValid := by
  exact MergedCutProfiles.Batch587.valid23482
theorem numericValid3854 : retention3854.NumericValid := by decide +kernel
def certificate3854 : RatCutBinCertificate := ⟨⟨retention3854,(1791692766558436391/1000000000000000000),(702642711920787/31250000000000000),(552164427511759861/62500000000000000),(4603011735212441710691/250000000000000000),(248247355641130823/250000000000000000)⟩,(499952389448307683/500000000000000000),(16837127586489659/250000000000000000),(743389125521802233/1000000000000000000),(726829523476475991/1000000000000000000)⟩
theorem valid3854 : certificate3854.Valid := by decide +kernel
theorem sound3854 : certificate3854.Sound := rat_cut_bin_certificate_sound certificate3854 profilesValid3854 numericValid3854 valid3854

def retention3855 : RatCutRetentionCertificate := ⟨(23/1000),(47/2000),(611043137609207474/1986665189665141222489),(558701075044607803/1000000000000000000),4,(1215386771576564290384251771831149307/558701075044607803000000000000000000),true,MergedCutProfiles.Batch587.profile23484,![MergedCutProfiles.Batch587.profile23484,MergedCutProfiles.Batch587.profile23485,MergedCutProfiles.Batch587.profile23486,MergedCutProfiles.Batch587.profile23487,MergedCutProfiles.Batch587.profile23488,MergedCutProfiles.Batch587.profile23489,MergedCutProfiles.Batch587.profile23490,MergedCutProfiles.Batch587.profile23491,MergedCutProfiles.Batch587.profile23492,MergedCutProfiles.Batch587.profile23493,MergedCutProfiles.Batch587.profile23494,MergedCutProfiles.Batch587.profile23495,MergedCutProfiles.Batch587.profile23496,MergedCutProfiles.Batch587.profile23497,MergedCutProfiles.Batch587.profile23498,MergedCutProfiles.Batch587.profile23499]⟩
theorem profilesValid3855 : retention3855.ProfilesValid := by
  change ∀ j : Fin 16, (retention3855.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch587.valid23484
  · exact MergedCutProfiles.Batch587.valid23485
  · exact MergedCutProfiles.Batch587.valid23486
  · exact MergedCutProfiles.Batch587.valid23487
  · exact MergedCutProfiles.Batch587.valid23488
  · exact MergedCutProfiles.Batch587.valid23489
  · exact MergedCutProfiles.Batch587.valid23490
  · exact MergedCutProfiles.Batch587.valid23491
  · exact MergedCutProfiles.Batch587.valid23492
  · exact MergedCutProfiles.Batch587.valid23493
  · exact MergedCutProfiles.Batch587.valid23494
  · exact MergedCutProfiles.Batch587.valid23495
  · exact MergedCutProfiles.Batch587.valid23496
  · exact MergedCutProfiles.Batch587.valid23497
  · exact MergedCutProfiles.Batch587.valid23498
  · exact MergedCutProfiles.Batch587.valid23499
theorem numericValid3855 : retention3855.NumericValid := by decide +kernel
def certificate3855 : RatCutBinCertificate := ⟨⟨retention3855,(91076842403946083/50000000000000000),(11758447315912833/500000000000000000),(8894166710876154947/1000000000000000000),(8856374180019400121829/500000000000000000),(1078057079533907177/500000000000000000)⟩,(499949737204432811/500000000000000000),(712296865920848557/1000000000000000000),(46048937532402489/1000000000000000000),(1249734896560279/62500000000000000)⟩
theorem valid3855 : certificate3855.Valid := by decide +kernel
theorem sound3855 : certificate3855.Sound := rat_cut_bin_certificate_sound certificate3855 profilesValid3855 numericValid3855 valid3855

def retention3856 : RatCutRetentionCertificate := ⟨(23/1000),(47/2000),(175174201000000000/283809312809305888927),(305521568804603737/500000000000000000),4,(347797877189638772375116484899320051/152760784402301868500000000000000000),true,MergedCutProfiles.Batch587.profile23485,![MergedCutProfiles.Batch587.profile23485,MergedCutProfiles.Batch587.profile23487,MergedCutProfiles.Batch587.profile23500,MergedCutProfiles.Batch587.profile23491,MergedCutProfiles.Batch587.profile23493,MergedCutProfiles.Batch587.profile23495,MergedCutProfiles.Batch587.profile23497,MergedCutProfiles.Batch587.profile23499,MergedCutProfiles.Batch587.profile23501,MergedCutProfiles.Batch587.profile23502,MergedCutProfiles.Batch587.profile23503,MergedCutProfiles.Batch587.profile23504,MergedCutProfiles.Batch587.profile23505,MergedCutProfiles.Batch587.profile23506,MergedCutProfiles.Batch587.profile23507,MergedCutProfiles.Batch587.profile23508]⟩
theorem profilesValid3856 : retention3856.ProfilesValid := by
  change ∀ j : Fin 16, (retention3856.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch587.valid23485
  · exact MergedCutProfiles.Batch587.valid23487
  · exact MergedCutProfiles.Batch587.valid23500
  · exact MergedCutProfiles.Batch587.valid23491
  · exact MergedCutProfiles.Batch587.valid23493
  · exact MergedCutProfiles.Batch587.valid23495
  · exact MergedCutProfiles.Batch587.valid23497
  · exact MergedCutProfiles.Batch587.valid23499
  · exact MergedCutProfiles.Batch587.valid23501
  · exact MergedCutProfiles.Batch587.valid23502
  · exact MergedCutProfiles.Batch587.valid23503
  · exact MergedCutProfiles.Batch587.valid23504
  · exact MergedCutProfiles.Batch587.valid23505
  · exact MergedCutProfiles.Batch587.valid23506
  · exact MergedCutProfiles.Batch587.valid23507
  · exact MergedCutProfiles.Batch587.valid23508
theorem numericValid3856 : retention3856.NumericValid := by decide +kernel
def certificate3856 : RatCutBinCertificate := ⟨⟨retention3856,(91076842403946083/50000000000000000),(11758447315912833/500000000000000000),(8894166710876154947/1000000000000000000),(8856374180019400121829/500000000000000000),(112874163260105921/50000000000000000)⟩,(499949737204432811/500000000000000000),(640191843442257679/1000000000000000000),(9286333207537891/125000000000000000),(34058254179446119/1000000000000000000)⟩
theorem valid3856 : certificate3856.Valid := by decide +kernel
theorem sound3856 : certificate3856.Sound := rat_cut_bin_certificate_sound certificate3856 profilesValid3856 numericValid3856 valid3856

def retention3857 : RatCutRetentionCertificate := ⟨(23/1000),(47/2000),(3700330588020168080/1986665189665141222489),(1226219407/1000000000),(13/5),(460005233393109921870703190800457671/196195105120000000000000000000000000),true,MergedCutProfiles.Batch587.profile23500,![MergedCutProfiles.Batch587.profile23500,MergedCutProfiles.Batch587.profile23495,MergedCutProfiles.Batch587.profile23501,MergedCutProfiles.Batch587.profile23504,MergedCutProfiles.Batch587.profile23507,MergedCutProfiles.Batch587.profile23509,MergedCutProfiles.Batch587.profile23510,MergedCutProfiles.Batch587.profile23511,MergedCutProfiles.Batch587.profile23512,MergedCutProfiles.Batch587.profile23513,MergedCutProfiles.Batch587.profile23514,MergedCutProfiles.Batch587.profile23515,MergedCutProfiles.Batch587.profile23516,MergedCutProfiles.Batch587.profile23517,MergedCutProfiles.Batch587.profile23518,MergedCutProfiles.Batch587.profile23519]⟩
theorem profilesValid3857 : retention3857.ProfilesValid := by
  change ∀ j : Fin 16, (retention3857.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch587.valid23500
  · exact MergedCutProfiles.Batch587.valid23495
  · exact MergedCutProfiles.Batch587.valid23501
  · exact MergedCutProfiles.Batch587.valid23504
  · exact MergedCutProfiles.Batch587.valid23507
  · exact MergedCutProfiles.Batch587.valid23509
  · exact MergedCutProfiles.Batch587.valid23510
  · exact MergedCutProfiles.Batch587.valid23511
  · exact MergedCutProfiles.Batch587.valid23512
  · exact MergedCutProfiles.Batch587.valid23513
  · exact MergedCutProfiles.Batch587.valid23514
  · exact MergedCutProfiles.Batch587.valid23515
  · exact MergedCutProfiles.Batch587.valid23516
  · exact MergedCutProfiles.Batch587.valid23517
  · exact MergedCutProfiles.Batch587.valid23518
  · exact MergedCutProfiles.Batch587.valid23519
theorem numericValid3857 : retention3857.NumericValid := by decide +kernel
def certificate3857 : RatCutBinCertificate := ⟨⟨retention3857,(91076842403946083/50000000000000000),(11758447315912833/500000000000000000),(8894166710876154947/1000000000000000000),(8856374180019400121829/500000000000000000),(1166054594748926351/500000000000000000)⟩,(499949737204432811/500000000000000000),(82347267075900859/200000000000000000),(222899390065135033/1000000000000000000),(78008095818846127/500000000000000000)⟩
theorem valid3857 : certificate3857.Valid := by decide +kernel
theorem sound3857 : certificate3857.Sound := rat_cut_bin_certificate_sound certificate3857 profilesValid3857 numericValid3857 valid3857

def retention3858 : RatCutRetentionCertificate := ⟨(23/1000),(47/2000),(64000000000000000000/1986665189665141222489),(46254132350252101/12500000000000000),(27/20),(1948808635131188066511476944775684871/925082647005042020000000000000000000),true,MergedCutProfiles.Batch588.profile23520,![MergedCutProfiles.Batch588.profile23520,MergedCutProfiles.Batch588.profile23521,MergedCutProfiles.Batch588.profile23522,MergedCutProfiles.Batch588.profile23523,MergedCutProfiles.Batch588.profile23524,MergedCutProfiles.Batch588.profile23525,MergedCutProfiles.Batch588.profile23526,MergedCutProfiles.Batch588.profile23527,MergedCutProfiles.Batch588.profile23528,MergedCutProfiles.Batch588.profile23529,MergedCutProfiles.Batch588.profile23530,MergedCutProfiles.Batch588.profile23531,MergedCutProfiles.Batch588.profile23532,MergedCutProfiles.Batch588.profile23533,MergedCutProfiles.Batch588.profile23534,MergedCutProfiles.Batch588.profile23535]⟩
theorem profilesValid3858 : retention3858.ProfilesValid := by
  change ∀ j : Fin 16, (retention3858.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch588.valid23520
  · exact MergedCutProfiles.Batch588.valid23521
  · exact MergedCutProfiles.Batch588.valid23522
  · exact MergedCutProfiles.Batch588.valid23523
  · exact MergedCutProfiles.Batch588.valid23524
  · exact MergedCutProfiles.Batch588.valid23525
  · exact MergedCutProfiles.Batch588.valid23526
  · exact MergedCutProfiles.Batch588.valid23527
  · exact MergedCutProfiles.Batch588.valid23528
  · exact MergedCutProfiles.Batch588.valid23529
  · exact MergedCutProfiles.Batch588.valid23530
  · exact MergedCutProfiles.Batch588.valid23531
  · exact MergedCutProfiles.Batch588.valid23532
  · exact MergedCutProfiles.Batch588.valid23533
  · exact MergedCutProfiles.Batch588.valid23534
  · exact MergedCutProfiles.Batch588.valid23535
theorem numericValid3858 : retention3858.NumericValid := by decide +kernel
def certificate3858 : RatCutBinCertificate := ⟨⟨retention3858,(91076842403946083/50000000000000000),(11758447315912833/500000000000000000),(8894166710876154947/1000000000000000000),(8856374180019400121829/500000000000000000),(525032482168491821/250000000000000000)⟩,(499949737204432811/500000000000000000),(151920864864625851/500000000000000000),(83546639418006443/250000000000000000),(396382135649555833/1000000000000000000)⟩
theorem valid3858 : certificate3858.Valid := by decide +kernel
theorem sound3858 : certificate3858.Sound := rat_cut_bin_certificate_sound certificate3858 profilesValid3858 numericValid3858 valid3858

def retention3859 : RatCutRetentionCertificate := ⟨(23/1000),(47/2000),(1/2),64,1,(159608034891270032407857955280106711/160000000000000000000000000000000000),false,MergedCutProfiles.Batch588.profile23536,(fun _ => MergedCutProfiles.Batch588.profile23536)⟩
theorem profilesValid3859 : retention3859.ProfilesValid := by
  exact MergedCutProfiles.Batch588.valid23536
theorem numericValid3859 : retention3859.NumericValid := by decide +kernel
def certificate3859 : RatCutBinCertificate := ⟨⟨retention3859,(91076842403946083/50000000000000000),(11758447315912833/500000000000000000),(8894166710876154947/1000000000000000000),(8856374180019400121829/500000000000000000),(99273392752794881/100000000000000000)⟩,(499949737204432811/500000000000000000),(61408015369925463/125000000000000000),(159558353160009011/1000000000000000000),(77981850363440101/500000000000000000)⟩
theorem valid3859 : certificate3859.Valid := by decide +kernel
theorem sound3859 : certificate3859.Sound := rat_cut_bin_certificate_sound certificate3859 profilesValid3859 numericValid3859 valid3859

def retention3860 : RatCutRetentionCertificate := ⟨(23/1000),(47/2000),(64000000000000000000/1986665189665141222489),(19714588126546406257/1000000000000000000),1,(41175445757507455822133044537754314449/19714588126546406257000000000000000000),false,MergedCutProfiles.Batch588.profile23537,(fun _ => MergedCutProfiles.Batch588.profile23537)⟩
theorem profilesValid3860 : retention3860.ProfilesValid := by
  exact MergedCutProfiles.Batch588.valid23537
theorem numericValid3860 : retention3860.NumericValid := by decide +kernel
def certificate3860 : RatCutBinCertificate := ⟨⟨retention3860,(89601737303946083/50000000000000000),(11758447315912833/500000000000000000),(8894166710876154947/1000000000000000000),(8856374180019400121829/500000000000000000),(208383924432485697/100000000000000000)⟩,(999901102552151791/1000000000000000000),(31884726254386933/1000000000000000000),(419396860428884613/500000000000000000),(395164419010918683/250000000000000000)⟩
theorem valid3860 : certificate3860.Valid := by decide +kernel
theorem sound3860 : certificate3860.Sound := rat_cut_bin_certificate_sound certificate3860 profilesValid3860 numericValid3860 valid3860

def retention3861 : RatCutRetentionCertificate := ⟨(23/1000),(47/2000),(1/2),64,1,(159608034891270032407857955280106711/160000000000000000000000000000000000),false,MergedCutProfiles.Batch588.profile23536,(fun _ => MergedCutProfiles.Batch588.profile23536)⟩
theorem profilesValid3861 : retention3861.ProfilesValid := by
  exact MergedCutProfiles.Batch588.valid23536
theorem numericValid3861 : retention3861.NumericValid := by decide +kernel
def certificate3861 : RatCutBinCertificate := ⟨⟨retention3861,(89601737303946083/50000000000000000),(11758447315912833/500000000000000000),(8894166710876154947/1000000000000000000),(8856374180019400121829/500000000000000000),(496405966734184971/500000000000000000)⟩,(999901102552151791/1000000000000000000),(66923695841699301/1000000000000000000),(93056825829781547/125000000000000000),(14554809106438471/20000000000000000)⟩
theorem valid3861 : certificate3861.Valid := by decide +kernel
theorem sound3861 : certificate3861.Sound := rat_cut_bin_certificate_sound certificate3861 profilesValid3861 numericValid3861 valid3861

def retention3862 : RatCutRetentionCertificate := ⟨(47/2000),(3/125),(581616391509173255/1900110362806017032742),(2183288751052101/3906250000000000),4,(108113311343975616907449026439973963/49681948468385587200000000000000000),true,MergedCutProfiles.Batch588.profile23538,![MergedCutProfiles.Batch588.profile23538,MergedCutProfiles.Batch588.profile23539,MergedCutProfiles.Batch588.profile23540,MergedCutProfiles.Batch588.profile23541,MergedCutProfiles.Batch588.profile23542,MergedCutProfiles.Batch588.profile23543,MergedCutProfiles.Batch588.profile23544,MergedCutProfiles.Batch588.profile23545,MergedCutProfiles.Batch588.profile23546,MergedCutProfiles.Batch588.profile23547,MergedCutProfiles.Batch588.profile23548,MergedCutProfiles.Batch588.profile23549,MergedCutProfiles.Batch588.profile23550,MergedCutProfiles.Batch588.profile23551,MergedCutProfiles.Batch588.profile23552,MergedCutProfiles.Batch588.profile23553]⟩
theorem profilesValid3862 : retention3862.ProfilesValid := by
  change ∀ j : Fin 16, (retention3862.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch588.valid23538
  · exact MergedCutProfiles.Batch588.valid23539
  · exact MergedCutProfiles.Batch588.valid23540
  · exact MergedCutProfiles.Batch588.valid23541
  · exact MergedCutProfiles.Batch588.valid23542
  · exact MergedCutProfiles.Batch588.valid23543
  · exact MergedCutProfiles.Batch588.valid23544
  · exact MergedCutProfiles.Batch588.valid23545
  · exact MergedCutProfiles.Batch588.valid23546
  · exact MergedCutProfiles.Batch588.valid23547
  · exact MergedCutProfiles.Batch588.valid23548
  · exact MergedCutProfiles.Batch588.valid23549
  · exact MergedCutProfiles.Batch588.valid23550
  · exact MergedCutProfiles.Batch588.valid23551
  · exact MergedCutProfiles.Batch588.valid23552
  · exact MergedCutProfiles.Batch588.valid23553
theorem numericValid3862 : retention3862.NumericValid := by decide +kernel
def certificate3862 : RatCutBinCertificate := ⟨⟨retention3862,(911448032109917467/500000000000000000),(12287303118992409/500000000000000000),(8954321247761919431/1000000000000000000),(2131967635031285304207/125000000000000000),(86243887369841423/40000000000000000)⟩,(999895634456660183/1000000000000000000),(713800747935033727/1000000000000000000),(2846269763984621/62500000000000000),(9888100716798351/500000000000000000)⟩
theorem valid3862 : certificate3862.Valid := by decide +kernel
theorem sound3862 : certificate3862.Sound := rat_cut_bin_certificate_sound certificate3862 profilesValid3862 numericValid3862 valid3862

def retention3863 : RatCutRetentionCertificate := ⟨(47/2000),(3/125),(205275931000000000/316685060467669505457),(116323278301834651/200000000000000000),4,(569148358260051013207/256000000000000000000),true,MergedCutProfiles.Batch588.profile23554,![MergedCutProfiles.Batch588.profile23554,MergedCutProfiles.Batch588.profile23555,MergedCutProfiles.Batch588.profile23556,MergedCutProfiles.Batch588.profile23546,MergedCutProfiles.Batch588.profile23548,MergedCutProfiles.Batch588.profile23549,MergedCutProfiles.Batch588.profile23552,MergedCutProfiles.Batch588.profile23557,MergedCutProfiles.Batch588.profile23558,MergedCutProfiles.Batch588.profile23559,MergedCutProfiles.Batch589.profile23560,MergedCutProfiles.Batch589.profile23561,MergedCutProfiles.Batch589.profile23562,MergedCutProfiles.Batch589.profile23563,MergedCutProfiles.Batch589.profile23564,MergedCutProfiles.Batch589.profile23565]⟩
theorem profilesValid3863 : retention3863.ProfilesValid := by
  change ∀ j : Fin 16, (retention3863.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch588.valid23554
  · exact MergedCutProfiles.Batch588.valid23555
  · exact MergedCutProfiles.Batch588.valid23556
  · exact MergedCutProfiles.Batch588.valid23546
  · exact MergedCutProfiles.Batch588.valid23548
  · exact MergedCutProfiles.Batch588.valid23549
  · exact MergedCutProfiles.Batch588.valid23552
  · exact MergedCutProfiles.Batch588.valid23557
  · exact MergedCutProfiles.Batch588.valid23558
  · exact MergedCutProfiles.Batch588.valid23559
  · exact MergedCutProfiles.Batch589.valid23560
  · exact MergedCutProfiles.Batch589.valid23561
  · exact MergedCutProfiles.Batch589.valid23562
  · exact MergedCutProfiles.Batch589.valid23563
  · exact MergedCutProfiles.Batch589.valid23564
  · exact MergedCutProfiles.Batch589.valid23565
theorem numericValid3863 : retention3863.NumericValid := by decide +kernel
def certificate3863 : RatCutBinCertificate := ⟨⟨retention3863,(911448032109917467/500000000000000000),(12287303118992409/500000000000000000),(8954321247761919431/1000000000000000000),(2131967635031285304207/125000000000000000),(2203224439369231227/1000000000000000000)⟩,(999895634456660183/1000000000000000000),(339889658053714399/500000000000000000),(57834658338911191/1000000000000000000),(5150842632559723/200000000000000000)⟩
theorem valid3863 : certificate3863.Valid := by decide +kernel
theorem sound3863 : certificate3863.Sound := rat_cut_bin_certificate_sound certificate3863 profilesValid3863 numericValid3863 valid3863

def certificates : List RatCutBinCertificate := [certificate3852,certificate3853,certificate3854,certificate3855,certificate3856,certificate3857,certificate3858,certificate3859,certificate3860,certificate3861,certificate3862,certificate3863]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3852,List.forall_mem_cons.mpr ⟨sound3853,List.forall_mem_cons.mpr ⟨sound3854,List.forall_mem_cons.mpr ⟨sound3855,List.forall_mem_cons.mpr ⟨sound3856,List.forall_mem_cons.mpr ⟨sound3857,List.forall_mem_cons.mpr ⟨sound3858,List.forall_mem_cons.mpr ⟨sound3859,List.forall_mem_cons.mpr ⟨sound3860,List.forall_mem_cons.mpr ⟨sound3861,List.forall_mem_cons.mpr ⟨sound3862,List.forall_mem_cons.mpr ⟨sound3863,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch321
