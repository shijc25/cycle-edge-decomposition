import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch111
import Cycle12.MergedCutProfiles.Batch112
import Cycle12.MergedCutProfiles.Batch113

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch056

def retention672 : RatCutRetentionCertificate := ⟨(179/4000),(9/200),(12099010711803185579/24225736566934492529),(11979218526537807503/1000000000000000000),(21/20),(2736121803372417815431415272153987545233/2738107091780070286400000000000000000000),false,MergedCutProfiles.Batch111.profile4475,(fun _ => MergedCutProfiles.Batch111.profile4475)⟩
theorem profilesValid672 : retention672.ProfilesValid := by
  exact MergedCutProfiles.Batch111.valid4475
theorem numericValid672 : retention672.NumericValid := by decide +kernel
def certificate672 : RatCutBinCertificate := ⟨⟨retention672,(1245821470341272169/500000000000000000),(11819389720817643/125000000000000000),(12226730527229093307/1000000000000000000),(148306153012655465129/500000000000000000),(7832335332625157/8000000000000000)⟩,(3876476994746011/3906250000000000),(204518968963679909/500000000000000000),(28162831630339719/125000000000000000),(38806919384327993/200000000000000000)⟩
theorem valid672 : certificate672.Valid := by decide +kernel
theorem sound672 : certificate672.Sound := rat_cut_bin_certificate_sound certificate672 profilesValid672 numericValid672 valid672

def retention673 : RatCutRetentionCertificate := ⟨(179/4000),(9/200),(1/2),(12099010711803185579/1000000000000000000),(21/20),(19325135164689932070793007223055172645039/19358417138885096926400000000000000000000),false,MergedCutProfiles.Batch111.profile4472,(fun _ => MergedCutProfiles.Batch111.profile4472)⟩
theorem profilesValid673 : retention673.ProfilesValid := by
  exact MergedCutProfiles.Batch111.valid4472
theorem numericValid673 : retention673.NumericValid := by decide +kernel
def certificate673 : RatCutBinCertificate := ⟨⟨retention673,(1245821470341272169/500000000000000000),(11819389720817643/125000000000000000),(12226730527229093307/1000000000000000000),(148306153012655465129/500000000000000000),(122255966195909063/125000000000000000)⟩,(3876476994746011/3906250000000000),(204726862807992201/500000000000000000),(224931184927572947/1000000000000000000),(193664227998101523/1000000000000000000)⟩
theorem valid673 : certificate673.Valid := by decide +kernel
theorem sound673 : certificate673.Sound := rat_cut_bin_certificate_sound certificate673 profilesValid673 numericValid673 valid673

def retention674 : RatCutRetentionCertificate := ⟨(9/200),(181/4000),(817755378651608485/23925557571886382669),(25301837210755213/31250000000000000),(31/10),(84801030323529290757/40000000000000000000),true,MergedCutProfiles.Batch111.profile4476,![MergedCutProfiles.Batch111.profile4476,MergedCutProfiles.Batch111.profile4477,MergedCutProfiles.Batch111.profile4478,MergedCutProfiles.Batch111.profile4479,MergedCutProfiles.Batch112.profile4480,MergedCutProfiles.Batch112.profile4481,MergedCutProfiles.Batch112.profile4482,MergedCutProfiles.Batch112.profile4483,MergedCutProfiles.Batch112.profile4484,MergedCutProfiles.Batch112.profile4485,MergedCutProfiles.Batch112.profile4486,MergedCutProfiles.Batch112.profile4487,MergedCutProfiles.Batch112.profile4488,MergedCutProfiles.Batch112.profile4489,MergedCutProfiles.Batch112.profile4490,MergedCutProfiles.Batch112.profile4491]⟩
theorem profilesValid674 : retention674.ProfilesValid := by
  change ∀ j : Fin 16, (retention674.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch111.valid4476
  · exact MergedCutProfiles.Batch111.valid4477
  · exact MergedCutProfiles.Batch111.valid4478
  · exact MergedCutProfiles.Batch111.valid4479
  · exact MergedCutProfiles.Batch112.valid4480
  · exact MergedCutProfiles.Batch112.valid4481
  · exact MergedCutProfiles.Batch112.valid4482
  · exact MergedCutProfiles.Batch112.valid4483
  · exact MergedCutProfiles.Batch112.valid4484
  · exact MergedCutProfiles.Batch112.valid4485
  · exact MergedCutProfiles.Batch112.valid4486
  · exact MergedCutProfiles.Batch112.valid4487
  · exact MergedCutProfiles.Batch112.valid4488
  · exact MergedCutProfiles.Batch112.valid4489
  · exact MergedCutProfiles.Batch112.valid4490
  · exact MergedCutProfiles.Batch112.valid4491
theorem numericValid674 : retention674.NumericValid := by decide +kernel
def certificate674 : RatCutBinCertificate := ⟨⟨retention674,(2109382053114026477/1000000000000000000),(11965748524255287/125000000000000000),(3068906201132341919/250000000000000000),(29410909641871090571/100000000000000000),(2069027011032378149/1000000000000000000)⟩,(39740061975658313/40000000000000000),(390450248657066093/1000000000000000000),(9693887185921817/40000000000000000),(15849111836943961/125000000000000000)⟩
theorem valid674 : certificate674.Valid := by decide +kernel
theorem sound674 : certificate674.Sound := rat_cut_bin_certificate_sound certificate674 profilesValid674 numericValid674 valid674

def retention675 : RatCutRetentionCertificate := ⟨(9/200),(181/4000),(893700359000000000/23925557571886382669),(163551075730321697/200000000000000000),(61/20),(538753618859491477177/256000000000000000000),true,MergedCutProfiles.Batch112.profile4492,![MergedCutProfiles.Batch112.profile4492,MergedCutProfiles.Batch112.profile4493,MergedCutProfiles.Batch112.profile4494,MergedCutProfiles.Batch112.profile4495,MergedCutProfiles.Batch112.profile4496,MergedCutProfiles.Batch112.profile4497,MergedCutProfiles.Batch112.profile4498,MergedCutProfiles.Batch112.profile4499,MergedCutProfiles.Batch112.profile4500,MergedCutProfiles.Batch112.profile4501,MergedCutProfiles.Batch112.profile4502,MergedCutProfiles.Batch112.profile4503,MergedCutProfiles.Batch112.profile4504,MergedCutProfiles.Batch112.profile4505,MergedCutProfiles.Batch112.profile4506,MergedCutProfiles.Batch112.profile4507]⟩
theorem profilesValid675 : retention675.ProfilesValid := by
  change ∀ j : Fin 16, (retention675.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch112.valid4492
  · exact MergedCutProfiles.Batch112.valid4493
  · exact MergedCutProfiles.Batch112.valid4494
  · exact MergedCutProfiles.Batch112.valid4495
  · exact MergedCutProfiles.Batch112.valid4496
  · exact MergedCutProfiles.Batch112.valid4497
  · exact MergedCutProfiles.Batch112.valid4498
  · exact MergedCutProfiles.Batch112.valid4499
  · exact MergedCutProfiles.Batch112.valid4500
  · exact MergedCutProfiles.Batch112.valid4501
  · exact MergedCutProfiles.Batch112.valid4502
  · exact MergedCutProfiles.Batch112.valid4503
  · exact MergedCutProfiles.Batch112.valid4504
  · exact MergedCutProfiles.Batch112.valid4505
  · exact MergedCutProfiles.Batch112.valid4506
  · exact MergedCutProfiles.Batch112.valid4507
theorem numericValid675 : retention675.NumericValid := by decide +kernel
def certificate675 : RatCutBinCertificate := ⟨⟨retention675,(2109382053114026477/1000000000000000000),(11965748524255287/125000000000000000),(3068906201132341919/250000000000000000),(29410909641871090571/100000000000000000),(1027165047933973757/500000000000000000)⟩,(39740061975658313/40000000000000000),(195768523274775889/500000000000000000),(48265332772883767/200000000000000000),(127001624081084227/1000000000000000000)⟩
theorem valid675 : certificate675.Valid := by decide +kernel
theorem sound675 : certificate675.Sound := rat_cut_bin_certificate_sound certificate675 profilesValid675 numericValid675 valid675

def retention676 : RatCutRetentionCertificate := ⟨(9/200),(181/4000),(1007795137826016615/23925557571886382669),(893700359/1000000000),(14/5),(16624852096155526853/8000000000000000000),true,MergedCutProfiles.Batch112.profile4508,![MergedCutProfiles.Batch112.profile4508,MergedCutProfiles.Batch112.profile4509,MergedCutProfiles.Batch112.profile4510,MergedCutProfiles.Batch112.profile4511,MergedCutProfiles.Batch112.profile4512,MergedCutProfiles.Batch112.profile4513,MergedCutProfiles.Batch112.profile4514,MergedCutProfiles.Batch112.profile4515,MergedCutProfiles.Batch112.profile4516,MergedCutProfiles.Batch112.profile4517,MergedCutProfiles.Batch112.profile4518,MergedCutProfiles.Batch112.profile4519,MergedCutProfiles.Batch112.profile4491,MergedCutProfiles.Batch113.profile4520,MergedCutProfiles.Batch113.profile4521,MergedCutProfiles.Batch113.profile4522]⟩
theorem profilesValid676 : retention676.ProfilesValid := by
  change ∀ j : Fin 16, (retention676.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch112.valid4508
  · exact MergedCutProfiles.Batch112.valid4509
  · exact MergedCutProfiles.Batch112.valid4510
  · exact MergedCutProfiles.Batch112.valid4511
  · exact MergedCutProfiles.Batch112.valid4512
  · exact MergedCutProfiles.Batch112.valid4513
  · exact MergedCutProfiles.Batch112.valid4514
  · exact MergedCutProfiles.Batch112.valid4515
  · exact MergedCutProfiles.Batch112.valid4516
  · exact MergedCutProfiles.Batch112.valid4517
  · exact MergedCutProfiles.Batch112.valid4518
  · exact MergedCutProfiles.Batch112.valid4519
  · exact MergedCutProfiles.Batch112.valid4491
  · exact MergedCutProfiles.Batch113.valid4520
  · exact MergedCutProfiles.Batch113.valid4521
  · exact MergedCutProfiles.Batch113.valid4522
theorem numericValid676 : retention676.NumericValid := by decide +kernel
def certificate676 : RatCutBinCertificate := ⟨⟨retention676,(2109382053114026477/1000000000000000000),(11965748524255287/125000000000000000),(3068906201132341919/250000000000000000),(29410909641871090571/100000000000000000),(127002694342958953/62500000000000000)⟩,(39740061975658313/40000000000000000),(23823157867716689/62500000000000000),(62796232174606257/250000000000000000),(140228834800662081/1000000000000000000)⟩
theorem valid676 : certificate676.Valid := by decide +kernel
theorem sound676 : certificate676.Sound := rat_cut_bin_certificate_sound certificate676 profilesValid676 numericValid676 valid676

def retention677 : RatCutRetentionCertificate := ⟨(9/200),(181/4000),(2022406365436227131/23925557571886382669),(201559027565203323/200000000000000000),(51/20),(497523026388865520667/256000000000000000000),true,MergedCutProfiles.Batch112.profile4509,![MergedCutProfiles.Batch112.profile4509,MergedCutProfiles.Batch112.profile4511,MergedCutProfiles.Batch112.profile4513,MergedCutProfiles.Batch112.profile4515,MergedCutProfiles.Batch112.profile4517,MergedCutProfiles.Batch112.profile4519,MergedCutProfiles.Batch113.profile4520,MergedCutProfiles.Batch113.profile4523,MergedCutProfiles.Batch113.profile4524,MergedCutProfiles.Batch113.profile4525,MergedCutProfiles.Batch113.profile4526,MergedCutProfiles.Batch113.profile4527,MergedCutProfiles.Batch113.profile4528,MergedCutProfiles.Batch113.profile4529,MergedCutProfiles.Batch113.profile4530,MergedCutProfiles.Batch113.profile4531]⟩
theorem profilesValid677 : retention677.ProfilesValid := by
  change ∀ j : Fin 16, (retention677.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch112.valid4509
  · exact MergedCutProfiles.Batch112.valid4511
  · exact MergedCutProfiles.Batch112.valid4513
  · exact MergedCutProfiles.Batch112.valid4515
  · exact MergedCutProfiles.Batch112.valid4517
  · exact MergedCutProfiles.Batch112.valid4519
  · exact MergedCutProfiles.Batch113.valid4520
  · exact MergedCutProfiles.Batch113.valid4523
  · exact MergedCutProfiles.Batch113.valid4524
  · exact MergedCutProfiles.Batch113.valid4525
  · exact MergedCutProfiles.Batch113.valid4526
  · exact MergedCutProfiles.Batch113.valid4527
  · exact MergedCutProfiles.Batch113.valid4528
  · exact MergedCutProfiles.Batch113.valid4529
  · exact MergedCutProfiles.Batch113.valid4530
  · exact MergedCutProfiles.Batch113.valid4531
theorem numericValid677 : retention677.NumericValid := by decide +kernel
def certificate677 : RatCutBinCertificate := ⟨⟨retention677,(2109382053114026477/1000000000000000000),(11965748524255287/125000000000000000),(3068906201132341919/250000000000000000),(29410909641871090571/100000000000000000),(950749433215788059/500000000000000000)⟩,(39740061975658313/40000000000000000),(77648013084221087/200000000000000000),(244431902071645041/1000000000000000000),(70099802170404303/500000000000000000)⟩
theorem valid677 : certificate677.Valid := by decide +kernel
theorem sound677 : certificate677.Sound := rat_cut_bin_certificate_sound certificate677 profilesValid677 numericValid677 valid677

def retention678 : RatCutRetentionCertificate := ⟨(9/200),(181/4000),(7227769061192582231/23925557571886382669),(2022406365436227131/1000000000000000000),(31/20),(4533649364691885190924271251862919154439/3235850184697963409600000000000000000000),false,MergedCutProfiles.Batch113.profile4532,(fun _ => MergedCutProfiles.Batch113.profile4532)⟩
theorem profilesValid678 : retention678.ProfilesValid := by
  exact MergedCutProfiles.Batch113.valid4532
theorem numericValid678 : retention678.NumericValid := by decide +kernel
def certificate678 : RatCutBinCertificate := ⟨⟨retention678,(2109382053114026477/1000000000000000000),(11965748524255287/125000000000000000),(3068906201132341919/250000000000000000),(29410909641871090571/100000000000000000),(687785139979113887/500000000000000000)⟩,(39740061975658313/40000000000000000),(54116118321038701/125000000000000000),(204630395504749507/1000000000000000000),(70241269059321149/500000000000000000)⟩
theorem valid678 : certificate678.Valid := by decide +kernel
theorem sound678 : certificate678.Sound := rat_cut_bin_certificate_sound certificate678 profilesValid678 numericValid678 valid678

def retention679 : RatCutRetentionCertificate := ⟨(9/200),(181/4000),(11310090705455187029/23925557571886382669),(7227769061192582231/1000000000000000000),(11/10),(3042919847997163894381665417468786499279/2891107624477032892400000000000000000000),false,MergedCutProfiles.Batch113.profile4533,(fun _ => MergedCutProfiles.Batch113.profile4533)⟩
theorem profilesValid679 : retention679.ProfilesValid := by
  exact MergedCutProfiles.Batch113.valid4533
theorem numericValid679 : retention679.NumericValid := by decide +kernel
def certificate679 : RatCutBinCertificate := ⟨⟨retention679,(2109382053114026477/1000000000000000000),(11965748524255287/125000000000000000),(3068906201132341919/250000000000000000),(29410909641871090571/100000000000000000),(12930191651318881/12500000000000000)⟩,(39740061975658313/40000000000000000),(477016966629409701/1000000000000000000),(16989342596843377/100000000000000000),(17734724499204171/125000000000000000)⟩
theorem valid679 : certificate679.Valid := by decide +kernel
theorem sound679 : certificate679.Sound := rat_cut_bin_certificate_sound certificate679 profilesValid679 numericValid679 valid679

def retention680 : RatCutRetentionCertificate := ⟨(9/200),(181/4000),(11887018998976000464/23925557571886382669),(11310090705455187029/1000000000000000000),(21/20),(18160403197544021786920261020747253385159/18096145128728299246400000000000000000000),false,MergedCutProfiles.Batch113.profile4534,(fun _ => MergedCutProfiles.Batch113.profile4534)⟩
theorem profilesValid680 : retention680.ProfilesValid := by
  exact MergedCutProfiles.Batch113.valid4534
theorem numericValid680 : retention680.NumericValid := by decide +kernel
def certificate680 : RatCutBinCertificate := ⟨⟨retention680,(2109382053114026477/1000000000000000000),(11965748524255287/125000000000000000),(3068906201132341919/250000000000000000),(29410909641871090571/100000000000000000),(246569730743498287/250000000000000000)⟩,(39740061975658313/40000000000000000),(242891192838219201/500000000000000000),(2554457963516771/15625000000000000),(70670900261297299/500000000000000000)⟩
theorem valid680 : certificate680.Valid := by decide +kernel
theorem sound680 : certificate680.Sound := rat_cut_bin_certificate_sound certificate680 profilesValid680 numericValid680 valid680

def retention681 : RatCutRetentionCertificate := ⟨(9/200),(181/4000),(1/2),(742938687436000029/62500000000000000),(21/20),(74148596081097954672059537310844447319/74293868743600002900000000000000000000),false,MergedCutProfiles.Batch113.profile4535,(fun _ => MergedCutProfiles.Batch113.profile4535)⟩
theorem profilesValid681 : retention681.ProfilesValid := by
  exact MergedCutProfiles.Batch113.valid4535
theorem numericValid681 : retention681.NumericValid := by decide +kernel
def certificate681 : RatCutBinCertificate := ⟨⟨retention681,(2109382053114026477/1000000000000000000),(11965748524255287/125000000000000000),(3068906201132341919/250000000000000000),(29410909641871090571/100000000000000000),(245193160312210541/250000000000000000)⟩,(39740061975658313/40000000000000000),(487255320725909841/1000000000000000000),(40606023395741643/250000000000000000),(17524438426700951/125000000000000000)⟩
theorem valid681 : certificate681.Valid := by decide +kernel
theorem sound681 : certificate681.Sound := rat_cut_bin_certificate_sound certificate681 profilesValid681 numericValid681 valid681

def retention682 : RatCutRetentionCertificate := ⟨(9/200),(181/4000),(10653518446565390172/23925557571886382669),(3785037519171510523/1000000000000000000),(6/5),(417719332259965052677951231834359552351/378503751917151052300000000000000000000),false,MergedCutProfiles.Batch113.profile4536,(fun _ => MergedCutProfiles.Batch113.profile4536)⟩
theorem profilesValid682 : retention682.ProfilesValid := by
  exact MergedCutProfiles.Batch113.valid4536
theorem numericValid682 : retention682.NumericValid := by decide +kernel
def certificate682 : RatCutBinCertificate := ⟨⟨retention682,(2493425594114026477/1000000000000000000),(11965748524255287/125000000000000000),(3068906201132341919/250000000000000000),(29410909641871090571/100000000000000000),(13503406667756881/12500000000000000)⟩,(496158731657900961/500000000000000000),(369703634534909021/1000000000000000000),(131209068832545717/500000000000000000),(195509764508070619/1000000000000000000)⟩
theorem valid682 : certificate682.Valid := by decide +kernel
theorem sound682 : certificate682.Sound := rat_cut_bin_certificate_sound certificate682 profilesValid682 numericValid682 valid682

def retention683 : RatCutRetentionCertificate := ⟨(9/200),(181/4000),(11885793311448060432/23925557571886382669),(2663379611641347543/250000000000000000),(21/20),(260792167689653947112656308261639731/260095665199350345996093750000000000),false,MergedCutProfiles.Batch113.profile4537,(fun _ => MergedCutProfiles.Batch113.profile4537)⟩
theorem profilesValid683 : retention683.ProfilesValid := by
  exact MergedCutProfiles.Batch113.valid4537
theorem numericValid683 : retention683.NumericValid := by decide +kernel
def certificate683 : RatCutBinCertificate := ⟨⟨retention683,(2493425594114026477/1000000000000000000),(11965748524255287/125000000000000000),(3068906201132341919/250000000000000000),(29410909641871090571/100000000000000000),(491130607468660839/500000000000000000)⟩,(496158731657900961/500000000000000000),(40659315039665499/100000000000000000),(28436925726591561/125000000000000000),(1948256177668727/10000000000000000)⟩
theorem valid683 : certificate683.Valid := by decide +kernel
theorem sound683 : certificate683.Sound := rat_cut_bin_certificate_sound certificate683 profilesValid683 numericValid683 valid683

def certificates : List RatCutBinCertificate := [certificate672,certificate673,certificate674,certificate675,certificate676,certificate677,certificate678,certificate679,certificate680,certificate681,certificate682,certificate683]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound672,List.forall_mem_cons.mpr ⟨sound673,List.forall_mem_cons.mpr ⟨sound674,List.forall_mem_cons.mpr ⟨sound675,List.forall_mem_cons.mpr ⟨sound676,List.forall_mem_cons.mpr ⟨sound677,List.forall_mem_cons.mpr ⟨sound678,List.forall_mem_cons.mpr ⟨sound679,List.forall_mem_cons.mpr ⟨sound680,List.forall_mem_cons.mpr ⟨sound681,List.forall_mem_cons.mpr ⟨sound682,List.forall_mem_cons.mpr ⟨sound683,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch056
