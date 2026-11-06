import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch687
import Cycle12.MergedCutProfiles.Batch688

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch408

def retention4896 : RatCutRetentionCertificate := ⟨(89/2000),(9/200),(1/40),(7113994924954471057/125000000000000000),(21/20),(552037184012870493/250000000000000000),false,MergedCutProfiles.Batch687.profile27494,(fun _ => MergedCutProfiles.Batch687.profile27494)⟩
theorem profilesValid4896 : retention4896.ProfilesValid := by
  exact MergedCutProfiles.Batch687.valid27494
theorem numericValid4896 : retention4896.NumericValid := by decide +kernel
def certificate4896 : RatCutBinCertificate := ⟨⟨retention4896,(464424978036706361/250000000000000000),(11819389720817643/125000000000000000),(12179790867758249603/1000000000000000000),(14794134009094345190263/500000000000000000),(2193005799893368209/1000000000000000000)⟩,(499971502976635513/500000000000000000),(175191943225399149/250000000000000000),(50054114779934089/1000000000000000000),(20201123656928267/200000000000000000)⟩
theorem valid4896 : certificate4896.Valid := by decide +kernel
theorem sound4896 : certificate4896.Sound := rat_cut_bin_certificate_sound certificate4896 profilesValid4896 numericValid4896 valid4896

def retention4897 : RatCutRetentionCertificate := ⟨(9/200),(91/2000),(646734354540958963/2363048888244261850660),(73916872007611759/125000000000000000),4,(72341212519208883789/32000000000000000000),true,MergedCutProfiles.Batch687.profile27495,![MergedCutProfiles.Batch687.profile27495,MergedCutProfiles.Batch687.profile27496,MergedCutProfiles.Batch687.profile27497,MergedCutProfiles.Batch687.profile27498,MergedCutProfiles.Batch687.profile27499,MergedCutProfiles.Batch687.profile27500,MergedCutProfiles.Batch687.profile27501,MergedCutProfiles.Batch687.profile27502,MergedCutProfiles.Batch687.profile27503,MergedCutProfiles.Batch687.profile27504,MergedCutProfiles.Batch687.profile27505,MergedCutProfiles.Batch687.profile27506,MergedCutProfiles.Batch687.profile27507,MergedCutProfiles.Batch687.profile27508,MergedCutProfiles.Batch687.profile27509,MergedCutProfiles.Batch687.profile27510]⟩
theorem profilesValid4897 : retention4897.ProfilesValid := by
  change ∀ j : Fin 16, (retention4897.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch687.valid27495
  · exact MergedCutProfiles.Batch687.valid27496
  · exact MergedCutProfiles.Batch687.valid27497
  · exact MergedCutProfiles.Batch687.valid27498
  · exact MergedCutProfiles.Batch687.valid27499
  · exact MergedCutProfiles.Batch687.valid27500
  · exact MergedCutProfiles.Batch687.valid27501
  · exact MergedCutProfiles.Batch687.valid27502
  · exact MergedCutProfiles.Batch687.valid27503
  · exact MergedCutProfiles.Batch687.valid27504
  · exact MergedCutProfiles.Batch687.valid27505
  · exact MergedCutProfiles.Batch687.valid27506
  · exact MergedCutProfiles.Batch687.valid27507
  · exact MergedCutProfiles.Batch687.valid27508
  · exact MergedCutProfiles.Batch687.valid27509
  · exact MergedCutProfiles.Batch687.valid27510
theorem numericValid4897 : retention4897.NumericValid := by decide +kernel
def certificate4897 : RatCutBinCertificate := ⟨⟨retention4897,(476184619775959579/250000000000000000),(969058462737911/10000000000000000),(3069341678819371209/250000000000000000),(14546364203705432194003/500000000000000000),(2200526036650864153/1000000000000000000)⟩,(99994071898781603/100000000000000000),(35115620886065133/50000000000000000),(24753286529937067/500000000000000000),(22094429548717293/1000000000000000000)⟩
theorem valid4897 : certificate4897.Valid := by decide +kernel
theorem sound4897 : certificate4897.Sound := rat_cut_bin_certificate_sound certificate4897 profilesValid4897 numericValid4897 valid4897

def retention4898 : RatCutRetentionCertificate := ⟨(9/200),(91/2000),(56129066200000000/118152444412213092533),(646734354540958963/1000000000000000000),4,(150279787538050139363/64000000000000000000),true,MergedCutProfiles.Batch687.profile27496,![MergedCutProfiles.Batch687.profile27496,MergedCutProfiles.Batch687.profile27511,MergedCutProfiles.Batch687.profile27512,MergedCutProfiles.Batch687.profile27501,MergedCutProfiles.Batch687.profile27513,MergedCutProfiles.Batch687.profile27514,MergedCutProfiles.Batch687.profile27506,MergedCutProfiles.Batch687.profile27508,MergedCutProfiles.Batch687.profile27510,MergedCutProfiles.Batch687.profile27515,MergedCutProfiles.Batch687.profile27516,MergedCutProfiles.Batch687.profile27517,MergedCutProfiles.Batch687.profile27518,MergedCutProfiles.Batch687.profile27519,MergedCutProfiles.Batch688.profile27520,MergedCutProfiles.Batch688.profile27521]⟩
theorem profilesValid4898 : retention4898.ProfilesValid := by
  change ∀ j : Fin 16, (retention4898.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch687.valid27496
  · exact MergedCutProfiles.Batch687.valid27511
  · exact MergedCutProfiles.Batch687.valid27512
  · exact MergedCutProfiles.Batch687.valid27501
  · exact MergedCutProfiles.Batch687.valid27513
  · exact MergedCutProfiles.Batch687.valid27514
  · exact MergedCutProfiles.Batch687.valid27506
  · exact MergedCutProfiles.Batch687.valid27508
  · exact MergedCutProfiles.Batch687.valid27510
  · exact MergedCutProfiles.Batch687.valid27515
  · exact MergedCutProfiles.Batch687.valid27516
  · exact MergedCutProfiles.Batch687.valid27517
  · exact MergedCutProfiles.Batch687.valid27518
  · exact MergedCutProfiles.Batch687.valid27519
  · exact MergedCutProfiles.Batch688.valid27520
  · exact MergedCutProfiles.Batch688.valid27521
theorem numericValid4898 : retention4898.NumericValid := by decide +kernel
def certificate4898 : RatCutBinCertificate := ⟨⟨retention4898,(476184619775959579/250000000000000000),(969058462737911/10000000000000000),(3069341678819371209/250000000000000000),(14546364203705432194003/500000000000000000),(228798483296184503/100000000000000000)⟩,(99994071898781603/100000000000000000),(636945786130524801/1000000000000000000),(37873304845425447/500000000000000000),(1419158269378861/40000000000000000)⟩
theorem valid4898 : certificate4898.Valid := by decide +kernel
theorem sound4898 : certificate4898.Sound := rat_cut_bin_certificate_sound certificate4898 profilesValid4898 numericValid4898 valid4898

def retention4899 : RatCutRetentionCertificate := ⟨(9/200),(91/2000),(2381364618922000801/2363048888244261850660),(280645331/250000000),(14/5),(429560125044846707941765582381515519/179613011840000000000000000000000000),true,MergedCutProfiles.Batch687.profile27498,![MergedCutProfiles.Batch687.profile27498,MergedCutProfiles.Batch687.profile27501,MergedCutProfiles.Batch687.profile27505,MergedCutProfiles.Batch687.profile27509,MergedCutProfiles.Batch688.profile27522,MergedCutProfiles.Batch688.profile27523,MergedCutProfiles.Batch688.profile27520,MergedCutProfiles.Batch688.profile27524,MergedCutProfiles.Batch688.profile27525,MergedCutProfiles.Batch688.profile27526,MergedCutProfiles.Batch688.profile27527,MergedCutProfiles.Batch688.profile27528,MergedCutProfiles.Batch688.profile27529,MergedCutProfiles.Batch688.profile27530,MergedCutProfiles.Batch688.profile27531,MergedCutProfiles.Batch688.profile27532]⟩
theorem profilesValid4899 : retention4899.ProfilesValid := by
  change ∀ j : Fin 16, (retention4899.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch687.valid27498
  · exact MergedCutProfiles.Batch687.valid27501
  · exact MergedCutProfiles.Batch687.valid27505
  · exact MergedCutProfiles.Batch687.valid27509
  · exact MergedCutProfiles.Batch688.valid27522
  · exact MergedCutProfiles.Batch688.valid27523
  · exact MergedCutProfiles.Batch688.valid27520
  · exact MergedCutProfiles.Batch688.valid27524
  · exact MergedCutProfiles.Batch688.valid27525
  · exact MergedCutProfiles.Batch688.valid27526
  · exact MergedCutProfiles.Batch688.valid27527
  · exact MergedCutProfiles.Batch688.valid27528
  · exact MergedCutProfiles.Batch688.valid27529
  · exact MergedCutProfiles.Batch688.valid27530
  · exact MergedCutProfiles.Batch688.valid27531
  · exact MergedCutProfiles.Batch688.valid27532
theorem numericValid4899 : retention4899.NumericValid := by decide +kernel
def certificate4899 : RatCutBinCertificate := ⟨⟨retention4899,(476184619775959579/250000000000000000),(969058462737911/10000000000000000),(3069341678819371209/250000000000000000),(14546364203705432194003/500000000000000000),(146843194382170549/62500000000000000)⟩,(99994071898781603/100000000000000000),(450544783244961223/1000000000000000000),(95118289347746317/500000000000000000),(2519697209288027/20000000000000000)⟩
theorem valid4899 : certificate4899.Valid := by decide +kernel
theorem sound4899 : certificate4899.Sound := rat_cut_bin_certificate_sound certificate4899 profilesValid4899 numericValid4899 valid4899

def retention4900 : RatCutRetentionCertificate := ⟨(9/200),(91/2000),(3200000000000000000/118152444412213092533),(2381364618922000801/1000000000000000000),(17/10),(2781183707242575836461/1280000000000000000000),true,MergedCutProfiles.Batch688.profile27533,![MergedCutProfiles.Batch688.profile27533,MergedCutProfiles.Batch688.profile27534,MergedCutProfiles.Batch688.profile27535,MergedCutProfiles.Batch688.profile27536,MergedCutProfiles.Batch688.profile27537,MergedCutProfiles.Batch688.profile27538,MergedCutProfiles.Batch688.profile27539,MergedCutProfiles.Batch688.profile27540,MergedCutProfiles.Batch688.profile27541,MergedCutProfiles.Batch688.profile27542,MergedCutProfiles.Batch688.profile27543,MergedCutProfiles.Batch688.profile27544,MergedCutProfiles.Batch688.profile27545,MergedCutProfiles.Batch688.profile27546,MergedCutProfiles.Batch688.profile27547,MergedCutProfiles.Batch688.profile27548]⟩
theorem profilesValid4900 : retention4900.ProfilesValid := by
  change ∀ j : Fin 16, (retention4900.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch688.valid27533
  · exact MergedCutProfiles.Batch688.valid27534
  · exact MergedCutProfiles.Batch688.valid27535
  · exact MergedCutProfiles.Batch688.valid27536
  · exact MergedCutProfiles.Batch688.valid27537
  · exact MergedCutProfiles.Batch688.valid27538
  · exact MergedCutProfiles.Batch688.valid27539
  · exact MergedCutProfiles.Batch688.valid27540
  · exact MergedCutProfiles.Batch688.valid27541
  · exact MergedCutProfiles.Batch688.valid27542
  · exact MergedCutProfiles.Batch688.valid27543
  · exact MergedCutProfiles.Batch688.valid27544
  · exact MergedCutProfiles.Batch688.valid27545
  · exact MergedCutProfiles.Batch688.valid27546
  · exact MergedCutProfiles.Batch688.valid27547
  · exact MergedCutProfiles.Batch688.valid27548
theorem numericValid4900 : retention4900.NumericValid := by decide +kernel
def certificate4900 : RatCutBinCertificate := ⟨⟨retention4900,(476184619775959579/250000000000000000),(969058462737911/10000000000000000),(3069341678819371209/250000000000000000),(14546364203705432194003/500000000000000000),(2147241623051669537/1000000000000000000)⟩,(99994071898781603/100000000000000000),(359559989320917077/1000000000000000000),(272650931915737559/1000000000000000000),(262467602076882147/1000000000000000000)⟩
theorem valid4900 : certificate4900.Valid := by decide +kernel
theorem sound4900 : certificate4900.Sound := rat_cut_bin_certificate_sound certificate4900 profilesValid4900 numericValid4900 valid4900

def retention4901 : RatCutRetentionCertificate := ⟨(9/200),(91/2000),(1/2),64,1,(63847246665200033710903103172835453839/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch688.profile27549,(fun _ => MergedCutProfiles.Batch688.profile27549)⟩
theorem profilesValid4901 : retention4901.ProfilesValid := by
  exact MergedCutProfiles.Batch688.valid27549
theorem numericValid4901 : retention4901.NumericValid := by decide +kernel
def certificate4901 : RatCutBinCertificate := ⟨⟨retention4901,(476184619775959579/250000000000000000),(969058462737911/10000000000000000),(3069341678819371209/250000000000000000),(14546364203705432194003/500000000000000000),(15352797435768789/15625000000000000)⟩,(99994071898781603/100000000000000000),(535405618777208743/1000000000000000000),(32527516353123317/250000000000000000),(62951404719506511/500000000000000000)⟩
theorem valid4901 : certificate4901.Valid := by decide +kernel
theorem sound4901 : certificate4901.Sound := rat_cut_bin_certificate_sound certificate4901 profilesValid4901 numericValid4901 valid4901

def retention4902 : RatCutRetentionCertificate := ⟨(9/200),(91/2000),(3200000000000000000/118152444412213092533),(33687493866515866229/1000000000000000000),1,(58254976876628029170881476090138489767/26949995093212692983200000000000000000),false,MergedCutProfiles.Batch688.profile27550,(fun _ => MergedCutProfiles.Batch688.profile27550)⟩
theorem profilesValid4902 : retention4902.ProfilesValid := by
  exact MergedCutProfiles.Batch688.valid27550
theorem numericValid4902 : retention4902.NumericValid := by decide +kernel
def certificate4902 : RatCutBinCertificate := ⟨⟨retention4902,(436901711775959579/250000000000000000),(969058462737911/10000000000000000),(3069341678819371209/250000000000000000),(14546364203705432194003/500000000000000000),(536950284139505927/250000000000000000)⟩,(999945609409888057/1000000000000000000),(19506656318415467/1000000000000000000),(175100335800352987/200000000000000000),(441900710801140407/250000000000000000)⟩
theorem valid4902 : certificate4902.Valid := by decide +kernel
theorem sound4902 : certificate4902.Sound := rat_cut_bin_certificate_sound certificate4902 profilesValid4902 numericValid4902 valid4902

def retention4903 : RatCutRetentionCertificate := ⟨(9/200),(91/2000),(1/2),64,1,(63847246665200033710903103172835453839/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch688.profile27549,(fun _ => MergedCutProfiles.Batch688.profile27549)⟩
theorem profilesValid4903 : retention4903.ProfilesValid := by
  exact MergedCutProfiles.Batch688.valid27549
theorem numericValid4903 : retention4903.NumericValid := by decide +kernel
def certificate4903 : RatCutBinCertificate := ⟨⟨retention4903,(436901711775959579/250000000000000000),(969058462737911/10000000000000000),(3069341678819371209/250000000000000000),(14546364203705432194003/500000000000000000),(15372176304474117/15625000000000000)⟩,(999945609409888057/1000000000000000000),(8517096445329243/200000000000000000),(50534827119913299/62500000000000000),(783388090839514281/1000000000000000000)⟩
theorem valid4903 : certificate4903.Valid := by decide +kernel
theorem sound4903 : certificate4903.Sound := rat_cut_bin_certificate_sound certificate4903 profilesValid4903 numericValid4903 valid4903

def retention4904 : RatCutRetentionCertificate := ⟨(9/200),(91/2000),(702083650175313857/2363048888244261850660),(695132326906251343/1000000000000000000),4,(6678431866143408686166176686341702183/2780529307625005372000000000000000000),false,MergedCutProfiles.Batch688.profile27551,(fun _ => MergedCutProfiles.Batch688.profile27551)⟩
theorem profilesValid4904 : retention4904.ProfilesValid := by
  exact MergedCutProfiles.Batch688.valid27551
theorem numericValid4904 : retention4904.NumericValid := by decide +kernel
def certificate4904 : RatCutBinCertificate := ⟨⟨retention4904,(465453011275959579/250000000000000000),(969058462737911/10000000000000000),(3069341678819371209/250000000000000000),(14546364203705432194003/500000000000000000),(2343074752584394381/1000000000000000000)⟩,(499971027495810487/500000000000000000),(432297815021213617/500000000000000000),(2402861443481739/250000000000000000),(4650072897647883/1000000000000000000)⟩
theorem valid4904 : certificate4904.Valid := by decide +kernel
theorem sound4904 : certificate4904.Sound := rat_cut_bin_certificate_sound certificate4904 profilesValid4904 numericValid4904 valid4904

def retention4905 : RatCutRetentionCertificate := ⟨(9/200),(91/2000),(436947327122515313/1181524444122130925330),(702083650175313857/1000000000000000000),4,(337712790613325083079669357970146391/140416730035062771400000000000000000),false,MergedCutProfiles.Batch688.profile27552,(fun _ => MergedCutProfiles.Batch688.profile27552)⟩
theorem profilesValid4905 : retention4905.ProfilesValid := by
  exact MergedCutProfiles.Batch688.valid27552
theorem numericValid4905 : retention4905.NumericValid := by decide +kernel
def certificate4905 : RatCutBinCertificate := ⟨⟨retention4905,(465453011275959579/250000000000000000),(969058462737911/10000000000000000),(3069341678819371209/250000000000000000),(14546364203705432194003/500000000000000000),(586573402568070603/250000000000000000)⟩,(499971027495810487/500000000000000000),(430654445410184083/500000000000000000),(10095899671161437/1000000000000000000),(979689017669807/200000000000000000)⟩
theorem valid4905 : certificate4905.Valid := by decide +kernel
theorem sound4905 : certificate4905.Sound := rat_cut_bin_certificate_sound certificate4905 profilesValid4905 numericValid4905 valid4905

def retention4906 : RatCutRetentionCertificate := ⟨(9/200),(91/2000),(1106071031099092727/590762222061065462665),(436947327122515313/500000000000000000),(73/20),(840261324296429428950389225577183617479/349557861698012250400000000000000000000),false,MergedCutProfiles.Batch688.profile27553,(fun _ => MergedCutProfiles.Batch688.profile27553)⟩
theorem profilesValid4906 : retention4906.ProfilesValid := by
  exact MergedCutProfiles.Batch688.valid27553
theorem numericValid4906 : retention4906.NumericValid := by decide +kernel
def certificate4906 : RatCutBinCertificate := ⟨⟨retention4906,(465453011275959579/250000000000000000),(969058462737911/10000000000000000),(3069341678819371209/250000000000000000),(14546364203705432194003/500000000000000000),(293768132684034481/125000000000000000)⟩,(499971027495810487/500000000000000000),(818666281197717027/1000000000000000000),(4383998305248973/250000000000000000),(9393964710201963/1000000000000000000)⟩
theorem valid4906 : certificate4906.Valid := by decide +kernel
theorem sound4906 : certificate4906.Sound := rat_cut_bin_certificate_sound certificate4906 profilesValid4906 numericValid4906 valid4906

def retention4907 : RatCutRetentionCertificate := ⟨(9/200),(91/2000),(13987282053713070283/590762222061065462665),(1106071031099092727/250000000000000000),(29/20),(979297620496417115286845743966086450231/442428412439637090800000000000000000000),false,MergedCutProfiles.Batch688.profile27554,(fun _ => MergedCutProfiles.Batch688.profile27554)⟩
theorem profilesValid4907 : retention4907.ProfilesValid := by
  exact MergedCutProfiles.Batch688.valid27554
theorem numericValid4907 : retention4907.NumericValid := by decide +kernel
def certificate4907 : RatCutBinCertificate := ⟨⟨retention4907,(465453011275959579/250000000000000000),(969058462737911/10000000000000000),(3069341678819371209/250000000000000000),(14546364203705432194003/500000000000000000),(438430351957753331/200000000000000000)⟩,(499971027495810487/500000000000000000),(732718911392263541/1000000000000000000),(1231579459503179/31250000000000000),(2410780785531171/50000000000000000)⟩
theorem valid4907 : certificate4907.Valid := by decide +kernel
theorem sound4907 : certificate4907.Sound := rat_cut_bin_certificate_sound certificate4907 profilesValid4907 numericValid4907 valid4907

def certificates : List RatCutBinCertificate := [certificate4896,certificate4897,certificate4898,certificate4899,certificate4900,certificate4901,certificate4902,certificate4903,certificate4904,certificate4905,certificate4906,certificate4907]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4896,List.forall_mem_cons.mpr ⟨sound4897,List.forall_mem_cons.mpr ⟨sound4898,List.forall_mem_cons.mpr ⟨sound4899,List.forall_mem_cons.mpr ⟨sound4900,List.forall_mem_cons.mpr ⟨sound4901,List.forall_mem_cons.mpr ⟨sound4902,List.forall_mem_cons.mpr ⟨sound4903,List.forall_mem_cons.mpr ⟨sound4904,List.forall_mem_cons.mpr ⟨sound4905,List.forall_mem_cons.mpr ⟨sound4906,List.forall_mem_cons.mpr ⟨sound4907,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch408
