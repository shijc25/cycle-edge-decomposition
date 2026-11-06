import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch424
import Cycle12.MergedCutProfiles.Batch425
import Cycle12.MergedCutProfiles.Batch427
import Cycle12.MergedCutProfiles.Batch548
import Cycle12.MergedCutProfiles.Batch549

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch297

def retention3564 : RatCutRetentionCertificate := ⟨(8/125),(129/2000),(24184068779292358703/52537530222601784183),(2191236493344520453/250000000000000000),1,(36751690337862626291811803495430877287/35059783893512327248000000000000000000),false,MergedCutProfiles.Batch548.profile21925,(fun _ => MergedCutProfiles.Batch548.profile21925)⟩
theorem profilesValid3564 : retention3564.ProfilesValid := by
  exact MergedCutProfiles.Batch548.valid21925
theorem numericValid3564 : retention3564.NumericValid := by decide +kernel
def certificate3564 : RatCutBinCertificate := ⟨⟨retention3564,(2320902243367216253/1000000000000000000),(216862197802423917/1000000000000000000),(17097254971987718171/1000000000000000000),(450540175640321153547/500000000000000000),(50940926927395239/50000000000000000)⟩,(997971354724969089/1000000000000000000),(29347173225023987/250000000000000000),(157231880983022199/250000000000000000),(57279435183241907/100000000000000000)⟩
theorem valid3564 : certificate3564.Valid := by decide +kernel
theorem sound3564 : certificate3564.Sound := rat_cut_bin_certificate_sound certificate3564 profilesValid3564 numericValid3564 valid3564

def retention3565 : RatCutRetentionCertificate := ⟨(8/125),(129/2000),(26187881047027428119/52537530222601784183),(24184068779292358703/1000000000000000000),1,(24045787893088095272228539671023499153/24184068779292358703000000000000000000),false,MergedCutProfiles.Batch548.profile21926,(fun _ => MergedCutProfiles.Batch548.profile21926)⟩
theorem profilesValid3565 : retention3565.ProfilesValid := by
  exact MergedCutProfiles.Batch548.valid21926
theorem numericValid3565 : retention3565.NumericValid := by decide +kernel
def certificate3565 : RatCutBinCertificate := ⟨⟨retention3565,(2320902243367216253/1000000000000000000),(216862197802423917/1000000000000000000),(17097254971987718171/1000000000000000000),(450540175640321153547/500000000000000000),(482421724524845943/500000000000000000)⟩,(997971354724969089/1000000000000000000),(1549445361580687/12500000000000000),(615363792256700881/1000000000000000000),(8902535172775839/15625000000000000)⟩
theorem valid3565 : certificate3565.Valid := by decide +kernel
theorem sound3565 : certificate3565.Sound := rat_cut_bin_certificate_sound certificate3565 profilesValid3565 numericValid3565 valid3565

def retention3566 : RatCutRetentionCertificate := ⟨(8/125),(129/2000),(1/2),(26187881047027428119/1000000000000000000),1,(1039192598100476927691932529024573717/1047515241881097124760000000000000000),false,MergedCutProfiles.Batch424.profile16984,(fun _ => MergedCutProfiles.Batch424.profile16984)⟩
theorem profilesValid3566 : retention3566.ProfilesValid := by
  exact MergedCutProfiles.Batch424.valid16984
theorem numericValid3566 : retention3566.NumericValid := by decide +kernel
def certificate3566 : RatCutBinCertificate := ⟨⟨retention3566,(2320902243367216253/1000000000000000000),(216862197802423917/1000000000000000000),(17097254971987718171/1000000000000000000),(450540175640321153547/500000000000000000),(240654048191712569/250000000000000000)⟩,(997971354724969089/1000000000000000000),(62121215828898719/500000000000000000),(614778330430190103/1000000000000000000),(284813603696271513/500000000000000000)⟩
theorem valid3566 : certificate3566.Valid := by decide +kernel
theorem sound3566 : certificate3566.Sound := rat_cut_bin_certificate_sound certificate3566 profilesValid3566 numericValid3566 valid3566

def retention3567 : RatCutRetentionCertificate := ⟨(129/2000),(13/200),(72180151267396059/3966859336519937512),(929051451956582937/1000000000000000000),(14/5),(564720877070152837457/256000000000000000000),true,MergedCutProfiles.Batch548.profile21927,![MergedCutProfiles.Batch548.profile21927,MergedCutProfiles.Batch548.profile21928,MergedCutProfiles.Batch548.profile21929,MergedCutProfiles.Batch548.profile21930,MergedCutProfiles.Batch548.profile21931,MergedCutProfiles.Batch548.profile21932,MergedCutProfiles.Batch548.profile21933,MergedCutProfiles.Batch548.profile21934,MergedCutProfiles.Batch548.profile21935,MergedCutProfiles.Batch548.profile21936,MergedCutProfiles.Batch548.profile21937,MergedCutProfiles.Batch548.profile21938,MergedCutProfiles.Batch548.profile21939,MergedCutProfiles.Batch548.profile21940,MergedCutProfiles.Batch548.profile21941,MergedCutProfiles.Batch548.profile21942]⟩
theorem profilesValid3567 : retention3567.ProfilesValid := by
  change ∀ j : Fin 16, (retention3567.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch548.valid21927
  · exact MergedCutProfiles.Batch548.valid21928
  · exact MergedCutProfiles.Batch548.valid21929
  · exact MergedCutProfiles.Batch548.valid21930
  · exact MergedCutProfiles.Batch548.valid21931
  · exact MergedCutProfiles.Batch548.valid21932
  · exact MergedCutProfiles.Batch548.valid21933
  · exact MergedCutProfiles.Batch548.valid21934
  · exact MergedCutProfiles.Batch548.valid21935
  · exact MergedCutProfiles.Batch548.valid21936
  · exact MergedCutProfiles.Batch548.valid21937
  · exact MergedCutProfiles.Batch548.valid21938
  · exact MergedCutProfiles.Batch548.valid21939
  · exact MergedCutProfiles.Batch548.valid21940
  · exact MergedCutProfiles.Batch548.valid21941
  · exact MergedCutProfiles.Batch548.valid21942
theorem numericValid3567 : retention3567.NumericValid := by decide +kernel
def certificate3567 : RatCutBinCertificate := ⟨⟨retention3567,(1137156209224245929/500000000000000000),(55239130418189853/250000000000000000),(17261006915229141307/1000000000000000000),(446476391738544410619/500000000000000000),(265552005924869133/125000000000000000)⟩,(249501066843276023/250000000000000000),(293934151247103009/1000000000000000000),(173072983942564013/500000000000000000),(202836670063679399/1000000000000000000)⟩
theorem valid3567 : certificate3567.Valid := by decide +kernel
theorem sound3567 : certificate3567.Sound := rat_cut_bin_certificate_sound certificate3567 profilesValid3567 numericValid3567 valid3567

def retention3568 : RatCutRetentionCertificate := ⟨(129/2000),(13/200),(550139875762820537/25784585687379593828),(938341966476148767/1000000000000000000),(14/5),(175879302492904183227/80000000000000000000),true,MergedCutProfiles.Batch548.profile21943,![MergedCutProfiles.Batch548.profile21943,MergedCutProfiles.Batch548.profile21944,MergedCutProfiles.Batch548.profile21945,MergedCutProfiles.Batch548.profile21946,MergedCutProfiles.Batch548.profile21947,MergedCutProfiles.Batch548.profile21948,MergedCutProfiles.Batch548.profile21949,MergedCutProfiles.Batch548.profile21950,MergedCutProfiles.Batch548.profile21951,MergedCutProfiles.Batch548.profile21952,MergedCutProfiles.Batch548.profile21953,MergedCutProfiles.Batch548.profile21954,MergedCutProfiles.Batch548.profile21955,MergedCutProfiles.Batch548.profile21956,MergedCutProfiles.Batch548.profile21957,MergedCutProfiles.Batch548.profile21958]⟩
theorem profilesValid3568 : retention3568.ProfilesValid := by
  change ∀ j : Fin 16, (retention3568.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch548.valid21943
  · exact MergedCutProfiles.Batch548.valid21944
  · exact MergedCutProfiles.Batch548.valid21945
  · exact MergedCutProfiles.Batch548.valid21946
  · exact MergedCutProfiles.Batch548.valid21947
  · exact MergedCutProfiles.Batch548.valid21948
  · exact MergedCutProfiles.Batch548.valid21949
  · exact MergedCutProfiles.Batch548.valid21950
  · exact MergedCutProfiles.Batch548.valid21951
  · exact MergedCutProfiles.Batch548.valid21952
  · exact MergedCutProfiles.Batch548.valid21953
  · exact MergedCutProfiles.Batch548.valid21954
  · exact MergedCutProfiles.Batch548.valid21955
  · exact MergedCutProfiles.Batch548.valid21956
  · exact MergedCutProfiles.Batch548.valid21957
  · exact MergedCutProfiles.Batch548.valid21958
theorem numericValid3568 : retention3568.NumericValid := by decide +kernel
def certificate3568 : RatCutBinCertificate := ⟨⟨retention3568,(1137156209224245929/500000000000000000),(55239130418189853/250000000000000000),(17261006915229141307/1000000000000000000),(446476391738544410619/500000000000000000),(423393295855576427/200000000000000000)⟩,(249501066843276023/250000000000000000),(293679096231191823/1000000000000000000),(43307272971643241/125000000000000000),(202921031125497987/1000000000000000000)⟩
theorem valid3568 : certificate3568.Valid := by decide +kernel
theorem sound3568 : certificate3568.Sound := rat_cut_bin_certificate_sound certificate3568 profilesValid3568 numericValid3568 valid3568

def retention3569 : RatCutRetentionCertificate := ⟨(129/2000),(13/200),(137961469250000000/6446146421844898457),(550139875762820537/500000000000000000),(49/20),(10922732194812937471/5000000000000000000),true,MergedCutProfiles.Batch548.profile21943,![MergedCutProfiles.Batch548.profile21943,MergedCutProfiles.Batch548.profile21944,MergedCutProfiles.Batch548.profile21945,MergedCutProfiles.Batch548.profile21946,MergedCutProfiles.Batch548.profile21947,MergedCutProfiles.Batch548.profile21948,MergedCutProfiles.Batch548.profile21959,MergedCutProfiles.Batch548.profile21950,MergedCutProfiles.Batch548.profile21951,MergedCutProfiles.Batch548.profile21952,MergedCutProfiles.Batch548.profile21953,MergedCutProfiles.Batch548.profile21954,MergedCutProfiles.Batch549.profile21960,MergedCutProfiles.Batch549.profile21961,MergedCutProfiles.Batch424.profile16993,MergedCutProfiles.Batch548.profile21958]⟩
theorem profilesValid3569 : retention3569.ProfilesValid := by
  change ∀ j : Fin 16, (retention3569.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch548.valid21943
  · exact MergedCutProfiles.Batch548.valid21944
  · exact MergedCutProfiles.Batch548.valid21945
  · exact MergedCutProfiles.Batch548.valid21946
  · exact MergedCutProfiles.Batch548.valid21947
  · exact MergedCutProfiles.Batch548.valid21948
  · exact MergedCutProfiles.Batch548.valid21959
  · exact MergedCutProfiles.Batch548.valid21950
  · exact MergedCutProfiles.Batch548.valid21951
  · exact MergedCutProfiles.Batch548.valid21952
  · exact MergedCutProfiles.Batch548.valid21953
  · exact MergedCutProfiles.Batch548.valid21954
  · exact MergedCutProfiles.Batch549.valid21960
  · exact MergedCutProfiles.Batch549.valid21961
  · exact MergedCutProfiles.Batch424.valid16993
  · exact MergedCutProfiles.Batch548.valid21958
theorem numericValid3569 : retention3569.NumericValid := by decide +kernel
def certificate3569 : RatCutBinCertificate := ⟨⟨retention3569,(1137156209224245929/500000000000000000),(55239130418189853/250000000000000000),(17261006915229141307/1000000000000000000),(446476391738544410619/500000000000000000),(2113212407587221801/1000000000000000000)⟩,(249501066843276023/250000000000000000),(27518980967947229/100000000000000000),(369690055702911481/1000000000000000000),(60249908695932961/250000000000000000)⟩
theorem valid3569 : certificate3569.Valid := by decide +kernel
theorem sound3569 : certificate3569.Sound := rat_cut_bin_certificate_sound certificate3569 profilesValid3569 numericValid3569 valid3569

def retention3570 : RatCutRetentionCertificate := ⟨(129/2000),(13/200),(1203359760076401619/51569171374759187656),(551845877/500000000),(49/20),(4357370834088462433/2000000000000000000),true,MergedCutProfiles.Batch549.profile21962,![MergedCutProfiles.Batch549.profile21962,MergedCutProfiles.Batch549.profile21963,MergedCutProfiles.Batch549.profile21964,MergedCutProfiles.Batch549.profile21965,MergedCutProfiles.Batch549.profile21966,MergedCutProfiles.Batch549.profile21967,MergedCutProfiles.Batch549.profile21968,MergedCutProfiles.Batch549.profile21969,MergedCutProfiles.Batch549.profile21970,MergedCutProfiles.Batch549.profile21971,MergedCutProfiles.Batch548.profile21954,MergedCutProfiles.Batch549.profile21960,MergedCutProfiles.Batch425.profile17036,MergedCutProfiles.Batch549.profile21972,MergedCutProfiles.Batch549.profile21973,MergedCutProfiles.Batch549.profile21974]⟩
theorem profilesValid3570 : retention3570.ProfilesValid := by
  change ∀ j : Fin 16, (retention3570.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch549.valid21962
  · exact MergedCutProfiles.Batch549.valid21963
  · exact MergedCutProfiles.Batch549.valid21964
  · exact MergedCutProfiles.Batch549.valid21965
  · exact MergedCutProfiles.Batch549.valid21966
  · exact MergedCutProfiles.Batch549.valid21967
  · exact MergedCutProfiles.Batch549.valid21968
  · exact MergedCutProfiles.Batch549.valid21969
  · exact MergedCutProfiles.Batch549.valid21970
  · exact MergedCutProfiles.Batch549.valid21971
  · exact MergedCutProfiles.Batch548.valid21954
  · exact MergedCutProfiles.Batch549.valid21960
  · exact MergedCutProfiles.Batch425.valid17036
  · exact MergedCutProfiles.Batch549.valid21972
  · exact MergedCutProfiles.Batch549.valid21973
  · exact MergedCutProfiles.Batch549.valid21974
theorem numericValid3570 : retention3570.NumericValid := by decide +kernel
def certificate3570 : RatCutBinCertificate := ⟨⟨retention3570,(1137156209224245929/500000000000000000),(55239130418189853/250000000000000000),(17261006915229141307/1000000000000000000),(446476391738544410619/500000000000000000),(1053675702954830321/500000000000000000)⟩,(249501066843276023/250000000000000000),(275613676250538441/1000000000000000000),(369143957078252871/1000000000000000000),(24031752392271873/100000000000000000)⟩
theorem valid3570 : certificate3570.Valid := by decide +kernel
theorem sound3570 : certificate3570.Sound := rat_cut_bin_certificate_sound certificate3570 profilesValid3570 numericValid3570 valid3570

def retention3571 : RatCutRetentionCertificate := ⟨(129/2000),(13/200),(343541748493959393/6446146421844898457),(1203359760076401619/1000000000000000000),(9/4),(526712100432335954031/256000000000000000000),true,MergedCutProfiles.Batch549.profile21975,![MergedCutProfiles.Batch549.profile21975,MergedCutProfiles.Batch548.profile21947,MergedCutProfiles.Batch549.profile21976,MergedCutProfiles.Batch548.profile21952,MergedCutProfiles.Batch549.profile21977,MergedCutProfiles.Batch548.profile21957,MergedCutProfiles.Batch549.profile21974,MergedCutProfiles.Batch549.profile21978,MergedCutProfiles.Batch549.profile21979,MergedCutProfiles.Batch549.profile21980,MergedCutProfiles.Batch549.profile21981,MergedCutProfiles.Batch549.profile21982,MergedCutProfiles.Batch549.profile21983,MergedCutProfiles.Batch549.profile21984,MergedCutProfiles.Batch549.profile21985,MergedCutProfiles.Batch549.profile21986]⟩
theorem profilesValid3571 : retention3571.ProfilesValid := by
  change ∀ j : Fin 16, (retention3571.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch549.valid21975
  · exact MergedCutProfiles.Batch548.valid21947
  · exact MergedCutProfiles.Batch549.valid21976
  · exact MergedCutProfiles.Batch548.valid21952
  · exact MergedCutProfiles.Batch549.valid21977
  · exact MergedCutProfiles.Batch548.valid21957
  · exact MergedCutProfiles.Batch549.valid21974
  · exact MergedCutProfiles.Batch549.valid21978
  · exact MergedCutProfiles.Batch549.valid21979
  · exact MergedCutProfiles.Batch549.valid21980
  · exact MergedCutProfiles.Batch549.valid21981
  · exact MergedCutProfiles.Batch549.valid21982
  · exact MergedCutProfiles.Batch549.valid21983
  · exact MergedCutProfiles.Batch549.valid21984
  · exact MergedCutProfiles.Batch549.valid21985
  · exact MergedCutProfiles.Batch549.valid21986
theorem numericValid3571 : retention3571.NumericValid := by decide +kernel
def certificate3571 : RatCutBinCertificate := ⟨⟨retention3571,(1137156209224245929/500000000000000000),(55239130418189853/250000000000000000),(17261006915229141307/1000000000000000000),(446476391738544410619/500000000000000000),(15562174402678123/7812500000000000)⟩,(249501066843276023/250000000000000000),(281930515572863591/1000000000000000000),(1444326491679931/4000000000000000),(240328889698001017/1000000000000000000)⟩
theorem valid3571 : certificate3571.Valid := by decide +kernel
theorem sound3571 : certificate3571.Sound := rat_cut_bin_certificate_sound certificate3571 profilesValid3571 numericValid3571 valid3571

def retention3572 : RatCutRetentionCertificate := ⟨(129/2000),(13/200),(15678695320117327207/51569171374759187656),(343541748493959393/125000000000000000),(7/5),(7867477020703783707107979235116211919/5608844873370765600000000000000000000),false,MergedCutProfiles.Batch549.profile21987,(fun _ => MergedCutProfiles.Batch549.profile21987)⟩
theorem profilesValid3572 : retention3572.ProfilesValid := by
  exact MergedCutProfiles.Batch549.valid21987
theorem numericValid3572 : retention3572.NumericValid := by decide +kernel
def certificate3572 : RatCutBinCertificate := ⟨⟨retention3572,(1137156209224245929/500000000000000000),(55239130418189853/250000000000000000),(17261006915229141307/1000000000000000000),(446476391738544410619/500000000000000000),(68096497925121753/50000000000000000)⟩,(249501066843276023/250000000000000000),(40562081002120921/125000000000000000),(31027699941981827/100000000000000000),(6009427397460141/25000000000000000)⟩
theorem valid3572 : certificate3572.Valid := by decide +kernel
theorem sound3572 : certificate3572.Sound := rat_cut_bin_certificate_sound certificate3572 profilesValid3572 numericValid3572 valid3572

def retention3573 : RatCutRetentionCertificate := ⟨(129/2000),(13/200),(6256832044339398147/12892292843689796914),(15678695320117327207/1000000000000000000),1,(15900793644401995723992979383650017249/15678695320117327207000000000000000000),false,MergedCutProfiles.Batch549.profile21988,(fun _ => MergedCutProfiles.Batch549.profile21988)⟩
theorem profilesValid3573 : retention3573.ProfilesValid := by
  exact MergedCutProfiles.Batch549.valid21988
theorem numericValid3573 : retention3573.NumericValid := by decide +kernel
def certificate3573 : RatCutBinCertificate := ⟨⟨retention3573,(1137156209224245929/500000000000000000),(55239130418189853/250000000000000000),(17261006915229141307/1000000000000000000),(446476391738544410619/500000000000000000),(492525947182198177/500000000000000000)⟩,(249501066843276023/250000000000000000),(370622690785208793/1000000000000000000),(52300971187402001/200000000000000000),(60466222063114997/250000000000000000)⟩
theorem valid3573 : certificate3573.Valid := by decide +kernel
theorem sound3573 : certificate3573.Sound := rat_cut_bin_certificate_sound certificate3573 profilesValid3573 numericValid3573 valid3573

def retention3574 : RatCutRetentionCertificate := ⟨(129/2000),(13/200),(3191297184215310025/6446146421844898457),(6256832044339398147/250000000000000000),1,(25059804779916021817628301622870044719/25027328177357592588000000000000000000),false,MergedCutProfiles.Batch549.profile21989,(fun _ => MergedCutProfiles.Batch549.profile21989)⟩
theorem profilesValid3574 : retention3574.ProfilesValid := by
  exact MergedCutProfiles.Batch549.valid21989
theorem numericValid3574 : retention3574.NumericValid := by decide +kernel
def certificate3574 : RatCutBinCertificate := ⟨⟨retention3574,(1137156209224245929/500000000000000000),(55239130418189853/250000000000000000),(17261006915229141307/1000000000000000000),(446476391738544410619/500000000000000000),(60761506186591909/62500000000000000)⟩,(249501066843276023/250000000000000000),(92312856090950243/250000000000000000),(131434172012771743/500000000000000000),(49099334705585103/200000000000000000)⟩
theorem valid3574 : certificate3574.Valid := by decide +kernel
theorem sound3574 : certificate3574.Sound := rat_cut_bin_certificate_sound certificate3574 profilesValid3574 numericValid3574 valid3574

def retention3575 : RatCutRetentionCertificate := ⟨(129/2000),(13/200),(1/2),(127651887368612401/5000000000000000),1,(101285285930219227216699019885607715311/102121509894889920800000000000000000000),false,MergedCutProfiles.Batch427.profile17083,(fun _ => MergedCutProfiles.Batch427.profile17083)⟩
theorem profilesValid3575 : retention3575.ProfilesValid := by
  exact MergedCutProfiles.Batch427.valid17083
theorem numericValid3575 : retention3575.NumericValid := by decide +kernel
def certificate3575 : RatCutBinCertificate := ⟨⟨retention3575,(1137156209224245929/500000000000000000),(55239130418189853/250000000000000000),(17261006915229141307/1000000000000000000),(446476391738544410619/500000000000000000),(192539587929779039/200000000000000000)⟩,(249501066843276023/250000000000000000),(372680460085652279/1000000000000000000),(259468263452187771/1000000000000000000),(120109981519472337/500000000000000000)⟩
theorem valid3575 : certificate3575.Valid := by decide +kernel
theorem sound3575 : certificate3575.Sound := rat_cut_bin_certificate_sound certificate3575 profilesValid3575 numericValid3575 valid3575

def certificates : List RatCutBinCertificate := [certificate3564,certificate3565,certificate3566,certificate3567,certificate3568,certificate3569,certificate3570,certificate3571,certificate3572,certificate3573,certificate3574,certificate3575]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3564,List.forall_mem_cons.mpr ⟨sound3565,List.forall_mem_cons.mpr ⟨sound3566,List.forall_mem_cons.mpr ⟨sound3567,List.forall_mem_cons.mpr ⟨sound3568,List.forall_mem_cons.mpr ⟨sound3569,List.forall_mem_cons.mpr ⟨sound3570,List.forall_mem_cons.mpr ⟨sound3571,List.forall_mem_cons.mpr ⟨sound3572,List.forall_mem_cons.mpr ⟨sound3573,List.forall_mem_cons.mpr ⟨sound3574,List.forall_mem_cons.mpr ⟨sound3575,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch297
