import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch038
import Cycle12.MergedCutProfiles.Batch039
import Cycle12.MergedCutProfiles.Batch040
import Cycle12.MergedCutProfiles.Batch329
import Cycle12.MergedCutProfiles.Batch461
import Cycle12.MergedCutProfiles.Batch462

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch247

def retention2964 : RatCutRetentionCertificate := ⟨(13/500),(27/1000),(58332708773982079628/369822667834612896403),(504926092943324013/250000000000000000),(9/5),(1651395640655600190105063778735815027/948218014917040400000000000000000000),false,MergedCutProfiles.Batch461.profile18455,(fun _ => MergedCutProfiles.Batch461.profile18455)⟩
theorem profilesValid2964 : retention2964.ProfilesValid := by
  exact MergedCutProfiles.Batch461.valid18455
theorem numericValid2964 : retention2964.NumericValid := by decide +kernel
def certificate2964 : RatCutBinCertificate := ⟨⟨retention2964,(1896245715664698419/1000000000000000000),(31463473579235007/1000000000000000000),(4632338185813076749/500000000000000000),(3443312750537497668733/1000000000000000000),(1729986374024281663/1000000000000000000)⟩,(249866323117012463/250000000000000000),(818461198611021/2000000000000000),(225130475292888199/1000000000000000000),(171029161157016139/1000000000000000000)⟩
theorem valid2964 : certificate2964.Valid := by decide +kernel
theorem sound2964 : certificate2964.Sound := rat_cut_bin_certificate_sound certificate2964 profilesValid2964 numericValid2964 valid2964

def retention2965 : RatCutRetentionCertificate := ⟨(13/500),(27/1000),(64000000000000000000/369822667834612896403),(14583177193495519907/250000000000000000),1,(98730784145812856437951577134890909703/58332708773982079628000000000000000000),false,MergedCutProfiles.Batch461.profile18456,(fun _ => MergedCutProfiles.Batch461.profile18456)⟩
theorem profilesValid2965 : retention2965.ProfilesValid := by
  exact MergedCutProfiles.Batch461.valid18456
theorem numericValid2965 : retention2965.NumericValid := by decide +kernel
def certificate2965 : RatCutBinCertificate := ⟨⟨retention2965,(1896245715664698419/1000000000000000000),(31463473579235007/1000000000000000000),(4632338185813076749/500000000000000000),(3443312750537497668733/1000000000000000000),(843053034453763953/500000000000000000)⟩,(249866323117012463/250000000000000000),(277142747925216939/1000000000000000000),(367179308559833797/1000000000000000000),(150346518998805413/250000000000000000)⟩
theorem valid2965 : certificate2965.Valid := by decide +kernel
theorem sound2965 : certificate2965.Sound := rat_cut_bin_certificate_sound certificate2965 profilesValid2965 numericValid2965 valid2965

def retention2966 : RatCutRetentionCertificate := ⟨(13/500),(27/1000),(1/2),64,1,(15960890419747252013481485060871619639/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch038.profile1543,(fun _ => MergedCutProfiles.Batch038.profile1543)⟩
theorem profilesValid2966 : retention2966.ProfilesValid := by
  exact MergedCutProfiles.Batch038.valid1543
theorem numericValid2966 : retention2966.NumericValid := by decide +kernel
def certificate2966 : RatCutBinCertificate := ⟨⟨retention2966,(1896245715664698419/1000000000000000000),(31463473579235007/1000000000000000000),(4632338185813076749/500000000000000000),(3443312750537497668733/1000000000000000000),(991115870382759033/1000000000000000000)⟩,(249866323117012463/250000000000000000),(470709552143501799/1000000000000000000),(174604052718143381/1000000000000000000),(42580470291094977/250000000000000000)⟩
theorem valid2966 : certificate2966.Valid := by decide +kernel
theorem sound2966 : certificate2966.Sound := rat_cut_bin_certificate_sound certificate2966 profilesValid2966 numericValid2966 valid2966

def retention2967 : RatCutRetentionCertificate := ⟨(13/500),(27/1000),(64000000000000000000/369822667834612896403),(71575128691361747/7812500000000000),1,(14893839145638554978034609414647935647/9161616472494303616000000000000000000),false,MergedCutProfiles.Batch461.profile18456,(fun _ => MergedCutProfiles.Batch461.profile18456)⟩
theorem profilesValid2967 : retention2967.ProfilesValid := by
  exact MergedCutProfiles.Batch461.valid18456
theorem numericValid2967 : retention2967.NumericValid := by decide +kernel
def certificate2967 : RatCutBinCertificate := ⟨⟨retention2967,(2050177303664698419/1000000000000000000),(31463473579235007/1000000000000000000),(4632338185813076749/500000000000000000),(3443312750537497668733/1000000000000000000),(1618715538464567509/1000000000000000000)⟩,(124927735718705421/125000000000000000),(20793624839035573/250000000000000000),(704896499480341727/1000000000000000000),(242277258152507167/250000000000000000)⟩
theorem valid2967 : certificate2967.Valid := by decide +kernel
theorem sound2967 : certificate2967.Sound := rat_cut_bin_certificate_sound certificate2967 profilesValid2967 numericValid2967 valid2967

def retention2968 : RatCutRetentionCertificate := ⟨(13/500),(27/1000),(1/2),64,1,(15960890419747252013481485060871619639/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch038.profile1543,(fun _ => MergedCutProfiles.Batch038.profile1543)⟩
theorem profilesValid2968 : retention2968.ProfilesValid := by
  exact MergedCutProfiles.Batch038.valid1543
theorem numericValid2968 : retention2968.NumericValid := by decide +kernel
def certificate2968 : RatCutBinCertificate := ⟨⟨retention2968,(2050177303664698419/1000000000000000000),(31463473579235007/1000000000000000000),(4632338185813076749/500000000000000000),(3443312750537497668733/1000000000000000000),(495296554062170921/500000000000000000)⟩,(124927735718705421/125000000000000000),(67957193224737663/500000000000000000),(591427252648479111/1000000000000000000),(576597773607032073/1000000000000000000)⟩
theorem valid2968 : certificate2968.Valid := by decide +kernel
theorem sound2968 : certificate2968.Sound := rat_cut_bin_certificate_sound certificate2968 profilesValid2968 numericValid2968 valid2968

def retention2969 : RatCutRetentionCertificate := ⟨(27/1000),(7/250),(628071172125124282/342168125560045782465),(621852645668439883/1000000000000000000),4,(283872994625501323062600100216040199/124370529133687976600000000000000000),true,MergedCutProfiles.Batch461.profile18457,![MergedCutProfiles.Batch461.profile18457,MergedCutProfiles.Batch461.profile18458,MergedCutProfiles.Batch461.profile18459,MergedCutProfiles.Batch461.profile18460,MergedCutProfiles.Batch461.profile18461,MergedCutProfiles.Batch461.profile18462,MergedCutProfiles.Batch461.profile18463,MergedCutProfiles.Batch329.profile13163,MergedCutProfiles.Batch461.profile18464,MergedCutProfiles.Batch461.profile18465,MergedCutProfiles.Batch329.profile13164,MergedCutProfiles.Batch461.profile18466,MergedCutProfiles.Batch461.profile18467,MergedCutProfiles.Batch461.profile18468,MergedCutProfiles.Batch329.profile13179,MergedCutProfiles.Batch461.profile18469]⟩
theorem profilesValid2969 : retention2969.ProfilesValid := by
  change ∀ j : Fin 16, (retention2969.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch461.valid18457
  · exact MergedCutProfiles.Batch461.valid18458
  · exact MergedCutProfiles.Batch461.valid18459
  · exact MergedCutProfiles.Batch461.valid18460
  · exact MergedCutProfiles.Batch461.valid18461
  · exact MergedCutProfiles.Batch461.valid18462
  · exact MergedCutProfiles.Batch461.valid18463
  · exact MergedCutProfiles.Batch329.valid13163
  · exact MergedCutProfiles.Batch461.valid18464
  · exact MergedCutProfiles.Batch461.valid18465
  · exact MergedCutProfiles.Batch329.valid13164
  · exact MergedCutProfiles.Batch461.valid18466
  · exact MergedCutProfiles.Batch461.valid18467
  · exact MergedCutProfiles.Batch461.valid18468
  · exact MergedCutProfiles.Batch329.valid13179
  · exact MergedCutProfiles.Batch461.valid18469
theorem numericValid2969 : retention2969.NumericValid := by decide +kernel
def certificate2969 : RatCutBinCertificate := ⟨⟨retention2969,(1902067508901585643/1000000000000000000),(1358828718451041/40000000000000000),(4696733385487076059/500000000000000000),(1615105516787295487701/500000000000000000),(70467599076448151/31250000000000000)⟩,(999429679354074183/1000000000000000000),(280900314167376473/500000000000000000),(57130245968239801/500000000000000000),(52476629406949549/1000000000000000000)⟩
theorem valid2969 : certificate2969.Valid := by decide +kernel
theorem sound2969 : certificate2969.Sound := rat_cut_bin_certificate_sound certificate2969 profilesValid2969 numericValid2969 valid2969

def retention2970 : RatCutRetentionCertificate := ⟨(27/1000),(7/250),(236070060400000000/68433625112009156493),(314035586062562141/500000000000000000),4,(72860209435039441881/32000000000000000000),true,MergedCutProfiles.Batch461.profile18470,![MergedCutProfiles.Batch461.profile18470,MergedCutProfiles.Batch329.profile13177,MergedCutProfiles.Batch038.profile1546,MergedCutProfiles.Batch461.profile18471,MergedCutProfiles.Batch461.profile18472,MergedCutProfiles.Batch038.profile1547,MergedCutProfiles.Batch461.profile18467,MergedCutProfiles.Batch461.profile18473,MergedCutProfiles.Batch038.profile1548,MergedCutProfiles.Batch329.profile13167,MergedCutProfiles.Batch461.profile18474,MergedCutProfiles.Batch038.profile1549,MergedCutProfiles.Batch329.profile13169,MergedCutProfiles.Batch461.profile18475,MergedCutProfiles.Batch038.profile1550,MergedCutProfiles.Batch329.profile13171]⟩
theorem profilesValid2970 : retention2970.ProfilesValid := by
  change ∀ j : Fin 16, (retention2970.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch461.valid18470
  · exact MergedCutProfiles.Batch329.valid13177
  · exact MergedCutProfiles.Batch038.valid1546
  · exact MergedCutProfiles.Batch461.valid18471
  · exact MergedCutProfiles.Batch461.valid18472
  · exact MergedCutProfiles.Batch038.valid1547
  · exact MergedCutProfiles.Batch461.valid18467
  · exact MergedCutProfiles.Batch461.valid18473
  · exact MergedCutProfiles.Batch038.valid1548
  · exact MergedCutProfiles.Batch329.valid13167
  · exact MergedCutProfiles.Batch461.valid18474
  · exact MergedCutProfiles.Batch038.valid1549
  · exact MergedCutProfiles.Batch329.valid13169
  · exact MergedCutProfiles.Batch461.valid18475
  · exact MergedCutProfiles.Batch038.valid1550
  · exact MergedCutProfiles.Batch329.valid13171
theorem numericValid2970 : retention2970.NumericValid := by decide +kernel
def certificate2970 : RatCutBinCertificate := ⟨⟨retention2970,(1902067508901585643/1000000000000000000),(1358828718451041/40000000000000000),(4696733385487076059/500000000000000000),(1615105516787295487701/500000000000000000),(70292710383965433/31250000000000000)⟩,(999429679354074183/1000000000000000000),(34978027613894861/62500000000000000),(57752793817370829/500000000000000000),(26518978076242609/500000000000000000)⟩
theorem valid2970 : certificate2970.Valid := by decide +kernel
theorem sound2970 : certificate2970.Sound := rat_cut_bin_certificate_sound certificate2970 profilesValid2970 numericValid2970 valid2970

def retention2971 : RatCutRetentionCertificate := ⟨(27/1000),(7/250),(1247911109867179489/342168125560045782465),(590175151/500000000),(51/20),(36809982783340957027/16000000000000000000),true,MergedCutProfiles.Batch461.profile18470,![MergedCutProfiles.Batch461.profile18470,MergedCutProfiles.Batch461.profile18460,MergedCutProfiles.Batch461.profile18462,MergedCutProfiles.Batch461.profile18476,MergedCutProfiles.Batch461.profile18465,MergedCutProfiles.Batch461.profile18466,MergedCutProfiles.Batch039.profile1563,MergedCutProfiles.Batch461.profile18469,MergedCutProfiles.Batch461.profile18477,MergedCutProfiles.Batch461.profile18478,MergedCutProfiles.Batch329.profile13168,MergedCutProfiles.Batch461.profile18479,MergedCutProfiles.Batch039.profile1578,MergedCutProfiles.Batch039.profile1565,MergedCutProfiles.Batch462.profile18480,MergedCutProfiles.Batch039.profile1590]⟩
theorem profilesValid2971 : retention2971.ProfilesValid := by
  change ∀ j : Fin 16, (retention2971.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch461.valid18470
  · exact MergedCutProfiles.Batch461.valid18460
  · exact MergedCutProfiles.Batch461.valid18462
  · exact MergedCutProfiles.Batch461.valid18476
  · exact MergedCutProfiles.Batch461.valid18465
  · exact MergedCutProfiles.Batch461.valid18466
  · exact MergedCutProfiles.Batch039.valid1563
  · exact MergedCutProfiles.Batch461.valid18469
  · exact MergedCutProfiles.Batch461.valid18477
  · exact MergedCutProfiles.Batch461.valid18478
  · exact MergedCutProfiles.Batch329.valid13168
  · exact MergedCutProfiles.Batch461.valid18479
  · exact MergedCutProfiles.Batch039.valid1578
  · exact MergedCutProfiles.Batch039.valid1565
  · exact MergedCutProfiles.Batch462.valid18480
  · exact MergedCutProfiles.Batch039.valid1590
theorem numericValid2971 : retention2971.NumericValid := by decide +kernel
def certificate2971 : RatCutBinCertificate := ⟨⟨retention2971,(1902067508901585643/1000000000000000000),(1358828718451041/40000000000000000),(4696733385487076059/500000000000000000),(1615105516787295487701/500000000000000000),(2283083243092133411/1000000000000000000)⟩,(999429679354074183/1000000000000000000),(24233525809180177/62500000000000000),(30613590174442419/125000000000000000),(33778318552151633/200000000000000000)⟩
theorem valid2971 : certificate2971.Valid := by decide +kernel
theorem sound2971 : certificate2971.Sound := rat_cut_bin_certificate_sound certificate2971 profilesValid2971 numericValid2971 valid2971

def retention2972 : RatCutRetentionCertificate := ⟨(27/1000),(7/250),(891968445626504263/68433625112009156493),(1247911109867179489/1000000000000000000),(5/2),(143224503222864555397/64000000000000000000),true,MergedCutProfiles.Batch461.profile18463,![MergedCutProfiles.Batch461.profile18463,MergedCutProfiles.Batch461.profile18468,MergedCutProfiles.Batch462.profile18481,MergedCutProfiles.Batch038.profile1550,MergedCutProfiles.Batch329.profile13173,MergedCutProfiles.Batch039.profile1579,MergedCutProfiles.Batch462.profile18482,MergedCutProfiles.Batch038.profile1555,MergedCutProfiles.Batch462.profile18483,MergedCutProfiles.Batch462.profile18484,MergedCutProfiles.Batch462.profile18485,MergedCutProfiles.Batch039.profile1560,MergedCutProfiles.Batch462.profile18486,MergedCutProfiles.Batch462.profile18487,MergedCutProfiles.Batch462.profile18488,MergedCutProfiles.Batch462.profile18489]⟩
theorem profilesValid2972 : retention2972.ProfilesValid := by
  change ∀ j : Fin 16, (retention2972.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch461.valid18463
  · exact MergedCutProfiles.Batch461.valid18468
  · exact MergedCutProfiles.Batch462.valid18481
  · exact MergedCutProfiles.Batch038.valid1550
  · exact MergedCutProfiles.Batch329.valid13173
  · exact MergedCutProfiles.Batch039.valid1579
  · exact MergedCutProfiles.Batch462.valid18482
  · exact MergedCutProfiles.Batch038.valid1555
  · exact MergedCutProfiles.Batch462.valid18483
  · exact MergedCutProfiles.Batch462.valid18484
  · exact MergedCutProfiles.Batch462.valid18485
  · exact MergedCutProfiles.Batch039.valid1560
  · exact MergedCutProfiles.Batch462.valid18486
  · exact MergedCutProfiles.Batch462.valid18487
  · exact MergedCutProfiles.Batch462.valid18488
  · exact MergedCutProfiles.Batch462.valid18489
theorem numericValid2972 : retention2972.NumericValid := by decide +kernel
def certificate2972 : RatCutBinCertificate := ⟨⟨retention2972,(1902067508901585643/1000000000000000000),(1358828718451041/40000000000000000),(4696733385487076059/500000000000000000),(1615105516787295487701/500000000000000000),(2220686119025851597/1000000000000000000)⟩,(999429679354074183/1000000000000000000),(97068099983133993/250000000000000000),(244401312564400479/1000000000000000000),(168872344213656567/1000000000000000000)⟩
theorem valid2972 : certificate2972.Valid := by decide +kernel
theorem sound2972 : certificate2972.Sound := rat_cut_bin_certificate_sound certificate2972 profilesValid2972 numericValid2972 valid2972

def retention2973 : RatCutRetentionCertificate := ⟨(27/1000),(7/250),(12800000000000000000/68433625112009156493),(891968445626504263/200000000000000000),(5/4),(472006482398671731368569837751616382799/285429902600481364160000000000000000000),false,MergedCutProfiles.Batch462.profile18490,(fun _ => MergedCutProfiles.Batch462.profile18490)⟩
theorem profilesValid2973 : retention2973.ProfilesValid := by
  exact MergedCutProfiles.Batch462.valid18490
theorem numericValid2973 : retention2973.NumericValid := by decide +kernel
def certificate2973 : RatCutBinCertificate := ⟨⟨retention2973,(1902067508901585643/1000000000000000000),(1358828718451041/40000000000000000),(4696733385487076059/500000000000000000),(1615105516787295487701/500000000000000000),(329014058657162793/200000000000000000)⟩,(999429679354074183/1000000000000000000),(348188085008034243/1000000000000000000),(142231512590526941/500000000000000000),(302683308611892351/1000000000000000000)⟩
theorem valid2973 : certificate2973.Valid := by decide +kernel
theorem sound2973 : certificate2973.Sound := rat_cut_bin_certificate_sound certificate2973 profilesValid2973 numericValid2973 valid2973

def retention2974 : RatCutRetentionCertificate := ⟨(27/1000),(7/250),(1/2),64,1,(63843694446586541505180302875124093631/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch040.profile1621,(fun _ => MergedCutProfiles.Batch040.profile1621)⟩
theorem profilesValid2974 : retention2974.ProfilesValid := by
  exact MergedCutProfiles.Batch040.valid1621
theorem numericValid2974 : retention2974.NumericValid := by decide +kernel
def certificate2974 : RatCutBinCertificate := ⟨⟨retention2974,(1902067508901585643/1000000000000000000),(1358828718451041/40000000000000000),(4696733385487076059/500000000000000000),(1615105516787295487701/500000000000000000),(990679050252592143/1000000000000000000)⟩,(999429679354074183/1000000000000000000),(59072735366656527/125000000000000000),(43299238158778071/250000000000000000),(42217473124683521/250000000000000000)⟩
theorem valid2974 : certificate2974.Valid := by decide +kernel
theorem sound2974 : certificate2974.Sound := rat_cut_bin_certificate_sound certificate2974 profilesValid2974 numericValid2974 valid2974

def retention2975 : RatCutRetentionCertificate := ⟨(27/1000),(7/250),(12800000000000000000/68433625112009156493),(9300633999686685519/1000000000000000000),1,(19791065253878857875051417321660600801/12400845332915580692000000000000000000),false,MergedCutProfiles.Batch462.profile18490,(fun _ => MergedCutProfiles.Batch462.profile18490)⟩
theorem profilesValid2975 : retention2975.ProfilesValid := by
  exact MergedCutProfiles.Batch462.valid18490
theorem numericValid2975 : retention2975.NumericValid := by decide +kernel
def certificate2975 : RatCutBinCertificate := ⟨⟨retention2975,(2053212004901585643/1000000000000000000),(1358828718451041/40000000000000000),(4696733385487076059/500000000000000000),(1615105516787295487701/500000000000000000),(794259783035179031/500000000000000000)⟩,(99938435890663907/100000000000000000),(83812598227791397/1000000000000000000),(28135675995337559/40000000000000000),(476867957569956159/500000000000000000)⟩
theorem valid2975 : certificate2975.Valid := by decide +kernel
theorem sound2975 : certificate2975.Sound := rat_cut_bin_certificate_sound certificate2975 profilesValid2975 numericValid2975 valid2975

def certificates : List RatCutBinCertificate := [certificate2964,certificate2965,certificate2966,certificate2967,certificate2968,certificate2969,certificate2970,certificate2971,certificate2972,certificate2973,certificate2974,certificate2975]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2964,List.forall_mem_cons.mpr ⟨sound2965,List.forall_mem_cons.mpr ⟨sound2966,List.forall_mem_cons.mpr ⟨sound2967,List.forall_mem_cons.mpr ⟨sound2968,List.forall_mem_cons.mpr ⟨sound2969,List.forall_mem_cons.mpr ⟨sound2970,List.forall_mem_cons.mpr ⟨sound2971,List.forall_mem_cons.mpr ⟨sound2972,List.forall_mem_cons.mpr ⟨sound2973,List.forall_mem_cons.mpr ⟨sound2974,List.forall_mem_cons.mpr ⟨sound2975,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch247
