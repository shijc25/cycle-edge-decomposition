import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch038
import Cycle12.MergedCutProfiles.Batch039
import Cycle12.MergedCutProfiles.Batch040
import Cycle12.MergedCutProfiles.Batch329
import Cycle12.MergedCutProfiles.Batch330
import Cycle12.MergedCutProfiles.Batch461
import Cycle12.MergedCutProfiles.Batch592
import Cycle12.MergedCutProfiles.Batch593
import Cycle12.MergedCutProfiles.Batch653
import Cycle12.MergedCutProfiles.Batch654

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch380

def retention4560 : RatCutRetentionCertificate := ⟨(13/500),(27/1000),(1/40),(5095704884916536831/200000000000000000),(21/20),(3552114936696201689120038957066701917991/1630625563173291785920000000000000000000),false,MergedCutProfiles.Batch653.profile26139,(fun _ => MergedCutProfiles.Batch653.profile26139)⟩
theorem profilesValid4560 : retention4560.ProfilesValid := by
  exact MergedCutProfiles.Batch653.valid26139
theorem numericValid4560 : retention4560.NumericValid := by decide +kernel
def certificate4560 : RatCutBinCertificate := ⟨⟨retention4560,(1769874921933234921/1000000000000000000),(31463473579235007/1000000000000000000),(1852936718602131223/200000000000000000),(6886630868879403605273/100000000000000000),(434412891233528903/200000000000000000)⟩,(499987523369938537/500000000000000000),(338096105012250377/500000000000000000),(11845743186284237/200000000000000000),(14215690044027853/125000000000000000)⟩
theorem valid4560 : certificate4560.Valid := by decide +kernel
theorem sound4560 : certificate4560.Sound := rat_cut_bin_certificate_sound certificate4560 profilesValid4560 numericValid4560 valid4560

def retention4561 : RatCutRetentionCertificate := ⟨(27/1000),(7/250),(679126936936118144/6843362511200915649309),(652627637804430661/1000000000000000000),4,(6133479601537249160748219753886199367/2610510551217722644000000000000000000),true,MergedCutProfiles.Batch653.profile26140,![MergedCutProfiles.Batch653.profile26140,MergedCutProfiles.Batch653.profile26141,MergedCutProfiles.Batch653.profile26142,MergedCutProfiles.Batch592.profile23707,MergedCutProfiles.Batch653.profile26143,MergedCutProfiles.Batch653.profile26144,MergedCutProfiles.Batch653.profile26145,MergedCutProfiles.Batch592.profile23708,MergedCutProfiles.Batch592.profile23719,MergedCutProfiles.Batch653.profile26146,MergedCutProfiles.Batch653.profile26146,MergedCutProfiles.Batch653.profile26147,MergedCutProfiles.Batch592.profile23709,MergedCutProfiles.Batch653.profile26148,MergedCutProfiles.Batch653.profile26148,MergedCutProfiles.Batch593.profile23725]⟩
theorem profilesValid4561 : retention4561.ProfilesValid := by
  change ∀ j : Fin 16, (retention4561.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch653.valid26140
  · exact MergedCutProfiles.Batch653.valid26141
  · exact MergedCutProfiles.Batch653.valid26142
  · exact MergedCutProfiles.Batch592.valid23707
  · exact MergedCutProfiles.Batch653.valid26143
  · exact MergedCutProfiles.Batch653.valid26144
  · exact MergedCutProfiles.Batch653.valid26145
  · exact MergedCutProfiles.Batch592.valid23708
  · exact MergedCutProfiles.Batch592.valid23719
  · exact MergedCutProfiles.Batch653.valid26146
  · exact MergedCutProfiles.Batch653.valid26146
  · exact MergedCutProfiles.Batch653.valid26147
  · exact MergedCutProfiles.Batch592.valid23709
  · exact MergedCutProfiles.Batch653.valid26148
  · exact MergedCutProfiles.Batch653.valid26148
  · exact MergedCutProfiles.Batch593.valid23725
theorem numericValid4561 : retention4561.NumericValid := by decide +kernel
def certificate4561 : RatCutBinCertificate := ⟨⟨retention4561,(1928653278995079283/1000000000000000000),(1358828718451041/40000000000000000),(2348368801580123351/250000000000000000),(64604278686172635417061/1000000000000000000),(1160816662533544267/500000000000000000)⟩,(39998843437035317/40000000000000000),(94478961956399879/200000000000000000),(34667441686836847/200000000000000000),(82303895082273667/1000000000000000000)⟩
theorem valid4561 : certificate4561.Valid := by decide +kernel
theorem sound4561 : certificate4561.Sound := rat_cut_bin_certificate_sound certificate4561 profilesValid4561 numericValid4561 valid4561

def retention4562 : RatCutRetentionCertificate := ⟨(27/1000),(7/250),(1238936965000000000/6843362511200915649309),(5305679194813423/7812500000000000),4,(6451099342543219154254517814652590327/2716507747744472576000000000000000000),true,MergedCutProfiles.Batch653.profile26149,![MergedCutProfiles.Batch653.profile26149,MergedCutProfiles.Batch653.profile26150,MergedCutProfiles.Batch653.profile26143,MergedCutProfiles.Batch653.profile26145,MergedCutProfiles.Batch592.profile23719,MergedCutProfiles.Batch653.profile26146,MergedCutProfiles.Batch592.profile23709,MergedCutProfiles.Batch653.profile26148,MergedCutProfiles.Batch593.profile23725,MergedCutProfiles.Batch461.profile18457,MergedCutProfiles.Batch653.profile26151,MergedCutProfiles.Batch592.profile23710,MergedCutProfiles.Batch653.profile26152,MergedCutProfiles.Batch592.profile23711,MergedCutProfiles.Batch593.profile23720,MergedCutProfiles.Batch653.profile26153]⟩
theorem profilesValid4562 : retention4562.ProfilesValid := by
  change ∀ j : Fin 16, (retention4562.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch653.valid26149
  · exact MergedCutProfiles.Batch653.valid26150
  · exact MergedCutProfiles.Batch653.valid26143
  · exact MergedCutProfiles.Batch653.valid26145
  · exact MergedCutProfiles.Batch592.valid23719
  · exact MergedCutProfiles.Batch653.valid26146
  · exact MergedCutProfiles.Batch592.valid23709
  · exact MergedCutProfiles.Batch653.valid26148
  · exact MergedCutProfiles.Batch593.valid23725
  · exact MergedCutProfiles.Batch461.valid18457
  · exact MergedCutProfiles.Batch653.valid26151
  · exact MergedCutProfiles.Batch592.valid23710
  · exact MergedCutProfiles.Batch653.valid26152
  · exact MergedCutProfiles.Batch592.valid23711
  · exact MergedCutProfiles.Batch593.valid23720
  · exact MergedCutProfiles.Batch653.valid26153
theorem numericValid4562 : retention4562.NumericValid := by decide +kernel
def certificate4562 : RatCutBinCertificate := ⟨⟨retention4562,(1928653278995079283/1000000000000000000),(1358828718451041/40000000000000000),(2348368801580123351/250000000000000000),(64604278686172635417061/1000000000000000000),(2346877454991975829/1000000000000000000)⟩,(39998843437035317/40000000000000000),(227821453828488203/500000000000000000),(11637539576618683/62500000000000000),(89839934617933101/1000000000000000000)⟩
theorem valid4562 : certificate4562.Valid := by decide +kernel
theorem sound4562 : certificate4562.Sound := rat_cut_bin_certificate_sound certificate4562 profilesValid4562 numericValid4562 valid4562

def retention4563 : RatCutRetentionCertificate := ⟨(27/1000),(7/250),(1246105340880166894/6843362511200915649309),(247787393/200000000),(51/20),(38055040123323851417/16000000000000000000),true,MergedCutProfiles.Batch653.profile26149,![MergedCutProfiles.Batch653.profile26149,MergedCutProfiles.Batch653.profile26150,MergedCutProfiles.Batch653.profile26143,MergedCutProfiles.Batch653.profile26145,MergedCutProfiles.Batch592.profile23719,MergedCutProfiles.Batch653.profile26146,MergedCutProfiles.Batch592.profile23709,MergedCutProfiles.Batch653.profile26148,MergedCutProfiles.Batch593.profile23725,MergedCutProfiles.Batch461.profile18457,MergedCutProfiles.Batch653.profile26151,MergedCutProfiles.Batch592.profile23710,MergedCutProfiles.Batch653.profile26152,MergedCutProfiles.Batch592.profile23711,MergedCutProfiles.Batch593.profile23720,MergedCutProfiles.Batch653.profile26153]⟩
theorem profilesValid4563 : retention4563.ProfilesValid := by
  change ∀ j : Fin 16, (retention4563.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch653.valid26149
  · exact MergedCutProfiles.Batch653.valid26150
  · exact MergedCutProfiles.Batch653.valid26143
  · exact MergedCutProfiles.Batch653.valid26145
  · exact MergedCutProfiles.Batch592.valid23719
  · exact MergedCutProfiles.Batch653.valid26146
  · exact MergedCutProfiles.Batch592.valid23709
  · exact MergedCutProfiles.Batch653.valid26148
  · exact MergedCutProfiles.Batch593.valid23725
  · exact MergedCutProfiles.Batch461.valid18457
  · exact MergedCutProfiles.Batch653.valid26151
  · exact MergedCutProfiles.Batch592.valid23710
  · exact MergedCutProfiles.Batch653.valid26152
  · exact MergedCutProfiles.Batch592.valid23711
  · exact MergedCutProfiles.Batch593.valid23720
  · exact MergedCutProfiles.Batch653.valid26153
theorem numericValid4563 : retention4563.NumericValid := by decide +kernel
def certificate4563 : RatCutBinCertificate := ⟨⟨retention4563,(1928653278995079283/1000000000000000000),(1358828718451041/40000000000000000),(2348368801580123351/250000000000000000),(64604278686172635417061/1000000000000000000),(2360654230619790173/1000000000000000000)⟩,(39998843437035317/40000000000000000),(16193483187613177/50000000000000000),(62196611608885859/200000000000000000),(111321276015072091/500000000000000000)⟩
theorem valid4563 : certificate4563.Valid := by decide +kernel
theorem sound4563 : certificate4563.Sound := rat_cut_bin_certificate_sound certificate4563 profilesValid4563 numericValid4563 valid4563

def retention4564 : RatCutRetentionCertificate := ⟨(27/1000),(7/250),(958139843759484152/2281120837066971883103),(623052670440083447/500000000000000000),(5/2),(11762542679775074195869054471677701031/4984421363520667576000000000000000000),true,MergedCutProfiles.Batch592.profile23707,![MergedCutProfiles.Batch592.profile23707,MergedCutProfiles.Batch592.profile23708,MergedCutProfiles.Batch592.profile23709,MergedCutProfiles.Batch593.profile23725,MergedCutProfiles.Batch592.profile23710,MergedCutProfiles.Batch592.profile23711,MergedCutProfiles.Batch653.profile26153,MergedCutProfiles.Batch592.profile23713,MergedCutProfiles.Batch461.profile18458,MergedCutProfiles.Batch592.profile23714,MergedCutProfiles.Batch653.profile26154,MergedCutProfiles.Batch329.profile13161,MergedCutProfiles.Batch461.profile18459,MergedCutProfiles.Batch592.profile23717,MergedCutProfiles.Batch593.profile23721,MergedCutProfiles.Batch592.profile23718]⟩
theorem profilesValid4564 : retention4564.ProfilesValid := by
  change ∀ j : Fin 16, (retention4564.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch592.valid23707
  · exact MergedCutProfiles.Batch592.valid23708
  · exact MergedCutProfiles.Batch592.valid23709
  · exact MergedCutProfiles.Batch593.valid23725
  · exact MergedCutProfiles.Batch592.valid23710
  · exact MergedCutProfiles.Batch592.valid23711
  · exact MergedCutProfiles.Batch653.valid26153
  · exact MergedCutProfiles.Batch592.valid23713
  · exact MergedCutProfiles.Batch461.valid18458
  · exact MergedCutProfiles.Batch592.valid23714
  · exact MergedCutProfiles.Batch653.valid26154
  · exact MergedCutProfiles.Batch329.valid13161
  · exact MergedCutProfiles.Batch461.valid18459
  · exact MergedCutProfiles.Batch592.valid23717
  · exact MergedCutProfiles.Batch593.valid23721
  · exact MergedCutProfiles.Batch592.valid23718
theorem numericValid4564 : retention4564.NumericValid := by decide +kernel
def certificate4564 : RatCutBinCertificate := ⟨⟨retention4564,(1928653278995079283/1000000000000000000),(1358828718451041/40000000000000000),(2348368801580123351/250000000000000000),(64604278686172635417061/1000000000000000000),(2342424183570789477/1000000000000000000)⟩,(39998843437035317/40000000000000000),(162741066345399531/500000000000000000),(309169667640603721/1000000000000000000),(5567349732296657/25000000000000000)⟩
theorem valid4564 : certificate4564.Valid := by decide +kernel
theorem sound4564 : certificate4564.Sound := rat_cut_bin_certificate_sound certificate4564 profilesValid4564 numericValid4564 valid4564

def retention4565 : RatCutRetentionCertificate := ⟨(27/1000),(7/250),(64000000000000000000/6843362511200915649309),(359302441409806557/125000000000000000),(3/2),(1787244660359621329/800000000000000000),true,MergedCutProfiles.Batch461.profile18461,![MergedCutProfiles.Batch461.profile18461,MergedCutProfiles.Batch593.profile23727,MergedCutProfiles.Batch461.profile18473,MergedCutProfiles.Batch461.profile18474,MergedCutProfiles.Batch593.profile23729,MergedCutProfiles.Batch330.profile13200,MergedCutProfiles.Batch653.profile26155,MergedCutProfiles.Batch329.profile13175,MergedCutProfiles.Batch653.profile26156,MergedCutProfiles.Batch038.profile1554,MergedCutProfiles.Batch653.profile26157,MergedCutProfiles.Batch330.profile13202,MergedCutProfiles.Batch653.profile26158,MergedCutProfiles.Batch653.profile26159,MergedCutProfiles.Batch039.profile1571,MergedCutProfiles.Batch654.profile26160]⟩
theorem profilesValid4565 : retention4565.ProfilesValid := by
  change ∀ j : Fin 16, (retention4565.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch461.valid18461
  · exact MergedCutProfiles.Batch593.valid23727
  · exact MergedCutProfiles.Batch461.valid18473
  · exact MergedCutProfiles.Batch461.valid18474
  · exact MergedCutProfiles.Batch593.valid23729
  · exact MergedCutProfiles.Batch330.valid13200
  · exact MergedCutProfiles.Batch653.valid26155
  · exact MergedCutProfiles.Batch329.valid13175
  · exact MergedCutProfiles.Batch653.valid26156
  · exact MergedCutProfiles.Batch038.valid1554
  · exact MergedCutProfiles.Batch653.valid26157
  · exact MergedCutProfiles.Batch330.valid13202
  · exact MergedCutProfiles.Batch653.valid26158
  · exact MergedCutProfiles.Batch653.valid26159
  · exact MergedCutProfiles.Batch039.valid1571
  · exact MergedCutProfiles.Batch654.valid26160
theorem numericValid4565 : retention4565.NumericValid := by decide +kernel
def certificate4565 : RatCutBinCertificate := ⟨⟨retention4565,(1928653278995079283/1000000000000000000),(1358828718451041/40000000000000000),(2348368801580123351/250000000000000000),(64604278686172635417061/1000000000000000000),(2223593604098475267/1000000000000000000)⟩,(39998843437035317/40000000000000000),(249218456934403527/1000000000000000000),(202212241911286059/500000000000000000),(44611711696236451/100000000000000000)⟩
theorem valid4565 : certificate4565.Valid := by decide +kernel
theorem sound4565 : certificate4565.Sound := rat_cut_bin_certificate_sound certificate4565 profilesValid4565 numericValid4565 valid4565

def retention4566 : RatCutRetentionCertificate := ⟨(27/1000),(7/250),(1/2),64,1,(63843694446586541505180302875124093631/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch040.profile1621,(fun _ => MergedCutProfiles.Batch040.profile1621)⟩
theorem profilesValid4566 : retention4566.ProfilesValid := by
  exact MergedCutProfiles.Batch040.valid1621
theorem numericValid4566 : retention4566.NumericValid := by decide +kernel
def certificate4566 : RatCutBinCertificate := ⟨⟨retention4566,(1928653278995079283/1000000000000000000),(1358828718451041/40000000000000000),(2348368801580123351/250000000000000000),(64604278686172635417061/1000000000000000000),(247645728071798271/250000000000000000)⟩,(39998843437035317/40000000000000000),(405766352825002857/1000000000000000000),(22824028891993607/100000000000000000),(44527674420498461/200000000000000000)⟩
theorem valid4566 : certificate4566.Valid := by decide +kernel
theorem sound4566 : certificate4566.Sound := rat_cut_bin_certificate_sound certificate4566 profilesValid4566 numericValid4566 valid4566

def retention4567 : RatCutRetentionCertificate := ⟨(27/1000),(7/250),(64000000000000000000/6843362511200915649309),(19661602274635897567/1000000000000000000),1,(68349897799678165252228865178243921/30721253554118589948437500000000000),false,MergedCutProfiles.Batch654.profile26161,(fun _ => MergedCutProfiles.Batch654.profile26161)⟩
theorem profilesValid4567 : retention4567.ProfilesValid := by
  exact MergedCutProfiles.Batch654.valid26161
theorem numericValid4567 : retention4567.NumericValid := by decide +kernel
def certificate4567 : RatCutBinCertificate := ⟨⟨retention4567,(1799462516995079283/1000000000000000000),(1358828718451041/40000000000000000),(2348368801580123351/250000000000000000),(64604278686172635417061/1000000000000000000),(2218333176631429651/1000000000000000000)⟩,(199994604547133451/200000000000000000),(24862557572588779/1000000000000000000),(107422668963396993/125000000000000000),(856531896815013623/500000000000000000)⟩
theorem valid4567 : certificate4567.Valid := by decide +kernel
theorem sound4567 : certificate4567.Sound := rat_cut_bin_certificate_sound certificate4567 profilesValid4567 numericValid4567 valid4567

def retention4568 : RatCutRetentionCertificate := ⟨(27/1000),(7/250),(1/2),64,1,(63843694446586541505180302875124093631/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch040.profile1621,(fun _ => MergedCutProfiles.Batch040.profile1621)⟩
theorem profilesValid4568 : retention4568.ProfilesValid := by
  exact MergedCutProfiles.Batch040.valid1621
theorem numericValid4568 : retention4568.NumericValid := by decide +kernel
def certificate4568 : RatCutBinCertificate := ⟨⟨retention4568,(1799462516995079283/1000000000000000000),(1358828718451041/40000000000000000),(2348368801580123351/250000000000000000),(64604278686172635417061/1000000000000000000),(49552505994191227/50000000000000000)⟩,(199994604547133451/200000000000000000),(27825755333972419/500000000000000000),(96672189067605687/125000000000000000),(377373812289780359/500000000000000000)⟩
theorem valid4568 : certificate4568.Valid := by decide +kernel
theorem sound4568 : certificate4568.Sound := rat_cut_bin_certificate_sound certificate4568 profilesValid4568 numericValid4568 valid4568

def retention4569 : RatCutRetentionCertificate := ⟨(27/1000),(7/250),(671181424022596927/6843362511200915649309),(166134015847177457/250000000000000000),4,(19618621907153385667169754882806871/8306700792358872850000000000000000),false,MergedCutProfiles.Batch654.profile26162,(fun _ => MergedCutProfiles.Batch654.profile26162)⟩
theorem profilesValid4569 : retention4569.ProfilesValid := by
  exact MergedCutProfiles.Batch654.valid26162
theorem numericValid4569 : retention4569.NumericValid := by decide +kernel
def certificate4569 : RatCutBinCertificate := ⟨⟨retention4569,(1776840848995079283/1000000000000000000),(1358828718451041/40000000000000000),(2348368801580123351/250000000000000000),(64604278686172635417061/1000000000000000000),(2336079470918825667/1000000000000000000)⟩,(999973361876516047/1000000000000000000),(871594114612382723/1000000000000000000),(4310730646371333/500000000000000000),(1031996799538613/250000000000000000)⟩
theorem valid4569 : certificate4569.Valid := by decide +kernel
theorem sound4569 : certificate4569.Sound := rat_cut_bin_certificate_sound certificate4569 profilesValid4569 numericValid4569 valid4569

def retention4570 : RatCutRetentionCertificate := ⟨(27/1000),(7/250),(1071382370955725183/6843362511200915649309),(671181424022596927/1000000000000000000),4,(397000684441891130241230138552127933/167795356005649231750000000000000000),false,MergedCutProfiles.Batch654.profile26163,(fun _ => MergedCutProfiles.Batch654.profile26163)⟩
theorem profilesValid4570 : retention4570.ProfilesValid := by
  exact MergedCutProfiles.Batch654.valid26163
theorem numericValid4570 : retention4570.NumericValid := by decide +kernel
def certificate4570 : RatCutBinCertificate := ⟨⟨retention4570,(1776840848995079283/1000000000000000000),(1358828718451041/40000000000000000),(2348368801580123351/250000000000000000),(64604278686172635417061/1000000000000000000),(585069542080968221/250000000000000000)⟩,(999973361876516047/1000000000000000000),(8675439369477319/10000000000000000),(9187507912841199/1000000000000000000),(4413375541263543/1000000000000000000)⟩
theorem valid4570 : certificate4570.Valid := by decide +kernel
theorem sound4570 : certificate4570.Sound := rat_cut_bin_certificate_sound certificate4570 profilesValid4570 numericValid4570 valid4570

def retention4571 : RatCutRetentionCertificate := ⟨(27/1000),(7/250),(23653300126867139171/6843362511200915649309),(1071382370955725183/1000000000000000000),(63/20),(4035413826857761074572004124695938819999/1714211793529160292800000000000000000000),false,MergedCutProfiles.Batch654.profile26164,(fun _ => MergedCutProfiles.Batch654.profile26164)⟩
theorem profilesValid4571 : retention4571.ProfilesValid := by
  exact MergedCutProfiles.Batch654.valid26164
theorem numericValid4571 : retention4571.NumericValid := by decide +kernel
def certificate4571 : RatCutBinCertificate := ⟨⟨retention4571,(1776840848995079283/1000000000000000000),(1358828718451041/40000000000000000),(2348368801580123351/250000000000000000),(64604278686172635417061/1000000000000000000),(583462911662929629/250000000000000000)⟩,(999973361876516047/1000000000000000000),(388399498317771921/500000000000000000),(27002042617238781/1000000000000000000),(16404050093854679/1000000000000000000)⟩
theorem valid4571 : certificate4571.Valid := by decide +kernel
theorem sound4571 : certificate4571.Sound := rat_cut_bin_certificate_sound certificate4571 profilesValid4571 numericValid4571 valid4571

def certificates : List RatCutBinCertificate := [certificate4560,certificate4561,certificate4562,certificate4563,certificate4564,certificate4565,certificate4566,certificate4567,certificate4568,certificate4569,certificate4570,certificate4571]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4560,List.forall_mem_cons.mpr ⟨sound4561,List.forall_mem_cons.mpr ⟨sound4562,List.forall_mem_cons.mpr ⟨sound4563,List.forall_mem_cons.mpr ⟨sound4564,List.forall_mem_cons.mpr ⟨sound4565,List.forall_mem_cons.mpr ⟨sound4566,List.forall_mem_cons.mpr ⟨sound4567,List.forall_mem_cons.mpr ⟨sound4568,List.forall_mem_cons.mpr ⟨sound4569,List.forall_mem_cons.mpr ⟨sound4570,List.forall_mem_cons.mpr ⟨sound4571,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch380
