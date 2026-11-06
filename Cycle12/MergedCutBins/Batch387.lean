import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch063
import Cycle12.MergedCutProfiles.Batch064
import Cycle12.MergedCutProfiles.Batch341
import Cycle12.MergedCutProfiles.Batch342
import Cycle12.MergedCutProfiles.Batch467
import Cycle12.MergedCutProfiles.Batch599
import Cycle12.MergedCutProfiles.Batch658
import Cycle12.MergedCutProfiles.Batch659
import Cycle12.MergedCutProfiles.Batch660

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch387

def retention4644 : RatCutRetentionCertificate := ⟨(17/500),(7/200),(16000000000000000000/1056487743880087529817),(290044921433168459/125000000000000000),(7/4),(71402123411566583537/32000000000000000000),true,MergedCutProfiles.Batch658.profile26344,![MergedCutProfiles.Batch658.profile26344,MergedCutProfiles.Batch599.profile23964,MergedCutProfiles.Batch658.profile26345,MergedCutProfiles.Batch341.profile13644,MergedCutProfiles.Batch467.profile18719,MergedCutProfiles.Batch341.profile13672,MergedCutProfiles.Batch658.profile26346,MergedCutProfiles.Batch341.profile13651,MergedCutProfiles.Batch658.profile26347,MergedCutProfiles.Batch341.profile13666,MergedCutProfiles.Batch658.profile26348,MergedCutProfiles.Batch341.profile13677,MergedCutProfiles.Batch342.profile13688,MergedCutProfiles.Batch658.profile26349,MergedCutProfiles.Batch658.profile26350,MergedCutProfiles.Batch658.profile26351]⟩
theorem profilesValid4644 : retention4644.ProfilesValid := by
  change ∀ j : Fin 16, (retention4644.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch658.valid26344
  · exact MergedCutProfiles.Batch599.valid23964
  · exact MergedCutProfiles.Batch658.valid26345
  · exact MergedCutProfiles.Batch341.valid13644
  · exact MergedCutProfiles.Batch467.valid18719
  · exact MergedCutProfiles.Batch341.valid13672
  · exact MergedCutProfiles.Batch658.valid26346
  · exact MergedCutProfiles.Batch341.valid13651
  · exact MergedCutProfiles.Batch658.valid26347
  · exact MergedCutProfiles.Batch341.valid13666
  · exact MergedCutProfiles.Batch658.valid26348
  · exact MergedCutProfiles.Batch341.valid13677
  · exact MergedCutProfiles.Batch342.valid13688
  · exact MergedCutProfiles.Batch658.valid26349
  · exact MergedCutProfiles.Batch658.valid26350
  · exact MergedCutProfiles.Batch658.valid26351
theorem numericValid4644 : retention4644.NumericValid := by decide +kernel
def certificate4644 : RatCutBinCertificate := ⟨⟨retention4644,(466652432032111689/250000000000000000),(853665110250683/15625000000000000),(10377352996171688291/1000000000000000000),(5510348923315457000307/125000000000000000),(2214118567380929979/1000000000000000000)⟩,(999959830424307851/1000000000000000000),(169810595931829579/500000000000000000),(293605803268470141/1000000000000000000),(283213068820124849/1000000000000000000)⟩
theorem valid4644 : certificate4644.Valid := by decide +kernel
theorem sound4644 : certificate4644.Sound := rat_cut_bin_certificate_sound certificate4644 profilesValid4644 numericValid4644 valid4644

def retention4645 : RatCutRetentionCertificate := ⟨(17/500),(7/200),(1/2),64,1,(15961201781755751449307002574243876199/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch342.profile13711,(fun _ => MergedCutProfiles.Batch342.profile13711)⟩
theorem profilesValid4645 : retention4645.ProfilesValid := by
  exact MergedCutProfiles.Batch342.valid13711
theorem numericValid4645 : retention4645.NumericValid := by decide +kernel
def certificate4645 : RatCutBinCertificate := ⟨⟨retention4645,(466652432032111689/250000000000000000),(853665110250683/15625000000000000),(10377352996171688291/1000000000000000000),(5510348923315457000307/125000000000000000),(987747806037135001/1000000000000000000)⟩,(999959830424307851/1000000000000000000),(510114324355233529/1000000000000000000),(4578664866669177/31250000000000000),(17814588852240843/125000000000000000)⟩
theorem valid4645 : certificate4645.Valid := by decide +kernel
theorem sound4645 : certificate4645.Sound := rat_cut_bin_certificate_sound certificate4645 profilesValid4645 numericValid4645 valid4645

def retention4646 : RatCutRetentionCertificate := ⟨(17/500),(7/200),(16000000000000000000/1056487743880087529817),(2720584017209755229/100000000000000000),1,(7510359293347475672696171270720349/3400730021512194036250000000000000),false,MergedCutProfiles.Batch658.profile26352,(fun _ => MergedCutProfiles.Batch658.profile26352)⟩
theorem profilesValid4646 : retention4646.ProfilesValid := by
  exact MergedCutProfiles.Batch658.valid26352
theorem numericValid4646 : retention4646.NumericValid := by decide +kernel
def certificate4646 : RatCutBinCertificate := ⟨⟨retention4646,(439240564032111689/250000000000000000),(853665110250683/15625000000000000),(10377352996171688291/1000000000000000000),(5510348923315457000307/125000000000000000),(439840997369389747/200000000000000000)⟩,(999962190050624809/1000000000000000000),(22624247569378921/1000000000000000000),(433036688102384703/500000000000000000),(440538557968670697/250000000000000000)⟩
theorem valid4646 : certificate4646.Valid := by decide +kernel
theorem sound4646 : certificate4646.Sound := rat_cut_bin_certificate_sound certificate4646 profilesValid4646 numericValid4646 valid4646

def retention4647 : RatCutRetentionCertificate := ⟨(17/500),(7/200),(1/2),64,1,(15961201781755751449307002574243876199/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch342.profile13711,(fun _ => MergedCutProfiles.Batch342.profile13711)⟩
theorem profilesValid4647 : retention4647.ProfilesValid := by
  exact MergedCutProfiles.Batch342.valid13711
theorem numericValid4647 : retention4647.NumericValid := by decide +kernel
def certificate4647 : RatCutBinCertificate := ⟨⟨retention4647,(439240564032111689/250000000000000000),(853665110250683/15625000000000000),(10377352996171688291/1000000000000000000),(5510348923315457000307/125000000000000000),(988325076780428281/1000000000000000000)⟩,(999962190050624809/1000000000000000000),(6292888752797983/125000000000000000),(12303881607957653/15625000000000000),(766390268242467493/1000000000000000000)⟩
theorem valid4647 : certificate4647.Valid := by decide +kernel
theorem sound4647 : certificate4647.Sound := rat_cut_bin_certificate_sound certificate4647 profilesValid4647 numericValid4647 valid4647

def retention4648 : RatCutRetentionCertificate := ⟨(17/500),(7/200),(57284022581748134/352162581293362509939),(680602248496017433/1000000000000000000),4,(6483401321256051549692988671265127503/2722408993984069732000000000000000000),false,MergedCutProfiles.Batch658.profile26353,(fun _ => MergedCutProfiles.Batch658.profile26353)⟩
theorem profilesValid4648 : retention4648.ProfilesValid := by
  exact MergedCutProfiles.Batch658.valid26353
theorem numericValid4648 : retention4648.NumericValid := by decide +kernel
def certificate4648 : RatCutBinCertificate := ⟨⟨retention4648,(453714475782111689/250000000000000000),(853665110250683/15625000000000000),(10377352996171688291/1000000000000000000),(5510348923315457000307/125000000000000000),(1171637422752441783/500000000000000000)⟩,(999960944129660347/1000000000000000000),(854729929408089663/1000000000000000000),(2220668531354511/200000000000000000),(5352477562668433/1000000000000000000)⟩
theorem valid4648 : certificate4648.Valid := by decide +kernel
theorem sound4648 : certificate4648.Sound := rat_cut_bin_certificate_sound certificate4648 profilesValid4648 numericValid4648 valid4648

def retention4649 : RatCutRetentionCertificate := ⟨(17/500),(7/200),(973784451190341487/4225950975520350119268),(85926033872622201/125000000000000000),4,(6557668901901922472859472783492220903/2749633083923910432000000000000000000),false,MergedCutProfiles.Batch658.profile26354,(fun _ => MergedCutProfiles.Batch658.profile26354)⟩
theorem profilesValid4649 : retention4649.ProfilesValid := by
  exact MergedCutProfiles.Batch658.valid26354
theorem numericValid4649 : retention4649.NumericValid := by decide +kernel
def certificate4649 : RatCutBinCertificate := ⟨⟨retention4649,(453714475782111689/250000000000000000),(853665110250683/15625000000000000),(10377352996171688291/1000000000000000000),(5510348923315457000307/125000000000000000),(1173352845796000143/500000000000000000)⟩,(999960944129660347/1000000000000000000),(106396869518171007/125000000000000000),(11668769009753179/1000000000000000000),(5641726302513767/1000000000000000000)⟩
theorem valid4649 : certificate4649.Valid := by decide +kernel
theorem sound4649 : certificate4649.Sound := rat_cut_bin_certificate_sound certificate4649 profilesValid4649 numericValid4649 valid4649

def retention4650 : RatCutRetentionCertificate := ⟨(17/500),(7/200),(11716726201468223047/4225950975520350119268),(973784451190341487/1000000000000000000),(67/20),(3695402046884790916760706252492789601279/1558055121904546379200000000000000000000),false,MergedCutProfiles.Batch658.profile26355,(fun _ => MergedCutProfiles.Batch658.profile26355)⟩
theorem profilesValid4650 : retention4650.ProfilesValid := by
  exact MergedCutProfiles.Batch658.valid26355
theorem numericValid4650 : retention4650.NumericValid := by decide +kernel
def certificate4650 : RatCutBinCertificate := ⟨⟨retention4650,(453714475782111689/250000000000000000),(853665110250683/15625000000000000),(10377352996171688291/1000000000000000000),(5510348923315457000307/125000000000000000),(233979569891744943/100000000000000000)⟩,(999960944129660347/1000000000000000000),(785690750388688617/1000000000000000000),(6201729313111837/250000000000000000),(14270208844333949/1000000000000000000)⟩
theorem valid4650 : certificate4650.Valid := by decide +kernel
theorem sound4650 : certificate4650.Sound := rat_cut_bin_certificate_sound certificate4650 profilesValid4650 numericValid4650 valid4650

def retention4651 : RatCutRetentionCertificate := ⟨(17/500),(7/200),(1/40),(11716726201468223047/1000000000000000000),(23/20),(41070732545487263470669368430387002294159/18746761922349156875200000000000000000000),false,MergedCutProfiles.Batch658.profile26356,(fun _ => MergedCutProfiles.Batch658.profile26356)⟩
theorem profilesValid4651 : retention4651.ProfilesValid := by
  exact MergedCutProfiles.Batch658.valid26356
theorem numericValid4651 : retention4651.NumericValid := by decide +kernel
def certificate4651 : RatCutBinCertificate := ⟨⟨retention4651,(453714475782111689/250000000000000000),(853665110250683/15625000000000000),(10377352996171688291/1000000000000000000),(5510348923315457000307/125000000000000000),(435965869516199351/200000000000000000)⟩,(999960944129660347/1000000000000000000),(341355685635317271/500000000000000000),(11341847445930491/200000000000000000),(47116004932639041/500000000000000000)⟩
theorem valid4651 : certificate4651.Valid := by decide +kernel
theorem sound4651 : certificate4651.Sound := rat_cut_bin_certificate_sound certificate4651 profilesValid4651 numericValid4651 valid4651

def retention4652 : RatCutRetentionCertificate := ⟨(7/200),(71/2000),(92126288446208056/585290714988716696065),(57230182315698993/100000000000000000),4,(70872406774273144809/32000000000000000000),true,MergedCutProfiles.Batch658.profile26357,![MergedCutProfiles.Batch658.profile26357,MergedCutProfiles.Batch658.profile26358,MergedCutProfiles.Batch658.profile26359,MergedCutProfiles.Batch659.profile26360,MergedCutProfiles.Batch659.profile26361,MergedCutProfiles.Batch659.profile26362,MergedCutProfiles.Batch659.profile26363,MergedCutProfiles.Batch659.profile26364,MergedCutProfiles.Batch659.profile26365,MergedCutProfiles.Batch659.profile26366,MergedCutProfiles.Batch659.profile26367,MergedCutProfiles.Batch659.profile26368,MergedCutProfiles.Batch659.profile26369,MergedCutProfiles.Batch659.profile26370,MergedCutProfiles.Batch659.profile26370,MergedCutProfiles.Batch659.profile26371]⟩
theorem profilesValid4652 : retention4652.ProfilesValid := by
  change ∀ j : Fin 16, (retention4652.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch658.valid26357
  · exact MergedCutProfiles.Batch658.valid26358
  · exact MergedCutProfiles.Batch658.valid26359
  · exact MergedCutProfiles.Batch659.valid26360
  · exact MergedCutProfiles.Batch659.valid26361
  · exact MergedCutProfiles.Batch659.valid26362
  · exact MergedCutProfiles.Batch659.valid26363
  · exact MergedCutProfiles.Batch659.valid26364
  · exact MergedCutProfiles.Batch659.valid26365
  · exact MergedCutProfiles.Batch659.valid26366
  · exact MergedCutProfiles.Batch659.valid26367
  · exact MergedCutProfiles.Batch659.valid26368
  · exact MergedCutProfiles.Batch659.valid26369
  · exact MergedCutProfiles.Batch659.valid26370
  · exact MergedCutProfiles.Batch659.valid26370
  · exact MergedCutProfiles.Batch659.valid26371
theorem numericValid4652 : retention4652.NumericValid := by decide +kernel
def certificate4652 : RatCutBinCertificate := ⟨⟨retention4652,(233818033493685491/125000000000000000),(14082027828820247/250000000000000000),(52653784351561313/5000000000000000),(432576998846285068239/10000000000000000),(1087370584167250637/500000000000000000)⟩,(124994890065598909/125000000000000000),(141814008639725627/200000000000000000),(23575495565097439/500000000000000000),(20714379380607641/1000000000000000000)⟩
theorem valid4652 : certificate4652.Valid := by decide +kernel
theorem sound4652 : certificate4652.Sound := rat_cut_bin_certificate_sound certificate4652 profilesValid4652 numericValid4652 valid4652

def retention4653 : RatCutRetentionCertificate := ⟨(7/200),(71/2000),(233384636200000000/819407000984203374491),(80610502390432049/125000000000000000),4,(9361566757886132917/4000000000000000000),true,MergedCutProfiles.Batch659.profile26372,![MergedCutProfiles.Batch659.profile26372,MergedCutProfiles.Batch659.profile26360,MergedCutProfiles.Batch659.profile26361,MergedCutProfiles.Batch659.profile26373,MergedCutProfiles.Batch659.profile26365,MergedCutProfiles.Batch659.profile26367,MergedCutProfiles.Batch659.profile26368,MergedCutProfiles.Batch659.profile26370,MergedCutProfiles.Batch659.profile26371,MergedCutProfiles.Batch659.profile26374,MergedCutProfiles.Batch659.profile26375,MergedCutProfiles.Batch659.profile26376,MergedCutProfiles.Batch659.profile26377,MergedCutProfiles.Batch659.profile26378,MergedCutProfiles.Batch659.profile26379,MergedCutProfiles.Batch659.profile26380]⟩
theorem profilesValid4653 : retention4653.ProfilesValid := by
  change ∀ j : Fin 16, (retention4653.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch659.valid26372
  · exact MergedCutProfiles.Batch659.valid26360
  · exact MergedCutProfiles.Batch659.valid26361
  · exact MergedCutProfiles.Batch659.valid26373
  · exact MergedCutProfiles.Batch659.valid26365
  · exact MergedCutProfiles.Batch659.valid26367
  · exact MergedCutProfiles.Batch659.valid26368
  · exact MergedCutProfiles.Batch659.valid26370
  · exact MergedCutProfiles.Batch659.valid26371
  · exact MergedCutProfiles.Batch659.valid26374
  · exact MergedCutProfiles.Batch659.valid26375
  · exact MergedCutProfiles.Batch659.valid26376
  · exact MergedCutProfiles.Batch659.valid26377
  · exact MergedCutProfiles.Batch659.valid26378
  · exact MergedCutProfiles.Batch659.valid26379
  · exact MergedCutProfiles.Batch659.valid26380
theorem numericValid4653 : retention4653.NumericValid := by decide +kernel
def certificate4653 : RatCutBinCertificate := ⟨⟨retention4653,(233818033493685491/125000000000000000),(14082027828820247/250000000000000000),(52653784351561313/5000000000000000),(432576998846285068239/10000000000000000),(1150185074336116157/500000000000000000)⟩,(124994890065598909/125000000000000000),(123838035030973839/200000000000000000),(21001364345924213/250000000000000000),(617216475974967/15625000000000000)⟩
theorem valid4653 : certificate4653.Valid := by decide +kernel
theorem sound4653 : certificate4653.Sound := rat_cut_bin_certificate_sound certificate4653 profilesValid4653 numericValid4653 valid4653

def retention4654 : RatCutRetentionCertificate := ⟨(7/200),(71/2000),(3866596875736044574/4097035004921016872455),(1166923181/1000000000),(11/4),(19078717543005995073/8000000000000000000),true,MergedCutProfiles.Batch659.profile26362,![MergedCutProfiles.Batch659.profile26362,MergedCutProfiles.Batch659.profile26368,MergedCutProfiles.Batch659.profile26374,MergedCutProfiles.Batch659.profile26377,MergedCutProfiles.Batch659.profile26381,MergedCutProfiles.Batch659.profile26382,MergedCutProfiles.Batch659.profile26383,MergedCutProfiles.Batch659.profile26384,MergedCutProfiles.Batch659.profile26385,MergedCutProfiles.Batch659.profile26386,MergedCutProfiles.Batch659.profile26387,MergedCutProfiles.Batch659.profile26388,MergedCutProfiles.Batch659.profile26389,MergedCutProfiles.Batch659.profile26390,MergedCutProfiles.Batch659.profile26391,MergedCutProfiles.Batch659.profile26392]⟩
theorem profilesValid4654 : retention4654.ProfilesValid := by
  change ∀ j : Fin 16, (retention4654.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch659.valid26362
  · exact MergedCutProfiles.Batch659.valid26368
  · exact MergedCutProfiles.Batch659.valid26374
  · exact MergedCutProfiles.Batch659.valid26377
  · exact MergedCutProfiles.Batch659.valid26381
  · exact MergedCutProfiles.Batch659.valid26382
  · exact MergedCutProfiles.Batch659.valid26383
  · exact MergedCutProfiles.Batch659.valid26384
  · exact MergedCutProfiles.Batch659.valid26385
  · exact MergedCutProfiles.Batch659.valid26386
  · exact MergedCutProfiles.Batch659.valid26387
  · exact MergedCutProfiles.Batch659.valid26388
  · exact MergedCutProfiles.Batch659.valid26389
  · exact MergedCutProfiles.Batch659.valid26390
  · exact MergedCutProfiles.Batch659.valid26391
  · exact MergedCutProfiles.Batch659.valid26392
theorem numericValid4654 : retention4654.NumericValid := by decide +kernel
def certificate4654 : RatCutBinCertificate := ⟨⟨retention4654,(233818033493685491/125000000000000000),(14082027828820247/250000000000000000),(52653784351561313/5000000000000000),(432576998846285068239/10000000000000000),(471464977260173921/200000000000000000)⟩,(124994890065598909/125000000000000000),(214071233338017257/500000000000000000),(8346561090035129/40000000000000000),(17644327209164247/125000000000000000)⟩
theorem valid4654 : certificate4654.Valid := by decide +kernel
theorem sound4654 : certificate4654.Sound := rat_cut_bin_certificate_sound certificate4654 profilesValid4654 numericValid4654 valid4654

def retention4655 : RatCutRetentionCertificate := ⟨(7/200),(71/2000),(12800000000000000000/819407000984203374491),(1933298437868022287/500000000000000000),(27/20),(3412899385530882681702262245951306849039/1546638750294417829600000000000000000000),true,MergedCutProfiles.Batch659.profile26393,![MergedCutProfiles.Batch659.profile26393,MergedCutProfiles.Batch659.profile26394,MergedCutProfiles.Batch659.profile26395,MergedCutProfiles.Batch659.profile26396,MergedCutProfiles.Batch659.profile26397,MergedCutProfiles.Batch063.profile2558,MergedCutProfiles.Batch659.profile26398,MergedCutProfiles.Batch659.profile26399,MergedCutProfiles.Batch660.profile26400,MergedCutProfiles.Batch660.profile26401,MergedCutProfiles.Batch064.profile2577,MergedCutProfiles.Batch064.profile2563,MergedCutProfiles.Batch660.profile26402,MergedCutProfiles.Batch660.profile26403,MergedCutProfiles.Batch660.profile26404,MergedCutProfiles.Batch660.profile26405]⟩
theorem profilesValid4655 : retention4655.ProfilesValid := by
  change ∀ j : Fin 16, (retention4655.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch659.valid26393
  · exact MergedCutProfiles.Batch659.valid26394
  · exact MergedCutProfiles.Batch659.valid26395
  · exact MergedCutProfiles.Batch659.valid26396
  · exact MergedCutProfiles.Batch659.valid26397
  · exact MergedCutProfiles.Batch063.valid2558
  · exact MergedCutProfiles.Batch659.valid26398
  · exact MergedCutProfiles.Batch659.valid26399
  · exact MergedCutProfiles.Batch660.valid26400
  · exact MergedCutProfiles.Batch660.valid26401
  · exact MergedCutProfiles.Batch064.valid2577
  · exact MergedCutProfiles.Batch064.valid2563
  · exact MergedCutProfiles.Batch660.valid26402
  · exact MergedCutProfiles.Batch660.valid26403
  · exact MergedCutProfiles.Batch660.valid26404
  · exact MergedCutProfiles.Batch660.valid26405
theorem numericValid4655 : retention4655.NumericValid := by decide +kernel
def certificate4655 : RatCutBinCertificate := ⟨⟨retention4655,(233818033493685491/125000000000000000),(14082027828820247/250000000000000000),(52653784351561313/5000000000000000),(432576998846285068239/10000000000000000),(1096574272109837027/500000000000000000)⟩,(124994890065598909/125000000000000000),(7423680439240621/25000000000000000),(342474247295262827/1000000000000000000),(424293475552687117/1000000000000000000)⟩
theorem valid4655 : certificate4655.Valid := by decide +kernel
theorem sound4655 : certificate4655.Sound := rat_cut_bin_certificate_sound certificate4655 profilesValid4655 numericValid4655 valid4655

def certificates : List RatCutBinCertificate := [certificate4644,certificate4645,certificate4646,certificate4647,certificate4648,certificate4649,certificate4650,certificate4651,certificate4652,certificate4653,certificate4654,certificate4655]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4644,List.forall_mem_cons.mpr ⟨sound4645,List.forall_mem_cons.mpr ⟨sound4646,List.forall_mem_cons.mpr ⟨sound4647,List.forall_mem_cons.mpr ⟨sound4648,List.forall_mem_cons.mpr ⟨sound4649,List.forall_mem_cons.mpr ⟨sound4650,List.forall_mem_cons.mpr ⟨sound4651,List.forall_mem_cons.mpr ⟨sound4652,List.forall_mem_cons.mpr ⟨sound4653,List.forall_mem_cons.mpr ⟨sound4654,List.forall_mem_cons.mpr ⟨sound4655,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch387
