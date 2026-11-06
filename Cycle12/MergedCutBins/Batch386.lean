import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch339
import Cycle12.MergedCutProfiles.Batch340
import Cycle12.MergedCutProfiles.Batch466
import Cycle12.MergedCutProfiles.Batch467
import Cycle12.MergedCutProfiles.Batch468
import Cycle12.MergedCutProfiles.Batch597
import Cycle12.MergedCutProfiles.Batch598
import Cycle12.MergedCutProfiles.Batch657
import Cycle12.MergedCutProfiles.Batch658

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch386

def retention4632 : RatCutRetentionCertificate := ⟨(33/1000),(17/500),(606212330696377348/643076606777666988781),(1175616270227664461/1000000000000000000),(27/10),(1117061093875842799704551746952014616271/470246508091065784400000000000000000000),true,MergedCutProfiles.Batch657.profile26301,![MergedCutProfiles.Batch657.profile26301,MergedCutProfiles.Batch597.profile23912,MergedCutProfiles.Batch466.profile18650,MergedCutProfiles.Batch598.profile23923,MergedCutProfiles.Batch598.profile23934,MergedCutProfiles.Batch657.profile26312,MergedCutProfiles.Batch597.profile23917,MergedCutProfiles.Batch598.profile23925,MergedCutProfiles.Batch597.profile23919,MergedCutProfiles.Batch598.profile23920,MergedCutProfiles.Batch598.profile23921,MergedCutProfiles.Batch598.profile23926,MergedCutProfiles.Batch339.profile13585,MergedCutProfiles.Batch598.profile23930,MergedCutProfiles.Batch340.profile13607,MergedCutProfiles.Batch466.profile18654]⟩
theorem profilesValid4632 : retention4632.ProfilesValid := by
  change ∀ j : Fin 16, (retention4632.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch657.valid26301
  · exact MergedCutProfiles.Batch597.valid23912
  · exact MergedCutProfiles.Batch466.valid18650
  · exact MergedCutProfiles.Batch598.valid23923
  · exact MergedCutProfiles.Batch598.valid23934
  · exact MergedCutProfiles.Batch657.valid26312
  · exact MergedCutProfiles.Batch597.valid23917
  · exact MergedCutProfiles.Batch598.valid23925
  · exact MergedCutProfiles.Batch597.valid23919
  · exact MergedCutProfiles.Batch598.valid23920
  · exact MergedCutProfiles.Batch598.valid23921
  · exact MergedCutProfiles.Batch598.valid23926
  · exact MergedCutProfiles.Batch339.valid13585
  · exact MergedCutProfiles.Batch598.valid23930
  · exact MergedCutProfiles.Batch340.valid13607
  · exact MergedCutProfiles.Batch466.valid18654
theorem numericValid4632 : retention4632.NumericValid := by decide +kernel
def certificate4632 : RatCutBinCertificate := ⟨⟨retention4632,(4658249665960103/2500000000000000),(51337219122942991/1000000000000000000),(10227354861297963889/1000000000000000000),(46277353761204040216509/1000000000000000000),(470045334025459903/200000000000000000)⟩,(999961675194067381/1000000000000000000),(425362217663540617/1000000000000000000),(168825204509083/800000000000000),(9009610823177983/62500000000000000)⟩
theorem valid4632 : certificate4632.Valid := by decide +kernel
theorem sound4632 : certificate4632.Sound := rat_cut_bin_certificate_sound certificate4632 profilesValid4632 numericValid4632 valid4632

def retention4633 : RatCutRetentionCertificate := ⟨(33/1000),(17/500),(64000000000000000000/4501536247443668921467),(1060871578718660359/250000000000000000),(13/10),(937102529722060451408622401018907665239/424348631487464143600000000000000000000),true,MergedCutProfiles.Batch598.profile23931,![MergedCutProfiles.Batch598.profile23931,MergedCutProfiles.Batch598.profile23937,MergedCutProfiles.Batch340.profile13609,MergedCutProfiles.Batch657.profile26313,MergedCutProfiles.Batch339.profile13577,MergedCutProfiles.Batch339.profile13588,MergedCutProfiles.Batch467.profile18683,MergedCutProfiles.Batch339.profile13568,MergedCutProfiles.Batch339.profile13570,MergedCutProfiles.Batch657.profile26314,MergedCutProfiles.Batch657.profile26315,MergedCutProfiles.Batch339.profile13593,MergedCutProfiles.Batch657.profile26316,MergedCutProfiles.Batch657.profile26317,MergedCutProfiles.Batch657.profile26318,MergedCutProfiles.Batch657.profile26319]⟩
theorem profilesValid4633 : retention4633.ProfilesValid := by
  change ∀ j : Fin 16, (retention4633.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch598.valid23931
  · exact MergedCutProfiles.Batch598.valid23937
  · exact MergedCutProfiles.Batch340.valid13609
  · exact MergedCutProfiles.Batch657.valid26313
  · exact MergedCutProfiles.Batch339.valid13577
  · exact MergedCutProfiles.Batch339.valid13588
  · exact MergedCutProfiles.Batch467.valid18683
  · exact MergedCutProfiles.Batch339.valid13568
  · exact MergedCutProfiles.Batch339.valid13570
  · exact MergedCutProfiles.Batch657.valid26314
  · exact MergedCutProfiles.Batch657.valid26315
  · exact MergedCutProfiles.Batch339.valid13593
  · exact MergedCutProfiles.Batch657.valid26316
  · exact MergedCutProfiles.Batch657.valid26317
  · exact MergedCutProfiles.Batch657.valid26318
  · exact MergedCutProfiles.Batch657.valid26319
theorem numericValid4633 : retention4633.NumericValid := by decide +kernel
def certificate4633 : RatCutBinCertificate := ⟨⟨retention4633,(4658249665960103/2500000000000000),(51337219122942991/1000000000000000000),(10227354861297963889/1000000000000000000),(46277353761204040216509/1000000000000000000),(549043190585876033/250000000000000000)⟩,(999961675194067381/1000000000000000000),(288243664768507279/1000000000000000000),(88291108520340013/250000000000000000),(456730770785072751/1000000000000000000)⟩
theorem valid4633 : certificate4633.Valid := by decide +kernel
theorem sound4633 : certificate4633.Sound := rat_cut_bin_certificate_sound certificate4633 profilesValid4633 numericValid4633 valid4633

def retention4634 : RatCutRetentionCertificate := ⟨(33/1000),(17/500),(1/2),64,1,(255378512847706981515811673095846818951/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch340.profile13635,(fun _ => MergedCutProfiles.Batch340.profile13635)⟩
theorem profilesValid4634 : retention4634.ProfilesValid := by
  exact MergedCutProfiles.Batch340.valid13635
theorem numericValid4634 : retention4634.NumericValid := by decide +kernel
def certificate4634 : RatCutBinCertificate := ⟨⟨retention4634,(4658249665960103/2500000000000000),(51337219122942991/1000000000000000000),(10227354861297963889/1000000000000000000),(46277353761204040216509/1000000000000000000),(988219297705731253/1000000000000000000)⟩,(999961675194067381/1000000000000000000),(31739044648425641/62500000000000000),(148063601978727713/1000000000000000000),(28817757120598411/200000000000000000)⟩
theorem valid4634 : certificate4634.Valid := by decide +kernel
theorem sound4634 : certificate4634.Sound := rat_cut_bin_certificate_sound certificate4634 profilesValid4634 numericValid4634 valid4634

def retention4635 : RatCutRetentionCertificate := ⟨(33/1000),(17/500),(64000000000000000000/4501536247443668921467),(5340308616893727523/200000000000000000),1,(378120802654753870419265555058331699/170889875740599280736000000000000000),false,MergedCutProfiles.Batch658.profile26320,(fun _ => MergedCutProfiles.Batch658.profile26320)⟩
theorem profilesValid4635 : retention4635.ProfilesValid := by
  exact MergedCutProfiles.Batch658.valid26320
theorem numericValid4635 : retention4635.NumericValid := by decide +kernel
def certificate4635 : RatCutBinCertificate := ⟨⟨retention4635,(4394889223460103/2500000000000000),(51337219122942991/1000000000000000000),(10227354861297963889/1000000000000000000),(46277353761204040216509/1000000000000000000),(1101916743097200229/500000000000000000)⟩,(488263594698607/488281250000000),(1145424341396139/50000000000000000),(865220020775580143/1000000000000000000),(880677753230838617/500000000000000000)⟩
theorem valid4635 : certificate4635.Valid := by decide +kernel
theorem sound4635 : certificate4635.Sound := rat_cut_bin_certificate_sound certificate4635 profilesValid4635 numericValid4635 valid4635

def retention4636 : RatCutRetentionCertificate := ⟨(33/1000),(17/500),(1/2),64,1,(255378512847706981515811673095846818951/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch340.profile13635,(fun _ => MergedCutProfiles.Batch340.profile13635)⟩
theorem profilesValid4636 : retention4636.ProfilesValid := by
  exact MergedCutProfiles.Batch340.valid13635
theorem numericValid4636 : retention4636.NumericValid := by decide +kernel
def certificate4636 : RatCutBinCertificate := ⟨⟨retention4636,(4394889223460103/2500000000000000),(51337219122942991/1000000000000000000),(10227354861297963889/1000000000000000000),(46277353761204040216509/1000000000000000000),(988748083228973489/1000000000000000000)⟩,(488263594698607/488281250000000),(5106102479060679/100000000000000000),(785528029409009911/1000000000000000000),(191211186852542001/250000000000000000)⟩
theorem valid4636 : certificate4636.Valid := by decide +kernel
theorem sound4636 : certificate4636.Sound := rat_cut_bin_certificate_sound certificate4636 profilesValid4636 numericValid4636 valid4636

def retention4637 : RatCutRetentionCertificate := ⟨(33/1000),(17/500),(683734374045798823/4501536247443668921467),(169241181694504659/250000000000000000),4,(715311053286373823425638328235172479/300873211901341616000000000000000000),false,MergedCutProfiles.Batch658.profile26321,(fun _ => MergedCutProfiles.Batch658.profile26321)⟩
theorem profilesValid4637 : retention4637.ProfilesValid := by
  exact MergedCutProfiles.Batch658.valid26321
theorem numericValid4637 : retention4637.NumericValid := by decide +kernel
def certificate4637 : RatCutBinCertificate := ⟨⟨retention4637,(4518787778460103/2500000000000000),(51337219122942991/1000000000000000000),(10227354861297963889/1000000000000000000),(46277353761204040216509/1000000000000000000),(585289525057261623/250000000000000000)⟩,(999962822590667009/1000000000000000000),(861069939304274431/1000000000000000000),(1013160877872577/100000000000000000),(4875787239631419/1000000000000000000)⟩
theorem valid4637 : certificate4637.Valid := by decide +kernel
theorem sound4637 : certificate4637.Sound := rat_cut_bin_certificate_sound certificate4637 profilesValid4637 numericValid4637 valid4637

def retention4638 : RatCutRetentionCertificate := ⟨(33/1000),(17/500),(978265798653258317/4501536247443668921467),(683734374045798823/1000000000000000000),4,(6512201214162908347290857857382966623/2734937496183195292000000000000000000),false,MergedCutProfiles.Batch658.profile26322,(fun _ => MergedCutProfiles.Batch658.profile26322)⟩
theorem profilesValid4638 : retention4638.ProfilesValid := by
  exact MergedCutProfiles.Batch658.valid26322
theorem numericValid4638 : retention4638.NumericValid := by decide +kernel
def certificate4638 : RatCutBinCertificate := ⟨⟨retention4638,(4518787778460103/2500000000000000),(51337219122942991/1000000000000000000),(10227354861297963889/1000000000000000000),(46277353761204040216509/1000000000000000000),(2344823171261331533/1000000000000000000)⟩,(999962822590667009/1000000000000000000),(857382325207592843/1000000000000000000),(5345554001312681/500000000000000000),(516075803704989/100000000000000000)⟩
theorem valid4638 : certificate4638.Valid := by decide +kernel
theorem sound4638 : certificate4638.Sound := rat_cut_bin_certificate_sound certificate4638 profilesValid4638 numericValid4638 valid4638

def retention4639 : RatCutRetentionCertificate := ⟨(33/1000),(17/500),(12494778415834401140/4501536247443668921467),(978265798653258317/1000000000000000000),(67/20),(3711001961694136518061191553181603997319/1565225277845213307200000000000000000000),false,MergedCutProfiles.Batch658.profile26323,(fun _ => MergedCutProfiles.Batch658.profile26323)⟩
theorem profilesValid4639 : retention4639.ProfilesValid := by
  exact MergedCutProfiles.Batch658.valid26323
theorem numericValid4639 : retention4639.NumericValid := by decide +kernel
def certificate4639 : RatCutBinCertificate := ⟨⟨retention4639,(4518787778460103/2500000000000000),(51337219122942991/1000000000000000000),(10227354861297963889/1000000000000000000),(46277353761204040216509/1000000000000000000),(2340511410735795513/1000000000000000000)⟩,(999962822590667009/1000000000000000000),(31533143022057147/40000000000000000),(120875589884953/5000000000000000),(13921548875676761/1000000000000000000)⟩
theorem valid4639 : certificate4639.Valid := by decide +kernel
theorem sound4639 : certificate4639.Sound := rat_cut_bin_certificate_sound certificate4639 profilesValid4639 numericValid4639 valid4639

def retention4640 : RatCutRetentionCertificate := ⟨(33/1000),(17/500),(1/40),(624738920791720057/50000000000000000),(23/20),(109540919398756955535703088446938018279/49979113663337604560000000000000000000),false,MergedCutProfiles.Batch658.profile26324,(fun _ => MergedCutProfiles.Batch658.profile26324)⟩
theorem profilesValid4640 : retention4640.ProfilesValid := by
  exact MergedCutProfiles.Batch658.valid26324
theorem numericValid4640 : retention4640.NumericValid := by decide +kernel
def certificate4640 : RatCutBinCertificate := ⟨⟨retention4640,(4518787778460103/2500000000000000),(51337219122942991/1000000000000000000),(10227354861297963889/1000000000000000000),(46277353761204040216509/1000000000000000000),(2181299982049401957/1000000000000000000)⟩,(999962822590667009/1000000000000000000),(341852360132093269/500000000000000000),(56330815022962921/1000000000000000000),(94384005035476639/1000000000000000000)⟩
theorem valid4640 : certificate4640.Valid := by decide +kernel
theorem sound4640 : certificate4640.Sound := rat_cut_bin_certificate_sound certificate4640 profilesValid4640 numericValid4640 valid4640

def retention4641 : RatCutRetentionCertificate := ⟨(17/500),(7/200),(293883819027395747/2112975487760175059634),(285240739383341127/500000000000000000),4,(70732906625672306631/32000000000000000000),true,MergedCutProfiles.Batch658.profile26325,![MergedCutProfiles.Batch658.profile26325,MergedCutProfiles.Batch658.profile26326,MergedCutProfiles.Batch658.profile26327,MergedCutProfiles.Batch658.profile26328,MergedCutProfiles.Batch598.profile23940,MergedCutProfiles.Batch658.profile26329,MergedCutProfiles.Batch658.profile26330,MergedCutProfiles.Batch658.profile26331,MergedCutProfiles.Batch598.profile23952,MergedCutProfiles.Batch598.profile23941,MergedCutProfiles.Batch658.profile26332,MergedCutProfiles.Batch658.profile26332,MergedCutProfiles.Batch658.profile26333,MergedCutProfiles.Batch658.profile26334,MergedCutProfiles.Batch598.profile23942,MergedCutProfiles.Batch658.profile26335]⟩
theorem profilesValid4641 : retention4641.ProfilesValid := by
  change ∀ j : Fin 16, (retention4641.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch658.valid26325
  · exact MergedCutProfiles.Batch658.valid26326
  · exact MergedCutProfiles.Batch658.valid26327
  · exact MergedCutProfiles.Batch658.valid26328
  · exact MergedCutProfiles.Batch598.valid23940
  · exact MergedCutProfiles.Batch658.valid26329
  · exact MergedCutProfiles.Batch658.valid26330
  · exact MergedCutProfiles.Batch658.valid26331
  · exact MergedCutProfiles.Batch598.valid23952
  · exact MergedCutProfiles.Batch598.valid23941
  · exact MergedCutProfiles.Batch658.valid26332
  · exact MergedCutProfiles.Batch658.valid26332
  · exact MergedCutProfiles.Batch658.valid26333
  · exact MergedCutProfiles.Batch658.valid26334
  · exact MergedCutProfiles.Batch598.valid23942
  · exact MergedCutProfiles.Batch658.valid26335
theorem numericValid4641 : retention4641.NumericValid := by decide +kernel
def certificate4641 : RatCutBinCertificate := ⟨⟨retention4641,(466652432032111689/250000000000000000),(853665110250683/15625000000000000),(10377352996171688291/1000000000000000000),(5510348923315457000307/125000000000000000),(2171094090173409349/1000000000000000000)⟩,(999959830424307851/1000000000000000000),(355027565404488161/500000000000000000),(4681300101677609/100000000000000000),(10262739709175111/500000000000000000)⟩
theorem valid4641 : certificate4641.Valid := by decide +kernel
theorem sound4641 : certificate4641.Sound := rat_cut_bin_certificate_sound certificate4641 profilesValid4641 numericValid4641 valid4641

def retention4642 : RatCutRetentionCertificate := ⟨(17/500),(7/200),(290942840000000000/1056487743880087529817),(293883819027395747/500000000000000000),4,(287431877505506653947/128000000000000000000),true,MergedCutProfiles.Batch658.profile26326,![MergedCutProfiles.Batch658.profile26326,MergedCutProfiles.Batch658.profile26328,MergedCutProfiles.Batch658.profile26329,MergedCutProfiles.Batch658.profile26336,MergedCutProfiles.Batch598.profile23952,MergedCutProfiles.Batch658.profile26332,MergedCutProfiles.Batch658.profile26334,MergedCutProfiles.Batch658.profile26335,MergedCutProfiles.Batch658.profile26337,MergedCutProfiles.Batch598.profile23953,MergedCutProfiles.Batch467.profile18693,MergedCutProfiles.Batch658.profile26338,MergedCutProfiles.Batch598.profile23944,MergedCutProfiles.Batch658.profile26339,MergedCutProfiles.Batch598.profile23954,MergedCutProfiles.Batch598.profile23945]⟩
theorem profilesValid4642 : retention4642.ProfilesValid := by
  change ∀ j : Fin 16, (retention4642.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch658.valid26326
  · exact MergedCutProfiles.Batch658.valid26328
  · exact MergedCutProfiles.Batch658.valid26329
  · exact MergedCutProfiles.Batch658.valid26336
  · exact MergedCutProfiles.Batch598.valid23952
  · exact MergedCutProfiles.Batch658.valid26332
  · exact MergedCutProfiles.Batch658.valid26334
  · exact MergedCutProfiles.Batch658.valid26335
  · exact MergedCutProfiles.Batch658.valid26337
  · exact MergedCutProfiles.Batch598.valid23953
  · exact MergedCutProfiles.Batch467.valid18693
  · exact MergedCutProfiles.Batch658.valid26338
  · exact MergedCutProfiles.Batch598.valid23944
  · exact MergedCutProfiles.Batch658.valid26339
  · exact MergedCutProfiles.Batch598.valid23954
  · exact MergedCutProfiles.Batch598.valid23945
theorem numericValid4642 : retention4642.NumericValid := by decide +kernel
def certificate4642 : RatCutBinCertificate := ⟨⟨retention4642,(466652432032111689/250000000000000000),(853665110250683/15625000000000000),(10377352996171688291/1000000000000000000),(5510348923315457000307/125000000000000000),(1103126150880405673/500000000000000000)⟩,(999959830424307851/1000000000000000000),(684782268823786839/1000000000000000000),(1747560885531541/31250000000000000),(4996430930553769/200000000000000000)⟩
theorem valid4642 : certificate4642.Valid := by decide +kernel
theorem sound4642 : certificate4642.Sound := rat_cut_bin_certificate_sound certificate4642 profilesValid4642 numericValid4642 valid4642

def retention4643 : RatCutRetentionCertificate := ⟨(17/500),(7/200),(580089842866336918/1056487743880087529817),(7273571/6250000),(11/4),(11135588443579811708032417578370456031/4655085440000000000000000000000000000),true,MergedCutProfiles.Batch658.profile26340,![MergedCutProfiles.Batch658.profile26340,MergedCutProfiles.Batch658.profile26336,MergedCutProfiles.Batch658.profile26332,MergedCutProfiles.Batch598.profile23942,MergedCutProfiles.Batch598.profile23953,MergedCutProfiles.Batch658.profile26338,MergedCutProfiles.Batch658.profile26339,MergedCutProfiles.Batch598.profile23945,MergedCutProfiles.Batch598.profile23946,MergedCutProfiles.Batch468.profile18721,MergedCutProfiles.Batch658.profile26341,MergedCutProfiles.Batch658.profile26342,MergedCutProfiles.Batch598.profile23948,MergedCutProfiles.Batch658.profile26343,MergedCutProfiles.Batch598.profile23956,MergedCutProfiles.Batch340.profile13638]⟩
theorem profilesValid4643 : retention4643.ProfilesValid := by
  change ∀ j : Fin 16, (retention4643.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch658.valid26340
  · exact MergedCutProfiles.Batch658.valid26336
  · exact MergedCutProfiles.Batch658.valid26332
  · exact MergedCutProfiles.Batch598.valid23942
  · exact MergedCutProfiles.Batch598.valid23953
  · exact MergedCutProfiles.Batch658.valid26338
  · exact MergedCutProfiles.Batch658.valid26339
  · exact MergedCutProfiles.Batch598.valid23945
  · exact MergedCutProfiles.Batch598.valid23946
  · exact MergedCutProfiles.Batch468.valid18721
  · exact MergedCutProfiles.Batch658.valid26341
  · exact MergedCutProfiles.Batch658.valid26342
  · exact MergedCutProfiles.Batch598.valid23948
  · exact MergedCutProfiles.Batch658.valid26343
  · exact MergedCutProfiles.Batch598.valid23956
  · exact MergedCutProfiles.Batch340.valid13638
theorem numericValid4643 : retention4643.NumericValid := by decide +kernel
def certificate4643 : RatCutBinCertificate := ⟨⟨retention4643,(466652432032111689/250000000000000000),(853665110250683/15625000000000000),(10377352996171688291/1000000000000000000),(5510348923315457000307/125000000000000000),(473021792528604887/200000000000000000)⟩,(999959830424307851/1000000000000000000),(426112794559450969/1000000000000000000),(210390578023065091/1000000000000000000),(142611687916044837/1000000000000000000)⟩
theorem valid4643 : certificate4643.Valid := by decide +kernel
theorem sound4643 : certificate4643.Sound := rat_cut_bin_certificate_sound certificate4643 profilesValid4643 numericValid4643 valid4643

def certificates : List RatCutBinCertificate := [certificate4632,certificate4633,certificate4634,certificate4635,certificate4636,certificate4637,certificate4638,certificate4639,certificate4640,certificate4641,certificate4642,certificate4643]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4632,List.forall_mem_cons.mpr ⟨sound4633,List.forall_mem_cons.mpr ⟨sound4634,List.forall_mem_cons.mpr ⟨sound4635,List.forall_mem_cons.mpr ⟨sound4636,List.forall_mem_cons.mpr ⟨sound4637,List.forall_mem_cons.mpr ⟨sound4638,List.forall_mem_cons.mpr ⟨sound4639,List.forall_mem_cons.mpr ⟨sound4640,List.forall_mem_cons.mpr ⟨sound4641,List.forall_mem_cons.mpr ⟨sound4642,List.forall_mem_cons.mpr ⟨sound4643,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch386
