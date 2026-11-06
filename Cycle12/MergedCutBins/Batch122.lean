import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch237
import Cycle12.MergedCutProfiles.Batch238
import Cycle12.MergedCutProfiles.Batch239

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch122

def retention1464 : RatCutRetentionCertificate := ⟨(493/8000),(247/4000),(2736165209477070011/5831475237792161906),(3462494706945550139/1000000000000000000),(6/5),(364825956730449114836286307131410894559/346249470694555013900000000000000000000),false,MergedCutProfiles.Batch237.profile9505,(fun _ => MergedCutProfiles.Batch237.profile9505)⟩
theorem profilesValid1464 : retention1464.ProfilesValid := by
  exact MergedCutProfiles.Batch237.valid9505
theorem numericValid1464 : retention1464.NumericValid := by decide +kernel
def certificate1464 : RatCutBinCertificate := ⟨⟨retention1464,(2665695384042141187/1000000000000000000),(97658477082830291/500000000000000000),(4085881496331823223/250000000000000000),(38152244869143192641/200000000000000000),(63463298617317269/62500000000000000)⟩,(988710343330126601/1000000000000000000),(98494543011813759/250000000000000000),(59761349422208921/250000000000000000),(41485901301696307/250000000000000000)⟩
theorem valid1464 : certificate1464.Valid := by decide +kernel
theorem sound1464 : certificate1464.Sound := rat_cut_bin_certificate_sound certificate1464 profilesValid1464 numericValid1464 valid1464

def retention1465 : RatCutRetentionCertificate := ⟨(493/8000),(247/4000),(2875737133894372349/5831475237792161906),(2736165209477070011/500000000000000000),(11/10),(137541557091608940026910616427255907461/136808260473853500550000000000000000000),false,MergedCutProfiles.Batch237.profile9506,(fun _ => MergedCutProfiles.Batch237.profile9506)⟩
theorem profilesValid1465 : retention1465.ProfilesValid := by
  exact MergedCutProfiles.Batch237.valid9506
theorem numericValid1465 : retention1465.NumericValid := by decide +kernel
def certificate1465 : RatCutBinCertificate := ⟨⟨retention1465,(2665695384042141187/1000000000000000000),(97658477082830291/500000000000000000),(4085881496331823223/250000000000000000),(38152244869143192641/200000000000000000),(970311384982965089/1000000000000000000)⟩,(988710343330126601/1000000000000000000),(412290813333556081/1000000000000000000),(44481550180185181/200000000000000000),(169024903345438997/1000000000000000000)⟩
theorem valid1465 : certificate1465.Valid := by decide +kernel
theorem sound1465 : certificate1465.Sound := rat_cut_bin_certificate_sound certificate1465 profilesValid1465 numericValid1465 valid1465

def retention1466 : RatCutRetentionCertificate := ⟨(493/8000),(247/4000),(5808989010466632145/11662950475584323812),(2875737133894372349/500000000000000000),(21/20),(2261659211975526961364321995884708746039/2300589707115497879200000000000000000000),false,MergedCutProfiles.Batch237.profile9507,(fun _ => MergedCutProfiles.Batch237.profile9507)⟩
theorem profilesValid1466 : retention1466.ProfilesValid := by
  exact MergedCutProfiles.Batch237.valid9507
theorem numericValid1466 : retention1466.NumericValid := by decide +kernel
def certificate1466 : RatCutBinCertificate := ⟨⟨retention1466,(2665695384042141187/1000000000000000000),(97658477082830291/500000000000000000),(4085881496331823223/250000000000000000),(38152244869143192641/200000000000000000),(949622528373654419/1000000000000000000)⟩,(988710343330126601/1000000000000000000),(421273146064227909/1000000000000000000),(53636633939557357/250000000000000000),(83352754020628161/500000000000000000)⟩
theorem valid1466 : certificate1466.Valid := by decide +kernel
theorem sound1466 : certificate1466.Sound := rat_cut_bin_certificate_sound certificate1466 profilesValid1466 numericValid1466 valid1466

def retention1467 : RatCutRetentionCertificate := ⟨(493/8000),(247/4000),(1/2),(1161797802093326429/200000000000000000),(21/20),(364284394966901984259545591712075489759/371775296669864457280000000000000000000),false,MergedCutProfiles.Batch237.profile9504,(fun _ => MergedCutProfiles.Batch237.profile9504)⟩
theorem profilesValid1467 : retention1467.ProfilesValid := by
  exact MergedCutProfiles.Batch237.valid9504
theorem numericValid1467 : retention1467.NumericValid := by decide +kernel
def certificate1467 : RatCutBinCertificate := ⟨⟨retention1467,(2665695384042141187/1000000000000000000),(97658477082830291/500000000000000000),(4085881496331823223/250000000000000000),(38152244869143192641/200000000000000000),(946395544699098441/1000000000000000000)⟩,(988710343330126601/1000000000000000000),(52838698409742343/125000000000000000),(106653623385332091/500000000000000000),(165466477038809841/1000000000000000000)⟩
theorem valid1467 : certificate1467.Valid := by decide +kernel
theorem sound1467 : certificate1467.Sound := rat_cut_bin_certificate_sound certificate1467 profilesValid1467 numericValid1467 valid1467

def retention1468 : RatCutRetentionCertificate := ⟨(247/4000),(31/500),(1058333577403949283/11551178452882143772),(173470286226738963/200000000000000000),(53/20),(492257384523462878859/256000000000000000000),true,MergedCutProfiles.Batch237.profile9508,![MergedCutProfiles.Batch237.profile9508,MergedCutProfiles.Batch237.profile9509,MergedCutProfiles.Batch237.profile9510,MergedCutProfiles.Batch237.profile9511,MergedCutProfiles.Batch237.profile9512,MergedCutProfiles.Batch237.profile9513,MergedCutProfiles.Batch237.profile9514,MergedCutProfiles.Batch237.profile9515,MergedCutProfiles.Batch237.profile9516,MergedCutProfiles.Batch237.profile9517,MergedCutProfiles.Batch237.profile9518,MergedCutProfiles.Batch237.profile9519,MergedCutProfiles.Batch238.profile9520,MergedCutProfiles.Batch238.profile9521,MergedCutProfiles.Batch238.profile9522,MergedCutProfiles.Batch238.profile9523]⟩
theorem profilesValid1468 : retention1468.ProfilesValid := by
  change ∀ j : Fin 16, (retention1468.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch237.valid9508
  · exact MergedCutProfiles.Batch237.valid9509
  · exact MergedCutProfiles.Batch237.valid9510
  · exact MergedCutProfiles.Batch237.valid9511
  · exact MergedCutProfiles.Batch237.valid9512
  · exact MergedCutProfiles.Batch237.valid9513
  · exact MergedCutProfiles.Batch237.valid9514
  · exact MergedCutProfiles.Batch237.valid9515
  · exact MergedCutProfiles.Batch237.valid9516
  · exact MergedCutProfiles.Batch237.valid9517
  · exact MergedCutProfiles.Batch237.valid9518
  · exact MergedCutProfiles.Batch237.valid9519
  · exact MergedCutProfiles.Batch238.valid9520
  · exact MergedCutProfiles.Batch238.valid9521
  · exact MergedCutProfiles.Batch238.valid9522
  · exact MergedCutProfiles.Batch238.valid9523
theorem numericValid1468 : retention1468.NumericValid := by decide +kernel
def certificate1468 : RatCutBinCertificate := ⟨⟨retention1468,(584365333416809633/250000000000000000),(24651154762240763/125000000000000000),(4095364330316275257/250000000000000000),(189518456652147863977/1000000000000000000),(184827649621800309/100000000000000000)⟩,(990050235094895391/1000000000000000000),(346585788937361151/1000000000000000000),(143078438328183743/500000000000000000),(151275051433223337/1000000000000000000)⟩
theorem valid1468 : certificate1468.Valid := by decide +kernel
theorem sound1468 : certificate1468.Sound := rat_cut_bin_certificate_sound certificate1468 profilesValid1468 numericValid1468 valid1468

def retention1469 : RatCutRetentionCertificate := ⟨(247/4000),(31/500),(980658402740934131/5775589226441071886),(1058333577403949283/1000000000000000000),(11/5),(2184825445742701540383/1280000000000000000000),true,MergedCutProfiles.Batch238.profile9524,![MergedCutProfiles.Batch238.profile9524,MergedCutProfiles.Batch238.profile9525,MergedCutProfiles.Batch238.profile9526,MergedCutProfiles.Batch238.profile9527,MergedCutProfiles.Batch238.profile9528,MergedCutProfiles.Batch238.profile9529,MergedCutProfiles.Batch238.profile9520,MergedCutProfiles.Batch238.profile9530,MergedCutProfiles.Batch238.profile9531,MergedCutProfiles.Batch238.profile9532,MergedCutProfiles.Batch238.profile9533,MergedCutProfiles.Batch238.profile9534,MergedCutProfiles.Batch238.profile9535,MergedCutProfiles.Batch238.profile9536,MergedCutProfiles.Batch238.profile9537,MergedCutProfiles.Batch238.profile9538]⟩
theorem profilesValid1469 : retention1469.ProfilesValid := by
  change ∀ j : Fin 16, (retention1469.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch238.valid9524
  · exact MergedCutProfiles.Batch238.valid9525
  · exact MergedCutProfiles.Batch238.valid9526
  · exact MergedCutProfiles.Batch238.valid9527
  · exact MergedCutProfiles.Batch238.valid9528
  · exact MergedCutProfiles.Batch238.valid9529
  · exact MergedCutProfiles.Batch238.valid9520
  · exact MergedCutProfiles.Batch238.valid9530
  · exact MergedCutProfiles.Batch238.valid9531
  · exact MergedCutProfiles.Batch238.valid9532
  · exact MergedCutProfiles.Batch238.valid9533
  · exact MergedCutProfiles.Batch238.valid9534
  · exact MergedCutProfiles.Batch238.valid9535
  · exact MergedCutProfiles.Batch238.valid9536
  · exact MergedCutProfiles.Batch238.valid9537
  · exact MergedCutProfiles.Batch238.valid9538
theorem numericValid1469 : retention1469.NumericValid := by decide +kernel
def certificate1469 : RatCutBinCertificate := ⟨⟨retention1469,(584365333416809633/250000000000000000),(24651154762240763/125000000000000000),(4095364330316275257/250000000000000000),(189518456652147863977/1000000000000000000),(164495991559924823/100000000000000000)⟩,(990050235094895391/1000000000000000000),(361396592289122621/1000000000000000000),(270777228030237779/1000000000000000000),(75705325620997847/500000000000000000)⟩
theorem valid1469 : certificate1469.Valid := by decide +kernel
theorem sound1469 : certificate1469.Sound := rat_cut_bin_certificate_sound certificate1469 profilesValid1469 numericValid1469 valid1469

def retention1470 : RatCutRetentionCertificate := ⟨(247/4000),(31/500),(4095711990006937285/11551178452882143772),(980658402740934131/500000000000000000),(7/5),(816617901221007751247/640000000000000000000),true,MergedCutProfiles.Batch238.profile9539,![MergedCutProfiles.Batch238.profile9539,MergedCutProfiles.Batch238.profile9540,MergedCutProfiles.Batch238.profile9541,MergedCutProfiles.Batch238.profile9542,MergedCutProfiles.Batch238.profile9543,MergedCutProfiles.Batch238.profile9544,MergedCutProfiles.Batch238.profile9545,MergedCutProfiles.Batch238.profile9546,MergedCutProfiles.Batch238.profile9547,MergedCutProfiles.Batch238.profile9548,MergedCutProfiles.Batch238.profile9549,MergedCutProfiles.Batch238.profile9550,MergedCutProfiles.Batch238.profile9551,MergedCutProfiles.Batch238.profile9552,MergedCutProfiles.Batch238.profile9553,MergedCutProfiles.Batch238.profile9554]⟩
theorem profilesValid1470 : retention1470.ProfilesValid := by
  change ∀ j : Fin 16, (retention1470.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch238.valid9539
  · exact MergedCutProfiles.Batch238.valid9540
  · exact MergedCutProfiles.Batch238.valid9541
  · exact MergedCutProfiles.Batch238.valid9542
  · exact MergedCutProfiles.Batch238.valid9543
  · exact MergedCutProfiles.Batch238.valid9544
  · exact MergedCutProfiles.Batch238.valid9545
  · exact MergedCutProfiles.Batch238.valid9546
  · exact MergedCutProfiles.Batch238.valid9547
  · exact MergedCutProfiles.Batch238.valid9548
  · exact MergedCutProfiles.Batch238.valid9549
  · exact MergedCutProfiles.Batch238.valid9550
  · exact MergedCutProfiles.Batch238.valid9551
  · exact MergedCutProfiles.Batch238.valid9552
  · exact MergedCutProfiles.Batch238.valid9553
  · exact MergedCutProfiles.Batch238.valid9554
theorem numericValid1470 : retention1470.NumericValid := by decide +kernel
def certificate1470 : RatCutBinCertificate := ⟨⟨retention1470,(584365333416809633/250000000000000000),(24651154762240763/125000000000000000),(4095364330316275257/250000000000000000),(189518456652147863977/1000000000000000000),(1236554988944077917/1000000000000000000)⟩,(990050235094895391/1000000000000000000),(100700123794456077/250000000000000000),(46185237102886509/200000000000000000),(152521603434819191/1000000000000000000)⟩
theorem valid1470 : certificate1470.Valid := by decide +kernel
theorem sound1470 : certificate1470.Sound := rat_cut_bin_certificate_sound certificate1470 profilesValid1470 numericValid1470 valid1470

def retention1471 : RatCutRetentionCertificate := ⟨(247/4000),(31/500),(1352906813853256284/2887794613220535943),(819142398001387457/200000000000000000),1,(10385405847273842653/10240000000000000000),true,MergedCutProfiles.Batch238.profile9555,![MergedCutProfiles.Batch238.profile9555,MergedCutProfiles.Batch238.profile9556,MergedCutProfiles.Batch238.profile9557,MergedCutProfiles.Batch238.profile9558,MergedCutProfiles.Batch238.profile9559,MergedCutProfiles.Batch239.profile9560,MergedCutProfiles.Batch239.profile9561,MergedCutProfiles.Batch239.profile9562,MergedCutProfiles.Batch239.profile9563,MergedCutProfiles.Batch239.profile9564,MergedCutProfiles.Batch239.profile9565,MergedCutProfiles.Batch239.profile9566,MergedCutProfiles.Batch239.profile9567,MergedCutProfiles.Batch239.profile9568,MergedCutProfiles.Batch239.profile9569,MergedCutProfiles.Batch239.profile9570]⟩
theorem profilesValid1471 : retention1471.ProfilesValid := by
  change ∀ j : Fin 16, (retention1471.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch238.valid9555
  · exact MergedCutProfiles.Batch238.valid9556
  · exact MergedCutProfiles.Batch238.valid9557
  · exact MergedCutProfiles.Batch238.valid9558
  · exact MergedCutProfiles.Batch238.valid9559
  · exact MergedCutProfiles.Batch239.valid9560
  · exact MergedCutProfiles.Batch239.valid9561
  · exact MergedCutProfiles.Batch239.valid9562
  · exact MergedCutProfiles.Batch239.valid9563
  · exact MergedCutProfiles.Batch239.valid9564
  · exact MergedCutProfiles.Batch239.valid9565
  · exact MergedCutProfiles.Batch239.valid9566
  · exact MergedCutProfiles.Batch239.valid9567
  · exact MergedCutProfiles.Batch239.valid9568
  · exact MergedCutProfiles.Batch239.valid9569
  · exact MergedCutProfiles.Batch239.valid9570
theorem numericValid1471 : retention1471.NumericValid := by decide +kernel
def certificate1471 : RatCutBinCertificate := ⟨⟨retention1471,(584365333416809633/250000000000000000),(24651154762240763/125000000000000000),(4095364330316275257/250000000000000000),(189518456652147863977/1000000000000000000),(986052960334088109/1000000000000000000)⟩,(990050235094895391/1000000000000000000),(445418822959266643/1000000000000000000),(194352716623564211/1000000000000000000),(38182017546276919/250000000000000000)⟩
theorem valid1471 : certificate1471.Valid := by decide +kernel
theorem sound1471 : certificate1471.Sound := rat_cut_bin_certificate_sound certificate1471 profilesValid1471 numericValid1471 valid1471

def retention1472 : RatCutRetentionCertificate := ⟨(247/4000),(31/500),(5687674632834169047/11551178452882143772),(338226703463314071/62500000000000000),(11/10),(544640547071511428461017236948717007071/541162725541302513600000000000000000000),false,MergedCutProfiles.Batch239.profile9571,(fun _ => MergedCutProfiles.Batch239.profile9571)⟩
theorem profilesValid1472 : retention1472.ProfilesValid := by
  exact MergedCutProfiles.Batch239.valid9571
theorem numericValid1472 : retention1472.NumericValid := by decide +kernel
def certificate1472 : RatCutBinCertificate := ⟨⟨retention1472,(584365333416809633/250000000000000000),(24651154762240763/125000000000000000),(4095364330316275257/250000000000000000),(189518456652147863977/1000000000000000000),(975467513588294527/1000000000000000000)⟩,(990050235094895391/1000000000000000000),(436765331091878671/1000000000000000000),(2517945606011/12500000000000),(7689013220866671/50000000000000000)⟩
theorem valid1472 : certificate1472.Valid := by decide +kernel
theorem sound1472 : certificate1472.Sound := rat_cut_bin_certificate_sound certificate1472 profilesValid1472 numericValid1472 valid1472

def retention1473 : RatCutRetentionCertificate := ⟨(247/4000),(31/500),(2872275689581255369/5775589226441071886),(5687674632834169047/1000000000000000000),(11/10),(2271796580634041341682962385956779045311/2275069853133667618800000000000000000000),false,MergedCutProfiles.Batch239.profile9572,(fun _ => MergedCutProfiles.Batch239.profile9572)⟩
theorem profilesValid1473 : retention1473.ProfilesValid := by
  exact MergedCutProfiles.Batch239.valid9572
theorem numericValid1473 : retention1473.NumericValid := by decide +kernel
def certificate1473 : RatCutBinCertificate := ⟨⟨retention1473,(584365333416809633/250000000000000000),(24651154762240763/125000000000000000),(4095364330316275257/250000000000000000),(189518456652147863977/1000000000000000000),(120950305838076001/125000000000000000)⟩,(990050235094895391/1000000000000000000),(109565405656569123/250000000000000000),(50049690432094321/250000000000000000),(76361256473850081/500000000000000000)⟩
theorem valid1473 : certificate1473.Valid := by decide +kernel
theorem sound1473 : certificate1473.Sound := rat_cut_bin_certificate_sound certificate1473 profilesValid1473 numericValid1473 valid1473

def retention1474 : RatCutRetentionCertificate := ⟨(247/4000),(31/500),(1/2),(2872275689581255369/500000000000000000),(11/10),(570822901534075520780210112450169717799/574455137916251073800000000000000000000),false,MergedCutProfiles.Batch239.profile9573,(fun _ => MergedCutProfiles.Batch239.profile9573)⟩
theorem profilesValid1474 : retention1474.ProfilesValid := by
  exact MergedCutProfiles.Batch239.valid9573
theorem numericValid1474 : retention1474.NumericValid := by decide +kernel
def certificate1474 : RatCutBinCertificate := ⟨⟨retention1474,(584365333416809633/250000000000000000),(24651154762240763/125000000000000000),(4095364330316275257/250000000000000000),(189518456652147863977/1000000000000000000),(962718330244982143/1000000000000000000)⟩,(990050235094895391/1000000000000000000),(88016870202846941/200000000000000000),(9934946494286483/50000000000000000),(151091812760445563/1000000000000000000)⟩
theorem valid1474 : certificate1474.Valid := by decide +kernel
theorem sound1474 : certificate1474.Sound := rat_cut_bin_certificate_sound certificate1474 profilesValid1474 numericValid1474 valid1474

def retention1475 : RatCutRetentionCertificate := ⟨(247/4000),(31/500),(1/2),64,1,(63852742112836476935397430048221728751/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch239.profile9573,(fun _ => MergedCutProfiles.Batch239.profile9573)⟩
theorem profilesValid1475 : retention1475.ProfilesValid := by
  exact MergedCutProfiles.Batch239.valid9573
theorem numericValid1475 : retention1475.NumericValid := by decide +kernel
def certificate1475 : RatCutBinCertificate := ⟨⟨retention1475,(584365333416809633/250000000000000000),(24651154762240763/125000000000000000),(4095364330316275257/250000000000000000),(189518456652147863977/1000000000000000000),(969558957881639401/1000000000000000000)⟩,(990050235094895391/1000000000000000000),(400764698831388449/1000000000000000000),(232782437916690869/1000000000000000000),(110047237945341701/500000000000000000)⟩
theorem valid1475 : certificate1475.Valid := by decide +kernel
theorem sound1475 : certificate1475.Sound := rat_cut_bin_certificate_sound certificate1475 profilesValid1475 numericValid1475 valid1475

def certificates : List RatCutBinCertificate := [certificate1464,certificate1465,certificate1466,certificate1467,certificate1468,certificate1469,certificate1470,certificate1471,certificate1472,certificate1473,certificate1474,certificate1475]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1464,List.forall_mem_cons.mpr ⟨sound1465,List.forall_mem_cons.mpr ⟨sound1466,List.forall_mem_cons.mpr ⟨sound1467,List.forall_mem_cons.mpr ⟨sound1468,List.forall_mem_cons.mpr ⟨sound1469,List.forall_mem_cons.mpr ⟨sound1470,List.forall_mem_cons.mpr ⟨sound1471,List.forall_mem_cons.mpr ⟨sound1472,List.forall_mem_cons.mpr ⟨sound1473,List.forall_mem_cons.mpr ⟨sound1474,List.forall_mem_cons.mpr ⟨sound1475,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch122
