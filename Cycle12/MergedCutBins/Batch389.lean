import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch068
import Cycle12.MergedCutProfiles.Batch069
import Cycle12.MergedCutProfiles.Batch070
import Cycle12.MergedCutProfiles.Batch344
import Cycle12.MergedCutProfiles.Batch345
import Cycle12.MergedCutProfiles.Batch346
import Cycle12.MergedCutProfiles.Batch469
import Cycle12.MergedCutProfiles.Batch470
import Cycle12.MergedCutProfiles.Batch599
import Cycle12.MergedCutProfiles.Batch600
import Cycle12.MergedCutProfiles.Batch661
import Cycle12.MergedCutProfiles.Batch662

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch389

def retention4668 : RatCutRetentionCertificate := ⟨(71/2000),(9/250),(64000000000000000000/3973596522288482282311),(6996548262667684657/250000000000000000),1,(12343138556915743650947850039775150803/5597238610134147725600000000000000000),false,MergedCutProfiles.Batch661.profile26460,(fun _ => MergedCutProfiles.Batch661.profile26460)⟩
theorem profilesValid4668 : retention4668.ProfilesValid := by
  exact MergedCutProfiles.Batch661.valid26460
theorem numericValid4668 : retention4668.NumericValid := by decide +kernel
def certificate4668 : RatCutBinCertificate := ⟨⟨retention4668,(1756763532182606451/1000000000000000000),(3628243259175483/62500000000000000),(1060876861835579491/100000000000000000),(21132766810810694409729/500000000000000000),(274450770302457549/125000000000000000)⟩,(999960776261404669/1000000000000000000),(22146826536255009/1000000000000000000),(867509046288586881/1000000000000000000),(353215500392669479/200000000000000000)⟩
theorem valid4668 : certificate4668.Valid := by decide +kernel
theorem sound4668 : certificate4668.Sound := rat_cut_bin_certificate_sound certificate4668 profilesValid4668 numericValid4668 valid4668

def retention4669 : RatCutRetentionCertificate := ⟨(71/2000),(9/250),(1/2),64,1,(3990318709263329641199665529711342191/4000000000000000000000000000000000000),false,MergedCutProfiles.Batch068.profile2737,(fun _ => MergedCutProfiles.Batch068.profile2737)⟩
theorem profilesValid4669 : retention4669.ProfilesValid := by
  exact MergedCutProfiles.Batch068.valid2737
theorem numericValid4669 : retention4669.NumericValid := by decide +kernel
def certificate4669 : RatCutBinCertificate := ⟨⟨retention4669,(1756763532182606451/1000000000000000000),(3628243259175483/62500000000000000),(1060876861835579491/100000000000000000),(21132766810810694409729/500000000000000000),(246991637361107463/250000000000000000)⟩,(999960776261404669/1000000000000000000),(6152246354948049/125000000000000000),(158093848118244749/200000000000000000),(769054360452418363/1000000000000000000)⟩
theorem valid4669 : certificate4669.Valid := by decide +kernel
theorem sound4669 : certificate4669.Sound := rat_cut_bin_certificate_sound certificate4669 profilesValid4669 numericValid4669 valid4669

def retention4670 : RatCutRetentionCertificate := ⟨(71/2000),(9/250),(692739269795201379/3973596522288482282311),(685880465143763741/1000000000000000000),4,(6550040719596032930539884102768131071/2743521860575054964000000000000000000),false,MergedCutProfiles.Batch661.profile26461,(fun _ => MergedCutProfiles.Batch661.profile26461)⟩
theorem profilesValid4670 : retention4670.ProfilesValid := by
  exact MergedCutProfiles.Batch661.valid26461
theorem numericValid4670 : retention4670.NumericValid := by decide +kernel
def certificate4670 : RatCutBinCertificate := ⟨⟨retention4670,(1826996479182606451/1000000000000000000),(3628243259175483/62500000000000000),(1060876861835579491/100000000000000000),(21132766810810694409729/500000000000000000),(73358352577947031/31250000000000000)⟩,(999959208147420603/1000000000000000000),(845089403379338049/1000000000000000000),(2534237381941007/200000000000000000),(1531402617663129/250000000000000000)⟩
theorem valid4670 : certificate4670.Valid := by decide +kernel
theorem sound4670 : certificate4670.Sound := rat_cut_bin_certificate_sound certificate4670 profilesValid4670 numericValid4670 valid4670

def retention4671 : RatCutRetentionCertificate := ⟨(71/2000),(9/250),(971620157230663662/3973596522288482282311),(692739269795201379/1000000000000000000),4,(331207561158069939344176169367742447/138547853959040275800000000000000000),false,MergedCutProfiles.Batch661.profile26462,(fun _ => MergedCutProfiles.Batch661.profile26462)⟩
theorem profilesValid4671 : retention4671.ProfilesValid := by
  exact MergedCutProfiles.Batch661.valid26462
theorem numericValid4671 : retention4671.NumericValid := by decide +kernel
def certificate4671 : RatCutBinCertificate := ⟨⟨retention4671,(1826996479182606451/1000000000000000000),(3628243259175483/62500000000000000),(1060876861835579491/100000000000000000),(21132766810810694409729/500000000000000000),(2350574547122601737/1000000000000000000)⟩,(999959208147420603/1000000000000000000),(841720120201174773/1000000000000000000),(13245006012588859/1000000000000000000),(1605301737234307/250000000000000000)⟩
theorem valid4671 : certificate4671.Valid := by decide +kernel
theorem sound4671 : certificate4671.Sound := rat_cut_bin_certificate_sound certificate4671 profilesValid4671 numericValid4671 valid4671

def retention4672 : RatCutRetentionCertificate := ⟨(71/2000),(9/250),(11234518574858263559/3973596522288482282311),(485810078615331831/500000000000000000),(67/20),(922152143075646250320035655114614171831/388648062892265464800000000000000000000),false,MergedCutProfiles.Batch661.profile26463,(fun _ => MergedCutProfiles.Batch661.profile26463)⟩
theorem profilesValid4672 : retention4672.ProfilesValid := by
  exact MergedCutProfiles.Batch661.valid26463
theorem numericValid4672 : retention4672.NumericValid := by decide +kernel
def certificate4672 : RatCutBinCertificate := ⟨⟨retention4672,(1826996479182606451/1000000000000000000),(3628243259175483/62500000000000000),(1060876861835579491/100000000000000000),(21132766810810694409729/500000000000000000),(2339226251568445627/1000000000000000000)⟩,(999959208147420603/1000000000000000000),(780847391561684609/1000000000000000000),(25990055824125491/1000000000000000000),(7470957524721269/500000000000000000)⟩
theorem valid4672 : certificate4672.Valid := by decide +kernel
theorem sound4672 : certificate4672.Sound := rat_cut_bin_certificate_sound certificate4672 profilesValid4672 numericValid4672 valid4672

def retention4673 : RatCutRetentionCertificate := ⟨(71/2000),(9/250),(1/40),(11234518574858263559/1000000000000000000),(23/20),(39380232910674253620989244304488928120311/17975229719773221694400000000000000000000),false,MergedCutProfiles.Batch661.profile26464,(fun _ => MergedCutProfiles.Batch661.profile26464)⟩
theorem profilesValid4673 : retention4673.ProfilesValid := by
  exact MergedCutProfiles.Batch661.valid26464
theorem numericValid4673 : retention4673.NumericValid := by decide +kernel
def certificate4673 : RatCutBinCertificate := ⟨⟨retention4673,(1826996479182606451/1000000000000000000),(3628243259175483/62500000000000000),(1060876861835579491/100000000000000000),(21132766810810694409729/500000000000000000),(435861695576658571/200000000000000000)⟩,(999959208147420603/1000000000000000000),(679933608600218681/1000000000000000000),(57775120940974409/1000000000000000000),(11934695856602947/125000000000000000)⟩
theorem valid4673 : certificate4673.Valid := by decide +kernel
theorem sound4673 : certificate4673.Sound := rat_cut_bin_certificate_sound certificate4673 profilesValid4673 numericValid4673 valid4673

def retention4674 : RatCutRetentionCertificate := ⟨(9/250),(37/1000),(585840629978078804/3741964644565124703121),(287148627574786199/500000000000000000),4,(71034582764446802363/32000000000000000000),true,MergedCutProfiles.Batch661.profile26465,![MergedCutProfiles.Batch661.profile26465,MergedCutProfiles.Batch661.profile26466,MergedCutProfiles.Batch661.profile26467,MergedCutProfiles.Batch661.profile26468,MergedCutProfiles.Batch599.profile23996,MergedCutProfiles.Batch661.profile26469,MergedCutProfiles.Batch661.profile26470,MergedCutProfiles.Batch661.profile26471,MergedCutProfiles.Batch661.profile26472,MergedCutProfiles.Batch599.profile23997,MergedCutProfiles.Batch661.profile26473,MergedCutProfiles.Batch661.profile26474,MergedCutProfiles.Batch661.profile26475,MergedCutProfiles.Batch661.profile26475,MergedCutProfiles.Batch599.profile23998,MergedCutProfiles.Batch661.profile26476]⟩
theorem profilesValid4674 : retention4674.ProfilesValid := by
  change ∀ j : Fin 16, (retention4674.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch661.valid26465
  · exact MergedCutProfiles.Batch661.valid26466
  · exact MergedCutProfiles.Batch661.valid26467
  · exact MergedCutProfiles.Batch661.valid26468
  · exact MergedCutProfiles.Batch599.valid23996
  · exact MergedCutProfiles.Batch661.valid26469
  · exact MergedCutProfiles.Batch661.valid26470
  · exact MergedCutProfiles.Batch661.valid26471
  · exact MergedCutProfiles.Batch661.valid26472
  · exact MergedCutProfiles.Batch599.valid23997
  · exact MergedCutProfiles.Batch661.valid26473
  · exact MergedCutProfiles.Batch661.valid26474
  · exact MergedCutProfiles.Batch661.valid26475
  · exact MergedCutProfiles.Batch661.valid26475
  · exact MergedCutProfiles.Batch599.valid23998
  · exact MergedCutProfiles.Batch661.valid26476
theorem numericValid4674 : retention4674.NumericValid := by decide +kernel
def certificate4674 : RatCutBinCertificate := ⟨⟨retention4674,(1873135570296729437/1000000000000000000),(61591158108543061/1000000000000000000),(10687671490383747969/1000000000000000000),(8040784305062615797027/200000000000000000),(435330497657864281/200000000000000000)⟩,(499978056851021901/500000000000000000),(17715128684339261/25000000000000000),(5913871899947291/125000000000000000),(2081323466603067/100000000000000000)⟩
theorem valid4674 : certificate4674.Valid := by decide +kernel
theorem sound4674 : certificate4674.Sound := rat_cut_bin_certificate_sound certificate4674 profilesValid4674 numericValid4674 valid4674

def retention4675 : RatCutRetentionCertificate := ⟨(9/250),(37/1000),(1174747019000000000/3741964644565124703121),(146460157494519701/250000000000000000),4,(28705382680477201041/12800000000000000000),true,MergedCutProfiles.Batch661.profile26466,![MergedCutProfiles.Batch661.profile26466,MergedCutProfiles.Batch661.profile26468,MergedCutProfiles.Batch661.profile26469,MergedCutProfiles.Batch661.profile26471,MergedCutProfiles.Batch599.profile23997,MergedCutProfiles.Batch661.profile26474,MergedCutProfiles.Batch599.profile23998,MergedCutProfiles.Batch661.profile26476,MergedCutProfiles.Batch661.profile26477,MergedCutProfiles.Batch599.profile23999,MergedCutProfiles.Batch661.profile26478,MergedCutProfiles.Batch469.profile18785,MergedCutProfiles.Batch600.profile24012,MergedCutProfiles.Batch661.profile26479,MergedCutProfiles.Batch600.profile24000,MergedCutProfiles.Batch662.profile26480]⟩
theorem profilesValid4675 : retention4675.ProfilesValid := by
  change ∀ j : Fin 16, (retention4675.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch661.valid26466
  · exact MergedCutProfiles.Batch661.valid26468
  · exact MergedCutProfiles.Batch661.valid26469
  · exact MergedCutProfiles.Batch661.valid26471
  · exact MergedCutProfiles.Batch599.valid23997
  · exact MergedCutProfiles.Batch661.valid26474
  · exact MergedCutProfiles.Batch599.valid23998
  · exact MergedCutProfiles.Batch661.valid26476
  · exact MergedCutProfiles.Batch661.valid26477
  · exact MergedCutProfiles.Batch599.valid23999
  · exact MergedCutProfiles.Batch661.valid26478
  · exact MergedCutProfiles.Batch469.valid18785
  · exact MergedCutProfiles.Batch600.valid24012
  · exact MergedCutProfiles.Batch661.valid26479
  · exact MergedCutProfiles.Batch600.valid24000
  · exact MergedCutProfiles.Batch662.valid26480
theorem numericValid4675 : retention4675.NumericValid := by decide +kernel
def certificate4675 : RatCutBinCertificate := ⟨⟨retention4675,(1873135570296729437/1000000000000000000),(61591158108543061/1000000000000000000),(10687671490383747969/1000000000000000000),(8040784305062615797027/200000000000000000),(68732181230625507/31250000000000000)⟩,(499978056851021901/500000000000000000),(691915501494216347/1000000000000000000),(13314485784592817/250000000000000000),(23717532527157833/1000000000000000000)⟩
theorem valid4675 : certificate4675.Valid := by decide +kernel
theorem sound4675 : certificate4675.Sound := rat_cut_bin_certificate_sound certificate4675 profilesValid4675 numericValid4675 valid4675

def retention4676 : RatCutRetentionCertificate := ⟨(9/250),(37/1000),(6841617852737934322/3741964644565124703121),(1174747019/1000000000),(27/10),(111051221960199047383096176450540479/46989880760000000000000000000000000),true,MergedCutProfiles.Batch661.profile26473,![MergedCutProfiles.Batch661.profile26473,MergedCutProfiles.Batch661.profile26478,MergedCutProfiles.Batch600.profile24001,MergedCutProfiles.Batch469.profile18786,MergedCutProfiles.Batch662.profile26481,MergedCutProfiles.Batch469.profile18787,MergedCutProfiles.Batch600.profile24007,MergedCutProfiles.Batch345.profile13817,MergedCutProfiles.Batch662.profile26482,MergedCutProfiles.Batch469.profile18789,MergedCutProfiles.Batch344.profile13794,MergedCutProfiles.Batch600.profile24011,MergedCutProfiles.Batch068.profile2757,MergedCutProfiles.Batch662.profile26483,MergedCutProfiles.Batch662.profile26484,MergedCutProfiles.Batch345.profile13831]⟩
theorem profilesValid4676 : retention4676.ProfilesValid := by
  change ∀ j : Fin 16, (retention4676.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch661.valid26473
  · exact MergedCutProfiles.Batch661.valid26478
  · exact MergedCutProfiles.Batch600.valid24001
  · exact MergedCutProfiles.Batch469.valid18786
  · exact MergedCutProfiles.Batch662.valid26481
  · exact MergedCutProfiles.Batch469.valid18787
  · exact MergedCutProfiles.Batch600.valid24007
  · exact MergedCutProfiles.Batch345.valid13817
  · exact MergedCutProfiles.Batch662.valid26482
  · exact MergedCutProfiles.Batch469.valid18789
  · exact MergedCutProfiles.Batch344.valid13794
  · exact MergedCutProfiles.Batch600.valid24011
  · exact MergedCutProfiles.Batch068.valid2757
  · exact MergedCutProfiles.Batch662.valid26483
  · exact MergedCutProfiles.Batch662.valid26484
  · exact MergedCutProfiles.Batch345.valid13831
theorem numericValid4676 : retention4676.NumericValid := by decide +kernel
def certificate4676 : RatCutBinCertificate := ⟨⟨retention4676,(1873135570296729437/1000000000000000000),(61591158108543061/1000000000000000000),(10687671490383747969/1000000000000000000),(8040784305062615797027/200000000000000000),(1167077743532711679/500000000000000000)⟩,(499978056851021901/500000000000000000),(27013327365151973/62500000000000000),(20523015451288307/100000000000000000),(13941449333590693/100000000000000000)⟩
theorem valid4676 : certificate4676.Valid := by decide +kernel
theorem sound4676 : certificate4676.Sound := rat_cut_bin_certificate_sound certificate4676 profilesValid4676 numericValid4676 valid4676

def retention4677 : RatCutRetentionCertificate := ⟨(9/250),(37/1000),(64000000000000000000/3741964644565124703121),(3420808926368967161/500000000000000000),(23/20),(1404741996319106133937/640000000000000000000),true,MergedCutProfiles.Batch662.profile26485,![MergedCutProfiles.Batch662.profile26485,MergedCutProfiles.Batch662.profile26486,MergedCutProfiles.Batch662.profile26487,MergedCutProfiles.Batch469.profile18797,MergedCutProfiles.Batch345.profile13822,MergedCutProfiles.Batch068.profile2745,MergedCutProfiles.Batch345.profile13802,MergedCutProfiles.Batch662.profile26488,MergedCutProfiles.Batch470.profile18804,MergedCutProfiles.Batch600.profile24020,MergedCutProfiles.Batch346.profile13841,MergedCutProfiles.Batch346.profile13842,MergedCutProfiles.Batch069.profile2793,MergedCutProfiles.Batch662.profile26489,MergedCutProfiles.Batch069.profile2766,MergedCutProfiles.Batch662.profile26490]⟩
theorem profilesValid4677 : retention4677.ProfilesValid := by
  change ∀ j : Fin 16, (retention4677.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch662.valid26485
  · exact MergedCutProfiles.Batch662.valid26486
  · exact MergedCutProfiles.Batch662.valid26487
  · exact MergedCutProfiles.Batch469.valid18797
  · exact MergedCutProfiles.Batch345.valid13822
  · exact MergedCutProfiles.Batch068.valid2745
  · exact MergedCutProfiles.Batch345.valid13802
  · exact MergedCutProfiles.Batch662.valid26488
  · exact MergedCutProfiles.Batch470.valid18804
  · exact MergedCutProfiles.Batch600.valid24020
  · exact MergedCutProfiles.Batch346.valid13841
  · exact MergedCutProfiles.Batch346.valid13842
  · exact MergedCutProfiles.Batch069.valid2793
  · exact MergedCutProfiles.Batch662.valid26489
  · exact MergedCutProfiles.Batch069.valid2766
  · exact MergedCutProfiles.Batch662.valid26490
theorem numericValid4677 : retention4677.NumericValid := by decide +kernel
def certificate4677 : RatCutBinCertificate := ⟨⟨retention4677,(1873135570296729437/1000000000000000000),(61591158108543061/1000000000000000000),(10687671490383747969/1000000000000000000),(8040784305062615797027/200000000000000000),(545623908992231279/250000000000000000)⟩,(499978056851021901/500000000000000000),(268581337719563663/1000000000000000000),(378288605644201337/1000000000000000000),(578379121761778671/1000000000000000000)⟩
theorem valid4677 : certificate4677.Valid := by decide +kernel
theorem sound4677 : certificate4677.Sound := rat_cut_bin_certificate_sound certificate4677 profilesValid4677 numericValid4677 valid4677

def retention4678 : RatCutRetentionCertificate := ⟨(9/250),(37/1000),(1/2),64,1,(15961296343634275519387494158967405759/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch070.profile2821,(fun _ => MergedCutProfiles.Batch070.profile2821)⟩
theorem profilesValid4678 : retention4678.ProfilesValid := by
  exact MergedCutProfiles.Batch070.valid2821
theorem numericValid4678 : retention4678.NumericValid := by decide +kernel
def certificate4678 : RatCutBinCertificate := ⟨⟨retention4678,(1873135570296729437/1000000000000000000),(61591158108543061/1000000000000000000),(10687671490383747969/1000000000000000000),(8040784305062615797027/200000000000000000),(493393236321301431/500000000000000000)⟩,(499978056851021901/500000000000000000),(514724688662480209/1000000000000000000),(560291884337443/3906250000000000),(69692037925846457/500000000000000000)⟩
theorem valid4678 : certificate4678.Valid := by decide +kernel
theorem sound4678 : certificate4678.Sound := rat_cut_bin_certificate_sound certificate4678 profilesValid4678 numericValid4678 valid4678

def retention4679 : RatCutRetentionCertificate := ⟨(9/250),(37/1000),(64000000000000000000/3741964644565124703121),(28252501530893674889/1000000000000000000),1,(3884497209913954512618197156608041331/1765781345680854680562500000000000000),false,MergedCutProfiles.Batch662.profile26491,(fun _ => MergedCutProfiles.Batch662.profile26491)⟩
theorem profilesValid4679 : retention4679.ProfilesValid := by
  exact MergedCutProfiles.Batch662.valid26491
theorem numericValid4679 : retention4679.NumericValid := by decide +kernel
def certificate4679 : RatCutBinCertificate := ⟨⟨retention4679,(1755904959296729437/1000000000000000000),(61591158108543061/1000000000000000000),(10687671490383747969/1000000000000000000),(8040784305062615797027/200000000000000000),(2189755447995058027/1000000000000000000)⟩,(99995886034283681/100000000000000000),(11023581052656749/500000000000000000),(34712364839826901/40000000000000000),(881762542303581899/500000000000000000)⟩
theorem valid4679 : certificate4679.Valid := by decide +kernel
theorem sound4679 : certificate4679.Sound := rat_cut_bin_certificate_sound certificate4679 profilesValid4679 numericValid4679 valid4679

def certificates : List RatCutBinCertificate := [certificate4668,certificate4669,certificate4670,certificate4671,certificate4672,certificate4673,certificate4674,certificate4675,certificate4676,certificate4677,certificate4678,certificate4679]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4668,List.forall_mem_cons.mpr ⟨sound4669,List.forall_mem_cons.mpr ⟨sound4670,List.forall_mem_cons.mpr ⟨sound4671,List.forall_mem_cons.mpr ⟨sound4672,List.forall_mem_cons.mpr ⟨sound4673,List.forall_mem_cons.mpr ⟨sound4674,List.forall_mem_cons.mpr ⟨sound4675,List.forall_mem_cons.mpr ⟨sound4676,List.forall_mem_cons.mpr ⟨sound4677,List.forall_mem_cons.mpr ⟨sound4678,List.forall_mem_cons.mpr ⟨sound4679,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch389
