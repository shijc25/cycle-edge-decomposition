import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch666
import Cycle12.MergedCutProfiles.Batch667

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch393

def retention4716 : RatCutRetentionCertificate := ⟨(19/500),(153/4000),(8422315596312910643/3478271617621589972309),(934131258719788353/1000000000000000000),(69/20),(3561028092490442704149335500946647728071/1494610013951661364800000000000000000000),false,MergedCutProfiles.Batch666.profile26643,(fun _ => MergedCutProfiles.Batch666.profile26643)⟩
theorem profilesValid4716 : retention4716.ProfilesValid := by
  exact MergedCutProfiles.Batch666.valid26643
theorem numericValid4716 : retention4716.NumericValid := by decide +kernel
def certificate4716 : RatCutBinCertificate := ⟨⟨retention4716,(1833921001111608711/1000000000000000000),(66189823964231271/1000000000000000000),(11012473498530257251/1000000000000000000),(9588827198051339616499/250000000000000000),(2344551864119527159/1000000000000000000)⟩,(999955305927817671/1000000000000000000),(39817002748792441/50000000000000000),(892409474952243/40000000000000000),(1565074812529203/125000000000000000)⟩
theorem valid4716 : certificate4716.Valid := by decide +kernel
theorem sound4716 : certificate4716.Sound := rat_cut_bin_certificate_sound certificate4716 profilesValid4716 numericValid4716 valid4716

def retention4717 : RatCutRetentionCertificate := ⟨(19/500),(153/4000),(1/40),(8422315596312910643/1000000000000000000),(6/5),(1845957853382930183092054065803482277271/842231559631291064300000000000000000000),false,MergedCutProfiles.Batch666.profile26644,(fun _ => MergedCutProfiles.Batch666.profile26644)⟩
theorem profilesValid4717 : retention4717.ProfilesValid := by
  exact MergedCutProfiles.Batch666.valid26644
theorem numericValid4717 : retention4717.NumericValid := by decide +kernel
def certificate4717 : RatCutBinCertificate := ⟨⟨retention4717,(1833921001111608711/1000000000000000000),(66189823964231271/1000000000000000000),(11012473498530257251/1000000000000000000),(9588827198051339616499/250000000000000000),(1089259513926794593/500000000000000000)⟩,(999955305927817671/1000000000000000000),(698478520092433853/1000000000000000000),(12717966924157087/250000000000000000),(78287660521220399/1000000000000000000)⟩
theorem valid4717 : certificate4717.Valid := by decide +kernel
theorem sound4717 : certificate4717.Sound := rat_cut_bin_certificate_sound certificate4717 profilesValid4717 numericValid4717 valid4717

def retention4718 : RatCutRetentionCertificate := ⟨(153/4000),(77/2000),(603850100687123179/3428679673512159962684),(287271325630839073/500000000000000000),4,(14216686254446668457/6400000000000000000),true,MergedCutProfiles.Batch666.profile26645,![MergedCutProfiles.Batch666.profile26645,MergedCutProfiles.Batch666.profile26646,MergedCutProfiles.Batch666.profile26647,MergedCutProfiles.Batch666.profile26648,MergedCutProfiles.Batch666.profile26649,MergedCutProfiles.Batch666.profile26650,MergedCutProfiles.Batch666.profile26651,MergedCutProfiles.Batch666.profile26652,MergedCutProfiles.Batch666.profile26653,MergedCutProfiles.Batch666.profile26654,MergedCutProfiles.Batch666.profile26655,MergedCutProfiles.Batch666.profile26656,MergedCutProfiles.Batch666.profile26657,MergedCutProfiles.Batch666.profile26658,MergedCutProfiles.Batch666.profile26659,MergedCutProfiles.Batch666.profile26660]⟩
theorem profilesValid4718 : retention4718.ProfilesValid := by
  change ∀ j : Fin 16, (retention4718.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch666.valid26645
  · exact MergedCutProfiles.Batch666.valid26646
  · exact MergedCutProfiles.Batch666.valid26647
  · exact MergedCutProfiles.Batch666.valid26648
  · exact MergedCutProfiles.Batch666.valid26649
  · exact MergedCutProfiles.Batch666.valid26650
  · exact MergedCutProfiles.Batch666.valid26651
  · exact MergedCutProfiles.Batch666.valid26652
  · exact MergedCutProfiles.Batch666.valid26653
  · exact MergedCutProfiles.Batch666.valid26654
  · exact MergedCutProfiles.Batch666.valid26655
  · exact MergedCutProfiles.Batch666.valid26656
  · exact MergedCutProfiles.Batch666.valid26657
  · exact MergedCutProfiles.Batch666.valid26658
  · exact MergedCutProfiles.Batch666.valid26659
  · exact MergedCutProfiles.Batch666.valid26660
theorem numericValid4718 : retention4718.NumericValid := by decide +kernel
def certificate4718 : RatCutBinCertificate := ⟨⟨retention4718,(1878722856458620407/1000000000000000000),(6713316315302437/100000000000000000),(11054137380926391123/1000000000000000000),(37951572089304756498021/1000000000000000000),(271964789211313427/125000000000000000)⟩,(199990754658244263/200000000000000000),(717728094109976439/1000000000000000000),(4422699029275649/100000000000000000),(3890259457720043/200000000000000000)⟩
theorem valid4718 : certificate4718.Valid := by decide +kernel
theorem sound4718 : certificate4718.Sound := rat_cut_bin_certificate_sound certificate4718 profilesValid4718 numericValid4718 valid4718

def retention4719 : RatCutRetentionCertificate := ⟨(153/4000),(77/2000),(286632341750000000/857169918378039990671),(603850100687123179/1000000000000000000),4,(9114083020589820279/4000000000000000000),true,MergedCutProfiles.Batch666.profile26646,![MergedCutProfiles.Batch666.profile26646,MergedCutProfiles.Batch666.profile26648,MergedCutProfiles.Batch666.profile26650,MergedCutProfiles.Batch666.profile26661,MergedCutProfiles.Batch666.profile26653,MergedCutProfiles.Batch666.profile26655,MergedCutProfiles.Batch666.profile26657,MergedCutProfiles.Batch666.profile26659,MergedCutProfiles.Batch666.profile26662,MergedCutProfiles.Batch666.profile26663,MergedCutProfiles.Batch666.profile26664,MergedCutProfiles.Batch666.profile26665,MergedCutProfiles.Batch666.profile26666,MergedCutProfiles.Batch666.profile26667,MergedCutProfiles.Batch666.profile26668,MergedCutProfiles.Batch666.profile26669]⟩
theorem profilesValid4719 : retention4719.ProfilesValid := by
  change ∀ j : Fin 16, (retention4719.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch666.valid26646
  · exact MergedCutProfiles.Batch666.valid26648
  · exact MergedCutProfiles.Batch666.valid26650
  · exact MergedCutProfiles.Batch666.valid26661
  · exact MergedCutProfiles.Batch666.valid26653
  · exact MergedCutProfiles.Batch666.valid26655
  · exact MergedCutProfiles.Batch666.valid26657
  · exact MergedCutProfiles.Batch666.valid26659
  · exact MergedCutProfiles.Batch666.valid26662
  · exact MergedCutProfiles.Batch666.valid26663
  · exact MergedCutProfiles.Batch666.valid26664
  · exact MergedCutProfiles.Batch666.valid26665
  · exact MergedCutProfiles.Batch666.valid26666
  · exact MergedCutProfiles.Batch666.valid26667
  · exact MergedCutProfiles.Batch666.valid26668
  · exact MergedCutProfiles.Batch666.valid26669
theorem numericValid4719 : retention4719.NumericValid := by decide +kernel
def certificate4719 : RatCutBinCertificate := ⟨⟨retention4719,(1878722856458620407/1000000000000000000),(6713316315302437/100000000000000000),(11054137380926391123/1000000000000000000),(37951572089304756498021/1000000000000000000),(558220460821402457/250000000000000000)⟩,(199990754658244263/200000000000000000),(1321110811136013/1953125000000000),(59144029037383393/1000000000000000000),(3352015562274897/125000000000000000)⟩
theorem valid4719 : certificate4719.Valid := by decide +kernel
theorem sound4719 : certificate4719.Sound := rat_cut_bin_certificate_sound certificate4719 profilesValid4719 numericValid4719 valid4719

def retention4720 : RatCutRetentionCertificate := ⟨(153/4000),(77/2000),(2407687393565951749/3428679673512159962684),(1146529367/1000000000),(11/4),(27372943104765218888286860864999119/11465293670000000000000000000000000),true,MergedCutProfiles.Batch666.profile26648,![MergedCutProfiles.Batch666.profile26648,MergedCutProfiles.Batch666.profile26652,MergedCutProfiles.Batch666.profile26656,MergedCutProfiles.Batch666.profile26660,MergedCutProfiles.Batch666.profile26670,MergedCutProfiles.Batch666.profile26666,MergedCutProfiles.Batch666.profile26667,MergedCutProfiles.Batch666.profile26671,MergedCutProfiles.Batch666.profile26672,MergedCutProfiles.Batch666.profile26673,MergedCutProfiles.Batch666.profile26674,MergedCutProfiles.Batch666.profile26675,MergedCutProfiles.Batch666.profile26676,MergedCutProfiles.Batch666.profile26677,MergedCutProfiles.Batch666.profile26678,MergedCutProfiles.Batch666.profile26679]⟩
theorem profilesValid4720 : retention4720.ProfilesValid := by
  change ∀ j : Fin 16, (retention4720.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch666.valid26648
  · exact MergedCutProfiles.Batch666.valid26652
  · exact MergedCutProfiles.Batch666.valid26656
  · exact MergedCutProfiles.Batch666.valid26660
  · exact MergedCutProfiles.Batch666.valid26670
  · exact MergedCutProfiles.Batch666.valid26666
  · exact MergedCutProfiles.Batch666.valid26667
  · exact MergedCutProfiles.Batch666.valid26671
  · exact MergedCutProfiles.Batch666.valid26672
  · exact MergedCutProfiles.Batch666.valid26673
  · exact MergedCutProfiles.Batch666.valid26674
  · exact MergedCutProfiles.Batch666.valid26675
  · exact MergedCutProfiles.Batch666.valid26676
  · exact MergedCutProfiles.Batch666.valid26677
  · exact MergedCutProfiles.Batch666.valid26678
  · exact MergedCutProfiles.Batch666.valid26679
theorem numericValid4720 : retention4720.NumericValid := by decide +kernel
def certificate4720 : RatCutBinCertificate := ⟨⟨retention4720,(1878722856458620407/1000000000000000000),(6713316315302437/100000000000000000),(11054137380926391123/1000000000000000000),(37951572089304756498021/1000000000000000000),(294510549281386491/125000000000000000)⟩,(199990754658244263/200000000000000000),(87852971064363787/200000000000000000),(199372316030655361/1000000000000000000),(33577193981779381/250000000000000000)⟩
theorem valid4720 : certificate4720.Valid := by decide +kernel
theorem sound4720 : certificate4720.Sound := rat_cut_bin_certificate_sound certificate4720 profilesValid4720 numericValid4720 valid4720

def retention4721 : RatCutRetentionCertificate := ⟨(153/4000),(77/2000),(16000000000000000000/857169918378039990671),(2407687393565951749/1000000000000000000),(17/10),(2831368668482910480289/1280000000000000000000),true,MergedCutProfiles.Batch667.profile26680,![MergedCutProfiles.Batch667.profile26680,MergedCutProfiles.Batch667.profile26681,MergedCutProfiles.Batch667.profile26682,MergedCutProfiles.Batch667.profile26683,MergedCutProfiles.Batch667.profile26684,MergedCutProfiles.Batch667.profile26685,MergedCutProfiles.Batch667.profile26686,MergedCutProfiles.Batch667.profile26687,MergedCutProfiles.Batch667.profile26688,MergedCutProfiles.Batch667.profile26689,MergedCutProfiles.Batch667.profile26690,MergedCutProfiles.Batch667.profile26691,MergedCutProfiles.Batch667.profile26692,MergedCutProfiles.Batch667.profile26693,MergedCutProfiles.Batch667.profile26694,MergedCutProfiles.Batch667.profile26695]⟩
theorem profilesValid4721 : retention4721.ProfilesValid := by
  change ∀ j : Fin 16, (retention4721.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch667.valid26680
  · exact MergedCutProfiles.Batch667.valid26681
  · exact MergedCutProfiles.Batch667.valid26682
  · exact MergedCutProfiles.Batch667.valid26683
  · exact MergedCutProfiles.Batch667.valid26684
  · exact MergedCutProfiles.Batch667.valid26685
  · exact MergedCutProfiles.Batch667.valid26686
  · exact MergedCutProfiles.Batch667.valid26687
  · exact MergedCutProfiles.Batch667.valid26688
  · exact MergedCutProfiles.Batch667.valid26689
  · exact MergedCutProfiles.Batch667.valid26690
  · exact MergedCutProfiles.Batch667.valid26691
  · exact MergedCutProfiles.Batch667.valid26692
  · exact MergedCutProfiles.Batch667.valid26693
  · exact MergedCutProfiles.Batch667.valid26694
  · exact MergedCutProfiles.Batch667.valid26695
theorem numericValid4721 : retention4721.NumericValid := by decide +kernel
def certificate4721 : RatCutBinCertificate := ⟨⟨retention4721,(1878722856458620407/1000000000000000000),(6713316315302437/100000000000000000),(11054137380926391123/1000000000000000000),(37951572089304756498021/1000000000000000000),(2192610240533350763/1000000000000000000)⟩,(199990754658244263/200000000000000000),(6912871314883603/20000000000000000),(287156389353270479/1000000000000000000),(70402206382856393/250000000000000000)⟩
theorem valid4721 : certificate4721.Valid := by decide +kernel
theorem sound4721 : certificate4721.Sound := rat_cut_bin_certificate_sound certificate4721 profilesValid4721 numericValid4721 valid4721

def retention4722 : RatCutRetentionCertificate := ⟨(153/4000),(77/2000),(1/2),64,1,(2553826410217091191380347308953370351/2560000000000000000000000000000000000),false,MergedCutProfiles.Batch667.profile26696,(fun _ => MergedCutProfiles.Batch667.profile26696)⟩
theorem profilesValid4722 : retention4722.ProfilesValid := by
  exact MergedCutProfiles.Batch667.valid26696
theorem numericValid4722 : retention4722.NumericValid := by decide +kernel
def certificate4722 : RatCutBinCertificate := ⟨⟨retention4722,(1878722856458620407/1000000000000000000),(6713316315302437/100000000000000000),(11054137380926391123/1000000000000000000),(37951572089304756498021/1000000000000000000),(19723574431322639/20000000000000000)⟩,(199990754658244263/200000000000000000),(522663065809652249/1000000000000000000),(138223573054005717/1000000000000000000),(4194946955126153/31250000000000000)⟩
theorem valid4722 : certificate4722.Valid := by decide +kernel
theorem sound4722 : certificate4722.Sound := rat_cut_bin_certificate_sound certificate4722 profilesValid4722 numericValid4722 valid4722

def retention4723 : RatCutRetentionCertificate := ⟨(153/4000),(77/2000),(16000000000000000000/857169918378039990671),(29658336568448842767/1000000000000000000),1,(13020341362421122095180296132219290861/5931667313689768553400000000000000000),false,MergedCutProfiles.Batch667.profile26697,(fun _ => MergedCutProfiles.Batch667.profile26697)⟩
theorem profilesValid4723 : retention4723.ProfilesValid := by
  exact MergedCutProfiles.Batch667.valid26697
theorem numericValid4723 : retention4723.NumericValid := by decide +kernel
def certificate4723 : RatCutBinCertificate := ⟨⟨retention4723,(1753942150458620407/1000000000000000000),(6713316315302437/100000000000000000),(11054137380926391123/1000000000000000000),(37951572089304756498021/1000000000000000000),(2184403993470750373/1000000000000000000)⟩,(15624325680915027/15625000000000000),(10670867678656349/500000000000000000),(54371045091692537/62500000000000000),(442463915661891027/250000000000000000)⟩
theorem valid4723 : certificate4723.Valid := by decide +kernel
theorem sound4723 : certificate4723.Sound := rat_cut_bin_certificate_sound certificate4723 profilesValid4723 numericValid4723 valid4723

def retention4724 : RatCutRetentionCertificate := ⟨(153/4000),(77/2000),(1/2),64,1,(2553826410217091191380347308953370351/2560000000000000000000000000000000000),false,MergedCutProfiles.Batch667.profile26696,(fun _ => MergedCutProfiles.Batch667.profile26696)⟩
theorem profilesValid4724 : retention4724.ProfilesValid := by
  exact MergedCutProfiles.Batch667.valid26696
theorem numericValid4724 : retention4724.NumericValid := by decide +kernel
def certificate4724 : RatCutBinCertificate := ⟨⟨retention4724,(1753942150458620407/1000000000000000000),(6713316315302437/100000000000000000),(11054137380926391123/1000000000000000000),(37951572089304756498021/1000000000000000000),(98693653046945119/100000000000000000)⟩,(15624325680915027/15625000000000000),(11809009622922447/250000000000000000),(19895592170070179/25000000000000000),(773465707836935383/1000000000000000000)⟩
theorem valid4724 : certificate4724.Valid := by decide +kernel
theorem sound4724 : certificate4724.Sound := rat_cut_bin_certificate_sound certificate4724 profilesValid4724 numericValid4724 valid4724

def retention4725 : RatCutRetentionCertificate := ⟨(153/4000),(77/2000),(694016747650800373/3428679673512159962684),(137429058940752549/200000000000000000),4,(13140193229471324041882904757984463/5497162357630101960000000000000000),false,MergedCutProfiles.Batch667.profile26698,(fun _ => MergedCutProfiles.Batch667.profile26698)⟩
theorem profilesValid4725 : retention4725.ProfilesValid := by
  exact MergedCutProfiles.Batch667.valid26698
theorem numericValid4725 : retention4725.NumericValid := by decide +kernel
def certificate4725 : RatCutBinCertificate := ⟨⟨retention4725,(1835562192458620407/1000000000000000000),(6713316315302437/100000000000000000),(11054137380926391123/1000000000000000000),(37951572089304756498021/1000000000000000000),(1172884442535466373/500000000000000000)⟩,(999954835279595917/1000000000000000000),(5339869297706203/6250000000000000),(11158486211203247/1000000000000000000),(337052020035613/62500000000000000)⟩
theorem valid4725 : certificate4725.Valid := by decide +kernel
theorem sound4725 : certificate4725.Sound := rat_cut_bin_certificate_sound certificate4725 profilesValid4725 numericValid4725 valid4725

def retention4726 : RatCutRetentionCertificate := ⟨(153/4000),(77/2000),(935429720544002193/3428679673512159962684),(694016747650800373/1000000000000000000),4,(6644805211130126973314755028109937263/2776066990603201492000000000000000000),false,MergedCutProfiles.Batch667.profile26699,(fun _ => MergedCutProfiles.Batch667.profile26699)⟩
theorem profilesValid4726 : retention4726.ProfilesValid := by
  exact MergedCutProfiles.Batch667.valid26699
theorem numericValid4726 : retention4726.NumericValid := by decide +kernel
def certificate4726 : RatCutBinCertificate := ⟨⟨retention4726,(1835562192458620407/1000000000000000000),(6713316315302437/100000000000000000),(11054137380926391123/1000000000000000000),(37951572089304756498021/1000000000000000000),(1174506815314359221/500000000000000000)⟩,(999954835279595917/1000000000000000000),(850978641629386551/1000000000000000000),(11700425296973183/1000000000000000000),(1417769590399763/250000000000000000)⟩
theorem valid4726 : certificate4726.Valid := by decide +kernel
theorem sound4726 : certificate4726.Sound := rat_cut_bin_certificate_sound certificate4726 profilesValid4726 numericValid4726 valid4726

def retention4727 : RatCutRetentionCertificate := ⟨(153/4000),(77/2000),(4175258806770802869/1714339836756079981342),(935429720544002193/1000000000000000000),(69/20),(3566411812566674725892325386726844235511/1496687552870403508800000000000000000000),false,MergedCutProfiles.Batch667.profile26700,(fun _ => MergedCutProfiles.Batch667.profile26700)⟩
theorem profilesValid4727 : retention4727.ProfilesValid := by
  exact MergedCutProfiles.Batch667.valid26700
theorem numericValid4727 : retention4727.NumericValid := by decide +kernel
def certificate4727 : RatCutBinCertificate := ⟨⟨retention4727,(1835562192458620407/1000000000000000000),(6713316315302437/100000000000000000),(11054137380926391123/1000000000000000000),(37951572089304756498021/1000000000000000000),(1172205361464106511/500000000000000000)⟩,(999954835279595917/1000000000000000000),(159047351718635407/200000000000000000),(11281127036164783/500000000000000000),(12664456454552963/1000000000000000000)⟩
theorem valid4727 : certificate4727.Valid := by decide +kernel
theorem sound4727 : certificate4727.Sound := rat_cut_bin_certificate_sound certificate4727 profilesValid4727 numericValid4727 valid4727

def certificates : List RatCutBinCertificate := [certificate4716,certificate4717,certificate4718,certificate4719,certificate4720,certificate4721,certificate4722,certificate4723,certificate4724,certificate4725,certificate4726,certificate4727]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4716,List.forall_mem_cons.mpr ⟨sound4717,List.forall_mem_cons.mpr ⟨sound4718,List.forall_mem_cons.mpr ⟨sound4719,List.forall_mem_cons.mpr ⟨sound4720,List.forall_mem_cons.mpr ⟨sound4721,List.forall_mem_cons.mpr ⟨sound4722,List.forall_mem_cons.mpr ⟨sound4723,List.forall_mem_cons.mpr ⟨sound4724,List.forall_mem_cons.mpr ⟨sound4725,List.forall_mem_cons.mpr ⟨sound4726,List.forall_mem_cons.mpr ⟨sound4727,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch393
