import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch664
import Cycle12.MergedCutProfiles.Batch665
import Cycle12.MergedCutProfiles.Batch666

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch392

def retention4704 : RatCutRetentionCertificate := ⟨(3/80),(19/500),(186344197891819659/705775029171982801787),(138253031012600133/200000000000000000),4,(264422483364122074739907783076007399/110602424810080106400000000000000000),false,MergedCutProfiles.Batch664.profile26587,(fun _ => MergedCutProfiles.Batch664.profile26587)⟩
theorem profilesValid4704 : retention4704.ProfilesValid := by
  exact MergedCutProfiles.Batch664.valid26587
theorem numericValid4704 : retention4704.NumericValid := by decide +kernel
def certificate4704 : RatCutBinCertificate := ⟨⟨retention4704,(36590640528369051/20000000000000000),(65254397982896969/1000000000000000000),(683116614197489133/62500000000000000),(19336270263458644086213/500000000000000000),(1173528144465963273/500000000000000000)⟩,(499977845627288933/500000000000000000),(171162716121862017/200000000000000000),(546696443506029/50000000000000000),(5292249452423619/1000000000000000000)⟩
theorem valid4704 : certificate4704.Valid := by decide +kernel
theorem sound4704 : certificate4704.Sound := rat_cut_bin_certificate_sound certificate4704 profilesValid4704 numericValid4704 valid4704

def retention4705 : RatCutRetentionCertificate := ⟨(3/80),(19/500),(8317410022914307057/3528875145859914008935),(186344197891819659/200000000000000000),(7/2),(56877336820357550574648560962132439/23852057330152916352000000000000000),false,MergedCutProfiles.Batch664.profile26588,(fun _ => MergedCutProfiles.Batch664.profile26588)⟩
theorem profilesValid4705 : retention4705.ProfilesValid := by
  exact MergedCutProfiles.Batch664.valid26588
theorem numericValid4705 : retention4705.NumericValid := by decide +kernel
def certificate4705 : RatCutBinCertificate := ⟨⟨retention4705,(36590640528369051/20000000000000000),(65254397982896969/1000000000000000000),(683116614197489133/62500000000000000),(19336270263458644086213/500000000000000000),(2346358392111359667/1000000000000000000)⟩,(499977845627288933/500000000000000000),(15960896712756501/20000000000000000),(876953295353091/40000000000000000),(12190623049655199/1000000000000000000)⟩
theorem valid4705 : certificate4705.Valid := by decide +kernel
theorem sound4705 : certificate4705.Sound := rat_cut_bin_certificate_sound certificate4705 profilesValid4705 numericValid4705 valid4705

def retention4706 : RatCutRetentionCertificate := ⟨(3/80),(19/500),(1/40),(8317410022914307057/1000000000000000000),(6/5),(1821838849816521621207635443487179464071/831741002291430705700000000000000000000),false,MergedCutProfiles.Batch664.profile26589,(fun _ => MergedCutProfiles.Batch664.profile26589)⟩
theorem profilesValid4706 : retention4706.ProfilesValid := by
  exact MergedCutProfiles.Batch664.valid26589
theorem numericValid4706 : retention4706.NumericValid := by decide +kernel
def certificate4706 : RatCutBinCertificate := ⟨⟨retention4706,(36590640528369051/20000000000000000),(65254397982896969/1000000000000000000),(683116614197489133/62500000000000000),(19336270263458644086213/500000000000000000),(1088642311341461007/500000000000000000)⟩,(499977845627288933/500000000000000000),(43774588998388391/62500000000000000),(6273415662596709/125000000000000000),(77049224241062837/1000000000000000000)⟩
theorem valid4706 : certificate4706.Valid := by decide +kernel
theorem sound4706 : certificate4706.Sound := rat_cut_bin_certificate_sound certificate4706 profilesValid4706 numericValid4706 valid4706

def retention4707 : RatCutRetentionCertificate := ⟨(19/500),(153/4000),(609376571435633048/3478271617621589972309),(143515073899120711/250000000000000000),4,(35521923396433861087/16000000000000000000),true,MergedCutProfiles.Batch664.profile26590,![MergedCutProfiles.Batch664.profile26590,MergedCutProfiles.Batch664.profile26591,MergedCutProfiles.Batch664.profile26592,MergedCutProfiles.Batch664.profile26593,MergedCutProfiles.Batch664.profile26594,MergedCutProfiles.Batch664.profile26595,MergedCutProfiles.Batch664.profile26596,MergedCutProfiles.Batch664.profile26597,MergedCutProfiles.Batch664.profile26598,MergedCutProfiles.Batch664.profile26599,MergedCutProfiles.Batch665.profile26600,MergedCutProfiles.Batch665.profile26601,MergedCutProfiles.Batch665.profile26602,MergedCutProfiles.Batch665.profile26603,MergedCutProfiles.Batch665.profile26604,MergedCutProfiles.Batch665.profile26605]⟩
theorem profilesValid4707 : retention4707.ProfilesValid := by
  change ∀ j : Fin 16, (retention4707.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch664.valid26590
  · exact MergedCutProfiles.Batch664.valid26591
  · exact MergedCutProfiles.Batch664.valid26592
  · exact MergedCutProfiles.Batch664.valid26593
  · exact MergedCutProfiles.Batch664.valid26594
  · exact MergedCutProfiles.Batch664.valid26595
  · exact MergedCutProfiles.Batch664.valid26596
  · exact MergedCutProfiles.Batch664.valid26597
  · exact MergedCutProfiles.Batch664.valid26598
  · exact MergedCutProfiles.Batch664.valid26599
  · exact MergedCutProfiles.Batch665.valid26600
  · exact MergedCutProfiles.Batch665.valid26601
  · exact MergedCutProfiles.Batch665.valid26602
  · exact MergedCutProfiles.Batch665.valid26603
  · exact MergedCutProfiles.Batch665.valid26604
  · exact MergedCutProfiles.Batch665.valid26605
theorem numericValid4707 : retention4707.NumericValid := by decide +kernel
def certificate4707 : RatCutBinCertificate := ⟨⟨retention4707,(1877882667111608711/1000000000000000000),(66189823964231271/1000000000000000000),(11012473498530257251/1000000000000000000),(9588827198051339616499/250000000000000000),(1087486282629912891/500000000000000000)⟩,(499977117272308803/500000000000000000),(358974573427448993/500000000000000000),(44153708986414159/1000000000000000000),(970528780705333/50000000000000000)⟩
theorem valid4707 : certificate4707.Valid := by decide +kernel
theorem sound4707 : certificate4707.Sound := rat_cut_bin_certificate_sound certificate4707 profilesValid4707 numericValid4707 valid4707

def retention4708 : RatCutRetentionCertificate := ⟨(19/500),(153/4000),(1145707859000000000/3478271617621589972309),(76172071429454131/125000000000000000),4,(4576806913762633749/2000000000000000000),true,MergedCutProfiles.Batch664.profile26591,![MergedCutProfiles.Batch664.profile26591,MergedCutProfiles.Batch664.profile26593,MergedCutProfiles.Batch664.profile26595,MergedCutProfiles.Batch665.profile26606,MergedCutProfiles.Batch664.profile26598,MergedCutProfiles.Batch665.profile26600,MergedCutProfiles.Batch665.profile26602,MergedCutProfiles.Batch665.profile26604,MergedCutProfiles.Batch665.profile26605,MergedCutProfiles.Batch665.profile26607,MergedCutProfiles.Batch665.profile26608,MergedCutProfiles.Batch665.profile26609,MergedCutProfiles.Batch665.profile26610,MergedCutProfiles.Batch665.profile26611,MergedCutProfiles.Batch665.profile26612,MergedCutProfiles.Batch665.profile26613]⟩
theorem profilesValid4708 : retention4708.ProfilesValid := by
  change ∀ j : Fin 16, (retention4708.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch664.valid26591
  · exact MergedCutProfiles.Batch664.valid26593
  · exact MergedCutProfiles.Batch664.valid26595
  · exact MergedCutProfiles.Batch665.valid26606
  · exact MergedCutProfiles.Batch664.valid26598
  · exact MergedCutProfiles.Batch665.valid26600
  · exact MergedCutProfiles.Batch665.valid26602
  · exact MergedCutProfiles.Batch665.valid26604
  · exact MergedCutProfiles.Batch665.valid26605
  · exact MergedCutProfiles.Batch665.valid26607
  · exact MergedCutProfiles.Batch665.valid26608
  · exact MergedCutProfiles.Batch665.valid26609
  · exact MergedCutProfiles.Batch665.valid26610
  · exact MergedCutProfiles.Batch665.valid26611
  · exact MergedCutProfiles.Batch665.valid26612
  · exact MergedCutProfiles.Batch665.valid26613
theorem numericValid4708 : retention4708.NumericValid := by decide +kernel
def certificate4708 : RatCutBinCertificate := ⟨⟨retention4708,(1877882667111608711/1000000000000000000),(66189823964231271/1000000000000000000),(11012473498530257251/1000000000000000000),(9588827198051339616499/250000000000000000),(1121627905915213887/500000000000000000)⟩,(499977117272308803/500000000000000000),(334405904916710317/500000000000000000),(6215692805267361/100000000000000000),(28336889593095489/1000000000000000000)⟩
theorem valid4708 : certificate4708.Valid := by decide +kernel
theorem sound4708 : certificate4708.Sound := rat_cut_bin_certificate_sound certificate4708 profilesValid4708 numericValid4708 valid4708

def retention4709 : RatCutRetentionCertificate := ⟨(19/500),(153/4000),(2092840360131173319/3478271617621589972309),(1145707859/1000000000),(14/5),(2399353969690478899/1000000000000000000),true,MergedCutProfiles.Batch665.profile26614,![MergedCutProfiles.Batch665.profile26614,MergedCutProfiles.Batch664.profile26596,MergedCutProfiles.Batch664.profile26599,MergedCutProfiles.Batch665.profile26603,MergedCutProfiles.Batch665.profile26615,MergedCutProfiles.Batch665.profile26608,MergedCutProfiles.Batch665.profile26610,MergedCutProfiles.Batch665.profile26612,MergedCutProfiles.Batch665.profile26613,MergedCutProfiles.Batch665.profile26616,MergedCutProfiles.Batch665.profile26617,MergedCutProfiles.Batch665.profile26618,MergedCutProfiles.Batch665.profile26619,MergedCutProfiles.Batch665.profile26620,MergedCutProfiles.Batch665.profile26621,MergedCutProfiles.Batch665.profile26622]⟩
theorem profilesValid4709 : retention4709.ProfilesValid := by
  change ∀ j : Fin 16, (retention4709.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch665.valid26614
  · exact MergedCutProfiles.Batch664.valid26596
  · exact MergedCutProfiles.Batch664.valid26599
  · exact MergedCutProfiles.Batch665.valid26603
  · exact MergedCutProfiles.Batch665.valid26615
  · exact MergedCutProfiles.Batch665.valid26608
  · exact MergedCutProfiles.Batch665.valid26610
  · exact MergedCutProfiles.Batch665.valid26612
  · exact MergedCutProfiles.Batch665.valid26613
  · exact MergedCutProfiles.Batch665.valid26616
  · exact MergedCutProfiles.Batch665.valid26617
  · exact MergedCutProfiles.Batch665.valid26618
  · exact MergedCutProfiles.Batch665.valid26619
  · exact MergedCutProfiles.Batch665.valid26620
  · exact MergedCutProfiles.Batch665.valid26621
  · exact MergedCutProfiles.Batch665.valid26622
theorem numericValid4709 : retention4709.NumericValid := by decide +kernel
def certificate4709 : RatCutBinCertificate := ⟨⟨retention4709,(1877882667111608711/1000000000000000000),(66189823964231271/1000000000000000000),(11012473498530257251/1000000000000000000),(9588827198051339616499/250000000000000000),(1183875311764318163/500000000000000000)⟩,(499977117272308803/500000000000000000),(218477735494505193/500000000000000000),(50319547080228213/250000000000000000),(134692075917183811/1000000000000000000)⟩
theorem valid4709 : certificate4709.Valid := by decide +kernel
theorem sound4709 : certificate4709.Sound := rat_cut_bin_certificate_sound certificate4709 profilesValid4709 numericValid4709 valid4709

def retention4710 : RatCutRetentionCertificate := ⟨(19/500),(153/4000),(64000000000000000000/3478271617621589972309),(2092840360131173319/1000000000000000000),(37/20),(2838913316455424153487/1280000000000000000000),true,MergedCutProfiles.Batch665.profile26623,![MergedCutProfiles.Batch665.profile26623,MergedCutProfiles.Batch665.profile26624,MergedCutProfiles.Batch665.profile26625,MergedCutProfiles.Batch665.profile26626,MergedCutProfiles.Batch665.profile26627,MergedCutProfiles.Batch665.profile26628,MergedCutProfiles.Batch665.profile26629,MergedCutProfiles.Batch665.profile26630,MergedCutProfiles.Batch665.profile26631,MergedCutProfiles.Batch665.profile26632,MergedCutProfiles.Batch665.profile26633,MergedCutProfiles.Batch665.profile26634,MergedCutProfiles.Batch665.profile26635,MergedCutProfiles.Batch665.profile26636,MergedCutProfiles.Batch665.profile26637,MergedCutProfiles.Batch665.profile26638]⟩
theorem profilesValid4710 : retention4710.ProfilesValid := by
  change ∀ j : Fin 16, (retention4710.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch665.valid26623
  · exact MergedCutProfiles.Batch665.valid26624
  · exact MergedCutProfiles.Batch665.valid26625
  · exact MergedCutProfiles.Batch665.valid26626
  · exact MergedCutProfiles.Batch665.valid26627
  · exact MergedCutProfiles.Batch665.valid26628
  · exact MergedCutProfiles.Batch665.valid26629
  · exact MergedCutProfiles.Batch665.valid26630
  · exact MergedCutProfiles.Batch665.valid26631
  · exact MergedCutProfiles.Batch665.valid26632
  · exact MergedCutProfiles.Batch665.valid26633
  · exact MergedCutProfiles.Batch665.valid26634
  · exact MergedCutProfiles.Batch665.valid26635
  · exact MergedCutProfiles.Batch665.valid26636
  · exact MergedCutProfiles.Batch665.valid26637
  · exact MergedCutProfiles.Batch665.valid26638
theorem numericValid4710 : retention4710.NumericValid := by decide +kernel
def certificate4710 : RatCutBinCertificate := ⟨⟨retention4710,(1877882667111608711/1000000000000000000),(66189823964231271/1000000000000000000),(11012473498530257251/1000000000000000000),(9588827198051339616499/250000000000000000),(1098510124060505703/500000000000000000)⟩,(499977117272308803/500000000000000000),(361914690855407001/1000000000000000000),(67562587825835663/250000000000000000),(24559577185702127/100000000000000000)⟩
theorem valid4710 : certificate4710.Valid := by decide +kernel
theorem sound4710 : certificate4710.Sound := rat_cut_bin_certificate_sound certificate4710 profilesValid4710 numericValid4710 valid4710

def retention4711 : RatCutRetentionCertificate := ⟨(19/500),(153/4000),(1/2),64,1,(255382430361484332092211040358411666671/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch665.profile26639,(fun _ => MergedCutProfiles.Batch665.profile26639)⟩
theorem profilesValid4711 : retention4711.ProfilesValid := by
  exact MergedCutProfiles.Batch665.valid26639
theorem numericValid4711 : retention4711.NumericValid := by decide +kernel
def certificate4711 : RatCutBinCertificate := ⟨⟨retention4711,(1877882667111608711/1000000000000000000),(66189823964231271/1000000000000000000),(11012473498530257251/1000000000000000000),(9588827198051339616499/250000000000000000),(986300715023368363/1000000000000000000)⟩,(499977117272308803/500000000000000000),(26104212568251391/50000000000000000),(2165616227610153/15625000000000000),(134619792011446129/1000000000000000000)⟩
theorem valid4711 : certificate4711.Valid := by decide +kernel
theorem sound4711 : certificate4711.Sound := rat_cut_bin_certificate_sound certificate4711 profilesValid4711 numericValid4711 valid4711

def retention4712 : RatCutRetentionCertificate := ⟨(19/500),(153/4000),(64000000000000000000/3478271617621589972309),(29516229040970144381/1000000000000000000),1,(259290151445782357414502408537553912619/118064916163880577524000000000000000000),false,MergedCutProfiles.Batch666.profile26640,(fun _ => MergedCutProfiles.Batch666.profile26640)⟩
theorem profilesValid4712 : retention4712.ProfilesValid := by
  exact MergedCutProfiles.Batch666.valid26640
theorem numericValid4712 : retention4712.NumericValid := by decide +kernel
def certificate4712 : RatCutBinCertificate := ⟨⟨retention4712,(1753559105111608711/1000000000000000000),(66189823964231271/1000000000000000000),(11012473498530257251/1000000000000000000),(9588827198051339616499/250000000000000000),(2185626308240372737/1000000000000000000)⟩,(249989316103793867/250000000000000000),(21417835596016041/1000000000000000000),(434853444949825847/500000000000000000),(1769726160934498727/1000000000000000000)⟩
theorem valid4712 : certificate4712.Valid := by decide +kernel
theorem sound4712 : certificate4712.Sound := rat_cut_bin_certificate_sound certificate4712 profilesValid4712 numericValid4712 valid4712

def retention4713 : RatCutRetentionCertificate := ⟨(19/500),(153/4000),(1/2),64,1,(255382430361484332092211040358411666671/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch665.profile26639,(fun _ => MergedCutProfiles.Batch665.profile26639)⟩
theorem profilesValid4713 : retention4713.ProfilesValid := by
  exact MergedCutProfiles.Batch665.valid26639
theorem numericValid4713 : retention4713.NumericValid := by decide +kernel
def certificate4713 : RatCutBinCertificate := ⟨⟨retention4713,(1753559105111608711/1000000000000000000),(66189823964231271/1000000000000000000),(11012473498530257251/1000000000000000000),(9588827198051339616499/250000000000000000),(493523977248720131/500000000000000000)⟩,(249989316103793867/250000000000000000),(2964102752741507/62500000000000000),(39765479753503819/50000000000000000),(386526164890717541/500000000000000000)⟩
theorem valid4713 : certificate4713.Valid := by decide +kernel
theorem sound4713 : certificate4713.Sound := rat_cut_bin_certificate_sound certificate4713 profilesValid4713 numericValid4713 valid4713

def retention4714 : RatCutRetentionCertificate := ⟨(19/500),(153/4000),(693053389065544449/3478271617621589972309),(171547868580580309/250000000000000000),4,(409886699968978183927240863536524567/171547868580580309000000000000000000),false,MergedCutProfiles.Batch666.profile26641,(fun _ => MergedCutProfiles.Batch666.profile26641)⟩
theorem profilesValid4714 : retention4714.ProfilesValid := by
  exact MergedCutProfiles.Batch666.valid26641
theorem numericValid4714 : retention4714.NumericValid := by decide +kernel
def certificate4714 : RatCutBinCertificate := ⟨⟨retention4714,(1833921001111608711/1000000000000000000),(66189823964231271/1000000000000000000),(11012473498530257251/1000000000000000000),(9588827198051339616499/250000000000000000),(293156535139022779/125000000000000000)⟩,(999955305927817671/1000000000000000000),(427978824348123339/500000000000000000),(2182301840934243/200000000000000000),(5271227311827183/1000000000000000000)⟩
theorem valid4714 : certificate4714.Valid := by decide +kernel
theorem sound4714 : certificate4714.Sound := rat_cut_bin_certificate_sound certificate4714 profilesValid4714 numericValid4714 valid4714

def retention4715 : RatCutRetentionCertificate := ⟨(19/500),(153/4000),(133447322674255479/496895945374512853187),(693053389065544449/1000000000000000000),4,(6632983524858498427978703650551786287/2772213556262177796000000000000000000),false,MergedCutProfiles.Batch666.profile26642,(fun _ => MergedCutProfiles.Batch666.profile26642)⟩
theorem profilesValid4715 : retention4715.ProfilesValid := by
  exact MergedCutProfiles.Batch666.valid26642
theorem numericValid4715 : retention4715.NumericValid := by decide +kernel
def certificate4715 : RatCutBinCertificate := ⟨⟨retention4715,(1833921001111608711/1000000000000000000),(66189823964231271/1000000000000000000),(11012473498530257251/1000000000000000000),(9588827198051339616499/250000000000000000),(2348576142688383781/1000000000000000000)⟩,(999955305927817671/1000000000000000000),(852516631190910843/1000000000000000000),(2863407899249957/250000000000000000),(270960106401/48828125000000)⟩
theorem valid4715 : certificate4715.Valid := by decide +kernel
theorem sound4715 : certificate4715.Sound := rat_cut_bin_certificate_sound certificate4715 profilesValid4715 numericValid4715 valid4715

def certificates : List RatCutBinCertificate := [certificate4704,certificate4705,certificate4706,certificate4707,certificate4708,certificate4709,certificate4710,certificate4711,certificate4712,certificate4713,certificate4714,certificate4715]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4704,List.forall_mem_cons.mpr ⟨sound4705,List.forall_mem_cons.mpr ⟨sound4706,List.forall_mem_cons.mpr ⟨sound4707,List.forall_mem_cons.mpr ⟨sound4708,List.forall_mem_cons.mpr ⟨sound4709,List.forall_mem_cons.mpr ⟨sound4710,List.forall_mem_cons.mpr ⟨sound4711,List.forall_mem_cons.mpr ⟨sound4712,List.forall_mem_cons.mpr ⟨sound4713,List.forall_mem_cons.mpr ⟨sound4714,List.forall_mem_cons.mpr ⟨sound4715,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch392
