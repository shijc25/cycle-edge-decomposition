import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch070
import Cycle12.MergedCutProfiles.Batch071
import Cycle12.MergedCutProfiles.Batch072
import Cycle12.MergedCutProfiles.Batch662
import Cycle12.MergedCutProfiles.Batch663

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch390

def retention4680 : RatCutRetentionCertificate := ⟨(9/250),(37/1000),(1/2),64,1,(15961296343634275519387494158967405759/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch070.profile2821,(fun _ => MergedCutProfiles.Batch070.profile2821)⟩
theorem profilesValid4680 : retention4680.ProfilesValid := by
  exact MergedCutProfiles.Batch070.valid2821
theorem numericValid4680 : retention4680.NumericValid := by decide +kernel
def certificate4680 : RatCutBinCertificate := ⟨⟨retention4680,(1755904959296729437/1000000000000000000),(61591158108543061/1000000000000000000),(10687671490383747969/1000000000000000000),(8040784305062615797027/200000000000000000),(98746205190947991/100000000000000000)⟩,(99995886034283681/100000000000000000),(48890884707502697/1000000000000000000),(395674986008866829/500000000000000000),(153904513106285747/200000000000000000)⟩
theorem valid4680 : certificate4680.Valid := by decide +kernel
theorem sound4680 : certificate4680.Sound := rat_cut_bin_certificate_sound certificate4680 profilesValid4680 numericValid4680 valid4680

def retention4681 : RatCutRetentionCertificate := ⟨(9/250),(37/1000),(685805527078700950/3741964644565124703121),(135803074669049693/200000000000000000),4,(51737085699245960203436612223507291/21728491947047950880000000000000000),false,MergedCutProfiles.Batch662.profile26492,(fun _ => MergedCutProfiles.Batch662.profile26492)⟩
theorem profilesValid4681 : retention4681.ProfilesValid := by
  exact MergedCutProfiles.Batch662.valid26492
theorem numericValid4681 : retention4681.NumericValid := by decide +kernel
def certificate4681 : RatCutBinCertificate := ⟨⟨retention4681,(1816987105296729437/1000000000000000000),(61591158108543061/1000000000000000000),(10687671490383747969/1000000000000000000),(8040784305062615797027/200000000000000000),(1169593622356631253/500000000000000000)⟩,(124994678653250923/125000000000000000),(108677172346538049/125000000000000000),(4461666792409759/500000000000000000),(429361281195861/100000000000000000)⟩
theorem valid4681 : certificate4681.Valid := by decide +kernel
theorem sound4681 : certificate4681.Sound := rat_cut_bin_certificate_sound certificate4681 profilesValid4681 numericValid4681 valid4681

def retention4682 : RatCutRetentionCertificate := ⟨(9/250),(37/1000),(933605858160362135/3741964644565124703121),(13716110541574019/20000000000000000),4,(2093481165564201943833669018322467/877831074660737216000000000000000),false,MergedCutProfiles.Batch662.profile26493,(fun _ => MergedCutProfiles.Batch662.profile26493)⟩
theorem profilesValid4682 : retention4682.ProfilesValid := by
  exact MergedCutProfiles.Batch662.valid26493
theorem numericValid4682 : retention4682.NumericValid := by decide +kernel
def certificate4682 : RatCutBinCertificate := ⟨⟨retention4682,(1816987105296729437/1000000000000000000),(61591158108543061/1000000000000000000),(10687671490383747969/1000000000000000000),(8040784305062615797027/200000000000000000),(292868727216993373/125000000000000000)⟩,(124994678653250923/125000000000000000),(865718428357644033/1000000000000000000),(9448814813152823/1000000000000000000),(2280241555340553/500000000000000000)⟩
theorem valid4682 : certificate4682.Valid := by decide +kernel
theorem sound4682 : certificate4682.Sound := rat_cut_bin_certificate_sound certificate4682 profilesValid4682 numericValid4682 valid4682

def retention4683 : RatCutRetentionCertificate := ⟨(9/250),(37/1000),(8672639524527744263/3741964644565124703121),(186721171632072427/200000000000000000),(7/2),(35600724991521686020599196637085170119/14937693730565794160000000000000000000),false,MergedCutProfiles.Batch662.profile26494,(fun _ => MergedCutProfiles.Batch662.profile26494)⟩
theorem profilesValid4683 : retention4683.ProfilesValid := by
  exact MergedCutProfiles.Batch662.valid26494
theorem numericValid4683 : retention4683.NumericValid := by decide +kernel
def certificate4683 : RatCutBinCertificate := ⟨⟨retention4683,(1816987105296729437/1000000000000000000),(61591158108543061/1000000000000000000),(10687671490383747969/1000000000000000000),(8040784305062615797027/200000000000000000),(146664549636535911/62500000000000000)⟩,(124994678653250923/125000000000000000),(200833899785190711/250000000000000000),(162092076206793/7812500000000000),(5770902727321691/500000000000000000)⟩
theorem valid4683 : certificate4683.Valid := by decide +kernel
theorem sound4683 : certificate4683.Sound := rat_cut_bin_certificate_sound certificate4683 profilesValid4683 numericValid4683 valid4683

def retention4684 : RatCutRetentionCertificate := ⟨(9/250),(37/1000),(1/40),(8672639524527744263/1000000000000000000),(6/5),(475053114649658594082428303519199258629/216815988113193606575000000000000000000),false,MergedCutProfiles.Batch662.profile26495,(fun _ => MergedCutProfiles.Batch662.profile26495)⟩
theorem profilesValid4684 : retention4684.ProfilesValid := by
  exact MergedCutProfiles.Batch662.valid26495
theorem numericValid4684 : retention4684.NumericValid := by decide +kernel
def certificate4684 : RatCutBinCertificate := ⟨⟨retention4684,(1816987105296729437/1000000000000000000),(61591158108543061/1000000000000000000),(10687671490383747969/1000000000000000000),(8040784305062615797027/200000000000000000),(1089238825585593319/500000000000000000)⟩,(124994678653250923/125000000000000000),(175750895857569173/250000000000000000),(49262671027096993/1000000000000000000),(15228970886595093/200000000000000000)⟩
theorem valid4684 : certificate4684.Valid := by decide +kernel
theorem sound4684 : certificate4684.Sound := rat_cut_bin_certificate_sound certificate4684 profilesValid4684 numericValid4684 valid4684

def retention4685 : RatCutRetentionCertificate := ⟨(37/1000),(3/80),(636327225990491083/3633226978316589448064),(288029368302582717/500000000000000000),4,(71170509197762621193/32000000000000000000),true,MergedCutProfiles.Batch662.profile26496,![MergedCutProfiles.Batch662.profile26496,MergedCutProfiles.Batch662.profile26497,MergedCutProfiles.Batch662.profile26498,MergedCutProfiles.Batch662.profile26499,MergedCutProfiles.Batch662.profile26500,MergedCutProfiles.Batch662.profile26501,MergedCutProfiles.Batch662.profile26502,MergedCutProfiles.Batch662.profile26503,MergedCutProfiles.Batch662.profile26504,MergedCutProfiles.Batch662.profile26505,MergedCutProfiles.Batch662.profile26506,MergedCutProfiles.Batch662.profile26507,MergedCutProfiles.Batch662.profile26508,MergedCutProfiles.Batch662.profile26509,MergedCutProfiles.Batch662.profile26510,MergedCutProfiles.Batch662.profile26511]⟩
theorem profilesValid4685 : retention4685.ProfilesValid := by
  change ∀ j : Fin 16, (retention4685.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch662.valid26496
  · exact MergedCutProfiles.Batch662.valid26497
  · exact MergedCutProfiles.Batch662.valid26498
  · exact MergedCutProfiles.Batch662.valid26499
  · exact MergedCutProfiles.Batch662.valid26500
  · exact MergedCutProfiles.Batch662.valid26501
  · exact MergedCutProfiles.Batch662.valid26502
  · exact MergedCutProfiles.Batch662.valid26503
  · exact MergedCutProfiles.Batch662.valid26504
  · exact MergedCutProfiles.Batch662.valid26505
  · exact MergedCutProfiles.Batch662.valid26506
  · exact MergedCutProfiles.Batch662.valid26507
  · exact MergedCutProfiles.Batch662.valid26508
  · exact MergedCutProfiles.Batch662.valid26509
  · exact MergedCutProfiles.Batch662.valid26510
  · exact MergedCutProfiles.Batch662.valid26511
theorem numericValid4685 : retention4685.NumericValid := by decide +kernel
def certificate4685 : RatCutBinCertificate := ⟨⟨retention4685,(1877155443414554083/1000000000000000000),(247684185361181/3906250000000000),(5424102969128447237/500000000000000000),(39518323636388087884083/1000000000000000000),(136261931961156939/62500000000000000)⟩,(999955424616784063/1000000000000000000),(707718191931990137/1000000000000000000),(9523409676341101/200000000000000000),(4197539206825973/200000000000000000)⟩
theorem valid4685 : certificate4685.Valid := by decide +kernel
theorem sound4685 : certificate4685.Sound := rat_cut_bin_certificate_sound certificate4685 profilesValid4685 numericValid4685 valid4685

def retention4686 : RatCutRetentionCertificate := ⟨(37/1000),(3/80),(8977427929687500/28384585768098355063),(636327225990491083/1000000000000000000),4,(1186209789789685665123424920934720731/509061780792392866400000000000000000),true,MergedCutProfiles.Batch662.profile26497,![MergedCutProfiles.Batch662.profile26497,MergedCutProfiles.Batch662.profile26512,MergedCutProfiles.Batch662.profile26500,MergedCutProfiles.Batch662.profile26513,MergedCutProfiles.Batch662.profile26504,MergedCutProfiles.Batch662.profile26506,MergedCutProfiles.Batch662.profile26508,MergedCutProfiles.Batch662.profile26509,MergedCutProfiles.Batch662.profile26511,MergedCutProfiles.Batch662.profile26514,MergedCutProfiles.Batch662.profile26515,MergedCutProfiles.Batch662.profile26516,MergedCutProfiles.Batch662.profile26517,MergedCutProfiles.Batch662.profile26518,MergedCutProfiles.Batch662.profile26519,MergedCutProfiles.Batch663.profile26520]⟩
theorem profilesValid4686 : retention4686.ProfilesValid := by
  change ∀ j : Fin 16, (retention4686.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch662.valid26497
  · exact MergedCutProfiles.Batch662.valid26512
  · exact MergedCutProfiles.Batch662.valid26500
  · exact MergedCutProfiles.Batch662.valid26513
  · exact MergedCutProfiles.Batch662.valid26504
  · exact MergedCutProfiles.Batch662.valid26506
  · exact MergedCutProfiles.Batch662.valid26508
  · exact MergedCutProfiles.Batch662.valid26509
  · exact MergedCutProfiles.Batch662.valid26511
  · exact MergedCutProfiles.Batch662.valid26514
  · exact MergedCutProfiles.Batch662.valid26515
  · exact MergedCutProfiles.Batch662.valid26516
  · exact MergedCutProfiles.Batch662.valid26517
  · exact MergedCutProfiles.Batch662.valid26518
  · exact MergedCutProfiles.Batch662.valid26519
  · exact MergedCutProfiles.Batch663.valid26520
theorem numericValid4686 : retention4686.NumericValid := by decide +kernel
def certificate4686 : RatCutBinCertificate := ⟨⟨retention4686,(1877155443414554083/1000000000000000000),(247684185361181/3906250000000000),(5424102969128447237/500000000000000000),(39518323636388087884083/1000000000000000000),(2286300770825185819/1000000000000000000)⟩,(999955424616784063/1000000000000000000),(631687540719981629/1000000000000000000),(78140214709189043/1000000000000000000),(72941502030309/2000000000000000)⟩
theorem valid4686 : certificate4686.Valid := by decide +kernel
theorem sound4686 : certificate4686.Sound := rat_cut_bin_certificate_sound certificate4686 profilesValid4686 numericValid4686 valid4686

def retention4687 : RatCutRetentionCertificate := ⟨(37/1000),(3/80),(1827031883911682139/3633226978316589448064),(45964431/40000000),(11/4),(10995214969273137440309208674547306791/4596443100000000000000000000000000000),true,MergedCutProfiles.Batch662.profile26498,![MergedCutProfiles.Batch662.profile26498,MergedCutProfiles.Batch662.profile26501,MergedCutProfiles.Batch662.profile26503,MergedCutProfiles.Batch662.profile26506,MergedCutProfiles.Batch662.profile26509,MergedCutProfiles.Batch662.profile26514,MergedCutProfiles.Batch662.profile26515,MergedCutProfiles.Batch662.profile26517,MergedCutProfiles.Batch662.profile26518,MergedCutProfiles.Batch663.profile26520,MergedCutProfiles.Batch663.profile26521,MergedCutProfiles.Batch663.profile26522,MergedCutProfiles.Batch663.profile26523,MergedCutProfiles.Batch663.profile26524,MergedCutProfiles.Batch663.profile26525,MergedCutProfiles.Batch663.profile26526]⟩
theorem profilesValid4687 : retention4687.ProfilesValid := by
  change ∀ j : Fin 16, (retention4687.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch662.valid26498
  · exact MergedCutProfiles.Batch662.valid26501
  · exact MergedCutProfiles.Batch662.valid26503
  · exact MergedCutProfiles.Batch662.valid26506
  · exact MergedCutProfiles.Batch662.valid26509
  · exact MergedCutProfiles.Batch662.valid26514
  · exact MergedCutProfiles.Batch662.valid26515
  · exact MergedCutProfiles.Batch662.valid26517
  · exact MergedCutProfiles.Batch662.valid26518
  · exact MergedCutProfiles.Batch663.valid26520
  · exact MergedCutProfiles.Batch663.valid26521
  · exact MergedCutProfiles.Batch663.valid26522
  · exact MergedCutProfiles.Batch663.valid26523
  · exact MergedCutProfiles.Batch663.valid26524
  · exact MergedCutProfiles.Batch663.valid26525
  · exact MergedCutProfiles.Batch663.valid26526
theorem numericValid4687 : retention4687.NumericValid := by decide +kernel
def certificate4687 : RatCutBinCertificate := ⟨⟨retention4687,(1877155443414554083/1000000000000000000),(247684185361181/3906250000000000),(5424102969128447237/500000000000000000),(39518323636388087884083/1000000000000000000),(2361941148466515659/1000000000000000000)⟩,(999955424616784063/1000000000000000000),(433161725107428853/1000000000000000000),(102217791859999203/500000000000000000),(138055406546508063/1000000000000000000)⟩
theorem valid4687 : certificate4687.Valid := by decide +kernel
theorem sound4687 : certificate4687.Sound := rat_cut_bin_certificate_sound certificate4687 profilesValid4687 numericValid4687 valid4687

def retention4688 : RatCutRetentionCertificate := ⟨(37/1000),(3/80),(500000000000000000/28384585768098355063),(1827031883911682139/1000000000000000000),2,(569191464366712790283/256000000000000000000),true,MergedCutProfiles.Batch663.profile26527,![MergedCutProfiles.Batch663.profile26527,MergedCutProfiles.Batch663.profile26528,MergedCutProfiles.Batch071.profile2855,MergedCutProfiles.Batch663.profile26529,MergedCutProfiles.Batch663.profile26530,MergedCutProfiles.Batch071.profile2857,MergedCutProfiles.Batch663.profile26531,MergedCutProfiles.Batch663.profile26532,MergedCutProfiles.Batch071.profile2859,MergedCutProfiles.Batch663.profile26533,MergedCutProfiles.Batch663.profile26534,MergedCutProfiles.Batch071.profile2861,MergedCutProfiles.Batch663.profile26535,MergedCutProfiles.Batch071.profile2874,MergedCutProfiles.Batch071.profile2863,MergedCutProfiles.Batch663.profile26536]⟩
theorem profilesValid4688 : retention4688.ProfilesValid := by
  change ∀ j : Fin 16, (retention4688.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch663.valid26527
  · exact MergedCutProfiles.Batch663.valid26528
  · exact MergedCutProfiles.Batch071.valid2855
  · exact MergedCutProfiles.Batch663.valid26529
  · exact MergedCutProfiles.Batch663.valid26530
  · exact MergedCutProfiles.Batch071.valid2857
  · exact MergedCutProfiles.Batch663.valid26531
  · exact MergedCutProfiles.Batch663.valid26532
  · exact MergedCutProfiles.Batch071.valid2859
  · exact MergedCutProfiles.Batch663.valid26533
  · exact MergedCutProfiles.Batch663.valid26534
  · exact MergedCutProfiles.Batch071.valid2861
  · exact MergedCutProfiles.Batch663.valid26535
  · exact MergedCutProfiles.Batch071.valid2874
  · exact MergedCutProfiles.Batch071.valid2863
  · exact MergedCutProfiles.Batch663.valid26536
theorem numericValid4688 : retention4688.NumericValid := by decide +kernel
def certificate4688 : RatCutBinCertificate := ⟨⟨retention4688,(1877155443414554083/1000000000000000000),(247684185361181/3906250000000000),(5424102969128447237/500000000000000000),(39518323636388087884083/1000000000000000000),(275182551600149311/125000000000000000)⟩,(999955424616784063/1000000000000000000),(376657579618030987/1000000000000000000),(63891047584154927/250000000000000000),(108087006854013499/500000000000000000)⟩
theorem valid4688 : certificate4688.Valid := by decide +kernel
theorem sound4688 : certificate4688.Sound := rat_cut_bin_certificate_sound certificate4688 profilesValid4688 numericValid4688 valid4688

def retention4689 : RatCutRetentionCertificate := ⟨(37/1000),(3/80),(1/2),64,1,(638453958017065918268690066180853711/640000000000000000000000000000000000),false,MergedCutProfiles.Batch072.profile2900,(fun _ => MergedCutProfiles.Batch072.profile2900)⟩
theorem profilesValid4689 : retention4689.ProfilesValid := by
  exact MergedCutProfiles.Batch072.valid2900
theorem numericValid4689 : retention4689.NumericValid := by decide +kernel
def certificate4689 : RatCutBinCertificate := ⟨⟨retention4689,(1877155443414554083/1000000000000000000),(247684185361181/3906250000000000),(5424102969128447237/500000000000000000),(39518323636388087884083/1000000000000000000),(98661244150370763/100000000000000000)⟩,(999955424616784063/1000000000000000000),(516818526948953963/1000000000000000000),(142048411184242437/1000000000000000000),(220820549718369/1600000000000000)⟩
theorem valid4689 : certificate4689.Valid := by decide +kernel
theorem sound4689 : certificate4689.Sound := rat_cut_bin_certificate_sound certificate4689 profilesValid4689 numericValid4689 valid4689

def retention4690 : RatCutRetentionCertificate := ⟨(37/1000),(3/80),(500000000000000000/28384585768098355063),(1799751479631376659/62500000000000000),1,(84419106525210486692883068031508664661/38394698232136035392000000000000000000),false,MergedCutProfiles.Batch663.profile26537,(fun _ => MergedCutProfiles.Batch663.profile26537)⟩
theorem profilesValid4690 : retention4690.ProfilesValid := by
  exact MergedCutProfiles.Batch663.valid26537
theorem numericValid4690 : retention4690.NumericValid := by decide +kernel
def certificate4690 : RatCutBinCertificate := ⟨⟨retention4690,(1756710140414554083/1000000000000000000),(247684185361181/3906250000000000),(5424102969128447237/500000000000000000),(39518323636388087884083/1000000000000000000),(2188449930318837869/1000000000000000000)⟩,(999958284747657209/1000000000000000000),(2170881843742363/100000000000000000),(868828779027163163/1000000000000000000),(883508480538506563/500000000000000000)⟩
theorem valid4690 : certificate4690.Valid := by decide +kernel
theorem sound4690 : certificate4690.Sound := rat_cut_bin_certificate_sound certificate4690 profilesValid4690 numericValid4690 valid4690

def retention4691 : RatCutRetentionCertificate := ⟨(37/1000),(3/80),(1/2),64,1,(638453958017065918268690066180853711/640000000000000000000000000000000000),false,MergedCutProfiles.Batch072.profile2900,(fun _ => MergedCutProfiles.Batch072.profile2900)⟩
theorem profilesValid4691 : retention4691.ProfilesValid := by
  exact MergedCutProfiles.Batch072.valid2900
theorem numericValid4691 : retention4691.NumericValid := by decide +kernel
def certificate4691 : RatCutBinCertificate := ⟨⟨retention4691,(1756710140414554083/1000000000000000000),(247684185361181/3906250000000000),(5424102969128447237/500000000000000000),(39518323636388087884083/1000000000000000000),(987316437519637817/1000000000000000000)⟩,(999958284747657209/1000000000000000000),(24059491157686257/500000000000000000),(793433031597980171/1000000000000000000),(771435672593910231/1000000000000000000)⟩
theorem valid4691 : certificate4691.Valid := by decide +kernel
theorem sound4691 : certificate4691.Sound := rat_cut_bin_certificate_sound certificate4691 profilesValid4691 numericValid4691 valid4691

def certificates : List RatCutBinCertificate := [certificate4680,certificate4681,certificate4682,certificate4683,certificate4684,certificate4685,certificate4686,certificate4687,certificate4688,certificate4689,certificate4690,certificate4691]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4680,List.forall_mem_cons.mpr ⟨sound4681,List.forall_mem_cons.mpr ⟨sound4682,List.forall_mem_cons.mpr ⟨sound4683,List.forall_mem_cons.mpr ⟨sound4684,List.forall_mem_cons.mpr ⟨sound4685,List.forall_mem_cons.mpr ⟨sound4686,List.forall_mem_cons.mpr ⟨sound4687,List.forall_mem_cons.mpr ⟨sound4688,List.forall_mem_cons.mpr ⟨sound4689,List.forall_mem_cons.mpr ⟨sound4690,List.forall_mem_cons.mpr ⟨sound4691,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch390
