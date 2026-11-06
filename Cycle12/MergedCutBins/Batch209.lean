import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch195
import Cycle12.MergedCutProfiles.Batch390
import Cycle12.MergedCutProfiles.Batch391
import Cycle12.MergedCutProfiles.Batch392

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch209

def retention2508 : RatCutRetentionCertificate := ⟨(111/2000),(7/125),(1/2),(731141260788029903/50000000000000000),1,(14395157493553019488843928877000789631/14622825215760598060000000000000000000),false,MergedCutProfiles.Batch195.profile7817,(fun _ => MergedCutProfiles.Batch195.profile7817)⟩
theorem profilesValid2508 : retention2508.ProfilesValid := by
  exact MergedCutProfiles.Batch195.valid7817
theorem numericValid2508 : retention2508.NumericValid := by decide +kernel
def certificate2508 : RatCutBinCertificate := ⟨⟨retention2508,(4435331249270571/2000000000000000),(155212952940275013/1000000000000000000),(3659293138282251463/250000000000000000),(26948029335976110447/62500000000000000),(480456949501845677/500000000000000000)⟩,(995635036137647583/1000000000000000000),(213548432679801923/500000000000000000),(209552269016728063/1000000000000000000),(188088260493562733/1000000000000000000)⟩
theorem valid2508 : certificate2508.Valid := by decide +kernel
theorem sound2508 : certificate2508.Sound := rat_cut_bin_certificate_sound certificate2508 profilesValid2508 numericValid2508 valid2508

def retention2509 : RatCutRetentionCertificate := ⟨(111/2000),(7/125),(6564281643171832940/14684821021866378471),(21446358079377297/4000000000000000),(21/20),(92272404998955072241489274046977739791/85785432317509188000000000000000000000),false,MergedCutProfiles.Batch390.profile15614,(fun _ => MergedCutProfiles.Batch390.profile15614)⟩
theorem profilesValid2509 : retention2509.ProfilesValid := by
  exact MergedCutProfiles.Batch390.valid15614
theorem numericValid2509 : retention2509.NumericValid := by decide +kernel
def certificate2509 : RatCutBinCertificate := ⟨⟨retention2509,(4958650017270571/2000000000000000),(155212952940275013/1000000000000000000),(3659293138282251463/250000000000000000),(26948029335976110447/62500000000000000),(52400572439613879/50000000000000000)⟩,(995119569362839797/1000000000000000000),(222454638339903503/1000000000000000000),(443018774277256887/1000000000000000000),(373605231665962379/1000000000000000000)⟩
theorem valid2509 : certificate2509.Valid := by decide +kernel
theorem sound2509 : certificate2509.Sound := rat_cut_bin_certificate_sound certificate2509 profilesValid2509 numericValid2509 valid2509

def retention2510 : RatCutRetentionCertificate := ⟨(111/2000),(7/125),(14502101480956448123/29369642043732756942),(328214082158591647/25000000000000000),1,(52223992029449675468591852715959098311/52514253145374663520000000000000000000),false,MergedCutProfiles.Batch390.profile15615,(fun _ => MergedCutProfiles.Batch390.profile15615)⟩
theorem profilesValid2510 : retention2510.ProfilesValid := by
  exact MergedCutProfiles.Batch390.valid15615
theorem numericValid2510 : retention2510.NumericValid := by decide +kernel
def certificate2510 : RatCutBinCertificate := ⟨⟨retention2510,(4958650017270571/2000000000000000),(155212952940275013/1000000000000000000),(3659293138282251463/250000000000000000),(26948029335976110447/62500000000000000),(968181170601960723/1000000000000000000)⟩,(995119569362839797/1000000000000000000),(120398441374466177/500000000000000000),(406493055559801/976562500000000),(93355623610812049/250000000000000000)⟩
theorem valid2510 : certificate2510.Valid := by decide +kernel
theorem sound2510 : certificate2510.Sound := rat_cut_bin_certificate_sound certificate2510 profilesValid2510 numericValid2510 valid2510

def retention2511 : RatCutRetentionCertificate := ⟨(111/2000),(7/125),(4882374165255337535/9789880681244252314),(14502101480956448123/1000000000000000000),1,(357756200615881480298630633150338167/362552537023911203075000000000000000),false,MergedCutProfiles.Batch390.profile15616,(fun _ => MergedCutProfiles.Batch390.profile15616)⟩
theorem profilesValid2511 : retention2511.ProfilesValid := by
  exact MergedCutProfiles.Batch390.valid15616
theorem numericValid2511 : retention2511.NumericValid := by decide +kernel
def certificate2511 : RatCutBinCertificate := ⟨⟨retention2511,(4958650017270571/2000000000000000),(155212952940275013/1000000000000000000),(3659293138282251463/250000000000000000),(26948029335976110447/62500000000000000),(960479165923474331/1000000000000000000)⟩,(995119569362839797/1000000000000000000),(12136390672931021/50000000000000000),(413512471270288523/1000000000000000000),(74123381036078137/200000000000000000)⟩
theorem valid2511 : certificate2511.Valid := by decide +kernel
theorem sound2511 : certificate2511.Sound := rat_cut_bin_certificate_sound certificate2511 profilesValid2511 numericValid2511 valid2511

def retention2512 : RatCutRetentionCertificate := ⟨(111/2000),(7/125),(1/2),(2929424499153202521/200000000000000000),1,(14419493195672135744934957907462137701/14647122495766012605000000000000000000),false,MergedCutProfiles.Batch195.profile7817,(fun _ => MergedCutProfiles.Batch195.profile7817)⟩
theorem profilesValid2512 : retention2512.ProfilesValid := by
  exact MergedCutProfiles.Batch195.valid7817
theorem numericValid2512 : retention2512.NumericValid := by decide +kernel
def certificate2512 : RatCutBinCertificate := ⟨⟨retention2512,(4958650017270571/2000000000000000),(155212952940275013/1000000000000000000),(3659293138282251463/250000000000000000),(26948029335976110447/62500000000000000),(239541909808598443/250000000000000000)⟩,(995119569362839797/1000000000000000000),(243313380948084041/1000000000000000000),(206342814126932919/500000000000000000),(14770720983093791/40000000000000000)⟩
theorem valid2512 : certificate2512.Valid := by decide +kernel
theorem sound2512 : certificate2512.Sound := rat_cut_bin_certificate_sound certificate2512 profilesValid2512 numericValid2512 valid2512

def retention2513 : RatCutRetentionCertificate := ⟨(7/125),(57/1000),(894991256611083313/28179275827658174181),(886129957040676547/1000000000000000000),(57/20),(85254977973015957207/40000000000000000000),true,MergedCutProfiles.Batch390.profile15617,![MergedCutProfiles.Batch390.profile15617,MergedCutProfiles.Batch390.profile15618,MergedCutProfiles.Batch390.profile15619,MergedCutProfiles.Batch390.profile15620,MergedCutProfiles.Batch390.profile15621,MergedCutProfiles.Batch390.profile15622,MergedCutProfiles.Batch390.profile15623,MergedCutProfiles.Batch390.profile15624,MergedCutProfiles.Batch390.profile15625,MergedCutProfiles.Batch390.profile15626,MergedCutProfiles.Batch390.profile15627,MergedCutProfiles.Batch390.profile15628,MergedCutProfiles.Batch390.profile15629,MergedCutProfiles.Batch390.profile15630,MergedCutProfiles.Batch390.profile15631,MergedCutProfiles.Batch390.profile15632]⟩
theorem profilesValid2513 : retention2513.ProfilesValid := by
  change ∀ j : Fin 16, (retention2513.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch390.valid15617
  · exact MergedCutProfiles.Batch390.valid15618
  · exact MergedCutProfiles.Batch390.valid15619
  · exact MergedCutProfiles.Batch390.valid15620
  · exact MergedCutProfiles.Batch390.valid15621
  · exact MergedCutProfiles.Batch390.valid15622
  · exact MergedCutProfiles.Batch390.valid15623
  · exact MergedCutProfiles.Batch390.valid15624
  · exact MergedCutProfiles.Batch390.valid15625
  · exact MergedCutProfiles.Batch390.valid15626
  · exact MergedCutProfiles.Batch390.valid15627
  · exact MergedCutProfiles.Batch390.valid15628
  · exact MergedCutProfiles.Batch390.valid15629
  · exact MergedCutProfiles.Batch390.valid15630
  · exact MergedCutProfiles.Batch390.valid15631
  · exact MergedCutProfiles.Batch390.valid15632
theorem numericValid2513 : retention2513.NumericValid := by decide +kernel
def certificate2513 : RatCutBinCertificate := ⟨⟨retention2513,(557613105836908149/250000000000000000),(161735409484216873/1000000000000000000),(7383208782333271881/500000000000000000),(418600884141280149851/1000000000000000000),(257717297905594561/125000000000000000)⟩,(7777303772568247/7812500000000000),(40925233414099033/125000000000000000),(307021109934897933/1000000000000000000),(171724128044002457/1000000000000000000)⟩
theorem valid2513 : certificate2513.Valid := by decide +kernel
theorem sound2513 : certificate2513.Sound := rat_cut_bin_certificate_sound certificate2513 profilesValid2513 numericValid2513 valid2513

def retention2514 : RatCutRetentionCertificate := ⟨(7/125),(57/1000),(977745337000000000/28179275827658174181),(894991256611083313/1000000000000000000),(14/5),(169191400544597687813/80000000000000000000),true,MergedCutProfiles.Batch390.profile15633,![MergedCutProfiles.Batch390.profile15633,MergedCutProfiles.Batch390.profile15634,MergedCutProfiles.Batch390.profile15635,MergedCutProfiles.Batch390.profile15636,MergedCutProfiles.Batch390.profile15637,MergedCutProfiles.Batch390.profile15638,MergedCutProfiles.Batch390.profile15639,MergedCutProfiles.Batch391.profile15640,MergedCutProfiles.Batch391.profile15641,MergedCutProfiles.Batch391.profile15642,MergedCutProfiles.Batch390.profile15628,MergedCutProfiles.Batch391.profile15643,MergedCutProfiles.Batch391.profile15644,MergedCutProfiles.Batch391.profile15645,MergedCutProfiles.Batch391.profile15646,MergedCutProfiles.Batch391.profile15647]⟩
theorem profilesValid2514 : retention2514.ProfilesValid := by
  change ∀ j : Fin 16, (retention2514.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch390.valid15633
  · exact MergedCutProfiles.Batch390.valid15634
  · exact MergedCutProfiles.Batch390.valid15635
  · exact MergedCutProfiles.Batch390.valid15636
  · exact MergedCutProfiles.Batch390.valid15637
  · exact MergedCutProfiles.Batch390.valid15638
  · exact MergedCutProfiles.Batch390.valid15639
  · exact MergedCutProfiles.Batch391.valid15640
  · exact MergedCutProfiles.Batch391.valid15641
  · exact MergedCutProfiles.Batch391.valid15642
  · exact MergedCutProfiles.Batch390.valid15628
  · exact MergedCutProfiles.Batch391.valid15643
  · exact MergedCutProfiles.Batch391.valid15644
  · exact MergedCutProfiles.Batch391.valid15645
  · exact MergedCutProfiles.Batch391.valid15646
  · exact MergedCutProfiles.Batch391.valid15647
theorem numericValid2514 : retention2514.NumericValid := by decide +kernel
def certificate2514 : RatCutBinCertificate := ⟨⟨retention2514,(557613105836908149/250000000000000000),(161735409484216873/1000000000000000000),(7383208782333271881/500000000000000000),(418600884141280149851/1000000000000000000),(409295608936988889/200000000000000000)⟩,(7777303772568247/7812500000000000),(164229171636110929/500000000000000000),(12233740026513847/40000000000000000),(172133947833855847/1000000000000000000)⟩
theorem valid2514 : certificate2514.Valid := by decide +kernel
theorem sound2514 : certificate2514.Sound := rat_cut_bin_certificate_sound certificate2514 profilesValid2514 numericValid2514 valid2514

def retention2515 : RatCutRetentionCertificate := ⟨(7/125),(57/1000),(53609659747137881/1483119780403061799),(977745337/1000000000),(53/20),(33854834577858555617/16000000000000000000),true,MergedCutProfiles.Batch391.profile15648,![MergedCutProfiles.Batch391.profile15648,MergedCutProfiles.Batch391.profile15649,MergedCutProfiles.Batch391.profile15650,MergedCutProfiles.Batch391.profile15651,MergedCutProfiles.Batch391.profile15652,MergedCutProfiles.Batch391.profile15653,MergedCutProfiles.Batch391.profile15654,MergedCutProfiles.Batch391.profile15655,MergedCutProfiles.Batch391.profile15656,MergedCutProfiles.Batch391.profile15657,MergedCutProfiles.Batch391.profile15658,MergedCutProfiles.Batch391.profile15659,MergedCutProfiles.Batch391.profile15660,MergedCutProfiles.Batch390.profile15632,MergedCutProfiles.Batch391.profile15661,MergedCutProfiles.Batch391.profile15662]⟩
theorem profilesValid2515 : retention2515.ProfilesValid := by
  change ∀ j : Fin 16, (retention2515.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch391.valid15648
  · exact MergedCutProfiles.Batch391.valid15649
  · exact MergedCutProfiles.Batch391.valid15650
  · exact MergedCutProfiles.Batch391.valid15651
  · exact MergedCutProfiles.Batch391.valid15652
  · exact MergedCutProfiles.Batch391.valid15653
  · exact MergedCutProfiles.Batch391.valid15654
  · exact MergedCutProfiles.Batch391.valid15655
  · exact MergedCutProfiles.Batch391.valid15656
  · exact MergedCutProfiles.Batch391.valid15657
  · exact MergedCutProfiles.Batch391.valid15658
  · exact MergedCutProfiles.Batch391.valid15659
  · exact MergedCutProfiles.Batch391.valid15660
  · exact MergedCutProfiles.Batch390.valid15632
  · exact MergedCutProfiles.Batch391.valid15661
  · exact MergedCutProfiles.Batch391.valid15662
theorem numericValid2515 : retention2515.NumericValid := by decide +kernel
def certificate2515 : RatCutBinCertificate := ⟨⟨retention2515,(557613105836908149/250000000000000000),(161735409484216873/1000000000000000000),(7383208782333271881/500000000000000000),(418600884141280149851/1000000000000000000),(2051178087105092559/1000000000000000000)⟩,(7777303772568247/7812500000000000),(158005468637694971/500000000000000000),(319936335885374203/1000000000000000000),(189661935821029477/1000000000000000000)⟩
theorem valid2515 : certificate2515.Valid := by decide +kernel
theorem sound2515 : certificate2515.Sound := rat_cut_bin_certificate_sound certificate2515 profilesValid2515 numericValid2515 valid2515

def retention2516 : RatCutRetentionCertificate := ⟨(7/125),(57/1000),(8354630555301875/164791086711451311),(1018583535195619739/1000000000000000000),(51/20),(2639221682670456770843/1280000000000000000000),true,MergedCutProfiles.Batch391.profile15663,![MergedCutProfiles.Batch391.profile15663,MergedCutProfiles.Batch391.profile15664,MergedCutProfiles.Batch391.profile15665,MergedCutProfiles.Batch391.profile15666,MergedCutProfiles.Batch391.profile15654,MergedCutProfiles.Batch391.profile15667,MergedCutProfiles.Batch391.profile15668,MergedCutProfiles.Batch391.profile15669,MergedCutProfiles.Batch391.profile15670,MergedCutProfiles.Batch390.profile15632,MergedCutProfiles.Batch391.profile15671,MergedCutProfiles.Batch391.profile15672,MergedCutProfiles.Batch391.profile15673,MergedCutProfiles.Batch391.profile15674,MergedCutProfiles.Batch391.profile15675,MergedCutProfiles.Batch391.profile15676]⟩
theorem profilesValid2516 : retention2516.ProfilesValid := by
  change ∀ j : Fin 16, (retention2516.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch391.valid15663
  · exact MergedCutProfiles.Batch391.valid15664
  · exact MergedCutProfiles.Batch391.valid15665
  · exact MergedCutProfiles.Batch391.valid15666
  · exact MergedCutProfiles.Batch391.valid15654
  · exact MergedCutProfiles.Batch391.valid15667
  · exact MergedCutProfiles.Batch391.valid15668
  · exact MergedCutProfiles.Batch391.valid15669
  · exact MergedCutProfiles.Batch391.valid15670
  · exact MergedCutProfiles.Batch390.valid15632
  · exact MergedCutProfiles.Batch391.valid15671
  · exact MergedCutProfiles.Batch391.valid15672
  · exact MergedCutProfiles.Batch391.valid15673
  · exact MergedCutProfiles.Batch391.valid15674
  · exact MergedCutProfiles.Batch391.valid15675
  · exact MergedCutProfiles.Batch391.valid15676
theorem numericValid2516 : retention2516.NumericValid := by decide +kernel
def certificate2516 : RatCutBinCertificate := ⟨⟨retention2516,(557613105836908149/250000000000000000),(161735409484216873/1000000000000000000),(7383208782333271881/500000000000000000),(418600884141280149851/1000000000000000000),(399917249923109469/200000000000000000)⟩,(7777303772568247/7812500000000000),(318962604968256409/1000000000000000000),(79137743897938643/250000000000000000),(7585903902015721/40000000000000000)⟩
theorem valid2516 : certificate2516.Valid := by decide +kernel
theorem sound2516 : certificate2516.Sound := rat_cut_bin_certificate_sound certificate2516 profilesValid2516 numericValid2516 valid2516

def retention2517 : RatCutRetentionCertificate := ⟨(7/125),(57/1000),(4762221463687901179/28179275827658174181),(2285826919930593/1600000000000000),(39/20),(87660547886767344873/51200000000000000000),true,MergedCutProfiles.Batch391.profile15677,![MergedCutProfiles.Batch391.profile15677,MergedCutProfiles.Batch391.profile15678,MergedCutProfiles.Batch390.profile15632,MergedCutProfiles.Batch391.profile15679,MergedCutProfiles.Batch392.profile15680,MergedCutProfiles.Batch392.profile15681,MergedCutProfiles.Batch392.profile15682,MergedCutProfiles.Batch392.profile15683,MergedCutProfiles.Batch392.profile15684,MergedCutProfiles.Batch392.profile15685,MergedCutProfiles.Batch392.profile15686,MergedCutProfiles.Batch392.profile15687,MergedCutProfiles.Batch392.profile15688,MergedCutProfiles.Batch392.profile15689,MergedCutProfiles.Batch392.profile15690,MergedCutProfiles.Batch392.profile15691]⟩
theorem profilesValid2517 : retention2517.ProfilesValid := by
  change ∀ j : Fin 16, (retention2517.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch391.valid15677
  · exact MergedCutProfiles.Batch391.valid15678
  · exact MergedCutProfiles.Batch390.valid15632
  · exact MergedCutProfiles.Batch391.valid15679
  · exact MergedCutProfiles.Batch392.valid15680
  · exact MergedCutProfiles.Batch392.valid15681
  · exact MergedCutProfiles.Batch392.valid15682
  · exact MergedCutProfiles.Batch392.valid15683
  · exact MergedCutProfiles.Batch392.valid15684
  · exact MergedCutProfiles.Batch392.valid15685
  · exact MergedCutProfiles.Batch392.valid15686
  · exact MergedCutProfiles.Batch392.valid15687
  · exact MergedCutProfiles.Batch392.valid15688
  · exact MergedCutProfiles.Batch392.valid15689
  · exact MergedCutProfiles.Batch392.valid15690
  · exact MergedCutProfiles.Batch392.valid15691
theorem numericValid2517 : retention2517.NumericValid := by decide +kernel
def certificate2517 : RatCutBinCertificate := ⟨⟨retention2517,(557613105836908149/250000000000000000),(161735409484216873/1000000000000000000),(7383208782333271881/500000000000000000),(418600884141280149851/1000000000000000000),(832237513842730569/500000000000000000)⟩,(7777303772568247/7812500000000000),(340236175246309247/1000000000000000000),(73235589256801691/250000000000000000),(190395341530428807/1000000000000000000)⟩
theorem valid2517 : certificate2517.Valid := by decide +kernel
theorem sound2517 : certificate2517.Sound := rat_cut_bin_certificate_sound certificate2517 profilesValid2517 numericValid2517 valid2517

def retention2518 : RatCutRetentionCertificate := ⟨(7/125),(57/1000),(1348267960230668122/3131030647517574909),(4762221463687901179/1000000000000000000),(11/10),(1432255458278188437727/1280000000000000000000),true,MergedCutProfiles.Batch392.profile15692,![MergedCutProfiles.Batch392.profile15692,MergedCutProfiles.Batch392.profile15693,MergedCutProfiles.Batch392.profile15694,MergedCutProfiles.Batch392.profile15695,MergedCutProfiles.Batch392.profile15696,MergedCutProfiles.Batch392.profile15697,MergedCutProfiles.Batch392.profile15698,MergedCutProfiles.Batch392.profile15699,MergedCutProfiles.Batch392.profile15700,MergedCutProfiles.Batch392.profile15701,MergedCutProfiles.Batch392.profile15702,MergedCutProfiles.Batch392.profile15703,MergedCutProfiles.Batch392.profile15704,MergedCutProfiles.Batch392.profile15705,MergedCutProfiles.Batch392.profile15706,MergedCutProfiles.Batch392.profile15707]⟩
theorem profilesValid2518 : retention2518.ProfilesValid := by
  change ∀ j : Fin 16, (retention2518.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch392.valid15692
  · exact MergedCutProfiles.Batch392.valid15693
  · exact MergedCutProfiles.Batch392.valid15694
  · exact MergedCutProfiles.Batch392.valid15695
  · exact MergedCutProfiles.Batch392.valid15696
  · exact MergedCutProfiles.Batch392.valid15697
  · exact MergedCutProfiles.Batch392.valid15698
  · exact MergedCutProfiles.Batch392.valid15699
  · exact MergedCutProfiles.Batch392.valid15700
  · exact MergedCutProfiles.Batch392.valid15701
  · exact MergedCutProfiles.Batch392.valid15702
  · exact MergedCutProfiles.Batch392.valid15703
  · exact MergedCutProfiles.Batch392.valid15704
  · exact MergedCutProfiles.Batch392.valid15705
  · exact MergedCutProfiles.Batch392.valid15706
  · exact MergedCutProfiles.Batch392.valid15707
theorem numericValid2518 : retention2518.NumericValid := by decide +kernel
def certificate2518 : RatCutBinCertificate := ⟨⟨retention2518,(557613105836908149/250000000000000000),(161735409484216873/1000000000000000000),(7383208782333271881/500000000000000000),(418600884141280149851/1000000000000000000),(1092074627868384821/1000000000000000000)⟩,(7777303772568247/7812500000000000),(404758808536011089/1000000000000000000),(114575144090588731/500000000000000000),(95153073860394853/500000000000000000)⟩
theorem valid2518 : certificate2518.Valid := by decide +kernel
theorem sound2518 : certificate2518.Sound := rat_cut_bin_certificate_sound certificate2518 profilesValid2518 numericValid2518 valid2518

def retention2519 : RatCutRetentionCertificate := ⟨(7/125),(57/1000),(4649397758458923266/9393091942552724727),(6067205821038006549/500000000000000000),(21/20),(4893892953788464972305085833316625684639/4853764656830405239200000000000000000000),false,MergedCutProfiles.Batch392.profile15708,(fun _ => MergedCutProfiles.Batch392.profile15708)⟩
theorem profilesValid2519 : retention2519.ProfilesValid := by
  exact MergedCutProfiles.Batch392.valid15708
theorem numericValid2519 : retention2519.NumericValid := by decide +kernel
def certificate2519 : RatCutBinCertificate := ⟨⟨retention2519,(557613105836908149/250000000000000000),(161735409484216873/1000000000000000000),(7383208782333271881/500000000000000000),(418600884141280149851/1000000000000000000),(15353362688856949/15625000000000000)⟩,(7777303772568247/7812500000000000),(208457010079122871/500000000000000000),(109168707877554133/500000000000000000),(189448638058372203/1000000000000000000)⟩
theorem valid2519 : certificate2519.Valid := by decide +kernel
theorem sound2519 : certificate2519.Sound := rat_cut_bin_certificate_sound certificate2519 profilesValid2519 numericValid2519 valid2519

def certificates : List RatCutBinCertificate := [certificate2508,certificate2509,certificate2510,certificate2511,certificate2512,certificate2513,certificate2514,certificate2515,certificate2516,certificate2517,certificate2518,certificate2519]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2508,List.forall_mem_cons.mpr ⟨sound2509,List.forall_mem_cons.mpr ⟨sound2510,List.forall_mem_cons.mpr ⟨sound2511,List.forall_mem_cons.mpr ⟨sound2512,List.forall_mem_cons.mpr ⟨sound2513,List.forall_mem_cons.mpr ⟨sound2514,List.forall_mem_cons.mpr ⟨sound2515,List.forall_mem_cons.mpr ⟨sound2516,List.forall_mem_cons.mpr ⟨sound2517,List.forall_mem_cons.mpr ⟨sound2518,List.forall_mem_cons.mpr ⟨sound2519,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch209
