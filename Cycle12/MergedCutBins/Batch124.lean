import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch240
import Cycle12.MergedCutProfiles.Batch241
import Cycle12.MergedCutProfiles.Batch242

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch124

def retention1488 : RatCutRetentionCertificate := ⟨(31/500),(497/8000),(5675615705269870672/11495823748135086563),(2700076799803130003/500000000000000000),(11/10),(67759681723806814679090030281344521117/67501919995078250075000000000000000000),false,MergedCutProfiles.Batch240.profile9629,(fun _ => MergedCutProfiles.Batch240.profile9629)⟩
theorem profilesValid1488 : retention1488.ProfilesValid := by
  exact MergedCutProfiles.Batch240.valid9629
theorem numericValid1488 : retention1488.NumericValid := by decide +kernel
def certificate1488 : RatCutBinCertificate := ⟨⟨retention1488,(533869401535019277/200000000000000000),(198160259625531349/1000000000000000000),(1028618863260152853/62500000000000000),(189343907653076126043/1000000000000000000),(968458252450474977/1000000000000000000)⟩,(9886495369126001/10000000000000000),(205168102068543671/500000000000000000),(112072084707821333/500000000000000000),(169757344302583401/1000000000000000000)⟩
theorem valid1488 : certificate1488.Valid := by decide +kernel
theorem sound1488 : certificate1488.Sound := rat_cut_bin_certificate_sound certificate1488 profilesValid1488 numericValid1488 valid1488

def retention1489 : RatCutRetentionCertificate := ⟨(31/500),(497/8000),(5732371862322569379/11495823748135086563),(354725981579366917/62500000000000000),(21/20),(139259582228443415386436282358128335119/141890392631746766800000000000000000000),false,MergedCutProfiles.Batch240.profile9630,(fun _ => MergedCutProfiles.Batch240.profile9630)⟩
theorem profilesValid1489 : retention1489.ProfilesValid := by
  exact MergedCutProfiles.Batch240.valid9630
theorem numericValid1489 : retention1489.NumericValid := by decide +kernel
def certificate1489 : RatCutBinCertificate := ⟨⟨retention1489,(533869401535019277/200000000000000000),(198160259625531349/1000000000000000000),(1028618863260152853/62500000000000000),(189343907653076126043/1000000000000000000),(947705830337111927/1000000000000000000)⟩,(9886495369126001/10000000000000000),(20966077787788151/50000000000000000),(216238118149465673/1000000000000000000),(2615941332487961/15625000000000000)⟩
theorem valid1489 : certificate1489.Valid := by decide +kernel
theorem sound1489 : certificate1489.Sound := rat_cut_bin_certificate_sound certificate1489 profilesValid1489 numericValid1489 valid1489

def retention1490 : RatCutRetentionCertificate := ⟨(31/500),(497/8000),(1/2),(5732371862322569379/1000000000000000000),(21/20),(8982159141565227343199011645194062821079/9171794979716111006400000000000000000000),false,MergedCutProfiles.Batch240.profile9627,(fun _ => MergedCutProfiles.Batch240.profile9627)⟩
theorem profilesValid1490 : retention1490.ProfilesValid := by
  exact MergedCutProfiles.Batch240.valid9627
theorem numericValid1490 : retention1490.NumericValid := by decide +kernel
def certificate1490 : RatCutBinCertificate := ⟨⟨retention1490,(533869401535019277/200000000000000000),(198160259625531349/1000000000000000000),(1028618863260152853/62500000000000000),(189343907653076126043/1000000000000000000),(472785527839318521/500000000000000000)⟩,(9886495369126001/10000000000000000),(105067059949967317/250000000000000000),(43083285637004419/200000000000000000),(41668903145392953/250000000000000000)⟩
theorem valid1490 : certificate1490.Valid := by decide +kernel
theorem sound1490 : certificate1490.Sound := rat_cut_bin_certificate_sound certificate1490 profilesValid1490 numericValid1490 valid1490

def retention1491 : RatCutRetentionCertificate := ⟨(497/8000),(249/4000),(1120650425495245777/11440819367386345185),(436923918714374483/500000000000000000),(13/5),(1216997755026733871087/640000000000000000000),true,MergedCutProfiles.Batch240.profile9631,![MergedCutProfiles.Batch240.profile9631,MergedCutProfiles.Batch240.profile9632,MergedCutProfiles.Batch240.profile9633,MergedCutProfiles.Batch240.profile9634,MergedCutProfiles.Batch240.profile9635,MergedCutProfiles.Batch240.profile9636,MergedCutProfiles.Batch240.profile9637,MergedCutProfiles.Batch240.profile9638,MergedCutProfiles.Batch240.profile9639,MergedCutProfiles.Batch241.profile9640,MergedCutProfiles.Batch241.profile9641,MergedCutProfiles.Batch241.profile9642,MergedCutProfiles.Batch241.profile9643,MergedCutProfiles.Batch241.profile9644,MergedCutProfiles.Batch241.profile9645,MergedCutProfiles.Batch241.profile9646]⟩
theorem profilesValid1491 : retention1491.ProfilesValid := by
  change ∀ j : Fin 16, (retention1491.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch240.valid9631
  · exact MergedCutProfiles.Batch240.valid9632
  · exact MergedCutProfiles.Batch240.valid9633
  · exact MergedCutProfiles.Batch240.valid9634
  · exact MergedCutProfiles.Batch240.valid9635
  · exact MergedCutProfiles.Batch240.valid9636
  · exact MergedCutProfiles.Batch240.valid9637
  · exact MergedCutProfiles.Batch240.valid9638
  · exact MergedCutProfiles.Batch240.valid9639
  · exact MergedCutProfiles.Batch241.valid9640
  · exact MergedCutProfiles.Batch241.valid9641
  · exact MergedCutProfiles.Batch241.valid9642
  · exact MergedCutProfiles.Batch241.valid9643
  · exact MergedCutProfiles.Batch241.valid9644
  · exact MergedCutProfiles.Batch241.valid9645
  · exact MergedCutProfiles.Batch241.valid9646
theorem numericValid1491 : retention1491.NumericValid := by decide +kernel
def certificate1491 : RatCutBinCertificate := ⟨⟨retention1491,(583862532276796507/250000000000000000),(99557273866218649/500000000000000000),(3299259209000563867/200000000000000000),(11804854752523603839/62500000000000000),(1828232322816860861/1000000000000000000)⟩,(990059869617720289/1000000000000000000),(173111513359991407/500000000000000000),(57308278519755639/200000000000000000),(152009474571582051/1000000000000000000)⟩
theorem valid1491 : certificate1491.Valid := by decide +kernel
theorem sound1491 : certificate1491.Sound := rat_cut_bin_certificate_sound certificate1491 profilesValid1491 numericValid1491 valid1491

def retention1492 : RatCutRetentionCertificate := ⟨(497/8000),(249/4000),(734856132621167681/3813606455795448395),(1120650425495245777/1000000000000000000),(21/10),(2110327336357977240861/1280000000000000000000),true,MergedCutProfiles.Batch241.profile9647,![MergedCutProfiles.Batch241.profile9647,MergedCutProfiles.Batch241.profile9648,MergedCutProfiles.Batch241.profile9649,MergedCutProfiles.Batch241.profile9650,MergedCutProfiles.Batch241.profile9651,MergedCutProfiles.Batch241.profile9652,MergedCutProfiles.Batch241.profile9653,MergedCutProfiles.Batch241.profile9654,MergedCutProfiles.Batch241.profile9655,MergedCutProfiles.Batch241.profile9656,MergedCutProfiles.Batch241.profile9657,MergedCutProfiles.Batch241.profile9658,MergedCutProfiles.Batch241.profile9659,MergedCutProfiles.Batch241.profile9660,MergedCutProfiles.Batch241.profile9661,MergedCutProfiles.Batch241.profile9662]⟩
theorem profilesValid1492 : retention1492.ProfilesValid := by
  change ∀ j : Fin 16, (retention1492.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch241.valid9647
  · exact MergedCutProfiles.Batch241.valid9648
  · exact MergedCutProfiles.Batch241.valid9649
  · exact MergedCutProfiles.Batch241.valid9650
  · exact MergedCutProfiles.Batch241.valid9651
  · exact MergedCutProfiles.Batch241.valid9652
  · exact MergedCutProfiles.Batch241.valid9653
  · exact MergedCutProfiles.Batch241.valid9654
  · exact MergedCutProfiles.Batch241.valid9655
  · exact MergedCutProfiles.Batch241.valid9656
  · exact MergedCutProfiles.Batch241.valid9657
  · exact MergedCutProfiles.Batch241.valid9658
  · exact MergedCutProfiles.Batch241.valid9659
  · exact MergedCutProfiles.Batch241.valid9660
  · exact MergedCutProfiles.Batch241.valid9661
  · exact MergedCutProfiles.Batch241.valid9662
theorem numericValid1492 : retention1492.NumericValid := by decide +kernel
def certificate1492 : RatCutBinCertificate := ⟨⟨retention1492,(583862532276796507/250000000000000000),(99557273866218649/500000000000000000),(3299259209000563867/200000000000000000),(11804854752523603839/62500000000000000),(1589468794315180689/1000000000000000000)⟩,(990059869617720289/1000000000000000000),(363650026704122573/1000000000000000000),(268491003705234749/1000000000000000000),(6076930413981041/40000000000000000)⟩
theorem valid1492 : certificate1492.Valid := by decide +kernel
theorem sound1492 : certificate1492.Sound := rat_cut_bin_certificate_sound certificate1492 profilesValid1492 numericValid1492 valid1492

def retention1493 : RatCutRetentionCertificate := ⟨(497/8000),(249/4000),(4380244657380770158/11440819367386345185),(2204568397863503043/1000000000000000000),(13/10),(1552323456278024572647/1280000000000000000000),true,MergedCutProfiles.Batch241.profile9663,![MergedCutProfiles.Batch241.profile9663,MergedCutProfiles.Batch241.profile9664,MergedCutProfiles.Batch241.profile9665,MergedCutProfiles.Batch241.profile9666,MergedCutProfiles.Batch241.profile9667,MergedCutProfiles.Batch241.profile9668,MergedCutProfiles.Batch241.profile9669,MergedCutProfiles.Batch241.profile9670,MergedCutProfiles.Batch241.profile9671,MergedCutProfiles.Batch241.profile9672,MergedCutProfiles.Batch241.profile9673,MergedCutProfiles.Batch241.profile9674,MergedCutProfiles.Batch241.profile9675,MergedCutProfiles.Batch241.profile9676,MergedCutProfiles.Batch241.profile9677,MergedCutProfiles.Batch241.profile9678]⟩
theorem profilesValid1493 : retention1493.ProfilesValid := by
  change ∀ j : Fin 16, (retention1493.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch241.valid9663
  · exact MergedCutProfiles.Batch241.valid9664
  · exact MergedCutProfiles.Batch241.valid9665
  · exact MergedCutProfiles.Batch241.valid9666
  · exact MergedCutProfiles.Batch241.valid9667
  · exact MergedCutProfiles.Batch241.valid9668
  · exact MergedCutProfiles.Batch241.valid9669
  · exact MergedCutProfiles.Batch241.valid9670
  · exact MergedCutProfiles.Batch241.valid9671
  · exact MergedCutProfiles.Batch241.valid9672
  · exact MergedCutProfiles.Batch241.valid9673
  · exact MergedCutProfiles.Batch241.valid9674
  · exact MergedCutProfiles.Batch241.valid9675
  · exact MergedCutProfiles.Batch241.valid9676
  · exact MergedCutProfiles.Batch241.valid9677
  · exact MergedCutProfiles.Batch241.valid9678
theorem numericValid1493 : retention1493.NumericValid := by decide +kernel
def certificate1493 : RatCutBinCertificate := ⟨⟨retention1493,(583862532276796507/250000000000000000),(99557273866218649/500000000000000000),(3299259209000563867/200000000000000000),(11804854752523603839/62500000000000000),(588046444672127277/500000000000000000)⟩,(990059869617720289/1000000000000000000),(410106856893976847/1000000000000000000),(112174262082050079/500000000000000000),(152475380088554379/1000000000000000000)⟩
theorem valid1493 : certificate1493.Valid := by decide +kernel
theorem sound1493 : certificate1493.Sound := rat_cut_bin_certificate_sound certificate1493 profilesValid1493 numericValid1493 valid1493

def retention1494 : RatCutRetentionCertificate := ⟨(497/8000),(249/4000),(5452159994631083543/11440819367386345185),(2190122328690385079/500000000000000000),1,(128007008591215726559/128000000000000000000),true,MergedCutProfiles.Batch241.profile9679,![MergedCutProfiles.Batch241.profile9679,MergedCutProfiles.Batch242.profile9680,MergedCutProfiles.Batch242.profile9681,MergedCutProfiles.Batch242.profile9682,MergedCutProfiles.Batch242.profile9683,MergedCutProfiles.Batch242.profile9684,MergedCutProfiles.Batch242.profile9685,MergedCutProfiles.Batch242.profile9686,MergedCutProfiles.Batch242.profile9687,MergedCutProfiles.Batch242.profile9688,MergedCutProfiles.Batch242.profile9689,MergedCutProfiles.Batch242.profile9690,MergedCutProfiles.Batch242.profile9691,MergedCutProfiles.Batch242.profile9692,MergedCutProfiles.Batch242.profile9693,MergedCutProfiles.Batch242.profile9694]⟩
theorem profilesValid1494 : retention1494.ProfilesValid := by
  change ∀ j : Fin 16, (retention1494.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch241.valid9679
  · exact MergedCutProfiles.Batch242.valid9680
  · exact MergedCutProfiles.Batch242.valid9681
  · exact MergedCutProfiles.Batch242.valid9682
  · exact MergedCutProfiles.Batch242.valid9683
  · exact MergedCutProfiles.Batch242.valid9684
  · exact MergedCutProfiles.Batch242.valid9685
  · exact MergedCutProfiles.Batch242.valid9686
  · exact MergedCutProfiles.Batch242.valid9687
  · exact MergedCutProfiles.Batch242.valid9688
  · exact MergedCutProfiles.Batch242.valid9689
  · exact MergedCutProfiles.Batch242.valid9690
  · exact MergedCutProfiles.Batch242.valid9691
  · exact MergedCutProfiles.Batch242.valid9692
  · exact MergedCutProfiles.Batch242.valid9693
  · exact MergedCutProfiles.Batch242.valid9694
theorem numericValid1494 : retention1494.NumericValid := by decide +kernel
def certificate1494 : RatCutBinCertificate := ⟨⟨retention1494,(583862532276796507/250000000000000000),(99557273866218649/500000000000000000),(3299259209000563867/200000000000000000),(11804854752523603839/62500000000000000),(971858484842182741/1000000000000000000)⟩,(990059869617720289/1000000000000000000),(17829154614411237/40000000000000000),(48525520993236813/250000000000000000),(152668493622643723/1000000000000000000)⟩
theorem valid1494 : certificate1494.Valid := by decide +kernel
theorem sound1494 : certificate1494.Sound := rat_cut_bin_certificate_sound certificate1494 profilesValid1494 numericValid1494 valid1494

def retention1495 : RatCutRetentionCertificate := ⟨(497/8000),(249/4000),(1891179851191561336/3813606455795448395),(5452159994631083543/1000000000000000000),(11/10),(2180719577025983877088377221528551710151/2180863997852433417200000000000000000000),false,MergedCutProfiles.Batch242.profile9695,(fun _ => MergedCutProfiles.Batch242.profile9695)⟩
theorem profilesValid1495 : retention1495.ProfilesValid := by
  exact MergedCutProfiles.Batch242.valid9695
theorem numericValid1495 : retention1495.NumericValid := by decide +kernel
def certificate1495 : RatCutBinCertificate := ⟨⟨retention1495,(583862532276796507/250000000000000000),(99557273866218649/500000000000000000),(3299259209000563867/200000000000000000),(11804854752523603839/62500000000000000),(121114986710391211/125000000000000000)⟩,(990059869617720289/1000000000000000000),(218488803515802749/500000000000000000),(50314965555587543/250000000000000000),(152895778489893491/1000000000000000000)⟩
theorem valid1495 : certificate1495.Valid := by decide +kernel
theorem sound1495 : certificate1495.Sound := rat_cut_bin_certificate_sound certificate1495 profilesValid1495 numericValid1495 valid1495

def retention1496 : RatCutRetentionCertificate := ⟨(497/8000),(249/4000),(1/2),(709192444196835501/125000000000000000),(11/10),(46963217865701383847982624451010533077/47279496279789033400000000000000000000),false,MergedCutProfiles.Batch242.profile9696,(fun _ => MergedCutProfiles.Batch242.profile9696)⟩
theorem profilesValid1496 : retention1496.ProfilesValid := by
  exact MergedCutProfiles.Batch242.valid9696
theorem numericValid1496 : retention1496.NumericValid := by decide +kernel
def certificate1496 : RatCutBinCertificate := ⟨⟨retention1496,(583862532276796507/250000000000000000),(99557273866218649/500000000000000000),(3299259209000563867/200000000000000000),(11804854752523603839/62500000000000000),(962296781168293389/1000000000000000000)⟩,(990059869617720289/1000000000000000000),(109590785041680211/250000000000000000),(200115029009459699/1000000000000000000),(151878246059035109/1000000000000000000)⟩
theorem valid1496 : certificate1496.Valid := by decide +kernel
theorem sound1496 : certificate1496.Sound := rat_cut_bin_certificate_sound certificate1496 profilesValid1496 numericValid1496 valid1496

def retention1497 : RatCutRetentionCertificate := ⟨(497/8000),(249/4000),(1/2),64,1,(63852895011850367624910060223028157231/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch242.profile9696,(fun _ => MergedCutProfiles.Batch242.profile9696)⟩
theorem profilesValid1497 : retention1497.ProfilesValid := by
  exact MergedCutProfiles.Batch242.valid9696
theorem numericValid1497 : retention1497.NumericValid := by decide +kernel
def certificate1497 : RatCutBinCertificate := ⟨⟨retention1497,(583862532276796507/250000000000000000),(99557273866218649/500000000000000000),(3299259209000563867/200000000000000000),(11804854752523603839/62500000000000000),(19390230696914369/20000000000000000)⟩,(990059869617720289/1000000000000000000),(398966082304174007/1000000000000000000),(234431026934180623/1000000000000000000),(110822288332454701/500000000000000000)⟩
theorem valid1497 : certificate1497.Valid := by decide +kernel
theorem sound1497 : certificate1497.Sound := rat_cut_bin_certificate_sound certificate1497 profilesValid1497 numericValid1497 valid1497

def retention1498 : RatCutRetentionCertificate := ⟨(497/8000),(249/4000),(5373714370972225387/11440819367386345185),(3434098583795208547/1000000000000000000),(6/5),(90344846933766179401623803169249119549/85852464594880213675000000000000000000),false,MergedCutProfiles.Batch242.profile9697,(fun _ => MergedCutProfiles.Batch242.profile9697)⟩
theorem profilesValid1498 : retention1498.ProfilesValid := by
  exact MergedCutProfiles.Batch242.valid9697
theorem numericValid1498 : retention1498.NumericValid := by decide +kernel
def certificate1498 : RatCutBinCertificate := ⟨⟨retention1498,(667721499526796507/250000000000000000),(99557273866218649/500000000000000000),(3299259209000563867/200000000000000000),(11804854752523603839/62500000000000000),(50681546804363007/50000000000000000)⟩,(988628179305402093/1000000000000000000),(97815897939018593/250000000000000000),(120791578444456973/500000000000000000),(167208889030901093/1000000000000000000)⟩
theorem valid1498 : certificate1498.Valid := by decide +kernel
theorem sound1498 : certificate1498.Sound := rat_cut_bin_certificate_sound certificate1498 profilesValid1498 numericValid1498 valid1498

def retention1499 : RatCutRetentionCertificate := ⟨(497/8000),(249/4000),(1882609270086202864/3813606455795448395),(5373714370972225387/1000000000000000000),(11/10),(2157561463525042957267681005846381728111/2149485748388890154800000000000000000000),false,MergedCutProfiles.Batch242.profile9698,(fun _ => MergedCutProfiles.Batch242.profile9698)⟩
theorem profilesValid1499 : retention1499.ProfilesValid := by
  exact MergedCutProfiles.Batch242.valid9698
theorem numericValid1499 : retention1499.NumericValid := by decide +kernel
def certificate1499 : RatCutBinCertificate := ⟨⟨retention1499,(667721499526796507/250000000000000000),(99557273866218649/500000000000000000),(3299259209000563867/200000000000000000),(11804854752523603839/62500000000000000),(193657721938324957/200000000000000000)⟩,(988628179305402093/1000000000000000000),(409585403359107211/1000000000000000000),(224813630975354287/1000000000000000000),(170125473041459491/1000000000000000000)⟩
theorem valid1499 : certificate1499.Valid := by decide +kernel
theorem sound1499 : certificate1499.Sound := rat_cut_bin_certificate_sound certificate1499 profilesValid1499 numericValid1499 valid1499

def certificates : List RatCutBinCertificate := [certificate1488,certificate1489,certificate1490,certificate1491,certificate1492,certificate1493,certificate1494,certificate1495,certificate1496,certificate1497,certificate1498,certificate1499]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1488,List.forall_mem_cons.mpr ⟨sound1489,List.forall_mem_cons.mpr ⟨sound1490,List.forall_mem_cons.mpr ⟨sound1491,List.forall_mem_cons.mpr ⟨sound1492,List.forall_mem_cons.mpr ⟨sound1493,List.forall_mem_cons.mpr ⟨sound1494,List.forall_mem_cons.mpr ⟨sound1495,List.forall_mem_cons.mpr ⟨sound1496,List.forall_mem_cons.mpr ⟨sound1497,List.forall_mem_cons.mpr ⟨sound1498,List.forall_mem_cons.mpr ⟨sound1499,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch124
