import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch516
import Cycle12.MergedCutProfiles.Batch517
import Cycle12.MergedCutProfiles.Batch518

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch280

def retention3360 : RatCutRetentionCertificate := ⟨(23/400),(29/500),(26206716462361575231/67631818480710712871),(140727661875268097/31250000000000000),(23/20),(78110648369333591458340923467001583313/64332645428693987200000000000000000000),false,MergedCutProfiles.Batch516.profile20667,(fun _ => MergedCutProfiles.Batch516.profile20667)⟩
theorem profilesValid3360 : retention3360.ProfilesValid := by
  exact MergedCutProfiles.Batch516.valid20667
theorem numericValid3360 : retention3360.NumericValid := by decide +kernel
def certificate3360 : RatCutBinCertificate := ⟨⟨retention3360,(544253803962492951/250000000000000000),(168442616661570077/1000000000000000000),(3791517888527700071/250000000000000000),(1028803876931968117943/1000000000000000000),(1186361281240860727/1000000000000000000)⟩,(998232602848758741/1000000000000000000),(1237423646650567/3125000000000000),(237190053370731451/1000000000000000000),(50911487448407903/250000000000000000)⟩
theorem valid3360 : certificate3360.Valid := by decide +kernel
theorem sound3360 : certificate3360.Sound := rat_cut_bin_certificate_sound certificate3360 profilesValid3360 numericValid3360 valid3360

def retention3361 : RatCutRetentionCertificate := ⟨(23/400),(29/500),(33275575916512211657/67631818480710712871),(26206716462361575231/1000000000000000000),1,(21127554778180186021962890861740158607/20965373169889260184800000000000000000),false,MergedCutProfiles.Batch516.profile20668,(fun _ => MergedCutProfiles.Batch516.profile20668)⟩
theorem profilesValid3361 : retention3361.ProfilesValid := by
  exact MergedCutProfiles.Batch516.valid20668
theorem numericValid3361 : retention3361.NumericValid := by decide +kernel
def certificate3361 : RatCutBinCertificate := ⟨⟨retention3361,(544253803962492951/250000000000000000),(168442616661570077/1000000000000000000),(3791517888527700071/250000000000000000),(1028803876931968117943/1000000000000000000),(983556426234378981/1000000000000000000)⟩,(998232602848758741/1000000000000000000),(13055670479988669/31250000000000000),(217579441202355507/1000000000000000000),(51471849329406119/250000000000000000)⟩
theorem valid3361 : certificate3361.Valid := by decide +kernel
theorem sound3361 : certificate3361.Sound := rat_cut_bin_certificate_sound certificate3361 profilesValid3361 numericValid3361 valid3361

def retention3362 : RatCutRetentionCertificate := ⟨(23/400),(29/500),(33608331675677333774/67631818480710712871),(33275575916512211657/1000000000000000000),1,(33279351064647760726717156837961562049/33275575916512211657000000000000000000),false,MergedCutProfiles.Batch516.profile20669,(fun _ => MergedCutProfiles.Batch516.profile20669)⟩
theorem profilesValid3362 : retention3362.ProfilesValid := by
  exact MergedCutProfiles.Batch516.valid20669
theorem numericValid3362 : retention3362.NumericValid := by decide +kernel
def certificate3362 : RatCutBinCertificate := ⟨⟨retention3362,(544253803962492951/250000000000000000),(168442616661570077/1000000000000000000),(3791517888527700071/250000000000000000),(1028803876931968117943/1000000000000000000),(121991777533444281/125000000000000000)⟩,(998232602848758741/1000000000000000000),(52298255173605009/125000000000000000),(217052212198334063/1000000000000000000),(205422470294819157/1000000000000000000)⟩
theorem valid3362 : certificate3362.Valid := by decide +kernel
theorem sound3362 : certificate3362.Sound := rat_cut_bin_certificate_sound certificate3362 profilesValid3362 numericValid3362 valid3362

def retention3363 : RatCutRetentionCertificate := ⟨(23/400),(29/500),(1/2),(16804165837838666887/500000000000000000),1,(8352763618792514658798944291338786353/8402082918919333443500000000000000000),false,MergedCutProfiles.Batch516.profile20670,(fun _ => MergedCutProfiles.Batch516.profile20670)⟩
theorem profilesValid3363 : retention3363.ProfilesValid := by
  exact MergedCutProfiles.Batch516.valid20670
theorem numericValid3363 : retention3363.NumericValid := by decide +kernel
def certificate3363 : RatCutBinCertificate := ⟨⟨retention3363,(544253803962492951/250000000000000000),(168442616661570077/1000000000000000000),(3791517888527700071/250000000000000000),(1028803876931968117943/1000000000000000000),(969950880705297437/1000000000000000000)⟩,(998232602848758741/1000000000000000000),(105217190070937037/250000000000000000),(214896301959657809/1000000000000000000),(202227253509921947/1000000000000000000)⟩
theorem valid3363 : certificate3363.Valid := by decide +kernel
theorem sound3363 : certificate3363.Sound := rat_cut_bin_certificate_sound certificate3363 profilesValid3363 numericValid3363 valid3363

def retention3364 : RatCutRetentionCertificate := ⟨(23/400),(29/500),(31169425411229769600/67631818480710712871),(9538614917269786373/1000000000000000000),1,(8011178441396862264596901075573695631/7630891933815829098400000000000000000),false,MergedCutProfiles.Batch516.profile20671,(fun _ => MergedCutProfiles.Batch516.profile20671)⟩
theorem profilesValid3364 : retention3364.ProfilesValid := by
  exact MergedCutProfiles.Batch516.valid20671
theorem numericValid3364 : retention3364.NumericValid := by decide +kernel
def certificate3364 : RatCutBinCertificate := ⟨⟨retention3364,(564429357712492951/250000000000000000),(168442616661570077/1000000000000000000),(3791517888527700071/250000000000000000),(1028803876931968117943/1000000000000000000),(1024759267333519743/1000000000000000000)⟩,(998167061483296731/1000000000000000000),(118964036382215213/1000000000000000000),(6256457832314659/10000000000000000),(4622527310597527/8000000000000000)⟩
theorem valid3364 : certificate3364.Valid := by decide +kernel
theorem sound3364 : certificate3364.Sound := rat_cut_bin_certificate_sound certificate3364 profilesValid3364 numericValid3364 valid3364

def retention3365 : RatCutRetentionCertificate := ⟨(23/400),(29/500),(33417842888242013998/67631818480710712871),(9740445441009303/312500000000000),1,(2610842955800318323146238458591198957/2597452117602480800000000000000000000),false,MergedCutProfiles.Batch516.profile20672,(fun _ => MergedCutProfiles.Batch516.profile20672)⟩
theorem profilesValid3365 : retention3365.ProfilesValid := by
  exact MergedCutProfiles.Batch516.valid20672
theorem numericValid3365 : retention3365.NumericValid := by decide +kernel
def certificate3365 : RatCutBinCertificate := ⟨⟨retention3365,(564429357712492951/250000000000000000),(168442616661570077/1000000000000000000),(3791517888527700071/250000000000000000),(1028803876931968117943/1000000000000000000),(245019952085661181/250000000000000000)⟩,(998167061483296731/1000000000000000000),(124387317975901397/1000000000000000000),(614482785580395087/1000000000000000000),(291395968222037711/500000000000000000)⟩
theorem valid3365 : certificate3365.Valid := by decide +kernel
theorem sound3365 : certificate3365.Sound := rat_cut_bin_certificate_sound certificate3365 profilesValid3365 numericValid3365 valid3365

def retention3366 : RatCutRetentionCertificate := ⟨(23/400),(29/500),(33752021317124434138/67631818480710712871),(16708921444121006999/500000000000000000),1,(52003997218914514445733015294048501/52215379512878146871875000000000000),false,MergedCutProfiles.Batch516.profile20673,(fun _ => MergedCutProfiles.Batch516.profile20673)⟩
theorem profilesValid3366 : retention3366.ProfilesValid := by
  exact MergedCutProfiles.Batch516.valid20673
theorem numericValid3366 : retention3366.NumericValid := by decide +kernel
def certificate3366 : RatCutBinCertificate := ⟨⟨retention3366,(564429357712492951/250000000000000000),(168442616661570077/1000000000000000000),(3791517888527700071/250000000000000000),(1028803876931968117943/1000000000000000000),(121359520785562223/125000000000000000)⟩,(998167061483296731/1000000000000000000),(62783237963611553/500000000000000000),(306041451291299073/500000000000000000),(2251569753232961/3906250000000000)⟩
theorem valid3366 : certificate3366.Valid := by decide +kernel
theorem sound3366 : certificate3366.Sound := rat_cut_bin_certificate_sound certificate3366 profilesValid3366 numericValid3366 valid3366

def retention3367 : RatCutRetentionCertificate := ⟨(23/400),(29/500),(1/2),(16876010658562217069/500000000000000000),1,(8388743233873370623385017908134879877/8438005329281108534500000000000000000),false,MergedCutProfiles.Batch516.profile20670,(fun _ => MergedCutProfiles.Batch516.profile20670)⟩
theorem profilesValid3367 : retention3367.ProfilesValid := by
  exact MergedCutProfiles.Batch516.valid20670
theorem numericValid3367 : retention3367.NumericValid := by decide +kernel
def certificate3367 : RatCutBinCertificate := ⟨⟨retention3367,(564429357712492951/250000000000000000),(168442616661570077/1000000000000000000),(3791517888527700071/250000000000000000),(1028803876931968117943/1000000000000000000),(969086323086957497/1000000000000000000)⟩,(998167061483296731/1000000000000000000),(125798389532258351/1000000000000000000),(305806015460115351/500000000000000000),(35942950394655433/62500000000000000)⟩
theorem valid3367 : certificate3367.Valid := by decide +kernel
theorem sound3367 : certificate3367.Sound := rat_cut_bin_certificate_sound certificate3367 profilesValid3367 numericValid3367 valid3367

def retention3368 : RatCutRetentionCertificate := ⟨(29/500),(117/2000),(434466806637517402/33140000829945450993),(430165155086650893/500000000000000000),(31/10),(90030150406159438881/40000000000000000000),true,MergedCutProfiles.Batch516.profile20674,![MergedCutProfiles.Batch516.profile20674,MergedCutProfiles.Batch516.profile20675,MergedCutProfiles.Batch516.profile20676,MergedCutProfiles.Batch516.profile20677,MergedCutProfiles.Batch516.profile20678,MergedCutProfiles.Batch516.profile20679,MergedCutProfiles.Batch517.profile20680,MergedCutProfiles.Batch517.profile20681,MergedCutProfiles.Batch517.profile20682,MergedCutProfiles.Batch517.profile20683,MergedCutProfiles.Batch517.profile20684,MergedCutProfiles.Batch517.profile20685,MergedCutProfiles.Batch517.profile20686,MergedCutProfiles.Batch517.profile20687,MergedCutProfiles.Batch517.profile20688,MergedCutProfiles.Batch517.profile20689]⟩
theorem profilesValid3368 : retention3368.ProfilesValid := by
  change ∀ j : Fin 16, (retention3368.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch516.valid20674
  · exact MergedCutProfiles.Batch516.valid20675
  · exact MergedCutProfiles.Batch516.valid20676
  · exact MergedCutProfiles.Batch516.valid20677
  · exact MergedCutProfiles.Batch516.valid20678
  · exact MergedCutProfiles.Batch516.valid20679
  · exact MergedCutProfiles.Batch517.valid20680
  · exact MergedCutProfiles.Batch517.valid20681
  · exact MergedCutProfiles.Batch517.valid20682
  · exact MergedCutProfiles.Batch517.valid20683
  · exact MergedCutProfiles.Batch517.valid20684
  · exact MergedCutProfiles.Batch517.valid20685
  · exact MergedCutProfiles.Batch517.valid20686
  · exact MergedCutProfiles.Batch517.valid20687
  · exact MergedCutProfiles.Batch517.valid20688
  · exact MergedCutProfiles.Batch517.valid20689
theorem numericValid3368 : retention3368.NumericValid := by decide +kernel
def certificate3368 : RatCutBinCertificate := ⟨⟨retention3368,(2184127726165908029/1000000000000000000),(42966716513336319/250000000000000000),(3825645658661106153/250000000000000000),(1017325787371704994593/1000000000000000000),(21747045584996721/10000000000000000)⟩,(499107026461154473/500000000000000000),(175009387845446989/500000000000000000),(7063418422604171/25000000000000000),(19574175742692621/125000000000000000)⟩
theorem valid3368 : certificate3368.Valid := by decide +kernel
theorem sound3368 : certificate3368.Sound := rat_cut_bin_certificate_sound certificate3368 profilesValid3368 numericValid3368 valid3368

def retention3369 : RatCutRetentionCertificate := ⟨(29/500),(117/2000),(174961079256467968/11046666943315150331),(217233403318758701/250000000000000000),(61/20),(44627855310474324011/20000000000000000000),true,MergedCutProfiles.Batch517.profile20690,![MergedCutProfiles.Batch517.profile20690,MergedCutProfiles.Batch517.profile20691,MergedCutProfiles.Batch517.profile20692,MergedCutProfiles.Batch517.profile20693,MergedCutProfiles.Batch517.profile20694,MergedCutProfiles.Batch517.profile20695,MergedCutProfiles.Batch517.profile20696,MergedCutProfiles.Batch517.profile20697,MergedCutProfiles.Batch517.profile20698,MergedCutProfiles.Batch517.profile20685,MergedCutProfiles.Batch517.profile20699,MergedCutProfiles.Batch517.profile20700,MergedCutProfiles.Batch517.profile20701,MergedCutProfiles.Batch517.profile20702,MergedCutProfiles.Batch517.profile20703,MergedCutProfiles.Batch517.profile20704]⟩
theorem profilesValid3369 : retention3369.ProfilesValid := by
  change ∀ j : Fin 16, (retention3369.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch517.valid20690
  · exact MergedCutProfiles.Batch517.valid20691
  · exact MergedCutProfiles.Batch517.valid20692
  · exact MergedCutProfiles.Batch517.valid20693
  · exact MergedCutProfiles.Batch517.valid20694
  · exact MergedCutProfiles.Batch517.valid20695
  · exact MergedCutProfiles.Batch517.valid20696
  · exact MergedCutProfiles.Batch517.valid20697
  · exact MergedCutProfiles.Batch517.valid20698
  · exact MergedCutProfiles.Batch517.valid20685
  · exact MergedCutProfiles.Batch517.valid20699
  · exact MergedCutProfiles.Batch517.valid20700
  · exact MergedCutProfiles.Batch517.valid20701
  · exact MergedCutProfiles.Batch517.valid20702
  · exact MergedCutProfiles.Batch517.valid20703
  · exact MergedCutProfiles.Batch517.valid20704
theorem numericValid3369 : retention3369.NumericValid := by decide +kernel
def certificate3369 : RatCutBinCertificate := ⟨⟨retention3369,(2184127726165908029/1000000000000000000),(42966716513336319/250000000000000000),(3825645658661106153/250000000000000000),(1017325787371704994593/1000000000000000000),(2156570133895903393/1000000000000000000)⟩,(499107026461154473/500000000000000000),(351280717033068671/1000000000000000000),(281214467031378527/1000000000000000000),(15662807648422843/100000000000000000)⟩
theorem valid3369 : certificate3369.Valid := by decide +kernel
theorem sound3369 : certificate3369.Sound := rat_cut_bin_certificate_sound certificate3369 profilesValid3369 numericValid3369 valid3369

def retention3370 : RatCutRetentionCertificate := ⟨(29/500),(117/2000),(183424639000000000/11046666943315150331),(1025162573768367/976562500000000),(53/20),(44543134423567493541/20000000000000000000),true,MergedCutProfiles.Batch517.profile20705,![MergedCutProfiles.Batch517.profile20705,MergedCutProfiles.Batch517.profile20706,MergedCutProfiles.Batch517.profile20707,MergedCutProfiles.Batch516.profile20678,MergedCutProfiles.Batch517.profile20708,MergedCutProfiles.Batch517.profile20709,MergedCutProfiles.Batch517.profile20710,MergedCutProfiles.Batch517.profile20711,MergedCutProfiles.Batch517.profile20712,MergedCutProfiles.Batch517.profile20713,MergedCutProfiles.Batch517.profile20714,MergedCutProfiles.Batch517.profile20715,MergedCutProfiles.Batch517.profile20716,MergedCutProfiles.Batch517.profile20717,MergedCutProfiles.Batch517.profile20718,MergedCutProfiles.Batch517.profile20719]⟩
theorem profilesValid3370 : retention3370.ProfilesValid := by
  change ∀ j : Fin 16, (retention3370.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch517.valid20705
  · exact MergedCutProfiles.Batch517.valid20706
  · exact MergedCutProfiles.Batch517.valid20707
  · exact MergedCutProfiles.Batch516.valid20678
  · exact MergedCutProfiles.Batch517.valid20708
  · exact MergedCutProfiles.Batch517.valid20709
  · exact MergedCutProfiles.Batch517.valid20710
  · exact MergedCutProfiles.Batch517.valid20711
  · exact MergedCutProfiles.Batch517.valid20712
  · exact MergedCutProfiles.Batch517.valid20713
  · exact MergedCutProfiles.Batch517.valid20714
  · exact MergedCutProfiles.Batch517.valid20715
  · exact MergedCutProfiles.Batch517.valid20716
  · exact MergedCutProfiles.Batch517.valid20717
  · exact MergedCutProfiles.Batch517.valid20718
  · exact MergedCutProfiles.Batch517.valid20719
theorem numericValid3370 : retention3370.NumericValid := by decide +kernel
def certificate3370 : RatCutBinCertificate := ⟨⟨retention3370,(2184127726165908029/1000000000000000000),(42966716513336319/250000000000000000),(3825645658661106153/250000000000000000),(1017325787371704994593/1000000000000000000),(2162147089774867189/1000000000000000000)⟩,(499107026461154473/500000000000000000),(321486594090559709/1000000000000000000),(313677739589488797/1000000000000000000),(12342149387655603/62500000000000000)⟩
theorem valid3370 : certificate3370.Valid := by decide +kernel
theorem sound3370 : certificate3370.Sound := rat_cut_bin_certificate_sound certificate3370 profilesValid3370 numericValid3370 valid3370

def retention3371 : RatCutRetentionCertificate := ⟨(29/500),(117/2000),(1359716656682717717/66280001659890901986),(550273917/500000000),(51/20),(35279843369692962003/16000000000000000000),true,MergedCutProfiles.Batch518.profile20720,![MergedCutProfiles.Batch518.profile20720,MergedCutProfiles.Batch518.profile20721,MergedCutProfiles.Batch518.profile20722,MergedCutProfiles.Batch518.profile20723,MergedCutProfiles.Batch518.profile20724,MergedCutProfiles.Batch518.profile20725,MergedCutProfiles.Batch517.profile20684,MergedCutProfiles.Batch518.profile20726,MergedCutProfiles.Batch518.profile20727,MergedCutProfiles.Batch518.profile20728,MergedCutProfiles.Batch518.profile20729,MergedCutProfiles.Batch518.profile20730,MergedCutProfiles.Batch518.profile20731,MergedCutProfiles.Batch518.profile20732,MergedCutProfiles.Batch518.profile20733,MergedCutProfiles.Batch518.profile20734]⟩
theorem profilesValid3371 : retention3371.ProfilesValid := by
  change ∀ j : Fin 16, (retention3371.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch518.valid20720
  · exact MergedCutProfiles.Batch518.valid20721
  · exact MergedCutProfiles.Batch518.valid20722
  · exact MergedCutProfiles.Batch518.valid20723
  · exact MergedCutProfiles.Batch518.valid20724
  · exact MergedCutProfiles.Batch518.valid20725
  · exact MergedCutProfiles.Batch517.valid20684
  · exact MergedCutProfiles.Batch518.valid20726
  · exact MergedCutProfiles.Batch518.valid20727
  · exact MergedCutProfiles.Batch518.valid20728
  · exact MergedCutProfiles.Batch518.valid20729
  · exact MergedCutProfiles.Batch518.valid20730
  · exact MergedCutProfiles.Batch518.valid20731
  · exact MergedCutProfiles.Batch518.valid20732
  · exact MergedCutProfiles.Batch518.valid20733
  · exact MergedCutProfiles.Batch518.valid20734
theorem numericValid3371 : retention3371.NumericValid := by decide +kernel
def certificate3371 : RatCutBinCertificate := ⟨⟨retention3371,(2184127726165908029/1000000000000000000),(42966716513336319/250000000000000000),(3825645658661106153/250000000000000000),(1017325787371704994593/1000000000000000000),(267804225753094823/125000000000000000)⟩,(499107026461154473/500000000000000000),(317980716193718927/1000000000000000000),(317674100099185851/1000000000000000000),(102487345055528907/500000000000000000)⟩
theorem valid3371 : certificate3371.Valid := by decide +kernel
theorem sound3371 : certificate3371.Sound := rat_cut_bin_certificate_sound certificate3371 profilesValid3371 numericValid3371 valid3371

def certificates : List RatCutBinCertificate := [certificate3360,certificate3361,certificate3362,certificate3363,certificate3364,certificate3365,certificate3366,certificate3367,certificate3368,certificate3369,certificate3370,certificate3371]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3360,List.forall_mem_cons.mpr ⟨sound3361,List.forall_mem_cons.mpr ⟨sound3362,List.forall_mem_cons.mpr ⟨sound3363,List.forall_mem_cons.mpr ⟨sound3364,List.forall_mem_cons.mpr ⟨sound3365,List.forall_mem_cons.mpr ⟨sound3366,List.forall_mem_cons.mpr ⟨sound3367,List.forall_mem_cons.mpr ⟨sound3368,List.forall_mem_cons.mpr ⟨sound3369,List.forall_mem_cons.mpr ⟨sound3370,List.forall_mem_cons.mpr ⟨sound3371,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch280
