import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch263
import Cycle12.MergedCutProfiles.Batch264
import Cycle12.MergedCutProfiles.Batch265

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch137

def retention1644 : RatCutRetentionCertificate := ⟨(8/125),(513/8000),(2479502462844264679/5327952903643615745),(792269118560323921/250000000000000000),(6/5),(83685005212475646487207635698412304151/79226911856032392100000000000000000000),false,MergedCutProfiles.Batch263.profile10542,(fun _ => MergedCutProfiles.Batch263.profile10542)⟩
theorem profilesValid1644 : retention1644.ProfilesValid := by
  exact MergedCutProfiles.Batch263.valid10542
theorem numericValid1644 : retention1644.NumericValid := by decide +kernel
def certificate1644 : RatCutBinCertificate := ⟨⟨retention1644,(1343535584187517083/500000000000000000),(106913959738129263/500000000000000000),(17088822004878414449/1000000000000000000),(182240092104582146113/1000000000000000000),(507955176932612519/500000000000000000)⟩,(494177599493033801/500000000000000000),(12007266014595537/31250000000000000),(124122043493857487/500000000000000000),(42411888837384361/250000000000000000)⟩
theorem valid1644 : certificate1644.Valid := by decide +kernel
theorem sound1644 : certificate1644.Sound := rat_cut_bin_certificate_sound certificate1644 profilesValid1644 numericValid1644 valid1644

def retention1645 : RatCutRetentionCertificate := ⟨(8/125),(513/8000),(526408365554798850/1065590580728723149),(2479502462844264679/500000000000000000),(11/10),(495968146349143036849530055238851133759/495900492568852935800000000000000000000),false,MergedCutProfiles.Batch263.profile10543,(fun _ => MergedCutProfiles.Batch263.profile10543)⟩
theorem profilesValid1645 : retention1645.ProfilesValid := by
  exact MergedCutProfiles.Batch263.valid10543
theorem numericValid1645 : retention1645.NumericValid := by decide +kernel
def certificate1645 : RatCutBinCertificate := ⟨⟨retention1645,(1343535584187517083/500000000000000000),(106913959738129263/500000000000000000),(17088822004878414449/1000000000000000000),(182240092104582146113/1000000000000000000),(963143597243869837/1000000000000000000)⟩,(494177599493033801/500000000000000000),(20264153176325183/50000000000000000),(228676476281787613/1000000000000000000),(85170978201648397/500000000000000000)⟩
theorem valid1645 : certificate1645.Valid := by decide +kernel
theorem sound1645 : certificate1645.Sound := rat_cut_bin_certificate_sound certificate1645 profilesValid1645 numericValid1645 valid1645

def retention1646 : RatCutRetentionCertificate := ⟨(8/125),(513/8000),(1063344898420693677/2131181161457446298),(10528167311095977/2000000000000000),(11/10),(145189695347331365283697927931536341/146224545987444125000000000000000000),false,MergedCutProfiles.Batch263.profile10544,(fun _ => MergedCutProfiles.Batch263.profile10544)⟩
theorem profilesValid1646 : retention1646.ProfilesValid := by
  exact MergedCutProfiles.Batch263.valid10544
theorem numericValid1646 : retention1646.NumericValid := by decide +kernel
def certificate1646 : RatCutBinCertificate := ⟨⟨retention1646,(1343535584187517083/500000000000000000),(106913959738129263/500000000000000000),(17088822004878414449/1000000000000000000),(182240092104582146113/1000000000000000000),(477965249311403571/500000000000000000)⟩,(494177599493033801/500000000000000000),(81668235979351451/200000000000000000),(225926089775551783/1000000000000000000),(8427859187047897/50000000000000000)⟩
theorem valid1646 : certificate1646.Valid := by decide +kernel
theorem sound1646 : certificate1646.Sound := rat_cut_bin_certificate_sound certificate1646 profilesValid1646 numericValid1646 valid1646

def retention1647 : RatCutRetentionCertificate := ⟨(8/125),(513/8000),(1/2),(1063344898420693677/200000000000000000),(11/10),(84323020848352254096494957199338084951/85067591873655494160000000000000000000),false,MergedCutProfiles.Batch263.profile10541,(fun _ => MergedCutProfiles.Batch263.profile10541)⟩
theorem profilesValid1647 : retention1647.ProfilesValid := by
  exact MergedCutProfiles.Batch263.valid10541
theorem numericValid1647 : retention1647.NumericValid := by decide +kernel
def certificate1647 : RatCutBinCertificate := ⟨⟨retention1647,(1343535584187517083/500000000000000000),(106913959738129263/500000000000000000),(17088822004878414449/1000000000000000000),(182240092104582146113/1000000000000000000),(23856375184615029/25000000000000000)⟩,(494177599493033801/500000000000000000),(81811629949269591/200000000000000000),(901138343489797/4000000000000000),(84020282688853047/500000000000000000)⟩
theorem valid1647 : certificate1647.Valid := by decide +kernel
theorem sound1647 : certificate1647.Sound := rat_cut_bin_certificate_sound certificate1647 profilesValid1647 numericValid1647 valid1647

def retention1648 : RatCutRetentionCertificate := ⟨(513/8000),(257/4000),(620192629051343575/5303067409754754072),(893205237956365063/1000000000000000000),(51/20),(593013437065155533421/320000000000000000000),true,MergedCutProfiles.Batch263.profile10545,![MergedCutProfiles.Batch263.profile10545,MergedCutProfiles.Batch263.profile10546,MergedCutProfiles.Batch263.profile10547,MergedCutProfiles.Batch263.profile10548,MergedCutProfiles.Batch263.profile10549,MergedCutProfiles.Batch263.profile10550,MergedCutProfiles.Batch263.profile10551,MergedCutProfiles.Batch263.profile10552,MergedCutProfiles.Batch263.profile10553,MergedCutProfiles.Batch263.profile10554,MergedCutProfiles.Batch263.profile10555,MergedCutProfiles.Batch263.profile10556,MergedCutProfiles.Batch263.profile10557,MergedCutProfiles.Batch263.profile10558,MergedCutProfiles.Batch263.profile10559,MergedCutProfiles.Batch264.profile10560]⟩
theorem profilesValid1648 : retention1648.ProfilesValid := by
  change ∀ j : Fin 16, (retention1648.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch263.valid10545
  · exact MergedCutProfiles.Batch263.valid10546
  · exact MergedCutProfiles.Batch263.valid10547
  · exact MergedCutProfiles.Batch263.valid10548
  · exact MergedCutProfiles.Batch263.valid10549
  · exact MergedCutProfiles.Batch263.valid10550
  · exact MergedCutProfiles.Batch263.valid10551
  · exact MergedCutProfiles.Batch263.valid10552
  · exact MergedCutProfiles.Batch263.valid10553
  · exact MergedCutProfiles.Batch263.valid10554
  · exact MergedCutProfiles.Batch263.valid10555
  · exact MergedCutProfiles.Batch263.valid10556
  · exact MergedCutProfiles.Batch263.valid10557
  · exact MergedCutProfiles.Batch263.valid10558
  · exact MergedCutProfiles.Batch263.valid10559
  · exact MergedCutProfiles.Batch264.valid10560
theorem numericValid1648 : retention1648.NumericValid := by decide +kernel
def certificate1648 : RatCutBinCertificate := ⟨⟨retention1648,(2363870089547915511/1000000000000000000),(2148358950167401/10000000000000000),(4282365083292212793/250000000000000000),(45455093398152637613/250000000000000000),(888763437061750683/500000000000000000)⟩,(989748952627330989/1000000000000000000),(338883523411217261/1000000000000000000),(294403068862363141/1000000000000000000),(155168208175017047/1000000000000000000)⟩
theorem valid1648 : certificate1648.Valid := by decide +kernel
theorem sound1648 : certificate1648.Sound := rat_cut_bin_certificate_sound certificate1648 profilesValid1648 numericValid1648 valid1648

def retention1649 : RatCutRetentionCertificate := ⟨(513/8000),(257/4000),(634797952150288567/2651533704877377036),(24807705162053743/20000000000000000),(19/10),(7862740132798747567/5120000000000000000),true,MergedCutProfiles.Batch264.profile10561,![MergedCutProfiles.Batch264.profile10561,MergedCutProfiles.Batch264.profile10562,MergedCutProfiles.Batch264.profile10563,MergedCutProfiles.Batch264.profile10564,MergedCutProfiles.Batch264.profile10565,MergedCutProfiles.Batch264.profile10566,MergedCutProfiles.Batch264.profile10567,MergedCutProfiles.Batch264.profile10568,MergedCutProfiles.Batch264.profile10569,MergedCutProfiles.Batch264.profile10570,MergedCutProfiles.Batch264.profile10571,MergedCutProfiles.Batch264.profile10572,MergedCutProfiles.Batch264.profile10573,MergedCutProfiles.Batch264.profile10574,MergedCutProfiles.Batch264.profile10575,MergedCutProfiles.Batch264.profile10576]⟩
theorem profilesValid1649 : retention1649.ProfilesValid := by
  change ∀ j : Fin 16, (retention1649.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch264.valid10561
  · exact MergedCutProfiles.Batch264.valid10562
  · exact MergedCutProfiles.Batch264.valid10563
  · exact MergedCutProfiles.Batch264.valid10564
  · exact MergedCutProfiles.Batch264.valid10565
  · exact MergedCutProfiles.Batch264.valid10566
  · exact MergedCutProfiles.Batch264.valid10567
  · exact MergedCutProfiles.Batch264.valid10568
  · exact MergedCutProfiles.Batch264.valid10569
  · exact MergedCutProfiles.Batch264.valid10570
  · exact MergedCutProfiles.Batch264.valid10571
  · exact MergedCutProfiles.Batch264.valid10572
  · exact MergedCutProfiles.Batch264.valid10573
  · exact MergedCutProfiles.Batch264.valid10574
  · exact MergedCutProfiles.Batch264.valid10575
  · exact MergedCutProfiles.Batch264.valid10576
theorem numericValid1649 : retention1649.NumericValid := by decide +kernel
def certificate1649 : RatCutBinCertificate := ⟨⟨retention1649,(2363870089547915511/1000000000000000000),(2148358950167401/10000000000000000),(4282365083292212793/250000000000000000),(45455093398152637613/250000000000000000),(369833277457296337/250000000000000000)⟩,(989748952627330989/1000000000000000000),(181886226351411307/500000000000000000),(268367196523580349/1000000000000000000),(77558899490579317/500000000000000000)⟩
theorem valid1649 : certificate1649.Valid := by decide +kernel
theorem sound1649 : certificate1649.Sound := rat_cut_bin_certificate_sound certificate1649 profilesValid1649 numericValid1649 valid1649

def retention1650 : RatCutRetentionCertificate := ⟨(513/8000),(257/4000),(4389055437926395501/10606134819509508144),(634797952150288567/250000000000000000),(6/5),(366187187884691878107/320000000000000000000),true,MergedCutProfiles.Batch264.profile10577,![MergedCutProfiles.Batch264.profile10577,MergedCutProfiles.Batch264.profile10578,MergedCutProfiles.Batch264.profile10579,MergedCutProfiles.Batch264.profile10580,MergedCutProfiles.Batch264.profile10581,MergedCutProfiles.Batch264.profile10582,MergedCutProfiles.Batch264.profile10583,MergedCutProfiles.Batch264.profile10584,MergedCutProfiles.Batch264.profile10585,MergedCutProfiles.Batch264.profile10586,MergedCutProfiles.Batch264.profile10587,MergedCutProfiles.Batch264.profile10588,MergedCutProfiles.Batch264.profile10589,MergedCutProfiles.Batch264.profile10590,MergedCutProfiles.Batch264.profile10591,MergedCutProfiles.Batch264.profile10592]⟩
theorem profilesValid1650 : retention1650.ProfilesValid := by
  change ∀ j : Fin 16, (retention1650.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch264.valid10577
  · exact MergedCutProfiles.Batch264.valid10578
  · exact MergedCutProfiles.Batch264.valid10579
  · exact MergedCutProfiles.Batch264.valid10580
  · exact MergedCutProfiles.Batch264.valid10581
  · exact MergedCutProfiles.Batch264.valid10582
  · exact MergedCutProfiles.Batch264.valid10583
  · exact MergedCutProfiles.Batch264.valid10584
  · exact MergedCutProfiles.Batch264.valid10585
  · exact MergedCutProfiles.Batch264.valid10586
  · exact MergedCutProfiles.Batch264.valid10587
  · exact MergedCutProfiles.Batch264.valid10588
  · exact MergedCutProfiles.Batch264.valid10589
  · exact MergedCutProfiles.Batch264.valid10590
  · exact MergedCutProfiles.Batch264.valid10591
  · exact MergedCutProfiles.Batch264.valid10592
theorem numericValid1650 : retention1650.NumericValid := by decide +kernel
def certificate1650 : RatCutBinCertificate := ⟨⟨retention1650,(2363870089547915511/1000000000000000000),(2148358950167401/10000000000000000),(4282365083292212793/250000000000000000),(45455093398152637613/250000000000000000),(277186068291606461/250000000000000000)⟩,(989748952627330989/1000000000000000000),(409121207500958377/1000000000000000000),(225228225506241879/1000000000000000000),(6311030875698287/40000000000000000)⟩
theorem valid1650 : certificate1650.Valid := by decide +kernel
theorem sound1650 : certificate1650.Sound := rat_cut_bin_certificate_sound certificate1650 profilesValid1650 numericValid1650 valid1650

def retention1651 : RatCutRetentionCertificate := ⟨(513/8000),(257/4000),(5095557106830418843/10606134819509508144),(4389055437926395501/1000000000000000000),1,(254064905631417502621/256000000000000000000),true,MergedCutProfiles.Batch264.profile10562,![MergedCutProfiles.Batch264.profile10562,MergedCutProfiles.Batch264.profile10564,MergedCutProfiles.Batch264.profile10593,MergedCutProfiles.Batch264.profile10594,MergedCutProfiles.Batch264.profile10595,MergedCutProfiles.Batch264.profile10596,MergedCutProfiles.Batch264.profile10597,MergedCutProfiles.Batch264.profile10598,MergedCutProfiles.Batch264.profile10599,MergedCutProfiles.Batch265.profile10600,MergedCutProfiles.Batch265.profile10601,MergedCutProfiles.Batch265.profile10602,MergedCutProfiles.Batch265.profile10603,MergedCutProfiles.Batch265.profile10604,MergedCutProfiles.Batch265.profile10605,MergedCutProfiles.Batch265.profile10606]⟩
theorem profilesValid1651 : retention1651.ProfilesValid := by
  change ∀ j : Fin 16, (retention1651.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch264.valid10562
  · exact MergedCutProfiles.Batch264.valid10564
  · exact MergedCutProfiles.Batch264.valid10593
  · exact MergedCutProfiles.Batch264.valid10594
  · exact MergedCutProfiles.Batch264.valid10595
  · exact MergedCutProfiles.Batch264.valid10596
  · exact MergedCutProfiles.Batch264.valid10597
  · exact MergedCutProfiles.Batch264.valid10598
  · exact MergedCutProfiles.Batch264.valid10599
  · exact MergedCutProfiles.Batch265.valid10600
  · exact MergedCutProfiles.Batch265.valid10601
  · exact MergedCutProfiles.Batch265.valid10602
  · exact MergedCutProfiles.Batch265.valid10603
  · exact MergedCutProfiles.Batch265.valid10604
  · exact MergedCutProfiles.Batch265.valid10605
  · exact MergedCutProfiles.Batch265.valid10606
theorem numericValid1651 : retention1651.NumericValid := by decide +kernel
def certificate1651 : RatCutBinCertificate := ⟨⟨retention1651,(2363870089547915511/1000000000000000000),(2148358950167401/10000000000000000),(4282365083292212793/250000000000000000),(45455093398152637613/250000000000000000),(962785645457555947/1000000000000000000)⟩,(989748952627330989/1000000000000000000),(217902277465036701/500000000000000000),(202232560436754343/1000000000000000000),(49326141276449/312500000000000)⟩
theorem valid1651 : certificate1651.Valid := by decide +kernel
theorem sound1651 : certificate1651.Sound := rat_cut_bin_certificate_sound certificate1651 profilesValid1651 numericValid1651 valid1651

def retention1652 : RatCutRetentionCertificate := ⟨(513/8000),(257/4000),(2624978791362243683/5303067409754754072),(5095557106830418843/1000000000000000000),(11/10),(2036801279359336700506547275373489685991/2038222842732167537200000000000000000000),false,MergedCutProfiles.Batch265.profile10607,(fun _ => MergedCutProfiles.Batch265.profile10607)⟩
theorem profilesValid1652 : retention1652.ProfilesValid := by
  exact MergedCutProfiles.Batch265.valid10607
theorem numericValid1652 : retention1652.NumericValid := by decide +kernel
def certificate1652 : RatCutBinCertificate := ⟨⟨retention1652,(2363870089547915511/1000000000000000000),(2148358950167401/10000000000000000),(4282365083292212793/250000000000000000),(45455093398152637613/250000000000000000),(193336704201516949/200000000000000000)⟩,(989748952627330989/1000000000000000000),(417332715862941/976562500000000),(209338100043676289/1000000000000000000),(39309799988191451/250000000000000000)⟩
theorem valid1652 : certificate1652.Valid := by decide +kernel
theorem sound1652 : certificate1652.Sound := rat_cut_bin_certificate_sound certificate1652 profilesValid1652 numericValid1652 valid1652

def retention1653 : RatCutRetentionCertificate := ⟨(513/8000),(257/4000),(110467857469827755/220961142073114753),(2624978791362243683/500000000000000000),(11/10),(520231467592316602251624656115666755951/524995758272448736600000000000000000000),false,MergedCutProfiles.Batch265.profile10608,(fun _ => MergedCutProfiles.Batch265.profile10608)⟩
theorem profilesValid1653 : retention1653.ProfilesValid := by
  exact MergedCutProfiles.Batch265.valid10608
theorem numericValid1653 : retention1653.NumericValid := by decide +kernel
def certificate1653 : RatCutBinCertificate := ⟨⟨retention1653,(2363870089547915511/1000000000000000000),(2148358950167401/10000000000000000),(4282365083292212793/250000000000000000),(45455093398152637613/250000000000000000),(479153131431453317/500000000000000000)⟩,(989748952627330989/1000000000000000000),(429849903017759939/1000000000000000000),(103609519976972201/500000000000000000),(77548818752408197/500000000000000000)⟩
theorem valid1653 : certificate1653.Valid := by decide +kernel
theorem sound1653 : certificate1653.Sound := rat_cut_bin_certificate_sound certificate1653 profilesValid1653 numericValid1653 valid1653

def retention1654 : RatCutRetentionCertificate := ⟨(513/8000),(257/4000),(1/2),(66280714481896653/12500000000000000),(11/10),(7007422159046493649387256341724408973/7069942878068976320000000000000000000),false,MergedCutProfiles.Batch265.profile10609,(fun _ => MergedCutProfiles.Batch265.profile10609)⟩
theorem profilesValid1654 : retention1654.ProfilesValid := by
  exact MergedCutProfiles.Batch265.valid10609
theorem numericValid1654 : retention1654.NumericValid := by decide +kernel
def certificate1654 : RatCutBinCertificate := ⟨⟨retention1654,(2363870089547915511/1000000000000000000),(2148358950167401/10000000000000000),(4282365083292212793/250000000000000000),(45455093398152637613/250000000000000000),(11981725873816131/12500000000000000)⟩,(989748952627330989/1000000000000000000),(26833915500908461/62500000000000000),(41529523174778259/200000000000000000),(155654498253265293/1000000000000000000)⟩
theorem valid1654 : certificate1654.Valid := by decide +kernel
theorem sound1654 : certificate1654.Sound := rat_cut_bin_certificate_sound certificate1654 profilesValid1654 numericValid1654 valid1654

def retention1655 : RatCutRetentionCertificate := ⟨(513/8000),(257/4000),(1/2),64,1,(10216595266157481888238410414180338511/10240000000000000000000000000000000000),false,MergedCutProfiles.Batch265.profile10609,(fun _ => MergedCutProfiles.Batch265.profile10609)⟩
theorem profilesValid1655 : retention1655.ProfilesValid := by
  exact MergedCutProfiles.Batch265.valid10609
theorem numericValid1655 : retention1655.NumericValid := by decide +kernel
def certificate1655 : RatCutBinCertificate := ⟨⟨retention1655,(2363870089547915511/1000000000000000000),(2148358950167401/10000000000000000),(4282365083292212793/250000000000000000),(45455093398152637613/250000000000000000),(484033211677514357/500000000000000000)⟩,(989748952627330989/1000000000000000000),(388491969624758691/1000000000000000000),(61048415902930991/250000000000000000),(46092427808359993/200000000000000000)⟩
theorem valid1655 : certificate1655.Valid := by decide +kernel
theorem sound1655 : certificate1655.Sound := rat_cut_bin_certificate_sound certificate1655 profilesValid1655 numericValid1655 valid1655

def certificates : List RatCutBinCertificate := [certificate1644,certificate1645,certificate1646,certificate1647,certificate1648,certificate1649,certificate1650,certificate1651,certificate1652,certificate1653,certificate1654,certificate1655]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1644,List.forall_mem_cons.mpr ⟨sound1645,List.forall_mem_cons.mpr ⟨sound1646,List.forall_mem_cons.mpr ⟨sound1647,List.forall_mem_cons.mpr ⟨sound1648,List.forall_mem_cons.mpr ⟨sound1649,List.forall_mem_cons.mpr ⟨sound1650,List.forall_mem_cons.mpr ⟨sound1651,List.forall_mem_cons.mpr ⟨sound1652,List.forall_mem_cons.mpr ⟨sound1653,List.forall_mem_cons.mpr ⟨sound1654,List.forall_mem_cons.mpr ⟨sound1655,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch137
