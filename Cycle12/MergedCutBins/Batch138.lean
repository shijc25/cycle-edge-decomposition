import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch265
import Cycle12.MergedCutProfiles.Batch266
import Cycle12.MergedCutProfiles.Batch267

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch138

def retention1656 : RatCutRetentionCertificate := ⟨(513/8000),(257/4000),(4930918253328277321/10606134819509508144),(3151127548206655857/1000000000000000000),(6/5),(1321485223433475378501050197335406763/1250447439764545975000000000000000000),false,MergedCutProfiles.Batch265.profile10610,(fun _ => MergedCutProfiles.Batch265.profile10610)⟩
theorem profilesValid1656 : retention1656.ProfilesValid := by
  exact MergedCutProfiles.Batch265.valid10610
theorem numericValid1656 : retention1656.NumericValid := by decide +kernel
def certificate1656 : RatCutBinCertificate := ⟨⟨retention1656,(2688624605547915511/1000000000000000000),(2148358950167401/10000000000000000),(4282365083292212793/250000000000000000),(45455093398152637613/250000000000000000),(127041588766072163/125000000000000000)⟩,(247084043184408461/250000000000000000),(38312385384981031/100000000000000000),(249306056215570593/1000000000000000000),(42562350923979737/250000000000000000)⟩
theorem valid1656 : certificate1656.Valid := by decide +kernel
theorem sound1656 : certificate1656.Sound := rat_cut_bin_certificate_sound certificate1656 profilesValid1656 numericValid1656 valid1656

def retention1657 : RatCutRetentionCertificate := ⟨(513/8000),(257/4000),(2617134543437126407/5303067409754754072),(4930918253328277321/1000000000000000000),(11/10),(1974042509003531666714373370212877083319/1972367301331310928400000000000000000000),false,MergedCutProfiles.Batch265.profile10611,(fun _ => MergedCutProfiles.Batch265.profile10611)⟩
theorem profilesValid1657 : retention1657.ProfilesValid := by
  exact MergedCutProfiles.Batch265.valid10611
theorem numericValid1657 : retention1657.NumericValid := by decide +kernel
def certificate1657 : RatCutBinCertificate := ⟨⟨retention1657,(2688624605547915511/1000000000000000000),(2148358950167401/10000000000000000),(4282365083292212793/250000000000000000),(45455093398152637613/250000000000000000),(963748765639727267/1000000000000000000)⟩,(247084043184408461/250000000000000000),(6312934555998093/15625000000000000),(114906041416134279/500000000000000000),(42785224897434409/250000000000000000)⟩
theorem valid1657 : certificate1657.Valid := by decide +kernel
theorem sound1657 : certificate1657.Sound := rat_cut_bin_certificate_sound certificate1657 profilesValid1657 numericValid1657 valid1657

def retention1658 : RatCutRetentionCertificate := ⟨(513/8000),(257/4000),(1762203925914331781/3535378273169836048),(2617134543437126407/500000000000000000),(11/10),(130029376805071771326516922954526571509/130856727171856320350000000000000000000),false,MergedCutProfiles.Batch265.profile10612,(fun _ => MergedCutProfiles.Batch265.profile10612)⟩
theorem profilesValid1658 : retention1658.ProfilesValid := by
  exact MergedCutProfiles.Batch265.valid10612
theorem numericValid1658 : retention1658.NumericValid := by decide +kernel
def certificate1658 : RatCutBinCertificate := ⟨⟨retention1658,(2688624605547915511/1000000000000000000),(2148358950167401/10000000000000000),(4282365083292212793/250000000000000000),(45455093398152637613/250000000000000000),(956577328783759411/1000000000000000000)⟩,(247084043184408461/250000000000000000),(81411359642646283/200000000000000000),(227078429308491449/1000000000000000000),(2117324578153801/12500000000000000)⟩
theorem valid1658 : certificate1658.Valid := by decide +kernel
theorem sound1658 : certificate1658.Sound := rat_cut_bin_certificate_sound certificate1658 profilesValid1658 numericValid1658 valid1658

def retention1659 : RatCutRetentionCertificate := ⟨(513/8000),(257/4000),(1/2),(5286611777742995343/1000000000000000000),(11/10),(698576168403387694006368644344511434917/704881570365732712400000000000000000000),false,MergedCutProfiles.Batch265.profile10609,(fun _ => MergedCutProfiles.Batch265.profile10609)⟩
theorem profilesValid1659 : retention1659.ProfilesValid := by
  exact MergedCutProfiles.Batch265.valid10609
theorem numericValid1659 : retention1659.NumericValid := by decide +kernel
def certificate1659 : RatCutBinCertificate := ⟨⟨retention1659,(2688624605547915511/1000000000000000000),(2148358950167401/10000000000000000),(4282365083292212793/250000000000000000),(45455093398152637613/250000000000000000),(476977317725312873/500000000000000000)⟩,(247084043184408461/250000000000000000),(51021989179043627/125000000000000000),(226074139206201511/1000000000000000000),(168454739659808029/1000000000000000000)⟩
theorem valid1659 : certificate1659.Valid := by decide +kernel
theorem sound1659 : certificate1659.Sound := rat_cut_bin_certificate_sound certificate1659 profilesValid1659 numericValid1659 valid1659

def retention1660 : RatCutRetentionCertificate := ⟨(257/4000),(103/1600),(858631379759089933/10556669039628709734),(850130078969395973/1000000000000000000),(53/20),(77753583978458554727/40000000000000000000),true,MergedCutProfiles.Batch265.profile10613,![MergedCutProfiles.Batch265.profile10613,MergedCutProfiles.Batch265.profile10614,MergedCutProfiles.Batch265.profile10615,MergedCutProfiles.Batch265.profile10616,MergedCutProfiles.Batch265.profile10617,MergedCutProfiles.Batch265.profile10618,MergedCutProfiles.Batch265.profile10619,MergedCutProfiles.Batch265.profile10620,MergedCutProfiles.Batch265.profile10621,MergedCutProfiles.Batch265.profile10622,MergedCutProfiles.Batch265.profile10623,MergedCutProfiles.Batch265.profile10624,MergedCutProfiles.Batch265.profile10625,MergedCutProfiles.Batch265.profile10626,MergedCutProfiles.Batch265.profile10627,MergedCutProfiles.Batch265.profile10628]⟩
theorem profilesValid1660 : retention1660.ProfilesValid := by
  change ∀ j : Fin 16, (retention1660.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch265.valid10613
  · exact MergedCutProfiles.Batch265.valid10614
  · exact MergedCutProfiles.Batch265.valid10615
  · exact MergedCutProfiles.Batch265.valid10616
  · exact MergedCutProfiles.Batch265.valid10617
  · exact MergedCutProfiles.Batch265.valid10618
  · exact MergedCutProfiles.Batch265.valid10619
  · exact MergedCutProfiles.Batch265.valid10620
  · exact MergedCutProfiles.Batch265.valid10621
  · exact MergedCutProfiles.Batch265.valid10622
  · exact MergedCutProfiles.Batch265.valid10623
  · exact MergedCutProfiles.Batch265.valid10624
  · exact MergedCutProfiles.Batch265.valid10625
  · exact MergedCutProfiles.Batch265.valid10626
  · exact MergedCutProfiles.Batch265.valid10627
  · exact MergedCutProfiles.Batch265.valid10628
theorem numericValid1660 : retention1660.NumericValid := by decide +kernel
def certificate1660 : RatCutBinCertificate := ⟨⟨retention1660,(1188150434281344247/500000000000000000),(215847317439018643/1000000000000000000),(3434048892357245293/200000000000000000),(181403391249949363959/1000000000000000000),(932317828775059871/500000000000000000)⟩,(989684228199474133/1000000000000000000),(338385838891656867/1000000000000000000),(147470933504525331/500000000000000000),(156151265906004011/1000000000000000000)⟩
theorem valid1660 : certificate1660.Valid := by decide +kernel
theorem sound1660 : certificate1660.Sound := rat_cut_bin_certificate_sound certificate1660 profilesValid1660 numericValid1660 valid1660

def retention1661 : RatCutRetentionCertificate := ⟨(257/4000),(103/1600),(911454511552613573/10556669039628709734),(858631379759089933/1000000000000000000),(53/20),(2478147182071136624533/1280000000000000000000),true,MergedCutProfiles.Batch265.profile10629,![MergedCutProfiles.Batch265.profile10629,MergedCutProfiles.Batch265.profile10630,MergedCutProfiles.Batch265.profile10631,MergedCutProfiles.Batch265.profile10632,MergedCutProfiles.Batch265.profile10633,MergedCutProfiles.Batch265.profile10634,MergedCutProfiles.Batch265.profile10635,MergedCutProfiles.Batch265.profile10636,MergedCutProfiles.Batch265.profile10637,MergedCutProfiles.Batch265.profile10638,MergedCutProfiles.Batch265.profile10639,MergedCutProfiles.Batch266.profile10640,MergedCutProfiles.Batch266.profile10641,MergedCutProfiles.Batch266.profile10642,MergedCutProfiles.Batch266.profile10643,MergedCutProfiles.Batch266.profile10644]⟩
theorem profilesValid1661 : retention1661.ProfilesValid := by
  change ∀ j : Fin 16, (retention1661.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch265.valid10629
  · exact MergedCutProfiles.Batch265.valid10630
  · exact MergedCutProfiles.Batch265.valid10631
  · exact MergedCutProfiles.Batch265.valid10632
  · exact MergedCutProfiles.Batch265.valid10633
  · exact MergedCutProfiles.Batch265.valid10634
  · exact MergedCutProfiles.Batch265.valid10635
  · exact MergedCutProfiles.Batch265.valid10636
  · exact MergedCutProfiles.Batch265.valid10637
  · exact MergedCutProfiles.Batch265.valid10638
  · exact MergedCutProfiles.Batch265.valid10639
  · exact MergedCutProfiles.Batch266.valid10640
  · exact MergedCutProfiles.Batch266.valid10641
  · exact MergedCutProfiles.Batch266.valid10642
  · exact MergedCutProfiles.Batch266.valid10643
  · exact MergedCutProfiles.Batch266.valid10644
theorem numericValid1661 : retention1661.NumericValid := by decide +kernel
def certificate1661 : RatCutBinCertificate := ⟨⟨retention1661,(1188150434281344247/500000000000000000),(215847317439018643/1000000000000000000),(3434048892357245293/200000000000000000),(181403391249949363959/1000000000000000000),(1856848958049092993/1000000000000000000)⟩,(989684228199474133/1000000000000000000),(338401110347382717/1000000000000000000),(294925323123014539/1000000000000000000),(31202789879913991/200000000000000000)⟩
theorem valid1661 : certificate1661.Valid := by decide +kernel
theorem sound1661 : certificate1661.Sound := rat_cut_bin_certificate_sound certificate1661 profilesValid1661 numericValid1661 valid1661

def retention1662 : RatCutRetentionCertificate := ⟨(257/4000),(103/1600),(590283605947027604/5278334519814354867),(911454511552613573/1000000000000000000),(5/2),(119333390332027609921/64000000000000000000),true,MergedCutProfiles.Batch266.profile10645,![MergedCutProfiles.Batch266.profile10645,MergedCutProfiles.Batch266.profile10646,MergedCutProfiles.Batch266.profile10647,MergedCutProfiles.Batch266.profile10648,MergedCutProfiles.Batch266.profile10649,MergedCutProfiles.Batch266.profile10650,MergedCutProfiles.Batch266.profile10651,MergedCutProfiles.Batch265.profile10623,MergedCutProfiles.Batch266.profile10652,MergedCutProfiles.Batch266.profile10653,MergedCutProfiles.Batch266.profile10654,MergedCutProfiles.Batch266.profile10655,MergedCutProfiles.Batch266.profile10656,MergedCutProfiles.Batch266.profile10657,MergedCutProfiles.Batch266.profile10658,MergedCutProfiles.Batch266.profile10659]⟩
theorem profilesValid1662 : retention1662.ProfilesValid := by
  change ∀ j : Fin 16, (retention1662.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch266.valid10645
  · exact MergedCutProfiles.Batch266.valid10646
  · exact MergedCutProfiles.Batch266.valid10647
  · exact MergedCutProfiles.Batch266.valid10648
  · exact MergedCutProfiles.Batch266.valid10649
  · exact MergedCutProfiles.Batch266.valid10650
  · exact MergedCutProfiles.Batch266.valid10651
  · exact MergedCutProfiles.Batch265.valid10623
  · exact MergedCutProfiles.Batch266.valid10652
  · exact MergedCutProfiles.Batch266.valid10653
  · exact MergedCutProfiles.Batch266.valid10654
  · exact MergedCutProfiles.Batch266.valid10655
  · exact MergedCutProfiles.Batch266.valid10656
  · exact MergedCutProfiles.Batch266.valid10657
  · exact MergedCutProfiles.Batch266.valid10658
  · exact MergedCutProfiles.Batch266.valid10659
theorem numericValid1662 : retention1662.NumericValid := by decide +kernel
def certificate1662 : RatCutBinCertificate := ⟨⟨retention1662,(1188150434281344247/500000000000000000),(215847317439018643/1000000000000000000),(3434048892357245293/200000000000000000),(181403391249949363959/1000000000000000000),(1789863970483440489/1000000000000000000)⟩,(989684228199474133/1000000000000000000),(342625779468638927/1000000000000000000),(145187478076405627/500000000000000000),(78102580347507601/500000000000000000)⟩
theorem valid1662 : certificate1662.Valid := by decide +kernel
theorem sound1662 : certificate1662.Sound := rat_cut_bin_certificate_sound certificate1662 profilesValid1662 numericValid1662 valid1662

def retention1663 : RatCutRetentionCertificate := ⟨(257/4000),(103/1600),(736573365822937263/3518889679876236578),(147570901486756901/125000000000000000),2,(51481964534362763887/32000000000000000000),true,MergedCutProfiles.Batch266.profile10660,![MergedCutProfiles.Batch266.profile10660,MergedCutProfiles.Batch266.profile10661,MergedCutProfiles.Batch266.profile10662,MergedCutProfiles.Batch266.profile10663,MergedCutProfiles.Batch266.profile10664,MergedCutProfiles.Batch266.profile10665,MergedCutProfiles.Batch266.profile10666,MergedCutProfiles.Batch266.profile10667,MergedCutProfiles.Batch266.profile10668,MergedCutProfiles.Batch266.profile10669,MergedCutProfiles.Batch266.profile10670,MergedCutProfiles.Batch266.profile10671,MergedCutProfiles.Batch266.profile10672,MergedCutProfiles.Batch266.profile10673,MergedCutProfiles.Batch266.profile10674,MergedCutProfiles.Batch266.profile10675]⟩
theorem profilesValid1663 : retention1663.ProfilesValid := by
  change ∀ j : Fin 16, (retention1663.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch266.valid10660
  · exact MergedCutProfiles.Batch266.valid10661
  · exact MergedCutProfiles.Batch266.valid10662
  · exact MergedCutProfiles.Batch266.valid10663
  · exact MergedCutProfiles.Batch266.valid10664
  · exact MergedCutProfiles.Batch266.valid10665
  · exact MergedCutProfiles.Batch266.valid10666
  · exact MergedCutProfiles.Batch266.valid10667
  · exact MergedCutProfiles.Batch266.valid10668
  · exact MergedCutProfiles.Batch266.valid10669
  · exact MergedCutProfiles.Batch266.valid10670
  · exact MergedCutProfiles.Batch266.valid10671
  · exact MergedCutProfiles.Batch266.valid10672
  · exact MergedCutProfiles.Batch266.valid10673
  · exact MergedCutProfiles.Batch266.valid10674
  · exact MergedCutProfiles.Batch266.valid10675
theorem numericValid1663 : retention1663.NumericValid := by decide +kernel
def certificate1663 : RatCutBinCertificate := ⟨⟨retention1663,(1188150434281344247/500000000000000000),(215847317439018643/1000000000000000000),(3434048892357245293/200000000000000000),(181403391249949363959/1000000000000000000),(1549036278997533407/1000000000000000000)⟩,(989684228199474133/1000000000000000000),(89939814869858179/250000000000000000),(136223592017671871/500000000000000000),(39229077726642417/250000000000000000)⟩
theorem valid1663 : certificate1663.Valid := by decide +kernel
theorem sound1663 : certificate1663.Sound := rat_cut_bin_certificate_sound certificate1663 profilesValid1663 numericValid1663 valid1663

def retention1664 : RatCutRetentionCertificate := ⟨(257/4000),(103/1600),(2047540234529669302/5278334519814354867),(2209720097468811789/1000000000000000000),(5/4),(61263690304042598589/51200000000000000000),true,MergedCutProfiles.Batch266.profile10676,![MergedCutProfiles.Batch266.profile10676,MergedCutProfiles.Batch266.profile10677,MergedCutProfiles.Batch266.profile10678,MergedCutProfiles.Batch266.profile10679,MergedCutProfiles.Batch267.profile10680,MergedCutProfiles.Batch267.profile10681,MergedCutProfiles.Batch267.profile10682,MergedCutProfiles.Batch267.profile10683,MergedCutProfiles.Batch267.profile10684,MergedCutProfiles.Batch267.profile10685,MergedCutProfiles.Batch267.profile10686,MergedCutProfiles.Batch267.profile10687,MergedCutProfiles.Batch267.profile10688,MergedCutProfiles.Batch267.profile10689,MergedCutProfiles.Batch267.profile10690,MergedCutProfiles.Batch267.profile10691]⟩
theorem profilesValid1664 : retention1664.ProfilesValid := by
  change ∀ j : Fin 16, (retention1664.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch266.valid10676
  · exact MergedCutProfiles.Batch266.valid10677
  · exact MergedCutProfiles.Batch266.valid10678
  · exact MergedCutProfiles.Batch266.valid10679
  · exact MergedCutProfiles.Batch267.valid10680
  · exact MergedCutProfiles.Batch267.valid10681
  · exact MergedCutProfiles.Batch267.valid10682
  · exact MergedCutProfiles.Batch267.valid10683
  · exact MergedCutProfiles.Batch267.valid10684
  · exact MergedCutProfiles.Batch267.valid10685
  · exact MergedCutProfiles.Batch267.valid10686
  · exact MergedCutProfiles.Batch267.valid10687
  · exact MergedCutProfiles.Batch267.valid10688
  · exact MergedCutProfiles.Batch267.valid10689
  · exact MergedCutProfiles.Batch267.valid10690
  · exact MergedCutProfiles.Batch267.valid10691
theorem numericValid1664 : retention1664.NumericValid := by decide +kernel
def certificate1664 : RatCutBinCertificate := ⟨⟨retention1664,(1188150434281344247/500000000000000000),(215847317439018643/1000000000000000000),(3434048892357245293/200000000000000000),(181403391249949363959/1000000000000000000),(1159199737784573651/1000000000000000000)⟩,(989684228199474133/1000000000000000000),(40457858431909011/100000000000000000),(57328332050643813/250000000000000000),(7863716074596829/50000000000000000)⟩
theorem valid1664 : certificate1664.Valid := by decide +kernel
theorem sound1664 : certificate1664.Sound := rat_cut_bin_certificate_sound certificate1664 profilesValid1664 numericValid1664 valid1664

def retention1665 : RatCutRetentionCertificate := ⟨(257/4000),(103/1600),(2498388200565826552/5278334519814354867),(1023770117264834651/250000000000000000),1,(64259611225183070651/64000000000000000000),true,MergedCutProfiles.Batch267.profile10692,![MergedCutProfiles.Batch267.profile10692,MergedCutProfiles.Batch265.profile10639,MergedCutProfiles.Batch267.profile10693,MergedCutProfiles.Batch267.profile10694,MergedCutProfiles.Batch267.profile10695,MergedCutProfiles.Batch267.profile10696,MergedCutProfiles.Batch267.profile10697,MergedCutProfiles.Batch267.profile10698,MergedCutProfiles.Batch267.profile10699,MergedCutProfiles.Batch267.profile10700,MergedCutProfiles.Batch267.profile10701,MergedCutProfiles.Batch267.profile10702,MergedCutProfiles.Batch267.profile10703,MergedCutProfiles.Batch267.profile10704,MergedCutProfiles.Batch267.profile10705,MergedCutProfiles.Batch267.profile10706]⟩
theorem profilesValid1665 : retention1665.ProfilesValid := by
  change ∀ j : Fin 16, (retention1665.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch267.valid10692
  · exact MergedCutProfiles.Batch265.valid10639
  · exact MergedCutProfiles.Batch267.valid10693
  · exact MergedCutProfiles.Batch267.valid10694
  · exact MergedCutProfiles.Batch267.valid10695
  · exact MergedCutProfiles.Batch267.valid10696
  · exact MergedCutProfiles.Batch267.valid10697
  · exact MergedCutProfiles.Batch267.valid10698
  · exact MergedCutProfiles.Batch267.valid10699
  · exact MergedCutProfiles.Batch267.valid10700
  · exact MergedCutProfiles.Batch267.valid10701
  · exact MergedCutProfiles.Batch267.valid10702
  · exact MergedCutProfiles.Batch267.valid10703
  · exact MergedCutProfiles.Batch267.valid10704
  · exact MergedCutProfiles.Batch267.valid10705
  · exact MergedCutProfiles.Batch267.valid10706
theorem numericValid1665 : retention1665.NumericValid := by decide +kernel
def certificate1665 : RatCutBinCertificate := ⟨⟨retention1665,(1188150434281344247/500000000000000000),(215847317439018643/1000000000000000000),(3434048892357245293/200000000000000000),(181403391249949363959/1000000000000000000),(974175243236935861/1000000000000000000)⟩,(989684228199474133/1000000000000000000),(216776772345795107/500000000000000000),(204107953278576337/1000000000000000000),(79378549768465869/500000000000000000)⟩
theorem valid1665 : certificate1665.Valid := by decide +kernel
theorem sound1665 : certificate1665.Sound := rat_cut_bin_certificate_sound certificate1665 profilesValid1665 numericValid1665 valid1665

def retention1666 : RatCutRetentionCertificate := ⟨(257/4000),(103/1600),(1733221853363655587/3518889679876236578),(312298525070728319/62500000000000000),(11/10),(1958134119336798295615849213265000341/1951865781692051993750000000000000000),false,MergedCutProfiles.Batch267.profile10707,(fun _ => MergedCutProfiles.Batch267.profile10707)⟩
theorem profilesValid1666 : retention1666.ProfilesValid := by
  exact MergedCutProfiles.Batch267.valid10707
theorem numericValid1666 : retention1666.NumericValid := by decide +kernel
def certificate1666 : RatCutBinCertificate := ⟨⟨retention1666,(1188150434281344247/500000000000000000),(215847317439018643/1000000000000000000),(3434048892357245293/200000000000000000),(181403391249949363959/1000000000000000000),(970344593295086863/1000000000000000000)⟩,(989684228199474133/1000000000000000000),(106275330252192923/250000000000000000),(211254598766128809/1000000000000000000),(79378764913168277/500000000000000000)⟩
theorem valid1666 : certificate1666.Valid := by decide +kernel
theorem sound1666 : certificate1666.Sound := rat_cut_bin_certificate_sound certificate1666 profilesValid1666 numericValid1666 valid1666

def retention1667 : RatCutRetentionCertificate := ⟨(257/4000),(103/1600),(1750554071897292143/3518889679876236578),(5199665560090966761/1000000000000000000),(11/10),(2070105555123650982635928770773532479199/2079866224036386704400000000000000000000),false,MergedCutProfiles.Batch267.profile10708,(fun _ => MergedCutProfiles.Batch267.profile10708)⟩
theorem profilesValid1667 : retention1667.ProfilesValid := by
  exact MergedCutProfiles.Batch267.valid10708
theorem numericValid1667 : retention1667.NumericValid := by decide +kernel
def certificate1667 : RatCutBinCertificate := ⟨⟨retention1667,(1188150434281344247/500000000000000000),(215847317439018643/1000000000000000000),(3434048892357245293/200000000000000000),(181403391249949363959/1000000000000000000),(192488096076626557/200000000000000000)⟩,(989684228199474133/1000000000000000000),(213388296559043203/500000000000000000),(209824853054803047/1000000000000000000),(157423985986097943/1000000000000000000)⟩
theorem valid1667 : certificate1667.Valid := by decide +kernel
theorem sound1667 : certificate1667.Sound := rat_cut_bin_certificate_sound certificate1667 profilesValid1667 numericValid1667 valid1667

def certificates : List RatCutBinCertificate := [certificate1656,certificate1657,certificate1658,certificate1659,certificate1660,certificate1661,certificate1662,certificate1663,certificate1664,certificate1665,certificate1666,certificate1667]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1656,List.forall_mem_cons.mpr ⟨sound1657,List.forall_mem_cons.mpr ⟨sound1658,List.forall_mem_cons.mpr ⟨sound1659,List.forall_mem_cons.mpr ⟨sound1660,List.forall_mem_cons.mpr ⟨sound1661,List.forall_mem_cons.mpr ⟨sound1662,List.forall_mem_cons.mpr ⟨sound1663,List.forall_mem_cons.mpr ⟨sound1664,List.forall_mem_cons.mpr ⟨sound1665,List.forall_mem_cons.mpr ⟨sound1666,List.forall_mem_cons.mpr ⟨sound1667,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch138
