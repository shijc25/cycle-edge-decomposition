import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch339
import Cycle12.MergedCutProfiles.Batch340
import Cycle12.MergedCutProfiles.Batch341
import Cycle12.MergedCutProfiles.Batch342

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch184

def retention2208 : RatCutRetentionCertificate := ⟨(33/1000),(17/500),(4907792993995718602/90030724948873378429),(1268175625914733857/1000000000000000000),(23/10),(2609977241039967546813/1280000000000000000000),true,MergedCutProfiles.Batch340.profile13618,![MergedCutProfiles.Batch340.profile13618,MergedCutProfiles.Batch339.profile13589,MergedCutProfiles.Batch340.profile13619,MergedCutProfiles.Batch340.profile13620,MergedCutProfiles.Batch340.profile13621,MergedCutProfiles.Batch340.profile13622,MergedCutProfiles.Batch340.profile13623,MergedCutProfiles.Batch340.profile13624,MergedCutProfiles.Batch340.profile13625,MergedCutProfiles.Batch340.profile13626,MergedCutProfiles.Batch340.profile13627,MergedCutProfiles.Batch340.profile13628,MergedCutProfiles.Batch340.profile13629,MergedCutProfiles.Batch340.profile13630,MergedCutProfiles.Batch340.profile13631,MergedCutProfiles.Batch340.profile13632]⟩
theorem profilesValid2208 : retention2208.ProfilesValid := by
  change ∀ j : Fin 16, (retention2208.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch340.valid13618
  · exact MergedCutProfiles.Batch339.valid13589
  · exact MergedCutProfiles.Batch340.valid13619
  · exact MergedCutProfiles.Batch340.valid13620
  · exact MergedCutProfiles.Batch340.valid13621
  · exact MergedCutProfiles.Batch340.valid13622
  · exact MergedCutProfiles.Batch340.valid13623
  · exact MergedCutProfiles.Batch340.valid13624
  · exact MergedCutProfiles.Batch340.valid13625
  · exact MergedCutProfiles.Batch340.valid13626
  · exact MergedCutProfiles.Batch340.valid13627
  · exact MergedCutProfiles.Batch340.valid13628
  · exact MergedCutProfiles.Batch340.valid13629
  · exact MergedCutProfiles.Batch340.valid13630
  · exact MergedCutProfiles.Batch340.valid13631
  · exact MergedCutProfiles.Batch340.valid13632
theorem numericValid2208 : retention2208.NumericValid := by decide +kernel
def certificate2208 : RatCutBinCertificate := ⟨⟨retention2208,(1991983684202059961/1000000000000000000),(51337219122942991/1000000000000000000),(10227232806214502729/1000000000000000000),(925536029579625736477/1000000000000000000),(2016046401847932473/1000000000000000000)⟩,(124743898203826829/125000000000000000),(75596508682947287/200000000000000000),(127136450651550371/500000000000000000),(170976560922680739/1000000000000000000)⟩
theorem valid2208 : certificate2208.Valid := by decide +kernel
theorem sound2208 : certificate2208.Sound := rat_cut_bin_certificate_sound certificate2208 profilesValid2208 numericValid2208 valid2208

def retention2209 : RatCutRetentionCertificate := ⟨(33/1000),(17/500),(34849525679542764067/90030724948873378429),(2453896496997859301/500000000000000000),(6/5),(18830700979377846619759731234063477733/15336853106236620631250000000000000000),false,MergedCutProfiles.Batch340.profile13633,(fun _ => MergedCutProfiles.Batch340.profile13633)⟩
theorem profilesValid2209 : retention2209.ProfilesValid := by
  exact MergedCutProfiles.Batch340.valid13633
theorem numericValid2209 : retention2209.NumericValid := by decide +kernel
def certificate2209 : RatCutBinCertificate := ⟨⟨retention2209,(1991983684202059961/1000000000000000000),(51337219122942991/1000000000000000000),(10227232806214502729/1000000000000000000),(925536029579625736477/1000000000000000000),(1215808343513337797/1000000000000000000)⟩,(124743898203826829/125000000000000000),(3415781000482849/7812500000000000),(201059288474060049/1000000000000000000),(86711199572582129/500000000000000000)⟩
theorem valid2209 : certificate2209.Valid := by decide +kernel
theorem sound2209 : certificate2209.Sound := rat_cut_bin_certificate_sound certificate2209 profilesValid2209 numericValid2209 valid2209

def retention2210 : RatCutRetentionCertificate := ⟨(33/1000),(17/500),(44692146742620340885/90030724948873378429),(34849525679542764067/1000000000000000000),1,(27918230209483431929512104052054625367/27879620543634211253600000000000000000),false,MergedCutProfiles.Batch340.profile13634,(fun _ => MergedCutProfiles.Batch340.profile13634)⟩
theorem profilesValid2210 : retention2210.ProfilesValid := by
  exact MergedCutProfiles.Batch340.valid13634
theorem numericValid2210 : retention2210.NumericValid := by decide +kernel
def certificate2210 : RatCutBinCertificate := ⟨⟨retention2210,(1991983684202059961/1000000000000000000),(51337219122942991/1000000000000000000),(10227232806214502729/1000000000000000000),(925536029579625736477/1000000000000000000),(991385776226438963/1000000000000000000)⟩,(124743898203826829/125000000000000000),(466604632152025603/1000000000000000000),(177715097918337653/1000000000000000000),(17095442332128589/100000000000000000)⟩
theorem valid2210 : certificate2210.Valid := by decide +kernel
theorem sound2210 : certificate2210.Sound := rat_cut_bin_certificate_sound certificate2210 profilesValid2210 numericValid2210 valid2210

def retention2211 : RatCutRetentionCertificate := ⟨(33/1000),(17/500),(1/2),(8938429348524068177/200000000000000000),1,(178032008268622996852284649581501864171/178768586970481363540000000000000000000),false,MergedCutProfiles.Batch340.profile13635,(fun _ => MergedCutProfiles.Batch340.profile13635)⟩
theorem profilesValid2211 : retention2211.ProfilesValid := by
  exact MergedCutProfiles.Batch340.valid13635
theorem numericValid2211 : retention2211.NumericValid := by decide +kernel
def certificate2211 : RatCutBinCertificate := ⟨⟨retention2211,(1991983684202059961/1000000000000000000),(51337219122942991/1000000000000000000),(10227232806214502729/1000000000000000000),(925536029579625736477/1000000000000000000),(985880617596662613/1000000000000000000)⟩,(124743898203826829/125000000000000000),(93336806860618053/200000000000000000),(88827289493659617/500000000000000000),(42752655583823011/250000000000000000)⟩
theorem valid2211 : certificate2211.Valid := by decide +kernel
theorem sound2211 : certificate2211.Sound := rat_cut_bin_certificate_sound certificate2211 profilesValid2211 numericValid2211 valid2211

def retention2212 : RatCutRetentionCertificate := ⟨(33/1000),(17/500),(38390928999293095017/90030724948873378429),(5570345173891081219/1000000000000000000),(21/20),(9946948208758201955083731655446511807559/8912552278225729950400000000000000000000),false,MergedCutProfiles.Batch340.profile13636,(fun _ => MergedCutProfiles.Batch340.profile13636)⟩
theorem profilesValid2212 : retention2212.ProfilesValid := by
  exact MergedCutProfiles.Batch340.valid13636
theorem numericValid2212 : retention2212.NumericValid := by decide +kernel
def certificate2212 : RatCutBinCertificate := ⟨⟨retention2212,(2295111038202059961/1000000000000000000),(51337219122942991/1000000000000000000),(10227232806214502729/1000000000000000000),(925536029579625736477/1000000000000000000),(275990937737954937/250000000000000000)⟩,(498819686454792957/500000000000000000),(10745416672434423/50000000000000000),(454455387488388217/1000000000000000000),(40398466107649643/100000000000000000)⟩
theorem valid2212 : certificate2212.Valid := by decide +kernel
theorem sound2212 : certificate2212.Sound := rat_cut_bin_certificate_sound certificate2212 profilesValid2212 numericValid2212 valid2212

def retention2213 : RatCutRetentionCertificate := ⟨(33/1000),(17/500),(44570676735993087761/90030724948873378429),(38390928999293095017/1000000000000000000),1,(154289673050441511700722481086373553027/153563715997172380068000000000000000000),false,MergedCutProfiles.Batch340.profile13637,(fun _ => MergedCutProfiles.Batch340.profile13637)⟩
theorem profilesValid2213 : retention2213.ProfilesValid := by
  exact MergedCutProfiles.Batch340.valid13637
theorem numericValid2213 : retention2213.NumericValid := by decide +kernel
def certificate2213 : RatCutBinCertificate := ⟨⟨retention2213,(2295111038202059961/1000000000000000000),(51337219122942991/1000000000000000000),(10227232806214502729/1000000000000000000),(925536029579625736477/1000000000000000000),(198641341733248357/200000000000000000)⟩,(498819686454792957/500000000000000000),(119436874436449571/500000000000000000),(104747350143119557/250000000000000000),(8093586367413643/20000000000000000)⟩
theorem valid2213 : certificate2213.Valid := by decide +kernel
theorem sound2213 : certificate2213.Sound := rat_cut_bin_certificate_sound certificate2213 profilesValid2213 numericValid2213 valid2213

def retention2214 : RatCutRetentionCertificate := ⟨(33/1000),(17/500),(1/2),(44570676735993087761/1000000000000000000),1,(177545404175533299094802078421115935643/178282706943972351044000000000000000000),false,MergedCutProfiles.Batch340.profile13635,(fun _ => MergedCutProfiles.Batch340.profile13635)⟩
theorem profilesValid2214 : retention2214.ProfilesValid := by
  exact MergedCutProfiles.Batch340.valid13635
theorem numericValid2214 : retention2214.NumericValid := by decide +kernel
def certificate2214 : RatCutBinCertificate := ⟨⟨retention2214,(2295111038202059961/1000000000000000000),(51337219122942991/1000000000000000000),(10227232806214502729/1000000000000000000),(925536029579625736477/1000000000000000000),(984343729267678393/1000000000000000000)⟩,(498819686454792957/500000000000000000),(60256138900109119/250000000000000000),(207962726146991587/500000000000000000),(99902876861464397/250000000000000000)⟩
theorem valid2214 : certificate2214.Valid := by decide +kernel
theorem sound2214 : certificate2214.Sound := rat_cut_bin_certificate_sound certificate2214 profilesValid2214 numericValid2214 valid2214

def retention2215 : RatCutRetentionCertificate := ⟨(17/500),(7/200),(48834533613330520/5634601300693800159),(181316337673256881/250000000000000000),(73/20),(22668166563859679849/10000000000000000000),true,MergedCutProfiles.Batch340.profile13638,![MergedCutProfiles.Batch340.profile13638,MergedCutProfiles.Batch340.profile13639,MergedCutProfiles.Batch341.profile13640,MergedCutProfiles.Batch341.profile13641,MergedCutProfiles.Batch341.profile13642,MergedCutProfiles.Batch341.profile13643,MergedCutProfiles.Batch341.profile13644,MergedCutProfiles.Batch341.profile13645,MergedCutProfiles.Batch341.profile13646,MergedCutProfiles.Batch341.profile13647,MergedCutProfiles.Batch341.profile13648,MergedCutProfiles.Batch341.profile13649,MergedCutProfiles.Batch341.profile13650,MergedCutProfiles.Batch341.profile13651,MergedCutProfiles.Batch341.profile13652,MergedCutProfiles.Batch341.profile13653]⟩
theorem profilesValid2215 : retention2215.ProfilesValid := by
  change ∀ j : Fin 16, (retention2215.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch340.valid13638
  · exact MergedCutProfiles.Batch340.valid13639
  · exact MergedCutProfiles.Batch341.valid13640
  · exact MergedCutProfiles.Batch341.valid13641
  · exact MergedCutProfiles.Batch341.valid13642
  · exact MergedCutProfiles.Batch341.valid13643
  · exact MergedCutProfiles.Batch341.valid13644
  · exact MergedCutProfiles.Batch341.valid13645
  · exact MergedCutProfiles.Batch341.valid13646
  · exact MergedCutProfiles.Batch341.valid13647
  · exact MergedCutProfiles.Batch341.valid13648
  · exact MergedCutProfiles.Batch341.valid13649
  · exact MergedCutProfiles.Batch341.valid13650
  · exact MergedCutProfiles.Batch341.valid13651
  · exact MergedCutProfiles.Batch341.valid13652
  · exact MergedCutProfiles.Batch341.valid13653
theorem numericValid2215 : retention2215.NumericValid := by decide +kernel
def certificate2215 : RatCutBinCertificate := ⟨⟨retention2215,(2005697646422337791/1000000000000000000),(853665110250683/15625000000000000),(2594303627910352299/250000000000000000),(440822031069632704001/500000000000000000),(111413639810115241/50000000000000000)⟩,(99784158436982813/100000000000000000),(27687457973879771/62500000000000000),(196316016786803537/1000000000000000000),(9714293047799161/100000000000000000)⟩
theorem valid2215 : certificate2215.Valid := by decide +kernel
theorem sound2215 : certificate2215.Sound := rat_cut_bin_certificate_sound certificate2215 profilesValid2215 numericValid2215 valid2215

def retention2216 : RatCutRetentionCertificate := ⟨(17/500),(7/200),(306964848384862336/28173006503469000795),(3662590020999789/5000000000000000),(73/20),(72227161351202035403/32000000000000000000),true,MergedCutProfiles.Batch341.profile13654,![MergedCutProfiles.Batch341.profile13654,MergedCutProfiles.Batch341.profile13655,MergedCutProfiles.Batch341.profile13656,MergedCutProfiles.Batch341.profile13642,MergedCutProfiles.Batch341.profile13657,MergedCutProfiles.Batch341.profile13658,MergedCutProfiles.Batch341.profile13659,MergedCutProfiles.Batch341.profile13660,MergedCutProfiles.Batch341.profile13661,MergedCutProfiles.Batch341.profile13662,MergedCutProfiles.Batch341.profile13663,MergedCutProfiles.Batch341.profile13664,MergedCutProfiles.Batch341.profile13665,MergedCutProfiles.Batch341.profile13666,MergedCutProfiles.Batch341.profile13667,MergedCutProfiles.Batch341.profile13668]⟩
theorem profilesValid2216 : retention2216.ProfilesValid := by
  change ∀ j : Fin 16, (retention2216.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch341.valid13654
  · exact MergedCutProfiles.Batch341.valid13655
  · exact MergedCutProfiles.Batch341.valid13656
  · exact MergedCutProfiles.Batch341.valid13642
  · exact MergedCutProfiles.Batch341.valid13657
  · exact MergedCutProfiles.Batch341.valid13658
  · exact MergedCutProfiles.Batch341.valid13659
  · exact MergedCutProfiles.Batch341.valid13660
  · exact MergedCutProfiles.Batch341.valid13661
  · exact MergedCutProfiles.Batch341.valid13662
  · exact MergedCutProfiles.Batch341.valid13663
  · exact MergedCutProfiles.Batch341.valid13664
  · exact MergedCutProfiles.Batch341.valid13665
  · exact MergedCutProfiles.Batch341.valid13666
  · exact MergedCutProfiles.Batch341.valid13667
  · exact MergedCutProfiles.Batch341.valid13668
theorem numericValid2216 : retention2216.NumericValid := by decide +kernel
def certificate2216 : RatCutBinCertificate := ⟨⟨retention2216,(2005697646422337791/1000000000000000000),(853665110250683/15625000000000000),(2594303627910352299/250000000000000000),(440822031069632704001/500000000000000000),(2218554940974621727/1000000000000000000)⟩,(99784158436982813/100000000000000000),(110636626896857119/250000000000000000),(98342461649108523/500000000000000000),(6072510989512567/62500000000000000)⟩
theorem valid2216 : certificate2216.Valid := by decide +kernel
theorem sound2216 : certificate2216.Sound := rat_cut_bin_certificate_sound certificate2216 profilesValid2216 numericValid2216 valid2216

def retention2217 : RatCutRetentionCertificate := ⟨(17/500),(7/200),(220427893400000000/16903803902081400477),(7194488634020211/7812500000000000),3,(4464673488244933227/2000000000000000000),true,MergedCutProfiles.Batch341.profile13669,![MergedCutProfiles.Batch341.profile13669,MergedCutProfiles.Batch341.profile13640,MergedCutProfiles.Batch341.profile13670,MergedCutProfiles.Batch341.profile13643,MergedCutProfiles.Batch341.profile13658,MergedCutProfiles.Batch341.profile13671,MergedCutProfiles.Batch341.profile13672,MergedCutProfiles.Batch341.profile13649,MergedCutProfiles.Batch341.profile13673,MergedCutProfiles.Batch341.profile13652,MergedCutProfiles.Batch341.profile13674,MergedCutProfiles.Batch341.profile13675,MergedCutProfiles.Batch341.profile13676,MergedCutProfiles.Batch341.profile13677,MergedCutProfiles.Batch341.profile13678,MergedCutProfiles.Batch341.profile13679]⟩
theorem profilesValid2217 : retention2217.ProfilesValid := by
  change ∀ j : Fin 16, (retention2217.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch341.valid13669
  · exact MergedCutProfiles.Batch341.valid13640
  · exact MergedCutProfiles.Batch341.valid13670
  · exact MergedCutProfiles.Batch341.valid13643
  · exact MergedCutProfiles.Batch341.valid13658
  · exact MergedCutProfiles.Batch341.valid13671
  · exact MergedCutProfiles.Batch341.valid13672
  · exact MergedCutProfiles.Batch341.valid13649
  · exact MergedCutProfiles.Batch341.valid13673
  · exact MergedCutProfiles.Batch341.valid13652
  · exact MergedCutProfiles.Batch341.valid13674
  · exact MergedCutProfiles.Batch341.valid13675
  · exact MergedCutProfiles.Batch341.valid13676
  · exact MergedCutProfiles.Batch341.valid13677
  · exact MergedCutProfiles.Batch341.valid13678
  · exact MergedCutProfiles.Batch341.valid13679
theorem numericValid2217 : retention2217.NumericValid := by decide +kernel
def certificate2217 : RatCutBinCertificate := ⟨⟨retention2217,(2005697646422337791/1000000000000000000),(853665110250683/15625000000000000),(2594303627910352299/250000000000000000),(440822031069632704001/500000000000000000),(275082111254248939/125000000000000000)⟩,(99784158436982813/100000000000000000),(396791215146951751/1000000000000000000),(236435310939265437/1000000000000000000),(1367056835826411/10000000000000000)⟩
theorem valid2217 : certificate2217.Valid := by decide +kernel
theorem sound2217 : certificate2217.Sound := rat_cut_bin_certificate_sound certificate2217 profilesValid2217 numericValid2217 valid2217

def retention2218 : RatCutRetentionCertificate := ⟨(17/500),(7/200),(1384797355647283741/84519019510407002385),(1102139467/1000000000),(51/20),(3512767759656618151/1600000000000000000),true,MergedCutProfiles.Batch342.profile13680,![MergedCutProfiles.Batch342.profile13680,MergedCutProfiles.Batch341.profile13656,MergedCutProfiles.Batch342.profile13681,MergedCutProfiles.Batch342.profile13682,MergedCutProfiles.Batch342.profile13683,MergedCutProfiles.Batch341.profile13661,MergedCutProfiles.Batch342.profile13684,MergedCutProfiles.Batch341.profile13664,MergedCutProfiles.Batch342.profile13685,MergedCutProfiles.Batch342.profile13686,MergedCutProfiles.Batch342.profile13687,MergedCutProfiles.Batch342.profile13688,MergedCutProfiles.Batch342.profile13689,MergedCutProfiles.Batch342.profile13690,MergedCutProfiles.Batch342.profile13691,MergedCutProfiles.Batch342.profile13692]⟩
theorem profilesValid2218 : retention2218.ProfilesValid := by
  change ∀ j : Fin 16, (retention2218.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch342.valid13680
  · exact MergedCutProfiles.Batch341.valid13656
  · exact MergedCutProfiles.Batch342.valid13681
  · exact MergedCutProfiles.Batch342.valid13682
  · exact MergedCutProfiles.Batch342.valid13683
  · exact MergedCutProfiles.Batch341.valid13661
  · exact MergedCutProfiles.Batch342.valid13684
  · exact MergedCutProfiles.Batch341.valid13664
  · exact MergedCutProfiles.Batch342.valid13685
  · exact MergedCutProfiles.Batch342.valid13686
  · exact MergedCutProfiles.Batch342.valid13687
  · exact MergedCutProfiles.Batch342.valid13688
  · exact MergedCutProfiles.Batch342.valid13689
  · exact MergedCutProfiles.Batch342.valid13690
  · exact MergedCutProfiles.Batch342.valid13691
  · exact MergedCutProfiles.Batch342.valid13692
theorem numericValid2218 : retention2218.NumericValid := by decide +kernel
def certificate2218 : RatCutBinCertificate := ⟨⟨retention2218,(2005697646422337791/1000000000000000000),(853665110250683/15625000000000000),(2594303627910352299/250000000000000000),(440822031069632704001/500000000000000000),(2168551984076912923/1000000000000000000)⟩,(99784158436982813/100000000000000000),(185318785766010247/500000000000000000),(65372521858393809/250000000000000000),(21286632680798411/125000000000000000)⟩
theorem valid2218 : certificate2218.Valid := by decide +kernel
theorem sound2218 : certificate2218.Sound := rat_cut_bin_certificate_sound certificate2218 profilesValid2218 numericValid2218 valid2218

def retention2219 : RatCutRetentionCertificate := ⟨(17/500),(7/200),(2407759021425902881/28173006503469000795),(1384797355647283741/1000000000000000000),(43/20),(2477352814970969292877/1280000000000000000000),true,MergedCutProfiles.Batch342.profile13693,![MergedCutProfiles.Batch342.profile13693,MergedCutProfiles.Batch342.profile13694,MergedCutProfiles.Batch342.profile13695,MergedCutProfiles.Batch342.profile13696,MergedCutProfiles.Batch342.profile13697,MergedCutProfiles.Batch342.profile13698,MergedCutProfiles.Batch342.profile13699,MergedCutProfiles.Batch342.profile13700,MergedCutProfiles.Batch342.profile13701,MergedCutProfiles.Batch342.profile13702,MergedCutProfiles.Batch342.profile13703,MergedCutProfiles.Batch342.profile13704,MergedCutProfiles.Batch342.profile13705,MergedCutProfiles.Batch342.profile13706,MergedCutProfiles.Batch342.profile13707,MergedCutProfiles.Batch342.profile13708]⟩
theorem profilesValid2219 : retention2219.ProfilesValid := by
  change ∀ j : Fin 16, (retention2219.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch342.valid13693
  · exact MergedCutProfiles.Batch342.valid13694
  · exact MergedCutProfiles.Batch342.valid13695
  · exact MergedCutProfiles.Batch342.valid13696
  · exact MergedCutProfiles.Batch342.valid13697
  · exact MergedCutProfiles.Batch342.valid13698
  · exact MergedCutProfiles.Batch342.valid13699
  · exact MergedCutProfiles.Batch342.valid13700
  · exact MergedCutProfiles.Batch342.valid13701
  · exact MergedCutProfiles.Batch342.valid13702
  · exact MergedCutProfiles.Batch342.valid13703
  · exact MergedCutProfiles.Batch342.valid13704
  · exact MergedCutProfiles.Batch342.valid13705
  · exact MergedCutProfiles.Batch342.valid13706
  · exact MergedCutProfiles.Batch342.valid13707
  · exact MergedCutProfiles.Batch342.valid13708
theorem numericValid2219 : retention2219.NumericValid := by decide +kernel
def certificate2219 : RatCutBinCertificate := ⟨⟨retention2219,(2005697646422337791/1000000000000000000),(853665110250683/15625000000000000),(2594303627910352299/250000000000000000),(440822031069632704001/500000000000000000),(29886375437146637/15625000000000000)⟩,(99784158436982813/100000000000000000),(382550927309502137/1000000000000000000),(9994244428792799/40000000000000000),(170721128997898363/1000000000000000000)⟩
theorem valid2219 : certificate2219.Valid := by decide +kernel
theorem sound2219 : certificate2219.Sound := rat_cut_bin_certificate_sound certificate2219 profilesValid2219 numericValid2219 valid2219

def certificates : List RatCutBinCertificate := [certificate2208,certificate2209,certificate2210,certificate2211,certificate2212,certificate2213,certificate2214,certificate2215,certificate2216,certificate2217,certificate2218,certificate2219]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2208,List.forall_mem_cons.mpr ⟨sound2209,List.forall_mem_cons.mpr ⟨sound2210,List.forall_mem_cons.mpr ⟨sound2211,List.forall_mem_cons.mpr ⟨sound2212,List.forall_mem_cons.mpr ⟨sound2213,List.forall_mem_cons.mpr ⟨sound2214,List.forall_mem_cons.mpr ⟨sound2215,List.forall_mem_cons.mpr ⟨sound2216,List.forall_mem_cons.mpr ⟨sound2217,List.forall_mem_cons.mpr ⟨sound2218,List.forall_mem_cons.mpr ⟨sound2219,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch184
