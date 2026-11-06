import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch414
import Cycle12.MergedCutProfiles.Batch415
import Cycle12.MergedCutProfiles.Batch416
import Cycle12.MergedCutProfiles.Batch417

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch220

def retention2640 : RatCutRetentionCertificate := ⟨(1/16),(63/1000),(157967998517826455/3705996998632225119),(938423753571246267/1000000000000000000),(13/5),(106130065580032475367/51200000000000000000),true,MergedCutProfiles.Batch414.profile16582,![MergedCutProfiles.Batch414.profile16582,MergedCutProfiles.Batch414.profile16583,MergedCutProfiles.Batch414.profile16584,MergedCutProfiles.Batch414.profile16585,MergedCutProfiles.Batch414.profile16586,MergedCutProfiles.Batch414.profile16587,MergedCutProfiles.Batch414.profile16588,MergedCutProfiles.Batch414.profile16589,MergedCutProfiles.Batch414.profile16590,MergedCutProfiles.Batch414.profile16591,MergedCutProfiles.Batch414.profile16592,MergedCutProfiles.Batch414.profile16593,MergedCutProfiles.Batch414.profile16594,MergedCutProfiles.Batch414.profile16595,MergedCutProfiles.Batch414.profile16596,MergedCutProfiles.Batch414.profile16597]⟩
theorem profilesValid2640 : retention2640.ProfilesValid := by
  change ∀ j : Fin 16, (retention2640.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch414.valid16582
  · exact MergedCutProfiles.Batch414.valid16583
  · exact MergedCutProfiles.Batch414.valid16584
  · exact MergedCutProfiles.Batch414.valid16585
  · exact MergedCutProfiles.Batch414.valid16586
  · exact MergedCutProfiles.Batch414.valid16587
  · exact MergedCutProfiles.Batch414.valid16588
  · exact MergedCutProfiles.Batch414.valid16589
  · exact MergedCutProfiles.Batch414.valid16590
  · exact MergedCutProfiles.Batch414.valid16591
  · exact MergedCutProfiles.Batch414.valid16592
  · exact MergedCutProfiles.Batch414.valid16593
  · exact MergedCutProfiles.Batch414.valid16594
  · exact MergedCutProfiles.Batch414.valid16595
  · exact MergedCutProfiles.Batch414.valid16596
  · exact MergedCutProfiles.Batch414.valid16597
theorem numericValid2640 : retention2640.NumericValid := by decide +kernel
def certificate2640 : RatCutBinCertificate := ⟨⟨retention2640,(2309763809708753259/1000000000000000000),(204909449857824037/1000000000000000000),(16618134290879467777/1000000000000000000),(74134781647593655627/200000000000000000),(1998786819733654393/1000000000000000000)⟩,(995015036970164963/1000000000000000000),(144731422615218951/500000000000000000),(175825704298749503/500000000000000000),(204334358625812379/1000000000000000000)⟩
theorem valid2640 : certificate2640.Valid := by decide +kernel
theorem sound2640 : certificate2640.Sound := rat_cut_bin_certificate_sound certificate2640 profilesValid2640 numericValid2640 valid2640

def retention2641 : RatCutRetentionCertificate := ⟨(1/16),(63/1000),(492965728000000000/11117990995896675357),(94780799110695873/100000000000000000),(13/5),(16582548931378451361/8000000000000000000),true,MergedCutProfiles.Batch414.profile16598,![MergedCutProfiles.Batch414.profile16598,MergedCutProfiles.Batch414.profile16599,MergedCutProfiles.Batch415.profile16600,MergedCutProfiles.Batch415.profile16601,MergedCutProfiles.Batch415.profile16602,MergedCutProfiles.Batch415.profile16603,MergedCutProfiles.Batch415.profile16604,MergedCutProfiles.Batch415.profile16605,MergedCutProfiles.Batch415.profile16606,MergedCutProfiles.Batch415.profile16607,MergedCutProfiles.Batch415.profile16608,MergedCutProfiles.Batch415.profile16609,MergedCutProfiles.Batch415.profile16610,MergedCutProfiles.Batch415.profile16611,MergedCutProfiles.Batch415.profile16612,MergedCutProfiles.Batch415.profile16613]⟩
theorem profilesValid2641 : retention2641.ProfilesValid := by
  change ∀ j : Fin 16, (retention2641.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch414.valid16598
  · exact MergedCutProfiles.Batch414.valid16599
  · exact MergedCutProfiles.Batch415.valid16600
  · exact MergedCutProfiles.Batch415.valid16601
  · exact MergedCutProfiles.Batch415.valid16602
  · exact MergedCutProfiles.Batch415.valid16603
  · exact MergedCutProfiles.Batch415.valid16604
  · exact MergedCutProfiles.Batch415.valid16605
  · exact MergedCutProfiles.Batch415.valid16606
  · exact MergedCutProfiles.Batch415.valid16607
  · exact MergedCutProfiles.Batch415.valid16608
  · exact MergedCutProfiles.Batch415.valid16609
  · exact MergedCutProfiles.Batch415.valid16610
  · exact MergedCutProfiles.Batch415.valid16611
  · exact MergedCutProfiles.Batch415.valid16612
  · exact MergedCutProfiles.Batch415.valid16613
theorem numericValid2641 : retention2641.NumericValid := by decide +kernel
def certificate2641 : RatCutBinCertificate := ⟨⟨retention2641,(2309763809708753259/1000000000000000000),(204909449857824037/1000000000000000000),(16618134290879467777/1000000000000000000),(74134781647593655627/200000000000000000),(1998752758906380501/1000000000000000000)⟩,(995015036970164963/1000000000000000000),(72087207592704763/250000000000000000),(44129214992167979/125000000000000000),(102812132305478743/500000000000000000)⟩
theorem valid2641 : certificate2641.Valid := by decide +kernel
theorem sound2641 : certificate2641.Sound := rat_cut_bin_certificate_sound certificate2641 profilesValid2641 numericValid2641 valid2641

def retention2642 : RatCutRetentionCertificate := ⟨(1/16),(63/1000),(188953022666372932/3705996998632225119),(15405179/15625000),(5/2),(204657290703145199/100000000000000000),true,MergedCutProfiles.Batch415.profile16614,![MergedCutProfiles.Batch415.profile16614,MergedCutProfiles.Batch415.profile16615,MergedCutProfiles.Batch415.profile16616,MergedCutProfiles.Batch415.profile16617,MergedCutProfiles.Batch414.profile16587,MergedCutProfiles.Batch415.profile16618,MergedCutProfiles.Batch415.profile16619,MergedCutProfiles.Batch415.profile16620,MergedCutProfiles.Batch415.profile16621,MergedCutProfiles.Batch415.profile16622,MergedCutProfiles.Batch415.profile16623,MergedCutProfiles.Batch415.profile16624,MergedCutProfiles.Batch415.profile16625,MergedCutProfiles.Batch415.profile16626,MergedCutProfiles.Batch415.profile16627,MergedCutProfiles.Batch415.profile16628]⟩
theorem profilesValid2642 : retention2642.ProfilesValid := by
  change ∀ j : Fin 16, (retention2642.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch415.valid16614
  · exact MergedCutProfiles.Batch415.valid16615
  · exact MergedCutProfiles.Batch415.valid16616
  · exact MergedCutProfiles.Batch415.valid16617
  · exact MergedCutProfiles.Batch414.valid16587
  · exact MergedCutProfiles.Batch415.valid16618
  · exact MergedCutProfiles.Batch415.valid16619
  · exact MergedCutProfiles.Batch415.valid16620
  · exact MergedCutProfiles.Batch415.valid16621
  · exact MergedCutProfiles.Batch415.valid16622
  · exact MergedCutProfiles.Batch415.valid16623
  · exact MergedCutProfiles.Batch415.valid16624
  · exact MergedCutProfiles.Batch415.valid16625
  · exact MergedCutProfiles.Batch415.valid16626
  · exact MergedCutProfiles.Batch415.valid16627
  · exact MergedCutProfiles.Batch415.valid16628
theorem numericValid2642 : retention2642.NumericValid := by decide +kernel
def certificate2642 : RatCutBinCertificate := ⟨⟨retention2642,(2309763809708753259/1000000000000000000),(204909449857824037/1000000000000000000),(16618134290879467777/1000000000000000000),(74134781647593655627/200000000000000000),(1975355739763629071/1000000000000000000)⟩,(995015036970164963/1000000000000000000),(287386232720910053/1000000000000000000),(177115795834656063/500000000000000000),(105340789789392789/500000000000000000)⟩
theorem valid2642 : certificate2642.Valid := by decide +kernel
theorem sound2642 : certificate2642.Sound := rat_cut_bin_certificate_sound certificate2642 profilesValid2642 numericValid2642 valid2642

def retention2643 : RatCutRetentionCertificate := ⟨(1/16),(63/1000),(2320833616317434903/22235981991793350714),(141714766999779699/125000000000000000),(9/4),(60555686641520690109/32000000000000000000),true,MergedCutProfiles.Batch415.profile16629,![MergedCutProfiles.Batch415.profile16629,MergedCutProfiles.Batch415.profile16630,MergedCutProfiles.Batch415.profile16631,MergedCutProfiles.Batch415.profile16632,MergedCutProfiles.Batch415.profile16633,MergedCutProfiles.Batch415.profile16634,MergedCutProfiles.Batch415.profile16635,MergedCutProfiles.Batch415.profile16636,MergedCutProfiles.Batch415.profile16637,MergedCutProfiles.Batch415.profile16638,MergedCutProfiles.Batch415.profile16639,MergedCutProfiles.Batch416.profile16640,MergedCutProfiles.Batch416.profile16641,MergedCutProfiles.Batch416.profile16642,MergedCutProfiles.Batch416.profile16643,MergedCutProfiles.Batch416.profile16644]⟩
theorem profilesValid2643 : retention2643.ProfilesValid := by
  change ∀ j : Fin 16, (retention2643.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch415.valid16629
  · exact MergedCutProfiles.Batch415.valid16630
  · exact MergedCutProfiles.Batch415.valid16631
  · exact MergedCutProfiles.Batch415.valid16632
  · exact MergedCutProfiles.Batch415.valid16633
  · exact MergedCutProfiles.Batch415.valid16634
  · exact MergedCutProfiles.Batch415.valid16635
  · exact MergedCutProfiles.Batch415.valid16636
  · exact MergedCutProfiles.Batch415.valid16637
  · exact MergedCutProfiles.Batch415.valid16638
  · exact MergedCutProfiles.Batch415.valid16639
  · exact MergedCutProfiles.Batch416.valid16640
  · exact MergedCutProfiles.Batch416.valid16641
  · exact MergedCutProfiles.Batch416.valid16642
  · exact MergedCutProfiles.Batch416.valid16643
  · exact MergedCutProfiles.Batch416.valid16644
theorem numericValid2643 : retention2643.NumericValid := by decide +kernel
def certificate2643 : RatCutBinCertificate := ⟨⟨retention2643,(2309763809708753259/1000000000000000000),(204909449857824037/1000000000000000000),(16618134290879467777/1000000000000000000),(74134781647593655627/200000000000000000),(182827024174947019/100000000000000000)⟩,(995015036970164963/1000000000000000000),(14758849279744343/50000000000000000),(172313872881222713/500000000000000000),(42223249975058811/200000000000000000)⟩
theorem valid2643 : certificate2643.Valid := by decide +kernel
theorem sound2643 : certificate2643.Sound := rat_cut_bin_certificate_sound certificate2643 profilesValid2643 numericValid2643 valid2643

def retention2644 : RatCutRetentionCertificate := ⟨(1/16),(63/1000),(1202622617423294755/3705996998632225119),(2320833616317434903/1000000000000000000),(7/5),(1724716771255657795811/1280000000000000000000),true,MergedCutProfiles.Batch416.profile16645,![MergedCutProfiles.Batch416.profile16645,MergedCutProfiles.Batch416.profile16646,MergedCutProfiles.Batch416.profile16647,MergedCutProfiles.Batch416.profile16648,MergedCutProfiles.Batch416.profile16649,MergedCutProfiles.Batch416.profile16650,MergedCutProfiles.Batch416.profile16651,MergedCutProfiles.Batch416.profile16652,MergedCutProfiles.Batch416.profile16653,MergedCutProfiles.Batch416.profile16654,MergedCutProfiles.Batch416.profile16655,MergedCutProfiles.Batch416.profile16656,MergedCutProfiles.Batch416.profile16657,MergedCutProfiles.Batch416.profile16658,MergedCutProfiles.Batch416.profile16659,MergedCutProfiles.Batch416.profile16660]⟩
theorem profilesValid2644 : retention2644.ProfilesValid := by
  change ∀ j : Fin 16, (retention2644.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch416.valid16645
  · exact MergedCutProfiles.Batch416.valid16646
  · exact MergedCutProfiles.Batch416.valid16647
  · exact MergedCutProfiles.Batch416.valid16648
  · exact MergedCutProfiles.Batch416.valid16649
  · exact MergedCutProfiles.Batch416.valid16650
  · exact MergedCutProfiles.Batch416.valid16651
  · exact MergedCutProfiles.Batch416.valid16652
  · exact MergedCutProfiles.Batch416.valid16653
  · exact MergedCutProfiles.Batch416.valid16654
  · exact MergedCutProfiles.Batch416.valid16655
  · exact MergedCutProfiles.Batch416.valid16656
  · exact MergedCutProfiles.Batch416.valid16657
  · exact MergedCutProfiles.Batch416.valid16658
  · exact MergedCutProfiles.Batch416.valid16659
  · exact MergedCutProfiles.Batch416.valid16660
theorem numericValid2644 : retention2644.NumericValid := by decide +kernel
def certificate2644 : RatCutBinCertificate := ⟨⟨retention2644,(2309763809708753259/1000000000000000000),(204909449857824037/1000000000000000000),(16618134290879467777/1000000000000000000),(74134781647593655627/200000000000000000),(1307555522562202569/1000000000000000000)⟩,(995015036970164963/1000000000000000000),(84895961150790991/250000000000000000),(58729225880257473/200000000000000000),(211795832810973149/1000000000000000000)⟩
theorem valid2644 : certificate2644.Valid := by decide +kernel
theorem sound2644 : certificate2644.Sound := rat_cut_bin_certificate_sound certificate2644 profilesValid2644 numericValid2644 valid2644

def retention2645 : RatCutRetentionCertificate := ⟨(1/16),(63/1000),(5265781394788212536/11117990995896675357),(721573570453976853/100000000000000000),1,(26015508106602377613/25600000000000000000),true,MergedCutProfiles.Batch416.profile16661,![MergedCutProfiles.Batch416.profile16661,MergedCutProfiles.Batch416.profile16662,MergedCutProfiles.Batch416.profile16663,MergedCutProfiles.Batch416.profile16664,MergedCutProfiles.Batch416.profile16665,MergedCutProfiles.Batch416.profile16666,MergedCutProfiles.Batch416.profile16667,MergedCutProfiles.Batch416.profile16668,MergedCutProfiles.Batch416.profile16669,MergedCutProfiles.Batch416.profile16670,MergedCutProfiles.Batch416.profile16671,MergedCutProfiles.Batch416.profile16672,MergedCutProfiles.Batch416.profile16673,MergedCutProfiles.Batch416.profile16674,MergedCutProfiles.Batch416.profile16675,MergedCutProfiles.Batch416.profile16676]⟩
theorem profilesValid2645 : retention2645.ProfilesValid := by
  change ∀ j : Fin 16, (retention2645.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch416.valid16661
  · exact MergedCutProfiles.Batch416.valid16662
  · exact MergedCutProfiles.Batch416.valid16663
  · exact MergedCutProfiles.Batch416.valid16664
  · exact MergedCutProfiles.Batch416.valid16665
  · exact MergedCutProfiles.Batch416.valid16666
  · exact MergedCutProfiles.Batch416.valid16667
  · exact MergedCutProfiles.Batch416.valid16668
  · exact MergedCutProfiles.Batch416.valid16669
  · exact MergedCutProfiles.Batch416.valid16670
  · exact MergedCutProfiles.Batch416.valid16671
  · exact MergedCutProfiles.Batch416.valid16672
  · exact MergedCutProfiles.Batch416.valid16673
  · exact MergedCutProfiles.Batch416.valid16674
  · exact MergedCutProfiles.Batch416.valid16675
  · exact MergedCutProfiles.Batch416.valid16676
theorem numericValid2645 : retention2645.NumericValid := by decide +kernel
def certificate2645 : RatCutBinCertificate := ⟨⟨retention2645,(2309763809708753259/1000000000000000000),(204909449857824037/1000000000000000000),(16618134290879467777/1000000000000000000),(74134781647593655627/200000000000000000),(493874062046189753/500000000000000000)⟩,(995015036970164963/1000000000000000000),(19340210614980887/50000000000000000),(122896491331979639/500000000000000000),(212400170139231101/1000000000000000000)⟩
theorem valid2645 : certificate2645.Valid := by decide +kernel
theorem sound2645 : certificate2645.Sound := rat_cut_bin_certificate_sound certificate2645 profilesValid2645 numericValid2645 valid2645

def retention2646 : RatCutRetentionCertificate := ⟨(1/16),(63/1000),(5534389167552007138/11117990995896675357),(658222674348526567/62500000000000000),(21/20),(16465444772746716905518370571630213779/16455566858713164175000000000000000000),false,MergedCutProfiles.Batch416.profile16677,(fun _ => MergedCutProfiles.Batch416.profile16677)⟩
theorem profilesValid2646 : retention2646.ProfilesValid := by
  exact MergedCutProfiles.Batch416.valid16677
theorem numericValid2646 : retention2646.NumericValid := by decide +kernel
def certificate2646 : RatCutBinCertificate := ⟨⟨retention2646,(2309763809708753259/1000000000000000000),(204909449857824037/1000000000000000000),(16618134290879467777/1000000000000000000),(74134781647593655627/200000000000000000),(242673569907499257/250000000000000000)⟩,(995015036970164963/1000000000000000000),(384071348966947217/1000000000000000000),(62099566138593301/250000000000000000),(210806365460125701/1000000000000000000)⟩
theorem valid2646 : certificate2646.Valid := by decide +kernel
theorem sound2646 : certificate2646.Sound := rat_cut_bin_certificate_sound certificate2646 profilesValid2646 numericValid2646 valid2646

def retention2647 : RatCutRetentionCertificate := ⟨(1/16),(63/1000),(1/2),(2767194583776003569/250000000000000000),(21/20),(1103652232973089091295529389017409905039/1106877833510401427600000000000000000000),false,MergedCutProfiles.Batch416.profile16678,(fun _ => MergedCutProfiles.Batch416.profile16678)⟩
theorem profilesValid2647 : retention2647.ProfilesValid := by
  exact MergedCutProfiles.Batch416.valid16678
theorem numericValid2647 : retention2647.NumericValid := by decide +kernel
def certificate2647 : RatCutBinCertificate := ⟨⟨retention2647,(2309763809708753259/1000000000000000000),(204909449857824037/1000000000000000000),(16618134290879467777/1000000000000000000),(74134781647593655627/200000000000000000),(967179931007223449/1000000000000000000)⟩,(995015036970164963/1000000000000000000),(96114218361264719/250000000000000000),(9921182553182461/40000000000000000),(105289202320744309/500000000000000000)⟩
theorem valid2647 : certificate2647.Valid := by decide +kernel
theorem sound2647 : certificate2647.Sound := rat_cut_bin_certificate_sound certificate2647 profilesValid2647 numericValid2647 valid2647

def retention2648 : RatCutRetentionCertificate := ⟨(1/16),(63/1000),(560190879266728783/1235332332877408373),(246285946343669653/50000000000000000),(21/20),(4172725069517942004206781452312861619/3940575141498714448000000000000000000),false,MergedCutProfiles.Batch416.profile16679,(fun _ => MergedCutProfiles.Batch416.profile16679)⟩
theorem profilesValid2648 : retention2648.ProfilesValid := by
  exact MergedCutProfiles.Batch416.valid16679
theorem numericValid2648 : retention2648.NumericValid := by decide +kernel
def certificate2648 : RatCutBinCertificate := ⟨⟨retention2648,(2557108763708753259/1000000000000000000),(204909449857824037/1000000000000000000),(16618134290879467777/1000000000000000000),(74134781647593655627/200000000000000000),(51290114279438587/50000000000000000)⟩,(198896094506464451/200000000000000000),(113763176511580767/500000000000000000),(54434185498792411/125000000000000000),(355679679986891869/1000000000000000000)⟩
theorem valid2648 : certificate2648.Valid := by decide +kernel
theorem sound2648 : certificate2648.Sound := rat_cut_bin_certificate_sound certificate2648 profilesValid2648 numericValid2648 valid2648

def retention2649 : RatCutRetentionCertificate := ⟨(1/16),(63/1000),(1838017543638372494/3705996998632225119),(5041717913400559047/500000000000000000),1,(9926613986880635581552012671616729811/10083435826801118094000000000000000000),false,MergedCutProfiles.Batch417.profile16680,(fun _ => MergedCutProfiles.Batch417.profile16680)⟩
theorem profilesValid2649 : retention2649.ProfilesValid := by
  exact MergedCutProfiles.Batch417.valid16680
theorem numericValid2649 : retention2649.NumericValid := by decide +kernel
def certificate2649 : RatCutBinCertificate := ⟨⟨retention2649,(2557108763708753259/1000000000000000000),(204909449857824037/1000000000000000000),(16618134290879467777/1000000000000000000),(74134781647593655627/200000000000000000),(952915490740120611/1000000000000000000)⟩,(198896094506464451/200000000000000000),(12246471761182071/50000000000000000),(51301361263992833/125000000000000000),(71048359620313619/200000000000000000)⟩
theorem valid2649 : certificate2649.Valid := by decide +kernel
theorem sound2649 : certificate2649.Sound := rat_cut_bin_certificate_sound certificate2649 profilesValid2649 numericValid2649 valid2649

def retention2650 : RatCutRetentionCertificate := ⟨(1/16),(63/1000),(1/2),(2757026315457558741/250000000000000000),1,(719679228523070202421011856984517817/735207017455348997600000000000000000),false,MergedCutProfiles.Batch416.profile16678,(fun _ => MergedCutProfiles.Batch416.profile16678)⟩
theorem profilesValid2650 : retention2650.ProfilesValid := by
  exact MergedCutProfiles.Batch416.valid16678
theorem numericValid2650 : retention2650.NumericValid := by decide +kernel
def certificate2650 : RatCutBinCertificate := ⟨⟨retention2650,(2557108763708753259/1000000000000000000),(204909449857824037/1000000000000000000),(16618134290879467777/1000000000000000000),(74134781647593655627/200000000000000000),(473673882556362121/500000000000000000)⟩,(198896094506464451/200000000000000000),(61592231902047369/250000000000000000),(40839352656760039/100000000000000000),(88555408991478061/250000000000000000)⟩
theorem valid2650 : certificate2650.Valid := by decide +kernel
theorem sound2650 : certificate2650.Sound := rat_cut_bin_certificate_sound certificate2650 profilesValid2650 numericValid2650 valid2650

def retention2651 : RatCutRetentionCertificate := ⟨(63/1000),(127/2000),(939431925151892189/21818850745261242328),(465065309481134747/500000000000000000),(53/20),(41607515910168919283/20000000000000000000),true,MergedCutProfiles.Batch417.profile16681,![MergedCutProfiles.Batch417.profile16681,MergedCutProfiles.Batch417.profile16682,MergedCutProfiles.Batch417.profile16683,MergedCutProfiles.Batch417.profile16684,MergedCutProfiles.Batch417.profile16685,MergedCutProfiles.Batch417.profile16686,MergedCutProfiles.Batch417.profile16687,MergedCutProfiles.Batch417.profile16688,MergedCutProfiles.Batch417.profile16689,MergedCutProfiles.Batch417.profile16690,MergedCutProfiles.Batch417.profile16691,MergedCutProfiles.Batch417.profile16692,MergedCutProfiles.Batch417.profile16693,MergedCutProfiles.Batch417.profile16694,MergedCutProfiles.Batch417.profile16695,MergedCutProfiles.Batch417.profile16696]⟩
theorem profilesValid2651 : retention2651.ProfilesValid := by
  change ∀ j : Fin 16, (retention2651.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch417.valid16681
  · exact MergedCutProfiles.Batch417.valid16682
  · exact MergedCutProfiles.Batch417.valid16683
  · exact MergedCutProfiles.Batch417.valid16684
  · exact MergedCutProfiles.Batch417.valid16685
  · exact MergedCutProfiles.Batch417.valid16686
  · exact MergedCutProfiles.Batch417.valid16687
  · exact MergedCutProfiles.Batch417.valid16688
  · exact MergedCutProfiles.Batch417.valid16689
  · exact MergedCutProfiles.Batch417.valid16690
  · exact MergedCutProfiles.Batch417.valid16691
  · exact MergedCutProfiles.Batch417.valid16692
  · exact MergedCutProfiles.Batch417.valid16693
  · exact MergedCutProfiles.Batch417.valid16694
  · exact MergedCutProfiles.Batch417.valid16695
  · exact MergedCutProfiles.Batch417.valid16696
theorem numericValid2651 : retention2651.NumericValid := by decide +kernel
def certificate2651 : RatCutBinCertificate := ⟨⟨retention2651,(1145909313582507563/500000000000000000),(2610492019033761/12500000000000000),(16774951468829863873/1000000000000000000),(183578255566301162661/500000000000000000),(2004748701652612511/1000000000000000000)⟩,(995030470150701123/1000000000000000000),(290851906277251379/1000000000000000000),(43741722249291507/125000000000000000),(100672777397951683/500000000000000000)⟩
theorem valid2651 : certificate2651.Valid := by decide +kernel
theorem sound2651 : certificate2651.Sound := rat_cut_bin_certificate_sound certificate2651 profilesValid2651 numericValid2651 valid2651

def certificates : List RatCutBinCertificate := [certificate2640,certificate2641,certificate2642,certificate2643,certificate2644,certificate2645,certificate2646,certificate2647,certificate2648,certificate2649,certificate2650,certificate2651]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2640,List.forall_mem_cons.mpr ⟨sound2641,List.forall_mem_cons.mpr ⟨sound2642,List.forall_mem_cons.mpr ⟨sound2643,List.forall_mem_cons.mpr ⟨sound2644,List.forall_mem_cons.mpr ⟨sound2645,List.forall_mem_cons.mpr ⟨sound2646,List.forall_mem_cons.mpr ⟨sound2647,List.forall_mem_cons.mpr ⟨sound2648,List.forall_mem_cons.mpr ⟨sound2649,List.forall_mem_cons.mpr ⟨sound2650,List.forall_mem_cons.mpr ⟨sound2651,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch220
