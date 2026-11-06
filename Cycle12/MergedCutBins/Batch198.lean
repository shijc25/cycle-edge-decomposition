import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch367
import Cycle12.MergedCutProfiles.Batch368
import Cycle12.MergedCutProfiles.Batch369
import Cycle12.MergedCutProfiles.Batch370

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch198

def retention2376 : RatCutRetentionCertificate := ⟨(23/500),(47/1000),(5920120628381517232/43922520259805796461),(176588632867617457/125000000000000000),(41/20),(287971433544458236973/160000000000000000000),true,MergedCutProfiles.Batch367.profile14713,![MergedCutProfiles.Batch367.profile14713,MergedCutProfiles.Batch367.profile14714,MergedCutProfiles.Batch367.profile14715,MergedCutProfiles.Batch367.profile14716,MergedCutProfiles.Batch367.profile14717,MergedCutProfiles.Batch367.profile14718,MergedCutProfiles.Batch367.profile14719,MergedCutProfiles.Batch368.profile14720,MergedCutProfiles.Batch368.profile14721,MergedCutProfiles.Batch368.profile14722,MergedCutProfiles.Batch368.profile14723,MergedCutProfiles.Batch368.profile14724,MergedCutProfiles.Batch368.profile14725,MergedCutProfiles.Batch368.profile14726,MergedCutProfiles.Batch368.profile14727,MergedCutProfiles.Batch368.profile14728]⟩
theorem profilesValid2376 : retention2376.ProfilesValid := by
  change ∀ j : Fin 16, (retention2376.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch367.valid14713
  · exact MergedCutProfiles.Batch367.valid14714
  · exact MergedCutProfiles.Batch367.valid14715
  · exact MergedCutProfiles.Batch367.valid14716
  · exact MergedCutProfiles.Batch367.valid14717
  · exact MergedCutProfiles.Batch367.valid14718
  · exact MergedCutProfiles.Batch367.valid14719
  · exact MergedCutProfiles.Batch368.valid14720
  · exact MergedCutProfiles.Batch368.valid14721
  · exact MergedCutProfiles.Batch368.valid14722
  · exact MergedCutProfiles.Batch368.valid14723
  · exact MergedCutProfiles.Batch368.valid14724
  · exact MergedCutProfiles.Batch368.valid14725
  · exact MergedCutProfiles.Batch368.valid14726
  · exact MergedCutProfiles.Batch368.valid14727
  · exact MergedCutProfiles.Batch368.valid14728
theorem numericValid2376 : retention2376.NumericValid := by decide +kernel
def certificate2376 : RatCutBinCertificate := ⟨⟨retention2376,(2113123257850819737/1000000000000000000),(6511012982960937/62500000000000000),(12475637297761025987/1000000000000000000),(551038808552737177489/1000000000000000000),(1763646101060843877/1000000000000000000)⟩,(249136159241087007/250000000000000000),(18617859776320503/50000000000000000),(25978744808655457/100000000000000000),(2681628202490677/15625000000000000)⟩
theorem valid2376 : certificate2376.Valid := by decide +kernel
theorem sound2376 : certificate2376.Sound := rat_cut_bin_certificate_sound certificate2376 profilesValid2376 numericValid2376 valid2376

def retention2377 : RatCutRetentionCertificate := ⟨(23/500),(47/1000),(18964058596667935196/43922520259805796461),(370007539273844827/62500000000000000),(21/20),(88763449906676068443/80000000000000000000),true,MergedCutProfiles.Batch368.profile14729,![MergedCutProfiles.Batch368.profile14729,MergedCutProfiles.Batch368.profile14730,MergedCutProfiles.Batch368.profile14731,MergedCutProfiles.Batch368.profile14732,MergedCutProfiles.Batch368.profile14733,MergedCutProfiles.Batch368.profile14734,MergedCutProfiles.Batch368.profile14735,MergedCutProfiles.Batch368.profile14736,MergedCutProfiles.Batch368.profile14737,MergedCutProfiles.Batch368.profile14738,MergedCutProfiles.Batch368.profile14739,MergedCutProfiles.Batch368.profile14740,MergedCutProfiles.Batch368.profile14741,MergedCutProfiles.Batch368.profile14742,MergedCutProfiles.Batch368.profile14743,MergedCutProfiles.Batch368.profile14744]⟩
theorem profilesValid2377 : retention2377.ProfilesValid := by
  change ∀ j : Fin 16, (retention2377.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch368.valid14729
  · exact MergedCutProfiles.Batch368.valid14730
  · exact MergedCutProfiles.Batch368.valid14731
  · exact MergedCutProfiles.Batch368.valid14732
  · exact MergedCutProfiles.Batch368.valid14733
  · exact MergedCutProfiles.Batch368.valid14734
  · exact MergedCutProfiles.Batch368.valid14735
  · exact MergedCutProfiles.Batch368.valid14736
  · exact MergedCutProfiles.Batch368.valid14737
  · exact MergedCutProfiles.Batch368.valid14738
  · exact MergedCutProfiles.Batch368.valid14739
  · exact MergedCutProfiles.Batch368.valid14740
  · exact MergedCutProfiles.Batch368.valid14741
  · exact MergedCutProfiles.Batch368.valid14742
  · exact MergedCutProfiles.Batch368.valid14743
  · exact MergedCutProfiles.Batch368.valid14744
theorem numericValid2377 : retention2377.NumericValid := by decide +kernel
def certificate2377 : RatCutBinCertificate := ⟨⟨retention2377,(2113123257850819737/1000000000000000000),(6511012982960937/62500000000000000),(12475637297761025987/1000000000000000000),(551038808552737177489/1000000000000000000),(545507463810148997/500000000000000000)⟩,(249136159241087007/250000000000000000),(222149518918709681/500000000000000000),(195259728721063383/1000000000000000000),(173181572503704779/1000000000000000000)⟩
theorem valid2377 : certificate2377.Valid := by decide +kernel
theorem sound2377 : certificate2377.Sound := rat_cut_bin_certificate_sound certificate2377 profilesValid2377 numericValid2377 valid2377

def retention2378 : RatCutRetentionCertificate := ⟨(23/500),(47/1000),(21798696335197042689/43922520259805796461),(4741014649166983799/250000000000000000),1,(3775867215900156260239930044544437531/3792811719333587039200000000000000000),false,MergedCutProfiles.Batch368.profile14745,(fun _ => MergedCutProfiles.Batch368.profile14745)⟩
theorem profilesValid2378 : retention2378.ProfilesValid := by
  exact MergedCutProfiles.Batch368.valid14745
theorem numericValid2378 : retention2378.NumericValid := by decide +kernel
def certificate2378 : RatCutBinCertificate := ⟨⟨retention2378,(2113123257850819737/1000000000000000000),(6511012982960937/62500000000000000),(12475637297761025987/1000000000000000000),(551038808552737177489/1000000000000000000),(488943464362889331/500000000000000000)⟩,(249136159241087007/250000000000000000),(457787265322936441/1000000000000000000),(18452012360396953/100000000000000000),(170981500281490423/1000000000000000000)⟩
theorem valid2378 : certificate2378.Valid := by decide +kernel
theorem sound2378 : certificate2378.Sound := rat_cut_bin_certificate_sound certificate2378 profilesValid2378 numericValid2378 valid2378

def retention2379 : RatCutRetentionCertificate := ⟨(23/500),(47/1000),(1/2),(21798696335197042689/1000000000000000000),1,(2697674865384102128053426934476916629/2724837041899630336125000000000000000),false,MergedCutProfiles.Batch368.profile14746,(fun _ => MergedCutProfiles.Batch368.profile14746)⟩
theorem profilesValid2379 : retention2379.ProfilesValid := by
  exact MergedCutProfiles.Batch368.valid14746
theorem numericValid2379 : retention2379.NumericValid := by decide +kernel
def certificate2379 : RatCutBinCertificate := ⟨⟨retention2379,(2113123257850819737/1000000000000000000),(6511012982960937/62500000000000000),(12475637297761025987/1000000000000000000),(551038808552737177489/1000000000000000000),(243096528787620557/250000000000000000)⟩,(249136159241087007/250000000000000000),(458126866751437203/1000000000000000000),(36850980828180749/200000000000000000),(85454133683023229/500000000000000000)⟩
theorem valid2379 : certificate2379.Valid := by decide +kernel
theorem sound2379 : certificate2379.Sound := rat_cut_bin_certificate_sound certificate2379 profilesValid2379 numericValid2379 valid2379

def retention2380 : RatCutRetentionCertificate := ⟨(23/500),(47/1000),(19303291113565105804/43922520259805796461),(278246456235761879/50000000000000000),(21/20),(24299119972832886499292817717192134631/22259716498860950320000000000000000000),false,MergedCutProfiles.Batch368.profile14747,(fun _ => MergedCutProfiles.Batch368.profile14747)⟩
theorem profilesValid2380 : retention2380.ProfilesValid := by
  exact MergedCutProfiles.Batch368.valid14747
theorem numericValid2380 : retention2380.NumericValid := by decide +kernel
def certificate2380 : RatCutBinCertificate := ⟨⟨retention2380,(2396364530850819737/1000000000000000000),(6511012982960937/62500000000000000),(12475637297761025987/1000000000000000000),(551038808552737177489/1000000000000000000),(107060683266847029/100000000000000000)⟩,(498040641462162519/500000000000000000),(222986541728521051/1000000000000000000),(110555546965970609/250000000000000000),(76458592477092457/200000000000000000)⟩
theorem valid2380 : certificate2380.Valid := by decide +kernel
theorem sound2380 : certificate2380.Sound := rat_cut_bin_certificate_sound certificate2380 profilesValid2380 numericValid2380 valid2380

def retention2381 : RatCutRetentionCertificate := ⟨(23/500),(47/1000),(21751431590689183697/43922520259805796461),(4825822778391276451/250000000000000000),1,(3081946607307288799450671171001557447/3088526578170416928640000000000000000),false,MergedCutProfiles.Batch368.profile14748,(fun _ => MergedCutProfiles.Batch368.profile14748)⟩
theorem profilesValid2381 : retention2381.ProfilesValid := by
  exact MergedCutProfiles.Batch368.valid14748
theorem numericValid2381 : retention2381.NumericValid := by decide +kernel
def certificate2381 : RatCutBinCertificate := ⟨⟨retention2381,(2396364530850819737/1000000000000000000),(6511012982960937/62500000000000000),(12475637297761025987/1000000000000000000),(551038808552737177489/1000000000000000000),(244464703336319843/250000000000000000)⟩,(498040641462162519/500000000000000000),(244136384424417257/1000000000000000000),(411525861978589913/1000000000000000000),(381472988944994353/1000000000000000000)⟩
theorem valid2381 : certificate2381.Valid := by decide +kernel
theorem sound2381 : certificate2381.Sound := rat_cut_bin_certificate_sound certificate2381 profilesValid2381 numericValid2381 valid2381

def retention2382 : RatCutRetentionCertificate := ⟨(23/500),(47/1000),(1/2),(21751431590689183697/1000000000000000000),1,(2691757700713052512503504098903100741/2718928948836147962125000000000000000),false,MergedCutProfiles.Batch368.profile14746,(fun _ => MergedCutProfiles.Batch368.profile14746)⟩
theorem profilesValid2382 : retention2382.ProfilesValid := by
  exact MergedCutProfiles.Batch368.valid14746
theorem numericValid2382 : retention2382.NumericValid := by decide +kernel
def certificate2382 : RatCutBinCertificate := ⟨⟨retention2382,(2396364530850819737/1000000000000000000),(6511012982960937/62500000000000000),(12475637297761025987/1000000000000000000),(551038808552737177489/1000000000000000000),(969995927156856221/1000000000000000000)⟩,(498040641462162519/500000000000000000),(246115378924743543/1000000000000000000),(408748257302941357/1000000000000000000),(189018540626754823/500000000000000000)⟩
theorem valid2382 : certificate2382.Valid := by decide +kernel
theorem sound2382 : certificate2382.Sound := rat_cut_bin_certificate_sound certificate2382 profilesValid2382 numericValid2382 valid2382

def retention2383 : RatCutRetentionCertificate := ⟨(47/1000),(6/125),(826324939143621065/41874804427165708876),(818143504102595113/1000000000000000000),(16/5),(2817082375467886999669/1280000000000000000000),true,MergedCutProfiles.Batch368.profile14749,![MergedCutProfiles.Batch368.profile14749,MergedCutProfiles.Batch368.profile14750,MergedCutProfiles.Batch368.profile14751,MergedCutProfiles.Batch368.profile14752,MergedCutProfiles.Batch368.profile14753,MergedCutProfiles.Batch368.profile14754,MergedCutProfiles.Batch368.profile14755,MergedCutProfiles.Batch368.profile14756,MergedCutProfiles.Batch368.profile14757,MergedCutProfiles.Batch368.profile14758,MergedCutProfiles.Batch368.profile14759,MergedCutProfiles.Batch369.profile14760,MergedCutProfiles.Batch369.profile14761,MergedCutProfiles.Batch369.profile14762,MergedCutProfiles.Batch369.profile14763,MergedCutProfiles.Batch369.profile14764]⟩
theorem profilesValid2383 : retention2383.ProfilesValid := by
  change ∀ j : Fin 16, (retention2383.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch368.valid14749
  · exact MergedCutProfiles.Batch368.valid14750
  · exact MergedCutProfiles.Batch368.valid14751
  · exact MergedCutProfiles.Batch368.valid14752
  · exact MergedCutProfiles.Batch368.valid14753
  · exact MergedCutProfiles.Batch368.valid14754
  · exact MergedCutProfiles.Batch368.valid14755
  · exact MergedCutProfiles.Batch368.valid14756
  · exact MergedCutProfiles.Batch368.valid14757
  · exact MergedCutProfiles.Batch368.valid14758
  · exact MergedCutProfiles.Batch368.valid14759
  · exact MergedCutProfiles.Batch369.valid14760
  · exact MergedCutProfiles.Batch369.valid14761
  · exact MergedCutProfiles.Batch369.valid14762
  · exact MergedCutProfiles.Batch369.valid14763
  · exact MergedCutProfiles.Batch369.valid14764
theorem numericValid2383 : retention2383.NumericValid := by decide +kernel
def certificate2383 : RatCutBinCertificate := ⟨⟨retention2383,(265436194193411509/125000000000000000),(13651068898300767/125000000000000000),(12679345253919373993/1000000000000000000),(266972989700765776997/500000000000000000),(2142313540028687167/1000000000000000000)⟩,(996435836592471459/1000000000000000000),(188618870175395209/500000000000000000),(254998202572840873/1000000000000000000),(135379758637789271/1000000000000000000)⟩
theorem valid2383 : certificate2383.Valid := by decide +kernel
theorem sound2383 : certificate2383.Sound := rat_cut_bin_certificate_sound certificate2383 profilesValid2383 numericValid2383 valid2383

def retention2384 : RatCutRetentionCertificate := ⟨(47/1000),(6/125),(959337601393747367/41874804427165708876),(165264987828724213/200000000000000000),(63/20),(558811877665330467973/256000000000000000000),true,MergedCutProfiles.Batch369.profile14765,![MergedCutProfiles.Batch369.profile14765,MergedCutProfiles.Batch369.profile14766,MergedCutProfiles.Batch369.profile14767,MergedCutProfiles.Batch369.profile14768,MergedCutProfiles.Batch369.profile14769,MergedCutProfiles.Batch369.profile14770,MergedCutProfiles.Batch369.profile14771,MergedCutProfiles.Batch369.profile14772,MergedCutProfiles.Batch369.profile14773,MergedCutProfiles.Batch369.profile14774,MergedCutProfiles.Batch369.profile14775,MergedCutProfiles.Batch369.profile14776,MergedCutProfiles.Batch369.profile14777,MergedCutProfiles.Batch369.profile14778,MergedCutProfiles.Batch369.profile14779,MergedCutProfiles.Batch369.profile14780]⟩
theorem profilesValid2384 : retention2384.ProfilesValid := by
  change ∀ j : Fin 16, (retention2384.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch369.valid14765
  · exact MergedCutProfiles.Batch369.valid14766
  · exact MergedCutProfiles.Batch369.valid14767
  · exact MergedCutProfiles.Batch369.valid14768
  · exact MergedCutProfiles.Batch369.valid14769
  · exact MergedCutProfiles.Batch369.valid14770
  · exact MergedCutProfiles.Batch369.valid14771
  · exact MergedCutProfiles.Batch369.valid14772
  · exact MergedCutProfiles.Batch369.valid14773
  · exact MergedCutProfiles.Batch369.valid14774
  · exact MergedCutProfiles.Batch369.valid14775
  · exact MergedCutProfiles.Batch369.valid14776
  · exact MergedCutProfiles.Batch369.valid14777
  · exact MergedCutProfiles.Batch369.valid14778
  · exact MergedCutProfiles.Batch369.valid14779
  · exact MergedCutProfiles.Batch369.valid14780
theorem numericValid2384 : retention2384.NumericValid := by decide +kernel
def certificate2384 : RatCutBinCertificate := ⟨⟨retention2384,(265436194193411509/125000000000000000),(13651068898300767/125000000000000000),(12679345253919373993/1000000000000000000),(266972989700765776997/500000000000000000),(531310342170153559/250000000000000000)⟩,(996435836592471459/1000000000000000000),(94623282869307321/250000000000000000),(126888264892981801/500000000000000000),(135402741626355603/1000000000000000000)⟩
theorem valid2384 : certificate2384.Valid := by decide +kernel
theorem sound2384 : certificate2384.Sound := rat_cut_bin_certificate_sound certificate2384 profilesValid2384 numericValid2384 valid2384

def retention2385 : RatCutRetentionCertificate := ⟨(47/1000),(6/125),(255294556000000000/10468701106791427219),(959337601393747367/1000000000000000000),(11/4),(2160954604561060723/1000000000000000000),true,MergedCutProfiles.Batch369.profile14781,![MergedCutProfiles.Batch369.profile14781,MergedCutProfiles.Batch369.profile14782,MergedCutProfiles.Batch369.profile14783,MergedCutProfiles.Batch369.profile14784,MergedCutProfiles.Batch369.profile14785,MergedCutProfiles.Batch369.profile14786,MergedCutProfiles.Batch369.profile14787,MergedCutProfiles.Batch369.profile14788,MergedCutProfiles.Batch369.profile14789,MergedCutProfiles.Batch369.profile14790,MergedCutProfiles.Batch369.profile14791,MergedCutProfiles.Batch369.profile14792,MergedCutProfiles.Batch369.profile14793,MergedCutProfiles.Batch369.profile14794,MergedCutProfiles.Batch369.profile14780,MergedCutProfiles.Batch369.profile14795]⟩
theorem profilesValid2385 : retention2385.ProfilesValid := by
  change ∀ j : Fin 16, (retention2385.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch369.valid14781
  · exact MergedCutProfiles.Batch369.valid14782
  · exact MergedCutProfiles.Batch369.valid14783
  · exact MergedCutProfiles.Batch369.valid14784
  · exact MergedCutProfiles.Batch369.valid14785
  · exact MergedCutProfiles.Batch369.valid14786
  · exact MergedCutProfiles.Batch369.valid14787
  · exact MergedCutProfiles.Batch369.valid14788
  · exact MergedCutProfiles.Batch369.valid14789
  · exact MergedCutProfiles.Batch369.valid14790
  · exact MergedCutProfiles.Batch369.valid14791
  · exact MergedCutProfiles.Batch369.valid14792
  · exact MergedCutProfiles.Batch369.valid14793
  · exact MergedCutProfiles.Batch369.valid14794
  · exact MergedCutProfiles.Batch369.valid14780
  · exact MergedCutProfiles.Batch369.valid14795
theorem numericValid2385 : retention2385.NumericValid := by decide +kernel
def certificate2385 : RatCutBinCertificate := ⟨⟨retention2385,(265436194193411509/125000000000000000),(13651068898300767/125000000000000000),(12679345253919373993/1000000000000000000),(266972989700765776997/500000000000000000),(527663410118844641/250000000000000000)⟩,(996435836592471459/1000000000000000000),(35632881136486109/100000000000000000),(34496269244177913/125000000000000000),(10211963768981693/62500000000000000)⟩
theorem valid2385 : certificate2385.Valid := by decide +kernel
theorem sound2385 : certificate2385.Sound := rat_cut_bin_certificate_sound certificate2385 profilesValid2385 numericValid2385 valid2385

def retention2386 : RatCutRetentionCertificate := ⟨(47/1000),(6/125),(1242588086390935397/41874804427165708876),(63823639/62500000),(53/20),(34300805207884929253/16000000000000000000),true,MergedCutProfiles.Batch369.profile14796,![MergedCutProfiles.Batch369.profile14796,MergedCutProfiles.Batch368.profile14751,MergedCutProfiles.Batch369.profile14797,MergedCutProfiles.Batch368.profile14754,MergedCutProfiles.Batch369.profile14798,MergedCutProfiles.Batch369.profile14799,MergedCutProfiles.Batch370.profile14800,MergedCutProfiles.Batch369.profile14760,MergedCutProfiles.Batch370.profile14801,MergedCutProfiles.Batch369.profile14763,MergedCutProfiles.Batch370.profile14802,MergedCutProfiles.Batch370.profile14803,MergedCutProfiles.Batch370.profile14804,MergedCutProfiles.Batch370.profile14805,MergedCutProfiles.Batch370.profile14806,MergedCutProfiles.Batch370.profile14807]⟩
theorem profilesValid2386 : retention2386.ProfilesValid := by
  change ∀ j : Fin 16, (retention2386.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch369.valid14796
  · exact MergedCutProfiles.Batch368.valid14751
  · exact MergedCutProfiles.Batch369.valid14797
  · exact MergedCutProfiles.Batch368.valid14754
  · exact MergedCutProfiles.Batch369.valid14798
  · exact MergedCutProfiles.Batch369.valid14799
  · exact MergedCutProfiles.Batch370.valid14800
  · exact MergedCutProfiles.Batch369.valid14760
  · exact MergedCutProfiles.Batch370.valid14801
  · exact MergedCutProfiles.Batch369.valid14763
  · exact MergedCutProfiles.Batch370.valid14802
  · exact MergedCutProfiles.Batch370.valid14803
  · exact MergedCutProfiles.Batch370.valid14804
  · exact MergedCutProfiles.Batch370.valid14805
  · exact MergedCutProfiles.Batch370.valid14806
  · exact MergedCutProfiles.Batch370.valid14807
theorem numericValid2386 : retention2386.NumericValid := by decide +kernel
def certificate2386 : RatCutBinCertificate := ⟨⟨retention2386,(265436194193411509/125000000000000000),(13651068898300767/125000000000000000),(12679345253919373993/1000000000000000000),(266972989700765776997/500000000000000000),(261916072714726239/125000000000000000)⟩,(996435836592471459/1000000000000000000),(174772102793526403/500000000000000000),(141517584439291441/500000000000000000),(172469513967338517/1000000000000000000)⟩
theorem valid2386 : certificate2386.Valid := by decide +kernel
theorem sound2386 : certificate2386.Sound := rat_cut_bin_certificate_sound certificate2386 profilesValid2386 numericValid2386 valid2386

def retention2387 : RatCutRetentionCertificate := ⟨(47/1000),(6/125),(3980411001909162859/41874804427165708876),(1242588086390935397/1000000000000000000),(9/4),(489905241629804893737/256000000000000000000),true,MergedCutProfiles.Batch370.profile14808,![MergedCutProfiles.Batch370.profile14808,MergedCutProfiles.Batch370.profile14809,MergedCutProfiles.Batch370.profile14810,MergedCutProfiles.Batch370.profile14811,MergedCutProfiles.Batch370.profile14807,MergedCutProfiles.Batch370.profile14812,MergedCutProfiles.Batch370.profile14813,MergedCutProfiles.Batch370.profile14814,MergedCutProfiles.Batch370.profile14815,MergedCutProfiles.Batch370.profile14816,MergedCutProfiles.Batch370.profile14817,MergedCutProfiles.Batch370.profile14818,MergedCutProfiles.Batch370.profile14819,MergedCutProfiles.Batch370.profile14820,MergedCutProfiles.Batch370.profile14821,MergedCutProfiles.Batch370.profile14822]⟩
theorem profilesValid2387 : retention2387.ProfilesValid := by
  change ∀ j : Fin 16, (retention2387.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch370.valid14808
  · exact MergedCutProfiles.Batch370.valid14809
  · exact MergedCutProfiles.Batch370.valid14810
  · exact MergedCutProfiles.Batch370.valid14811
  · exact MergedCutProfiles.Batch370.valid14807
  · exact MergedCutProfiles.Batch370.valid14812
  · exact MergedCutProfiles.Batch370.valid14813
  · exact MergedCutProfiles.Batch370.valid14814
  · exact MergedCutProfiles.Batch370.valid14815
  · exact MergedCutProfiles.Batch370.valid14816
  · exact MergedCutProfiles.Batch370.valid14817
  · exact MergedCutProfiles.Batch370.valid14818
  · exact MergedCutProfiles.Batch370.valid14819
  · exact MergedCutProfiles.Batch370.valid14820
  · exact MergedCutProfiles.Batch370.valid14821
  · exact MergedCutProfiles.Batch370.valid14822
theorem numericValid2387 : retention2387.NumericValid := by decide +kernel
def certificate2387 : RatCutBinCertificate := ⟨⟨retention2387,(265436194193411509/125000000000000000),(13651068898300767/125000000000000000),(12679345253919373993/1000000000000000000),(266972989700765776997/500000000000000000),(7490148783035457/4000000000000000)⟩,(996435836592471459/1000000000000000000),(7241722999173853/20000000000000000),(270076150362155273/1000000000000000000),(86246031481026953/500000000000000000)⟩
theorem valid2387 : certificate2387.Valid := by decide +kernel
theorem sound2387 : certificate2387.Sound := rat_cut_bin_certificate_sound certificate2387 profilesValid2387 numericValid2387 valid2387

def certificates : List RatCutBinCertificate := [certificate2376,certificate2377,certificate2378,certificate2379,certificate2380,certificate2381,certificate2382,certificate2383,certificate2384,certificate2385,certificate2386,certificate2387]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2376,List.forall_mem_cons.mpr ⟨sound2377,List.forall_mem_cons.mpr ⟨sound2378,List.forall_mem_cons.mpr ⟨sound2379,List.forall_mem_cons.mpr ⟨sound2380,List.forall_mem_cons.mpr ⟨sound2381,List.forall_mem_cons.mpr ⟨sound2382,List.forall_mem_cons.mpr ⟨sound2383,List.forall_mem_cons.mpr ⟨sound2384,List.forall_mem_cons.mpr ⟨sound2385,List.forall_mem_cons.mpr ⟨sound2386,List.forall_mem_cons.mpr ⟨sound2387,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch198
