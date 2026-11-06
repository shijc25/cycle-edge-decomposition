import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch422
import Cycle12.MergedCutProfiles.Batch423
import Cycle12.MergedCutProfiles.Batch424

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch223

def retention2676 : RatCutRetentionCertificate := ⟨(8/125),(129/2000),(319014153897045922/7005004029680237891),(236891698438400437/250000000000000000),(13/5),(41426946783493035739/20000000000000000000),true,MergedCutProfiles.Batch422.profile16880,![MergedCutProfiles.Batch422.profile16880,MergedCutProfiles.Batch422.profile16881,MergedCutProfiles.Batch422.profile16882,MergedCutProfiles.Batch422.profile16883,MergedCutProfiles.Batch422.profile16884,MergedCutProfiles.Batch422.profile16885,MergedCutProfiles.Batch422.profile16886,MergedCutProfiles.Batch422.profile16887,MergedCutProfiles.Batch422.profile16888,MergedCutProfiles.Batch422.profile16889,MergedCutProfiles.Batch422.profile16890,MergedCutProfiles.Batch422.profile16891,MergedCutProfiles.Batch422.profile16892,MergedCutProfiles.Batch422.profile16893,MergedCutProfiles.Batch422.profile16894,MergedCutProfiles.Batch422.profile16895]⟩
theorem profilesValid2676 : retention2676.ProfilesValid := by
  change ∀ j : Fin 16, (retention2676.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch422.valid16880
  · exact MergedCutProfiles.Batch422.valid16881
  · exact MergedCutProfiles.Batch422.valid16882
  · exact MergedCutProfiles.Batch422.valid16883
  · exact MergedCutProfiles.Batch422.valid16884
  · exact MergedCutProfiles.Batch422.valid16885
  · exact MergedCutProfiles.Batch422.valid16886
  · exact MergedCutProfiles.Batch422.valid16887
  · exact MergedCutProfiles.Batch422.valid16888
  · exact MergedCutProfiles.Batch422.valid16889
  · exact MergedCutProfiles.Batch422.valid16890
  · exact MergedCutProfiles.Batch422.valid16891
  · exact MergedCutProfiles.Batch422.valid16892
  · exact MergedCutProfiles.Batch422.valid16893
  · exact MergedCutProfiles.Batch422.valid16894
  · exact MergedCutProfiles.Batch422.valid16895
theorem numericValid2676 : retention2676.NumericValid := by decide +kernel
def certificate2676 : RatCutBinCertificate := ⟨⟨retention2676,(291167803739755079/125000000000000000),(216862197802423917/1000000000000000000),(534230152214430151/31250000000000000),(11262259210868497377/31250000000000000),(997250938484533521/500000000000000000)⟩,(994905011513720959/1000000000000000000),(139855153705050937/500000000000000000),(181949576542564821/500000000000000000),(52891112708140557/250000000000000000)⟩
theorem valid2676 : certificate2676.Valid := by decide +kernel
theorem sound2676 : certificate2676.Sound := rat_cut_bin_certificate_sound certificate2676 profilesValid2676 numericValid2676 valid2676

def retention2677 : RatCutRetentionCertificate := ⟨(8/125),(129/2000),(971200894000000000/21015012089040713673),(478521230845568883/500000000000000000),(51/20),(263882758463184558607/128000000000000000000),true,MergedCutProfiles.Batch422.profile16896,![MergedCutProfiles.Batch422.profile16896,MergedCutProfiles.Batch422.profile16897,MergedCutProfiles.Batch422.profile16898,MergedCutProfiles.Batch422.profile16899,MergedCutProfiles.Batch422.profile16900,MergedCutProfiles.Batch422.profile16901,MergedCutProfiles.Batch422.profile16902,MergedCutProfiles.Batch422.profile16903,MergedCutProfiles.Batch422.profile16904,MergedCutProfiles.Batch422.profile16905,MergedCutProfiles.Batch422.profile16906,MergedCutProfiles.Batch422.profile16907,MergedCutProfiles.Batch422.profile16908,MergedCutProfiles.Batch422.profile16909,MergedCutProfiles.Batch422.profile16910,MergedCutProfiles.Batch422.profile16911]⟩
theorem profilesValid2677 : retention2677.ProfilesValid := by
  change ∀ j : Fin 16, (retention2677.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch422.valid16896
  · exact MergedCutProfiles.Batch422.valid16897
  · exact MergedCutProfiles.Batch422.valid16898
  · exact MergedCutProfiles.Batch422.valid16899
  · exact MergedCutProfiles.Batch422.valid16900
  · exact MergedCutProfiles.Batch422.valid16901
  · exact MergedCutProfiles.Batch422.valid16902
  · exact MergedCutProfiles.Batch422.valid16903
  · exact MergedCutProfiles.Batch422.valid16904
  · exact MergedCutProfiles.Batch422.valid16905
  · exact MergedCutProfiles.Batch422.valid16906
  · exact MergedCutProfiles.Batch422.valid16907
  · exact MergedCutProfiles.Batch422.valid16908
  · exact MergedCutProfiles.Batch422.valid16909
  · exact MergedCutProfiles.Batch422.valid16910
  · exact MergedCutProfiles.Batch422.valid16911
theorem numericValid2677 : retention2677.NumericValid := by decide +kernel
def certificate2677 : RatCutBinCertificate := ⟨⟨retention2677,(291167803739755079/125000000000000000),(216862197802423917/1000000000000000000),(534230152214430151/31250000000000000),(11262259210868497377/31250000000000000),(496554052642343007/250000000000000000)⟩,(994905011513720959/1000000000000000000),(8743912467663591/31250000000000000),(90944593772192011/250000000000000000),(213475788094740261/1000000000000000000)⟩
theorem valid2677 : certificate2677.Valid := by decide +kernel
theorem sound2677 : certificate2677.Sound := rat_cut_bin_certificate_sound certificate2677 profilesValid2677 numericValid2677 valid2677

def retention2678 : RatCutRetentionCertificate := ⟨(8/125),(129/2000),(976279015171129636/21015012089040713673),(485600447/500000000),(51/20),(1033693117179498837/500000000000000000),true,MergedCutProfiles.Batch422.profile16896,![MergedCutProfiles.Batch422.profile16896,MergedCutProfiles.Batch422.profile16912,MergedCutProfiles.Batch422.profile16913,MergedCutProfiles.Batch422.profile16899,MergedCutProfiles.Batch422.profile16900,MergedCutProfiles.Batch422.profile16914,MergedCutProfiles.Batch422.profile16902,MergedCutProfiles.Batch422.profile16915,MergedCutProfiles.Batch422.profile16916,MergedCutProfiles.Batch422.profile16905,MergedCutProfiles.Batch422.profile16917,MergedCutProfiles.Batch422.profile16918,MergedCutProfiles.Batch422.profile16919,MergedCutProfiles.Batch423.profile16920,MergedCutProfiles.Batch423.profile16921,MergedCutProfiles.Batch423.profile16922]⟩
theorem profilesValid2678 : retention2678.ProfilesValid := by
  change ∀ j : Fin 16, (retention2678.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch422.valid16896
  · exact MergedCutProfiles.Batch422.valid16912
  · exact MergedCutProfiles.Batch422.valid16913
  · exact MergedCutProfiles.Batch422.valid16899
  · exact MergedCutProfiles.Batch422.valid16900
  · exact MergedCutProfiles.Batch422.valid16914
  · exact MergedCutProfiles.Batch422.valid16902
  · exact MergedCutProfiles.Batch422.valid16915
  · exact MergedCutProfiles.Batch422.valid16916
  · exact MergedCutProfiles.Batch422.valid16905
  · exact MergedCutProfiles.Batch422.valid16917
  · exact MergedCutProfiles.Batch422.valid16918
  · exact MergedCutProfiles.Batch422.valid16919
  · exact MergedCutProfiles.Batch423.valid16920
  · exact MergedCutProfiles.Batch423.valid16921
  · exact MergedCutProfiles.Batch423.valid16922
theorem numericValid2678 : retention2678.NumericValid := by decide +kernel
def certificate2678 : RatCutBinCertificate := ⟨⟨retention2678,(291167803739755079/125000000000000000),(216862197802423917/1000000000000000000),(534230152214430151/31250000000000000),(11262259210868497377/31250000000000000),(498004666320128659/250000000000000000)⟩,(994905011513720959/1000000000000000000),(6935800290684987/25000000000000000),(366808587142075641/1000000000000000000),(43299668518078911/200000000000000000)⟩
theorem valid2678 : certificate2678.Valid := by decide +kernel
theorem sound2678 : certificate2678.Sound := rat_cut_bin_certificate_sound certificate2678 profilesValid2678 numericValid2678 valid2678

def retention2679 : RatCutRetentionCertificate := ⟨(8/125),(129/2000),(1026079056646587622/21015012089040713673),(244069753792782409/250000000000000000),(5/2),(8202293994799273651/4000000000000000000),true,MergedCutProfiles.Batch423.profile16923,![MergedCutProfiles.Batch423.profile16923,MergedCutProfiles.Batch423.profile16924,MergedCutProfiles.Batch423.profile16925,MergedCutProfiles.Batch423.profile16926,MergedCutProfiles.Batch423.profile16927,MergedCutProfiles.Batch423.profile16928,MergedCutProfiles.Batch423.profile16929,MergedCutProfiles.Batch423.profile16930,MergedCutProfiles.Batch423.profile16931,MergedCutProfiles.Batch423.profile16932,MergedCutProfiles.Batch423.profile16933,MergedCutProfiles.Batch423.profile16934,MergedCutProfiles.Batch423.profile16935,MergedCutProfiles.Batch422.profile16894,MergedCutProfiles.Batch423.profile16936,MergedCutProfiles.Batch423.profile16937]⟩
theorem profilesValid2679 : retention2679.ProfilesValid := by
  change ∀ j : Fin 16, (retention2679.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch423.valid16923
  · exact MergedCutProfiles.Batch423.valid16924
  · exact MergedCutProfiles.Batch423.valid16925
  · exact MergedCutProfiles.Batch423.valid16926
  · exact MergedCutProfiles.Batch423.valid16927
  · exact MergedCutProfiles.Batch423.valid16928
  · exact MergedCutProfiles.Batch423.valid16929
  · exact MergedCutProfiles.Batch423.valid16930
  · exact MergedCutProfiles.Batch423.valid16931
  · exact MergedCutProfiles.Batch423.valid16932
  · exact MergedCutProfiles.Batch423.valid16933
  · exact MergedCutProfiles.Batch423.valid16934
  · exact MergedCutProfiles.Batch423.valid16935
  · exact MergedCutProfiles.Batch422.valid16894
  · exact MergedCutProfiles.Batch423.valid16936
  · exact MergedCutProfiles.Batch423.valid16937
theorem numericValid2679 : retention2679.NumericValid := by decide +kernel
def certificate2679 : RatCutBinCertificate := ⟨⟨retention2679,(291167803739755079/125000000000000000),(216862197802423917/1000000000000000000),(534230152214430151/31250000000000000),(11262259210868497377/31250000000000000),(1976683461343943901/1000000000000000000)⟩,(994905011513720959/1000000000000000000),(279032249057857813/1000000000000000000),(182381558298615509/500000000000000000),(108250856477605879/500000000000000000)⟩
theorem valid2679 : certificate2679.Valid := by decide +kernel
theorem sound2679 : certificate2679.Sound := rat_cut_bin_certificate_sound certificate2679 profilesValid2679 numericValid2679 valid2679

def retention2680 : RatCutRetentionCertificate := ⟨(8/125),(129/2000),(1453546419551519423/21015012089040713673),(513039528323293811/500000000000000000),(12/5),(1274409813632409896591/640000000000000000000),true,MergedCutProfiles.Batch423.profile16938,![MergedCutProfiles.Batch423.profile16938,MergedCutProfiles.Batch422.profile16898,MergedCutProfiles.Batch423.profile16939,MergedCutProfiles.Batch422.profile16901,MergedCutProfiles.Batch423.profile16940,MergedCutProfiles.Batch423.profile16941,MergedCutProfiles.Batch423.profile16942,MergedCutProfiles.Batch423.profile16943,MergedCutProfiles.Batch423.profile16944,MergedCutProfiles.Batch423.profile16945,MergedCutProfiles.Batch423.profile16946,MergedCutProfiles.Batch423.profile16947,MergedCutProfiles.Batch423.profile16948,MergedCutProfiles.Batch423.profile16949,MergedCutProfiles.Batch423.profile16950,MergedCutProfiles.Batch423.profile16951]⟩
theorem profilesValid2680 : retention2680.ProfilesValid := by
  change ∀ j : Fin 16, (retention2680.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch423.valid16938
  · exact MergedCutProfiles.Batch422.valid16898
  · exact MergedCutProfiles.Batch423.valid16939
  · exact MergedCutProfiles.Batch422.valid16901
  · exact MergedCutProfiles.Batch423.valid16940
  · exact MergedCutProfiles.Batch423.valid16941
  · exact MergedCutProfiles.Batch423.valid16942
  · exact MergedCutProfiles.Batch423.valid16943
  · exact MergedCutProfiles.Batch423.valid16944
  · exact MergedCutProfiles.Batch423.valid16945
  · exact MergedCutProfiles.Batch423.valid16946
  · exact MergedCutProfiles.Batch423.valid16947
  · exact MergedCutProfiles.Batch423.valid16948
  · exact MergedCutProfiles.Batch423.valid16949
  · exact MergedCutProfiles.Batch423.valid16950
  · exact MergedCutProfiles.Batch423.valid16951
theorem numericValid2680 : retention2680.NumericValid := by decide +kernel
def certificate2680 : RatCutBinCertificate := ⟨⟨retention2680,(291167803739755079/125000000000000000),(216862197802423917/1000000000000000000),(534230152214430151/31250000000000000),(11262259210868497377/31250000000000000),(15002586354464641/7812500000000000)⟩,(994905011513720959/1000000000000000000),(8810794417441577/31250000000000000),(180531382861410389/500000000000000000),(13544698653109159/62500000000000000)⟩
theorem valid2680 : certificate2680.Valid := by decide +kernel
theorem sound2680 : certificate2680.Sound := rat_cut_bin_certificate_sound certificate2680 profilesValid2680 numericValid2680 valid2680

def retention2681 : RatCutRetentionCertificate := ⟨(8/125),(129/2000),(4091210064681396548/21015012089040713673),(1453546419551519423/1000000000000000000),(37/20),(2108349953822641351079/1280000000000000000000),true,MergedCutProfiles.Batch423.profile16952,![MergedCutProfiles.Batch423.profile16952,MergedCutProfiles.Batch423.profile16930,MergedCutProfiles.Batch423.profile16934,MergedCutProfiles.Batch423.profile16953,MergedCutProfiles.Batch423.profile16954,MergedCutProfiles.Batch423.profile16955,MergedCutProfiles.Batch423.profile16956,MergedCutProfiles.Batch423.profile16957,MergedCutProfiles.Batch423.profile16958,MergedCutProfiles.Batch423.profile16959,MergedCutProfiles.Batch424.profile16960,MergedCutProfiles.Batch424.profile16961,MergedCutProfiles.Batch424.profile16962,MergedCutProfiles.Batch424.profile16963,MergedCutProfiles.Batch424.profile16964,MergedCutProfiles.Batch424.profile16965]⟩
theorem profilesValid2681 : retention2681.ProfilesValid := by
  change ∀ j : Fin 16, (retention2681.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch423.valid16952
  · exact MergedCutProfiles.Batch423.valid16930
  · exact MergedCutProfiles.Batch423.valid16934
  · exact MergedCutProfiles.Batch423.valid16953
  · exact MergedCutProfiles.Batch423.valid16954
  · exact MergedCutProfiles.Batch423.valid16955
  · exact MergedCutProfiles.Batch423.valid16956
  · exact MergedCutProfiles.Batch423.valid16957
  · exact MergedCutProfiles.Batch423.valid16958
  · exact MergedCutProfiles.Batch423.valid16959
  · exact MergedCutProfiles.Batch424.valid16960
  · exact MergedCutProfiles.Batch424.valid16961
  · exact MergedCutProfiles.Batch424.valid16962
  · exact MergedCutProfiles.Batch424.valid16963
  · exact MergedCutProfiles.Batch424.valid16964
  · exact MergedCutProfiles.Batch424.valid16965
theorem numericValid2681 : retention2681.NumericValid := by decide +kernel
def certificate2681 : RatCutBinCertificate := ⟨⟨retention2681,(291167803739755079/125000000000000000),(216862197802423917/1000000000000000000),(534230152214430151/31250000000000000),(11262259210868497377/31250000000000000),(1592471018558280247/1000000000000000000)⟩,(994905011513720959/1000000000000000000),(18957456973654561/62500000000000000),(334809043494212023/1000000000000000000),(108498536870772563/500000000000000000)⟩
theorem valid2681 : certificate2681.Valid := by decide +kernel
theorem sound2681 : certificate2681.Sound := rat_cut_bin_certificate_sound certificate2681 profilesValid2681 numericValid2681 valid2681

def retention2682 : RatCutRetentionCertificate := ⟨(8/125),(129/2000),(2993085018850676960/7005004029680237891),(1022802516170349137/250000000000000000),(11/10),(357918712321595499281/320000000000000000000),true,MergedCutProfiles.Batch424.profile16966,![MergedCutProfiles.Batch424.profile16966,MergedCutProfiles.Batch424.profile16967,MergedCutProfiles.Batch424.profile16968,MergedCutProfiles.Batch424.profile16969,MergedCutProfiles.Batch424.profile16970,MergedCutProfiles.Batch424.profile16971,MergedCutProfiles.Batch424.profile16972,MergedCutProfiles.Batch424.profile16973,MergedCutProfiles.Batch424.profile16974,MergedCutProfiles.Batch424.profile16975,MergedCutProfiles.Batch424.profile16976,MergedCutProfiles.Batch424.profile16977,MergedCutProfiles.Batch424.profile16978,MergedCutProfiles.Batch424.profile16979,MergedCutProfiles.Batch424.profile16980,MergedCutProfiles.Batch424.profile16981]⟩
theorem profilesValid2682 : retention2682.ProfilesValid := by
  change ∀ j : Fin 16, (retention2682.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch424.valid16966
  · exact MergedCutProfiles.Batch424.valid16967
  · exact MergedCutProfiles.Batch424.valid16968
  · exact MergedCutProfiles.Batch424.valid16969
  · exact MergedCutProfiles.Batch424.valid16970
  · exact MergedCutProfiles.Batch424.valid16971
  · exact MergedCutProfiles.Batch424.valid16972
  · exact MergedCutProfiles.Batch424.valid16973
  · exact MergedCutProfiles.Batch424.valid16974
  · exact MergedCutProfiles.Batch424.valid16975
  · exact MergedCutProfiles.Batch424.valid16976
  · exact MergedCutProfiles.Batch424.valid16977
  · exact MergedCutProfiles.Batch424.valid16978
  · exact MergedCutProfiles.Batch424.valid16979
  · exact MergedCutProfiles.Batch424.valid16980
  · exact MergedCutProfiles.Batch424.valid16981
theorem numericValid2682 : retention2682.NumericValid := by decide +kernel
def certificate2682 : RatCutBinCertificate := ⟨⟨retention2682,(291167803739755079/125000000000000000),(216862197802423917/1000000000000000000),(534230152214430151/31250000000000000),(11262259210868497377/31250000000000000),(1085988027079084347/1000000000000000000)⟩,(994905011513720959/1000000000000000000),(36155836862922301/100000000000000000),(33826578887619399/125000000000000000),(27231173905455167/125000000000000000)⟩
theorem valid2682 : certificate2682.Valid := by decide +kernel
theorem sound2682 : certificate2682.Sound := rat_cut_bin_certificate_sound certificate2682 profilesValid2682 numericValid2682 valid2682

def retention2683 : RatCutRetentionCertificate := ⟨(8/125),(129/2000),(10321422141590087545/21015012089040713673),(56120344103450193/6250000000000000),(21/20),(7257644987438791181018533373609717371/7183404045241624704000000000000000000),false,MergedCutProfiles.Batch424.profile16982,(fun _ => MergedCutProfiles.Batch424.profile16982)⟩
theorem profilesValid2683 : retention2683.ProfilesValid := by
  exact MergedCutProfiles.Batch424.valid16982
theorem numericValid2683 : retention2683.NumericValid := by decide +kernel
def certificate2683 : RatCutBinCertificate := ⟨⟨retention2683,(291167803739755079/125000000000000000),(216862197802423917/1000000000000000000),(534230152214430151/31250000000000000),(11262259210868497377/31250000000000000),(979306917664851459/1000000000000000000)⟩,(994905011513720959/1000000000000000000),(74651850262350079/200000000000000000),(129448738411631283/500000000000000000),(109269601579614431/500000000000000000)⟩
theorem valid2683 : certificate2683.Valid := by decide +kernel
theorem sound2683 : certificate2683.Sound := rat_cut_bin_certificate_sound certificate2683 profilesValid2683 numericValid2683 valid2683

def retention2684 : RatCutRetentionCertificate := ⟨(8/125),(129/2000),(3474878787668662807/7005004029680237891),(2064284428318017509/200000000000000000),(21/20),(662974548349443538754140270165953718919/660571017061765602880000000000000000000),false,MergedCutProfiles.Batch424.profile16983,(fun _ => MergedCutProfiles.Batch424.profile16983)⟩
theorem profilesValid2684 : retention2684.ProfilesValid := by
  exact MergedCutProfiles.Batch424.valid16983
theorem numericValid2684 : retention2684.NumericValid := by decide +kernel
def certificate2684 : RatCutBinCertificate := ⟨⟨retention2684,(291167803739755079/125000000000000000),(216862197802423917/1000000000000000000),(534230152214430151/31250000000000000),(11262259210868497377/31250000000000000),(38904427080007039/40000000000000000)⟩,(994905011513720959/1000000000000000000),(93198764763514881/250000000000000000),(64838794527616121/250000000000000000),(220131769536791841/1000000000000000000)⟩
theorem valid2684 : certificate2684.Valid := by decide +kernel
theorem sound2684 : certificate2684.Sound := rat_cut_bin_certificate_sound certificate2684 profilesValid2684 numericValid2684 valid2684

def retention2685 : RatCutRetentionCertificate := ⟨(8/125),(129/2000),(1/2),(10424636363005988421/1000000000000000000),(21/20),(5538110945925330447483624694024134735933/5559806060269860491200000000000000000000),false,MergedCutProfiles.Batch424.profile16984,(fun _ => MergedCutProfiles.Batch424.profile16984)⟩
theorem profilesValid2685 : retention2685.ProfilesValid := by
  exact MergedCutProfiles.Batch424.valid16984
theorem numericValid2685 : retention2685.NumericValid := by decide +kernel
def certificate2685 : RatCutBinCertificate := ⟨⟨retention2685,(291167803739755079/125000000000000000),(216862197802423917/1000000000000000000),(534230152214430151/31250000000000000),(11262259210868497377/31250000000000000),(965069992895135271/1000000000000000000)⟩,(994905011513720959/1000000000000000000),(375505396092072451/1000000000000000000),(3208635943087529/12500000000000000),(108240698945861487/500000000000000000)⟩
theorem valid2685 : certificate2685.Valid := by decide +kernel
theorem sound2685 : certificate2685.Sound := rat_cut_bin_certificate_sound certificate2685 profilesValid2685 numericValid2685 valid2685

def retention2686 : RatCutRetentionCertificate := ⟨(8/125),(129/2000),(9541777903513492544/21015012089040713673),(2425190680841736369/500000000000000000),(21/20),(683563684540517363537272866018189470973/646717514891129698400000000000000000000),false,MergedCutProfiles.Batch424.profile16985,(fun _ => MergedCutProfiles.Batch424.profile16985)⟩
theorem profilesValid2686 : retention2686.ProfilesValid := by
  exact MergedCutProfiles.Batch424.valid16985
theorem numericValid2686 : retention2686.NumericValid := by decide +kernel
def certificate2686 : RatCutBinCertificate := ⟨⟨retention2686,(321775190989755079/125000000000000000),(216862197802423917/1000000000000000000),(534230152214430151/31250000000000000),(11262259210868497377/31250000000000000),(127835307889270593/125000000000000000)⟩,(49718430702073567/50000000000000000),(362298359018549/1600000000000000),(87417100527060899/200000000000000000),(355158384466567823/1000000000000000000)⟩
theorem valid2686 : certificate2686.Valid := by decide +kernel
theorem sound2686 : certificate2686.Sound := rat_cut_bin_certificate_sound certificate2686 profilesValid2686 numericValid2686 valid2686

def retention2687 : RatCutRetentionCertificate := ⟨(8/125),(129/2000),(3478567322765921192/7005004029680237891),(149090279742398321/15625000000000000),1,(9368440531495726946871430366632794487/9541777903513492544000000000000000000),false,MergedCutProfiles.Batch424.profile16986,(fun _ => MergedCutProfiles.Batch424.profile16986)⟩
theorem profilesValid2687 : retention2687.ProfilesValid := by
  exact MergedCutProfiles.Batch424.valid16986
theorem numericValid2687 : retention2687.NumericValid := by decide +kernel
def certificate2687 : RatCutBinCertificate := ⟨⟨retention2687,(321775190989755079/125000000000000000),(216862197802423917/1000000000000000000),(534230152214430151/31250000000000000),(11262259210868497377/31250000000000000),(189835383086063039/200000000000000000)⟩,(49718430702073567/50000000000000000),(243972022075129867/1000000000000000000),(411757260704643759/1000000000000000000),(176676882691832539/500000000000000000)⟩
theorem valid2687 : certificate2687.Valid := by decide +kernel
theorem sound2687 : certificate2687.Sound := rat_cut_bin_certificate_sound certificate2687 profilesValid2687 numericValid2687 valid2687

def certificates : List RatCutBinCertificate := [certificate2676,certificate2677,certificate2678,certificate2679,certificate2680,certificate2681,certificate2682,certificate2683,certificate2684,certificate2685,certificate2686,certificate2687]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2676,List.forall_mem_cons.mpr ⟨sound2677,List.forall_mem_cons.mpr ⟨sound2678,List.forall_mem_cons.mpr ⟨sound2679,List.forall_mem_cons.mpr ⟨sound2680,List.forall_mem_cons.mpr ⟨sound2681,List.forall_mem_cons.mpr ⟨sound2682,List.forall_mem_cons.mpr ⟨sound2683,List.forall_mem_cons.mpr ⟨sound2684,List.forall_mem_cons.mpr ⟨sound2685,List.forall_mem_cons.mpr ⟨sound2686,List.forall_mem_cons.mpr ⟨sound2687,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch223
