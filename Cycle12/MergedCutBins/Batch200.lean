import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch372
import Cycle12.MergedCutProfiles.Batch373
import Cycle12.MergedCutProfiles.Batch374

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch200

def retention2400 : RatCutRetentionCertificate := ⟨(6/125),(49/1000),(10740664663930563376/39955790896714637025),(535683924259120101/250000000000000000),(31/20),(472142978997451812549/320000000000000000000),true,MergedCutProfiles.Batch372.profile14891,![MergedCutProfiles.Batch372.profile14891,MergedCutProfiles.Batch372.profile14902,MergedCutProfiles.Batch372.profile14900,MergedCutProfiles.Batch372.profile14903,MergedCutProfiles.Batch372.profile14904,MergedCutProfiles.Batch372.profile14905,MergedCutProfiles.Batch372.profile14906,MergedCutProfiles.Batch372.profile14907,MergedCutProfiles.Batch372.profile14908,MergedCutProfiles.Batch372.profile14909,MergedCutProfiles.Batch372.profile14910,MergedCutProfiles.Batch372.profile14911,MergedCutProfiles.Batch372.profile14912,MergedCutProfiles.Batch372.profile14913,MergedCutProfiles.Batch372.profile14914,MergedCutProfiles.Batch372.profile14915]⟩
theorem profilesValid2400 : retention2400.ProfilesValid := by
  change ∀ j : Fin 16, (retention2400.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch372.valid14891
  · exact MergedCutProfiles.Batch372.valid14902
  · exact MergedCutProfiles.Batch372.valid14900
  · exact MergedCutProfiles.Batch372.valid14903
  · exact MergedCutProfiles.Batch372.valid14904
  · exact MergedCutProfiles.Batch372.valid14905
  · exact MergedCutProfiles.Batch372.valid14906
  · exact MergedCutProfiles.Batch372.valid14907
  · exact MergedCutProfiles.Batch372.valid14908
  · exact MergedCutProfiles.Batch372.valid14909
  · exact MergedCutProfiles.Batch372.valid14910
  · exact MergedCutProfiles.Batch372.valid14911
  · exact MergedCutProfiles.Batch372.valid14912
  · exact MergedCutProfiles.Batch372.valid14913
  · exact MergedCutProfiles.Batch372.valid14914
  · exact MergedCutProfiles.Batch372.valid14915
theorem numericValid2400 : retention2400.NumericValid := by decide +kernel
def certificate2400 : RatCutBinCertificate := ⟨⟨retention2400,(1066424896630771283/500000000000000000),(114392751307786871/1000000000000000000),(6444096312630054391/500000000000000000),(828619419953648943/1600000000000000),(1446102267144331781/1000000000000000000)⟩,(2490824301896659/2500000000000000),(393009058861405301/1000000000000000000),(239949232956547767/1000000000000000000),(174040710509127837/1000000000000000000)⟩
theorem valid2400 : certificate2400.Valid := by decide +kernel
theorem sound2400 : certificate2400.Sound := rat_cut_bin_certificate_sound certificate2400 profilesValid2400 numericValid2400 valid2400

def retention2401 : RatCutRetentionCertificate := ⟨(6/125),(49/1000),(19128056107584196262/39955790896714637025),(671291541495660211/62500000000000000),(21/20),(9956932179863370899194162164580295897/9589879164223717300000000000000000000),false,MergedCutProfiles.Batch372.profile14916,(fun _ => MergedCutProfiles.Batch372.profile14916)⟩
theorem profilesValid2401 : retention2401.ProfilesValid := by
  exact MergedCutProfiles.Batch372.valid14916
theorem numericValid2401 : retention2401.NumericValid := by decide +kernel
def certificate2401 : RatCutBinCertificate := ⟨⟨retention2401,(1066424896630771283/500000000000000000),(114392751307786871/1000000000000000000),(6444096312630054391/500000000000000000),(828619419953648943/1600000000000000),(1018397412522351649/1000000000000000000)⟩,(2490824301896659/2500000000000000),(445518255308156379/1000000000000000000),(19427231382011243/100000000000000000),(43209068438329683/250000000000000000)⟩
theorem valid2401 : certificate2401.Valid := by decide +kernel
theorem sound2401 : certificate2401.Sound := rat_cut_bin_certificate_sound certificate2401 profilesValid2401 numericValid2401 valid2401

def retention2402 : RatCutRetentionCertificate := ⟨(6/125),(49/1000),(1326982125937140403/2663719393114309135),(9564028053792098131/500000000000000000),1,(75900617754698340534035919011065332127/76512224430336785048000000000000000000),false,MergedCutProfiles.Batch372.profile14917,(fun _ => MergedCutProfiles.Batch372.profile14917)⟩
theorem profilesValid2402 : retention2402.ProfilesValid := by
  exact MergedCutProfiles.Batch372.valid14917
theorem numericValid2402 : retention2402.NumericValid := by decide +kernel
def certificate2402 : RatCutBinCertificate := ⟨⟨retention2402,(1066424896630771283/500000000000000000),(114392751307786871/1000000000000000000),(6444096312630054391/500000000000000000),(828619419953648943/1600000000000000),(973075496523988347/1000000000000000000)⟩,(2490824301896659/2500000000000000),(453397106963628057/1000000000000000000),(23496432692512859/125000000000000000),(173398456956545777/1000000000000000000)⟩
theorem valid2402 : certificate2402.Valid := by decide +kernel
theorem sound2402 : certificate2402.Sound := rat_cut_bin_certificate_sound certificate2402 profilesValid2402 numericValid2402 valid2402

def retention2403 : RatCutRetentionCertificate := ⟨(6/125),(49/1000),(1/2),(3980946377811421209/200000000000000000),1,(24605868747676335887592234250690681/24880914861321382556250000000000000),false,MergedCutProfiles.Batch372.profile14918,(fun _ => MergedCutProfiles.Batch372.profile14918)⟩
theorem profilesValid2403 : retention2403.ProfilesValid := by
  exact MergedCutProfiles.Batch372.valid14918
theorem numericValid2403 : retention2403.NumericValid := by decide +kernel
def certificate2403 : RatCutBinCertificate := ⟨⟨retention2403,(1066424896630771283/500000000000000000),(114392751307786871/1000000000000000000),(6444096312630054391/500000000000000000),(828619419953648943/1600000000000000),(970014584592710431/1000000000000000000)⟩,(2490824301896659/2500000000000000),(113545656372035611/250000000000000000),(11709425818436881/62500000000000000),(172634321009767631/1000000000000000000)⟩
theorem valid2403 : certificate2403.Valid := by decide +kernel
theorem sound2403 : certificate2403.Sound := rat_cut_bin_certificate_sound certificate2403 profilesValid2403 numericValid2403 valid2403

def retention2404 : RatCutRetentionCertificate := ⟨(6/125),(49/1000),(17766293219199023827/39955790896714637025),(2773103617053132697/500000000000000000),(21/20),(2399844794987533513931874482848994778671/2218482893642506157600000000000000000000),false,MergedCutProfiles.Batch372.profile14919,(fun _ => MergedCutProfiles.Batch372.profile14919)⟩
theorem profilesValid2404 : retention2404.ProfilesValid := by
  exact MergedCutProfiles.Batch372.valid14919
theorem numericValid2404 : retention2404.NumericValid := by decide +kernel
def certificate2404 : RatCutBinCertificate := ⟨⟨retention2404,(1206400618630771283/500000000000000000),(114392751307786871/1000000000000000000),(6444096312630054391/500000000000000000),(828619419953648943/1600000000000000),(1059263298516870943/1000000000000000000)⟩,(497923862863976119/500000000000000000),(56215337492526201/250000000000000000),(439424317001597541/1000000000000000000),(376158010813635651/1000000000000000000)⟩
theorem valid2404 : certificate2404.Valid := by decide +kernel
theorem sound2404 : certificate2404.Sound := rat_cut_bin_certificate_sound certificate2404 profilesValid2404 numericValid2404 valid2404

def retention2405 : RatCutRetentionCertificate := ⟨(6/125),(49/1000),(19821290982234999367/39955790896714637025),(17766293219199023827/1000000000000000000),1,(70714221066537965077371501896434615467/71065172876796095308000000000000000000),false,MergedCutProfiles.Batch373.profile14920,(fun _ => MergedCutProfiles.Batch373.profile14920)⟩
theorem profilesValid2405 : retention2405.ProfilesValid := by
  exact MergedCutProfiles.Batch373.valid14920
theorem numericValid2405 : retention2405.NumericValid := by decide +kernel
def certificate2405 : RatCutBinCertificate := ⟨⟨retention2405,(1206400618630771283/500000000000000000),(114392751307786871/1000000000000000000),(6444096312630054391/500000000000000000),(828619419953648943/1600000000000000),(121705724093037551/125000000000000000)⟩,(497923862863976119/500000000000000000),(244634524231793873/1000000000000000000),(51353152211770811/125000000000000000),(188798972664033647/500000000000000000)⟩
theorem valid2405 : certificate2405.Valid := by decide +kernel
theorem sound2405 : certificate2405.Sound := rat_cut_bin_certificate_sound certificate2405 profilesValid2405 numericValid2405 valid2405

def retention2406 : RatCutRetentionCertificate := ⟨(6/125),(49/1000),(1/2),(19821290982234999367/1000000000000000000),1,(122507032790765216715997536209761719/123883068638968746043750000000000000),false,MergedCutProfiles.Batch372.profile14918,(fun _ => MergedCutProfiles.Batch372.profile14918)⟩
theorem profilesValid2406 : retention2406.ProfilesValid := by
  exact MergedCutProfiles.Batch372.valid14918
theorem numericValid2406 : retention2406.NumericValid := by decide +kernel
def certificate2406 : RatCutBinCertificate := ⟨⟨retention2406,(1206400618630771283/500000000000000000),(114392751307786871/1000000000000000000),(6444096312630054391/500000000000000000),(828619419953648943/1600000000000000),(483738366403964311/500000000000000000)⟩,(497923862863976119/500000000000000000),(61548605563617367/250000000000000000),(102159410762706993/250000000000000000),(93836092817130061/250000000000000000)⟩
theorem valid2406 : certificate2406.Valid := by decide +kernel
theorem sound2406 : certificate2406.Sound := rat_cut_bin_certificate_sound certificate2406 profilesValid2406 numericValid2406 valid2406

def retention2407 : RatCutRetentionCertificate := ⟨(49/1000),(1/20),(837724156137705777/38155106028494393599),(829429857562084927/1000000000000000000),(63/20),(2804387828077239620447/1280000000000000000000),true,MergedCutProfiles.Batch373.profile14921,![MergedCutProfiles.Batch373.profile14921,MergedCutProfiles.Batch373.profile14922,MergedCutProfiles.Batch373.profile14923,MergedCutProfiles.Batch373.profile14924,MergedCutProfiles.Batch373.profile14925,MergedCutProfiles.Batch373.profile14926,MergedCutProfiles.Batch373.profile14927,MergedCutProfiles.Batch373.profile14928,MergedCutProfiles.Batch373.profile14929,MergedCutProfiles.Batch373.profile14930,MergedCutProfiles.Batch373.profile14931,MergedCutProfiles.Batch373.profile14932,MergedCutProfiles.Batch373.profile14933,MergedCutProfiles.Batch373.profile14934,MergedCutProfiles.Batch373.profile14935,MergedCutProfiles.Batch373.profile14936]⟩
theorem profilesValid2407 : retention2407.ProfilesValid := by
  change ∀ j : Fin 16, (retention2407.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch373.valid14921
  · exact MergedCutProfiles.Batch373.valid14922
  · exact MergedCutProfiles.Batch373.valid14923
  · exact MergedCutProfiles.Batch373.valid14924
  · exact MergedCutProfiles.Batch373.valid14925
  · exact MergedCutProfiles.Batch373.valid14926
  · exact MergedCutProfiles.Batch373.valid14927
  · exact MergedCutProfiles.Batch373.valid14928
  · exact MergedCutProfiles.Batch373.valid14929
  · exact MergedCutProfiles.Batch373.valid14930
  · exact MergedCutProfiles.Batch373.valid14931
  · exact MergedCutProfiles.Batch373.valid14932
  · exact MergedCutProfiles.Batch373.valid14933
  · exact MergedCutProfiles.Batch373.valid14934
  · exact MergedCutProfiles.Batch373.valid14935
  · exact MergedCutProfiles.Batch373.valid14936
theorem numericValid2407 : retention2407.NumericValid := by decide +kernel
def certificate2407 : RatCutBinCertificate := ⟨⟨retention2407,(428977783796116503/200000000000000000),(59865971199444307/500000000000000000),(13102353185538516663/1000000000000000000),(100556738944896641207/200000000000000000),(2129181018299970399/1000000000000000000)⟩,(996220105590945219/1000000000000000000),(184248155862479069/500000000000000000),(263621344231193441/1000000000000000000),(140934561811172463/1000000000000000000)⟩
theorem valid2407 : certificate2407.Valid := by decide +kernel
theorem sound2407 : certificate2407.Sound := rat_cut_bin_certificate_sound certificate2407 profilesValid2407 numericValid2407 valid2407

def retention2408 : RatCutRetentionCertificate := ⟨(49/1000),(1/20),(953408232956970719/38155106028494393599),(837724156137705777/1000000000000000000),(31/10),(2781963100156443339333/1280000000000000000000),true,MergedCutProfiles.Batch373.profile14937,![MergedCutProfiles.Batch373.profile14937,MergedCutProfiles.Batch373.profile14938,MergedCutProfiles.Batch373.profile14939,MergedCutProfiles.Batch373.profile14940,MergedCutProfiles.Batch373.profile14941,MergedCutProfiles.Batch373.profile14942,MergedCutProfiles.Batch373.profile14928,MergedCutProfiles.Batch373.profile14943,MergedCutProfiles.Batch373.profile14944,MergedCutProfiles.Batch373.profile14945,MergedCutProfiles.Batch373.profile14946,MergedCutProfiles.Batch373.profile14947,MergedCutProfiles.Batch373.profile14948,MergedCutProfiles.Batch373.profile14949,MergedCutProfiles.Batch373.profile14950,MergedCutProfiles.Batch373.profile14951]⟩
theorem profilesValid2408 : retention2408.ProfilesValid := by
  change ∀ j : Fin 16, (retention2408.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch373.valid14937
  · exact MergedCutProfiles.Batch373.valid14938
  · exact MergedCutProfiles.Batch373.valid14939
  · exact MergedCutProfiles.Batch373.valid14940
  · exact MergedCutProfiles.Batch373.valid14941
  · exact MergedCutProfiles.Batch373.valid14942
  · exact MergedCutProfiles.Batch373.valid14928
  · exact MergedCutProfiles.Batch373.valid14943
  · exact MergedCutProfiles.Batch373.valid14944
  · exact MergedCutProfiles.Batch373.valid14945
  · exact MergedCutProfiles.Batch373.valid14946
  · exact MergedCutProfiles.Batch373.valid14947
  · exact MergedCutProfiles.Batch373.valid14948
  · exact MergedCutProfiles.Batch373.valid14949
  · exact MergedCutProfiles.Batch373.valid14950
  · exact MergedCutProfiles.Batch373.valid14951
theorem numericValid2408 : retention2408.NumericValid := by decide +kernel
def certificate2408 : RatCutBinCertificate := ⟨⟨retention2408,(428977783796116503/200000000000000000),(59865971199444307/500000000000000000),(13102353185538516663/1000000000000000000),(100556738944896641207/200000000000000000),(2112641776677118403/1000000000000000000)⟩,(996220105590945219/1000000000000000000),(369677847172229501/1000000000000000000),(131221897948304571/500000000000000000),(17630518109629379/125000000000000000)⟩
theorem valid2408 : certificate2408.Valid := by decide +kernel
theorem sound2408 : certificate2408.Sound := rat_cut_bin_certificate_sound certificate2408 profilesValid2408 numericValid2408 valid2408

def retention2409 : RatCutRetentionCertificate := ⟨(49/1000),(1/20),(1009452513000000000/38155106028494393599),(953408232956970719/1000000000000000000),(11/4),(4305112975435470263/2000000000000000000),true,MergedCutProfiles.Batch373.profile14952,![MergedCutProfiles.Batch373.profile14952,MergedCutProfiles.Batch373.profile14953,MergedCutProfiles.Batch373.profile14954,MergedCutProfiles.Batch373.profile14955,MergedCutProfiles.Batch373.profile14956,MergedCutProfiles.Batch373.profile14957,MergedCutProfiles.Batch373.profile14958,MergedCutProfiles.Batch373.profile14959,MergedCutProfiles.Batch374.profile14960,MergedCutProfiles.Batch374.profile14961,MergedCutProfiles.Batch374.profile14962,MergedCutProfiles.Batch374.profile14963,MergedCutProfiles.Batch374.profile14964,MergedCutProfiles.Batch374.profile14965,MergedCutProfiles.Batch374.profile14966,MergedCutProfiles.Batch374.profile14967]⟩
theorem profilesValid2409 : retention2409.ProfilesValid := by
  change ∀ j : Fin 16, (retention2409.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch373.valid14952
  · exact MergedCutProfiles.Batch373.valid14953
  · exact MergedCutProfiles.Batch373.valid14954
  · exact MergedCutProfiles.Batch373.valid14955
  · exact MergedCutProfiles.Batch373.valid14956
  · exact MergedCutProfiles.Batch373.valid14957
  · exact MergedCutProfiles.Batch373.valid14958
  · exact MergedCutProfiles.Batch373.valid14959
  · exact MergedCutProfiles.Batch374.valid14960
  · exact MergedCutProfiles.Batch374.valid14961
  · exact MergedCutProfiles.Batch374.valid14962
  · exact MergedCutProfiles.Batch374.valid14963
  · exact MergedCutProfiles.Batch374.valid14964
  · exact MergedCutProfiles.Batch374.valid14965
  · exact MergedCutProfiles.Batch374.valid14966
  · exact MergedCutProfiles.Batch374.valid14967
theorem numericValid2409 : retention2409.NumericValid := by decide +kernel
def certificate2409 : RatCutBinCertificate := ⟨⟨retention2409,(428977783796116503/200000000000000000),(59865971199444307/500000000000000000),(13102353185538516663/1000000000000000000),(100556738944896641207/200000000000000000),(1049325208947407183/500000000000000000)⟩,(996220105590945219/1000000000000000000),(175668547457750407/500000000000000000),(140577749844922541/500000000000000000),(165452474782265707/1000000000000000000)⟩
theorem valid2409 : certificate2409.Valid := by decide +kernel
theorem sound2409 : certificate2409.Sound := rat_cut_bin_certificate_sound certificate2409 profilesValid2409 numericValid2409 valid2409

def retention2410 : RatCutRetentionCertificate := ⟨(49/1000),(1/20),(1163339229858486573/38155106028494393599),(1009452513/1000000000),(53/20),(6845884953835272179/3200000000000000000),true,MergedCutProfiles.Batch374.profile14968,![MergedCutProfiles.Batch374.profile14968,MergedCutProfiles.Batch374.profile14969,MergedCutProfiles.Batch374.profile14970,MergedCutProfiles.Batch374.profile14971,MergedCutProfiles.Batch374.profile14972,MergedCutProfiles.Batch374.profile14973,MergedCutProfiles.Batch374.profile14974,MergedCutProfiles.Batch374.profile14975,MergedCutProfiles.Batch373.profile14946,MergedCutProfiles.Batch374.profile14976,MergedCutProfiles.Batch374.profile14977,MergedCutProfiles.Batch374.profile14978,MergedCutProfiles.Batch374.profile14966,MergedCutProfiles.Batch374.profile14979,MergedCutProfiles.Batch374.profile14980,MergedCutProfiles.Batch374.profile14981]⟩
theorem profilesValid2410 : retention2410.ProfilesValid := by
  change ∀ j : Fin 16, (retention2410.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch374.valid14968
  · exact MergedCutProfiles.Batch374.valid14969
  · exact MergedCutProfiles.Batch374.valid14970
  · exact MergedCutProfiles.Batch374.valid14971
  · exact MergedCutProfiles.Batch374.valid14972
  · exact MergedCutProfiles.Batch374.valid14973
  · exact MergedCutProfiles.Batch374.valid14974
  · exact MergedCutProfiles.Batch374.valid14975
  · exact MergedCutProfiles.Batch373.valid14946
  · exact MergedCutProfiles.Batch374.valid14976
  · exact MergedCutProfiles.Batch374.valid14977
  · exact MergedCutProfiles.Batch374.valid14978
  · exact MergedCutProfiles.Batch374.valid14966
  · exact MergedCutProfiles.Batch374.valid14979
  · exact MergedCutProfiles.Batch374.valid14980
  · exact MergedCutProfiles.Batch374.valid14981
theorem numericValid2410 : retention2410.NumericValid := by decide +kernel
def certificate2410 : RatCutBinCertificate := ⟨⟨retention2410,(428977783796116503/200000000000000000),(59865971199444307/500000000000000000),(13102353185538516663/1000000000000000000),(100556738944896641207/200000000000000000),(2087393292752852679/1000000000000000000)⟩,(996220105590945219/1000000000000000000),(172411034510432823/500000000000000000),(144014963592900443/500000000000000000),(174494781395102553/1000000000000000000)⟩
theorem valid2410 : certificate2410.Valid := by decide +kernel
theorem sound2410 : certificate2410.Sound := rat_cut_bin_certificate_sound certificate2410 profilesValid2410 numericValid2410 valid2410

def retention2411 : RatCutRetentionCertificate := ⟨(49/1000),(1/20),(2993897191497295767/38155106028494393599),(1163339229858486573/1000000000000000000),(47/20),(2518621814753951216349/1280000000000000000000),true,MergedCutProfiles.Batch374.profile14982,![MergedCutProfiles.Batch374.profile14982,MergedCutProfiles.Batch374.profile14983,MergedCutProfiles.Batch374.profile14984,MergedCutProfiles.Batch374.profile14985,MergedCutProfiles.Batch374.profile14986,MergedCutProfiles.Batch374.profile14987,MergedCutProfiles.Batch374.profile14988,MergedCutProfiles.Batch374.profile14989,MergedCutProfiles.Batch374.profile14990,MergedCutProfiles.Batch374.profile14991,MergedCutProfiles.Batch374.profile14992,MergedCutProfiles.Batch374.profile14993,MergedCutProfiles.Batch374.profile14994,MergedCutProfiles.Batch374.profile14995,MergedCutProfiles.Batch374.profile14996,MergedCutProfiles.Batch374.profile14997]⟩
theorem profilesValid2411 : retention2411.ProfilesValid := by
  change ∀ j : Fin 16, (retention2411.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch374.valid14982
  · exact MergedCutProfiles.Batch374.valid14983
  · exact MergedCutProfiles.Batch374.valid14984
  · exact MergedCutProfiles.Batch374.valid14985
  · exact MergedCutProfiles.Batch374.valid14986
  · exact MergedCutProfiles.Batch374.valid14987
  · exact MergedCutProfiles.Batch374.valid14988
  · exact MergedCutProfiles.Batch374.valid14989
  · exact MergedCutProfiles.Batch374.valid14990
  · exact MergedCutProfiles.Batch374.valid14991
  · exact MergedCutProfiles.Batch374.valid14992
  · exact MergedCutProfiles.Batch374.valid14993
  · exact MergedCutProfiles.Batch374.valid14994
  · exact MergedCutProfiles.Batch374.valid14995
  · exact MergedCutProfiles.Batch374.valid14996
  · exact MergedCutProfiles.Batch374.valid14997
theorem numericValid2411 : retention2411.NumericValid := by decide +kernel
def certificate2411 : RatCutBinCertificate := ⟨⟨retention2411,(428977783796116503/200000000000000000),(59865971199444307/500000000000000000),(13102353185538516663/1000000000000000000),(100556738944896641207/200000000000000000),(1921608277191524073/1000000000000000000)⟩,(996220105590945219/1000000000000000000),(354014024733862999/1000000000000000000),(278365989080105053/1000000000000000000),(43610520251385997/250000000000000000)⟩
theorem valid2411 : certificate2411.Valid := by decide +kernel
theorem sound2411 : certificate2411.Sound := rat_cut_bin_certificate_sound certificate2411 profilesValid2411 numericValid2411 valid2411

def certificates : List RatCutBinCertificate := [certificate2400,certificate2401,certificate2402,certificate2403,certificate2404,certificate2405,certificate2406,certificate2407,certificate2408,certificate2409,certificate2410,certificate2411]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2400,List.forall_mem_cons.mpr ⟨sound2401,List.forall_mem_cons.mpr ⟨sound2402,List.forall_mem_cons.mpr ⟨sound2403,List.forall_mem_cons.mpr ⟨sound2404,List.forall_mem_cons.mpr ⟨sound2405,List.forall_mem_cons.mpr ⟨sound2406,List.forall_mem_cons.mpr ⟨sound2407,List.forall_mem_cons.mpr ⟨sound2408,List.forall_mem_cons.mpr ⟨sound2409,List.forall_mem_cons.mpr ⟨sound2410,List.forall_mem_cons.mpr ⟨sound2411,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch200
