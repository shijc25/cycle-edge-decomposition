import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch446
import Cycle12.MergedCutProfiles.Batch447
import Cycle12.MergedCutProfiles.Batch448
import Cycle12.MergedCutProfiles.Batch449

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch237

def retention2844 : RatCutRetentionCertificate := ⟨(11/1000),(23/2000),(1677098463490789184/2194444176716075134529),(31809969/25000000),(49/20),(11881822999090218537473358691127912639/5089595040000000000000000000000000000),true,MergedCutProfiles.Batch446.profile17871,![MergedCutProfiles.Batch446.profile17871,MergedCutProfiles.Batch446.profile17874,MergedCutProfiles.Batch447.profile17888,MergedCutProfiles.Batch446.profile17879,MergedCutProfiles.Batch447.profile17882,MergedCutProfiles.Batch447.profile17890,MergedCutProfiles.Batch447.profile17899,MergedCutProfiles.Batch447.profile17893,MergedCutProfiles.Batch447.profile17894,MergedCutProfiles.Batch447.profile17895,MergedCutProfiles.Batch447.profile17896,MergedCutProfiles.Batch447.profile17898,MergedCutProfiles.Batch447.profile17900,MergedCutProfiles.Batch447.profile17901,MergedCutProfiles.Batch447.profile17902,MergedCutProfiles.Batch447.profile17903]⟩
theorem profilesValid2844 : retention2844.ProfilesValid := by
  change ∀ j : Fin 16, (retention2844.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch446.valid17871
  · exact MergedCutProfiles.Batch446.valid17874
  · exact MergedCutProfiles.Batch447.valid17888
  · exact MergedCutProfiles.Batch446.valid17879
  · exact MergedCutProfiles.Batch447.valid17882
  · exact MergedCutProfiles.Batch447.valid17890
  · exact MergedCutProfiles.Batch447.valid17899
  · exact MergedCutProfiles.Batch447.valid17893
  · exact MergedCutProfiles.Batch447.valid17894
  · exact MergedCutProfiles.Batch447.valid17895
  · exact MergedCutProfiles.Batch447.valid17896
  · exact MergedCutProfiles.Batch447.valid17898
  · exact MergedCutProfiles.Batch447.valid17900
  · exact MergedCutProfiles.Batch447.valid17901
  · exact MergedCutProfiles.Batch447.valid17902
  · exact MergedCutProfiles.Batch447.valid17903
theorem numericValid2844 : retention2844.NumericValid := by decide +kernel
def certificate2844 : RatCutBinCertificate := ⟨⟨retention2844,(911303731629063933/500000000000000000),(1349374580489341/250000000000000000),(7618207140337950593/1000000000000000000),(8377854801191924745717/500000000000000000),(2331368373349556387/1000000000000000000)⟩,(999891760913355757/1000000000000000000),(354683209470948057/1000000000000000000),(3470897813950563/12500000000000000),(6325277411407277/31250000000000000)⟩
theorem valid2844 : certificate2844.Valid := by decide +kernel
theorem sound2844 : certificate2844.Sound := rat_cut_bin_certificate_sound certificate2844 profilesValid2844 numericValid2844 valid2844

def retention2845 : RatCutRetentionCertificate := ⟨(11/1000),(23/2000),(64000000000000000000/2194444176716075134529),(26204663492043581/15625000000000000),(41/20),(170787895243845054961/80000000000000000000),true,MergedCutProfiles.Batch447.profile17904,![MergedCutProfiles.Batch447.profile17904,MergedCutProfiles.Batch447.profile17905,MergedCutProfiles.Batch447.profile17906,MergedCutProfiles.Batch447.profile17907,MergedCutProfiles.Batch447.profile17908,MergedCutProfiles.Batch447.profile17909,MergedCutProfiles.Batch447.profile17910,MergedCutProfiles.Batch447.profile17911,MergedCutProfiles.Batch447.profile17912,MergedCutProfiles.Batch447.profile17913,MergedCutProfiles.Batch447.profile17914,MergedCutProfiles.Batch447.profile17915,MergedCutProfiles.Batch447.profile17916,MergedCutProfiles.Batch447.profile17917,MergedCutProfiles.Batch447.profile17918,MergedCutProfiles.Batch447.profile17919]⟩
theorem profilesValid2845 : retention2845.ProfilesValid := by
  change ∀ j : Fin 16, (retention2845.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch447.valid17904
  · exact MergedCutProfiles.Batch447.valid17905
  · exact MergedCutProfiles.Batch447.valid17906
  · exact MergedCutProfiles.Batch447.valid17907
  · exact MergedCutProfiles.Batch447.valid17908
  · exact MergedCutProfiles.Batch447.valid17909
  · exact MergedCutProfiles.Batch447.valid17910
  · exact MergedCutProfiles.Batch447.valid17911
  · exact MergedCutProfiles.Batch447.valid17912
  · exact MergedCutProfiles.Batch447.valid17913
  · exact MergedCutProfiles.Batch447.valid17914
  · exact MergedCutProfiles.Batch447.valid17915
  · exact MergedCutProfiles.Batch447.valid17916
  · exact MergedCutProfiles.Batch447.valid17917
  · exact MergedCutProfiles.Batch447.valid17918
  · exact MergedCutProfiles.Batch447.valid17919
theorem numericValid2845 : retention2845.NumericValid := by decide +kernel
def certificate2845 : RatCutBinCertificate := ⟨⟨retention2845,(911303731629063933/500000000000000000),(1349374580489341/250000000000000000),(7618207140337950593/1000000000000000000),(8377854801191924745717/500000000000000000),(106610074517998637/50000000000000000)⟩,(999891760913355757/1000000000000000000),(341900376683459193/1000000000000000000),(291152568246786247/1000000000000000000),(232464129872175487/1000000000000000000)⟩
theorem valid2845 : certificate2845.Valid := by decide +kernel
theorem sound2845 : certificate2845.Sound := rat_cut_bin_certificate_sound certificate2845 profilesValid2845 numericValid2845 valid2845

def retention2846 : RatCutRetentionCertificate := ⟨(11/1000),(23/2000),(1/2),64,1,(255369345032327503311332944852825472151/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch448.profile17920,(fun _ => MergedCutProfiles.Batch448.profile17920)⟩
theorem profilesValid2846 : retention2846.ProfilesValid := by
  exact MergedCutProfiles.Batch448.valid17920
theorem numericValid2846 : retention2846.NumericValid := by decide +kernel
def certificate2846 : RatCutBinCertificate := ⟨⟨retention2846,(911303731629063933/500000000000000000),(1349374580489341/250000000000000000),(7618207140337950593/1000000000000000000),(8377854801191924745717/500000000000000000),(996245186982097789/1000000000000000000)⟩,(999891760913355757/1000000000000000000),(6732674643144751/15625000000000000),(206341149702249937/1000000000000000000),(202393414287230683/1000000000000000000)⟩
theorem valid2846 : certificate2846.Valid := by decide +kernel
theorem sound2846 : certificate2846.Sound := rat_cut_bin_certificate_sound certificate2846 profilesValid2846 numericValid2846 valid2846

def retention2847 : RatCutRetentionCertificate := ⟨(11/1000),(23/2000),(64000000000000000000/2194444176716075134529),(79847643337581981/10000000000000000),1,(4008077100882959405576220384286620851/1996191083439549525000000000000000000),false,MergedCutProfiles.Batch448.profile17921,(fun _ => MergedCutProfiles.Batch448.profile17921)⟩
theorem profilesValid2847 : retention2847.ProfilesValid := by
  exact MergedCutProfiles.Batch448.valid17921
theorem numericValid2847 : retention2847.NumericValid := by decide +kernel
def certificate2847 : RatCutBinCertificate := ⟨⟨retention2847,(984715784629063933/500000000000000000),(1349374580489341/250000000000000000),(7618207140337950593/1000000000000000000),(8377854801191924745717/500000000000000000),(401293419748115703/200000000000000000)⟩,(3124634504604373/3125000000000000),(71736169989457577/1000000000000000000),(732485257942358589/1000000000000000000),(1174412348641638401/1000000000000000000)⟩
theorem valid2847 : certificate2847.Valid := by decide +kernel
theorem sound2847 : certificate2847.Sound := rat_cut_bin_certificate_sound certificate2847 profilesValid2847 numericValid2847 valid2847

def retention2848 : RatCutRetentionCertificate := ⟨(11/1000),(23/2000),(1/2),64,1,(255369345032327503311332944852825472151/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch448.profile17920,(fun _ => MergedCutProfiles.Batch448.profile17920)⟩
theorem profilesValid2848 : retention2848.ProfilesValid := by
  exact MergedCutProfiles.Batch448.valid17920
theorem numericValid2848 : retention2848.NumericValid := by decide +kernel
def certificate2848 : RatCutBinCertificate := ⟨⟨retention2848,(984715784629063933/500000000000000000),(1349374580489341/250000000000000000),(7618207140337950593/1000000000000000000),(8377854801191924745717/500000000000000000),(199228232426033533/200000000000000000)⟩,(3124634504604373/3125000000000000),(4515432599611177/31250000000000000),(574834041241602207/1000000000000000000),(140943345547156031/250000000000000000)⟩
theorem valid2848 : certificate2848.Valid := by decide +kernel
theorem sound2848 : certificate2848.Sound := rat_cut_bin_certificate_sound certificate2848 profilesValid2848 numericValid2848 valid2848

def retention2849 : RatCutRetentionCertificate := ⟨(23/2000),(3/250),(298084024950029593/1005401235345527703908),(3616467723388961/6250000000000000),4,(10259416444950362699090643426193851/4629078685937870080000000000000000),true,MergedCutProfiles.Batch448.profile17922,![MergedCutProfiles.Batch448.profile17922,MergedCutProfiles.Batch448.profile17923,MergedCutProfiles.Batch448.profile17924,MergedCutProfiles.Batch448.profile17925,MergedCutProfiles.Batch448.profile17926,MergedCutProfiles.Batch448.profile17927,MergedCutProfiles.Batch448.profile17928,MergedCutProfiles.Batch448.profile17929,MergedCutProfiles.Batch448.profile17930,MergedCutProfiles.Batch448.profile17931,MergedCutProfiles.Batch448.profile17932,MergedCutProfiles.Batch448.profile17933,MergedCutProfiles.Batch448.profile17934,MergedCutProfiles.Batch448.profile17935,MergedCutProfiles.Batch448.profile17936,MergedCutProfiles.Batch448.profile17937]⟩
theorem profilesValid2849 : retention2849.ProfilesValid := by
  change ∀ j : Fin 16, (retention2849.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch448.valid17922
  · exact MergedCutProfiles.Batch448.valid17923
  · exact MergedCutProfiles.Batch448.valid17924
  · exact MergedCutProfiles.Batch448.valid17925
  · exact MergedCutProfiles.Batch448.valid17926
  · exact MergedCutProfiles.Batch448.valid17927
  · exact MergedCutProfiles.Batch448.valid17928
  · exact MergedCutProfiles.Batch448.valid17929
  · exact MergedCutProfiles.Batch448.valid17930
  · exact MergedCutProfiles.Batch448.valid17931
  · exact MergedCutProfiles.Batch448.valid17932
  · exact MergedCutProfiles.Batch448.valid17933
  · exact MergedCutProfiles.Batch448.valid17934
  · exact MergedCutProfiles.Batch448.valid17935
  · exact MergedCutProfiles.Batch448.valid17936
  · exact MergedCutProfiles.Batch448.valid17937
theorem numericValid2849 : retention2849.NumericValid := by decide +kernel
def certificate2849 : RatCutBinCertificate := ⟨⟨retention2849,(72983084715625443/40000000000000000),(5886872707676009/1000000000000000000),(3832795568351205139/500000000000000000),(7724553436294398938717/500000000000000000),(69084152658166647/31250000000000000)⟩,(499941267474616661/500000000000000000),(595369947898365939/1000000000000000000),(19177536881362959/200000000000000000),(42773525650315313/1000000000000000000)⟩
theorem valid2849 : certificate2849.Valid := by decide +kernel
theorem sound2849 : certificate2849.Sound := rat_cut_bin_certificate_sound certificate2849 profilesValid2849 numericValid2849 valid2849

def retention2850 : RatCutRetentionCertificate := ⟨(23/2000),(3/250),(159120898125000000/251350308836381925977),(298084024950029593/500000000000000000),4,(1122752533464131549/500000000000000000),true,MergedCutProfiles.Batch448.profile17923,![MergedCutProfiles.Batch448.profile17923,MergedCutProfiles.Batch448.profile17938,MergedCutProfiles.Batch448.profile17939,MergedCutProfiles.Batch448.profile17940,MergedCutProfiles.Batch448.profile17941,MergedCutProfiles.Batch448.profile17934,MergedCutProfiles.Batch448.profile17936,MergedCutProfiles.Batch448.profile17942,MergedCutProfiles.Batch448.profile17943,MergedCutProfiles.Batch448.profile17944,MergedCutProfiles.Batch448.profile17945,MergedCutProfiles.Batch448.profile17946,MergedCutProfiles.Batch448.profile17947,MergedCutProfiles.Batch448.profile17948,MergedCutProfiles.Batch448.profile17949,MergedCutProfiles.Batch448.profile17950]⟩
theorem profilesValid2850 : retention2850.ProfilesValid := by
  change ∀ j : Fin 16, (retention2850.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch448.valid17923
  · exact MergedCutProfiles.Batch448.valid17938
  · exact MergedCutProfiles.Batch448.valid17939
  · exact MergedCutProfiles.Batch448.valid17940
  · exact MergedCutProfiles.Batch448.valid17941
  · exact MergedCutProfiles.Batch448.valid17934
  · exact MergedCutProfiles.Batch448.valid17936
  · exact MergedCutProfiles.Batch448.valid17942
  · exact MergedCutProfiles.Batch448.valid17943
  · exact MergedCutProfiles.Batch448.valid17944
  · exact MergedCutProfiles.Batch448.valid17945
  · exact MergedCutProfiles.Batch448.valid17946
  · exact MergedCutProfiles.Batch448.valid17947
  · exact MergedCutProfiles.Batch448.valid17948
  · exact MergedCutProfiles.Batch448.valid17949
  · exact MergedCutProfiles.Batch448.valid17950
theorem numericValid2850 : retention2850.NumericValid := by decide +kernel
def certificate2850 : RatCutBinCertificate := ⟨⟨retention2850,(72983084715625443/40000000000000000),(5886872707676009/1000000000000000000),(3832795568351205139/500000000000000000),(7724553436294398938717/500000000000000000),(139993765748517809/62500000000000000)⟩,(499941267474616661/500000000000000000),(287939560232178627/500000000000000000),(106317664710289391/1000000000000000000),(24103433379453821/500000000000000000)⟩
theorem valid2850 : certificate2850.Valid := by decide +kernel
theorem sound2850 : certificate2850.Sound := rat_cut_bin_certificate_sound certificate2850 profilesValid2850 numericValid2850 valid2850

def retention2851 : RatCutRetentionCertificate := ⟨(23/2000),(3/250),(1013602509285090013/1005401235345527703908),(254593437/200000000),(49/20),(37283753737785693521/16000000000000000000),true,MergedCutProfiles.Batch448.profile17951,![MergedCutProfiles.Batch448.profile17951,MergedCutProfiles.Batch448.profile17939,MergedCutProfiles.Batch448.profile17941,MergedCutProfiles.Batch448.profile17935,MergedCutProfiles.Batch448.profile17942,MergedCutProfiles.Batch448.profile17952,MergedCutProfiles.Batch448.profile17953,MergedCutProfiles.Batch448.profile17954,MergedCutProfiles.Batch448.profile17948,MergedCutProfiles.Batch448.profile17950,MergedCutProfiles.Batch448.profile17955,MergedCutProfiles.Batch448.profile17956,MergedCutProfiles.Batch448.profile17957,MergedCutProfiles.Batch448.profile17958,MergedCutProfiles.Batch448.profile17959,MergedCutProfiles.Batch449.profile17960]⟩
theorem profilesValid2851 : retention2851.ProfilesValid := by
  change ∀ j : Fin 16, (retention2851.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch448.valid17951
  · exact MergedCutProfiles.Batch448.valid17939
  · exact MergedCutProfiles.Batch448.valid17941
  · exact MergedCutProfiles.Batch448.valid17935
  · exact MergedCutProfiles.Batch448.valid17942
  · exact MergedCutProfiles.Batch448.valid17952
  · exact MergedCutProfiles.Batch448.valid17953
  · exact MergedCutProfiles.Batch448.valid17954
  · exact MergedCutProfiles.Batch448.valid17948
  · exact MergedCutProfiles.Batch448.valid17950
  · exact MergedCutProfiles.Batch448.valid17955
  · exact MergedCutProfiles.Batch448.valid17956
  · exact MergedCutProfiles.Batch448.valid17957
  · exact MergedCutProfiles.Batch448.valid17958
  · exact MergedCutProfiles.Batch448.valid17959
  · exact MergedCutProfiles.Batch449.valid17960
theorem numericValid2851 : retention2851.NumericValid := by decide +kernel
def certificate2851 : RatCutBinCertificate := ⟨⟨retention2851,(72983084715625443/40000000000000000),(5886872707676009/1000000000000000000),(3832795568351205139/500000000000000000),(7724553436294398938717/500000000000000000),(1163400829791319131/500000000000000000)⟩,(499941267474616661/500000000000000000),(178141499023540791/500000000000000000),(69004356341624851/250000000000000000),(200919659091973533/1000000000000000000)⟩
theorem valid2851 : certificate2851.Valid := by decide +kernel
theorem sound2851 : certificate2851.Sound := rat_cut_bin_certificate_sound certificate2851 profilesValid2851 numericValid2851 valid2851

def retention2852 : RatCutRetentionCertificate := ⟨(23/2000),(3/250),(8000000000000000000/251350308836381925977),(1013602509285090013/500000000000000000),(37/20),(1357873533769599358549/640000000000000000000),true,MergedCutProfiles.Batch449.profile17961,![MergedCutProfiles.Batch449.profile17961,MergedCutProfiles.Batch449.profile17962,MergedCutProfiles.Batch449.profile17963,MergedCutProfiles.Batch449.profile17964,MergedCutProfiles.Batch449.profile17965,MergedCutProfiles.Batch449.profile17966,MergedCutProfiles.Batch449.profile17967,MergedCutProfiles.Batch449.profile17968,MergedCutProfiles.Batch449.profile17969,MergedCutProfiles.Batch449.profile17970,MergedCutProfiles.Batch449.profile17971,MergedCutProfiles.Batch449.profile17972,MergedCutProfiles.Batch449.profile17973,MergedCutProfiles.Batch449.profile17974,MergedCutProfiles.Batch449.profile17975,MergedCutProfiles.Batch449.profile17976]⟩
theorem profilesValid2852 : retention2852.ProfilesValid := by
  change ∀ j : Fin 16, (retention2852.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch449.valid17961
  · exact MergedCutProfiles.Batch449.valid17962
  · exact MergedCutProfiles.Batch449.valid17963
  · exact MergedCutProfiles.Batch449.valid17964
  · exact MergedCutProfiles.Batch449.valid17965
  · exact MergedCutProfiles.Batch449.valid17966
  · exact MergedCutProfiles.Batch449.valid17967
  · exact MergedCutProfiles.Batch449.valid17968
  · exact MergedCutProfiles.Batch449.valid17969
  · exact MergedCutProfiles.Batch449.valid17970
  · exact MergedCutProfiles.Batch449.valid17971
  · exact MergedCutProfiles.Batch449.valid17972
  · exact MergedCutProfiles.Batch449.valid17973
  · exact MergedCutProfiles.Batch449.valid17974
  · exact MergedCutProfiles.Batch449.valid17975
  · exact MergedCutProfiles.Batch449.valid17976
theorem numericValid2852 : retention2852.NumericValid := by decide +kernel
def certificate2852 : RatCutBinCertificate := ⟨⟨retention2852,(72983084715625443/40000000000000000),(5886872707676009/1000000000000000000),(3832795568351205139/500000000000000000),(7724553436294398938717/500000000000000000),(2119085169750542593/1000000000000000000)⟩,(499941267474616661/500000000000000000),(19995186340471599/62500000000000000),(157727686309879579/500000000000000000),(276761235730684933/1000000000000000000)⟩
theorem valid2852 : certificate2852.Valid := by decide +kernel
theorem sound2852 : certificate2852.Sound := rat_cut_bin_certificate_sound certificate2852 profilesValid2852 numericValid2852 valid2852

def retention2853 : RatCutRetentionCertificate := ⟨(23/2000),(3/250),(1/2),64,1,(255369421003437005324138814095447425119/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch449.profile17977,(fun _ => MergedCutProfiles.Batch449.profile17977)⟩
theorem profilesValid2853 : retention2853.ProfilesValid := by
  exact MergedCutProfiles.Batch449.valid17977
theorem numericValid2853 : retention2853.NumericValid := by decide +kernel
def certificate2853 : RatCutBinCertificate := ⟨⟨retention2853,(72983084715625443/40000000000000000),(5886872707676009/1000000000000000000),(3832795568351205139/500000000000000000),(7724553436294398938717/500000000000000000),(996135597272238489/1000000000000000000)⟩,(499941267474616661/500000000000000000),(432746827297769897/1000000000000000000),(25597862239846507/125000000000000000),(200841349086665051/1000000000000000000)⟩
theorem valid2853 : certificate2853.Valid := by decide +kernel
theorem sound2853 : certificate2853.Sound := rat_cut_bin_certificate_sound certificate2853 profilesValid2853 numericValid2853 valid2853

def retention2854 : RatCutRetentionCertificate := ⟨(23/2000),(3/250),(8000000000000000000/251350308836381925977),(992348042387879227/125000000000000000),1,(63385304922700221368017373449572769663/31755137356412135264000000000000000000),false,MergedCutProfiles.Batch449.profile17978,(fun _ => MergedCutProfiles.Batch449.profile17978)⟩
theorem profilesValid2854 : retention2854.ProfilesValid := by
  exact MergedCutProfiles.Batch449.valid17978
theorem numericValid2854 : retention2854.NumericValid := by decide +kernel
def certificate2854 : RatCutBinCertificate := ⟨⟨retention2854,(79006695995625443/40000000000000000),(5886872707676009/1000000000000000000),(3832795568351205139/500000000000000000),(7724553436294398938717/500000000000000000),(997273864694939929/500000000000000000)⟩,(999872840041216901/1000000000000000000),(72853812249465731/1000000000000000000),(145947363868789343/200000000000000000),(1163085570121181899/1000000000000000000)⟩
theorem valid2854 : certificate2854.Valid := by decide +kernel
theorem sound2854 : certificate2854.Sound := rat_cut_bin_certificate_sound certificate2854 profilesValid2854 numericValid2854 valid2854

def retention2855 : RatCutRetentionCertificate := ⟨(23/2000),(3/250),(1/2),64,1,(255369421003437005324138814095447425119/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch449.profile17977,(fun _ => MergedCutProfiles.Batch449.profile17977)⟩
theorem profilesValid2855 : retention2855.ProfilesValid := by
  exact MergedCutProfiles.Batch449.valid17977
theorem numericValid2855 : retention2855.NumericValid := by decide +kernel
def certificate2855 : RatCutBinCertificate := ⟨⟨retention2855,(79006695995625443/40000000000000000),(5886872707676009/1000000000000000000),(3832795568351205139/500000000000000000),(7724553436294398938717/500000000000000000),(996019949853713823/1000000000000000000)⟩,(999872840041216901/1000000000000000000),(145891059532402271/1000000000000000000),(572175866957857591/1000000000000000000),(140273337248732757/250000000000000000)⟩
theorem valid2855 : certificate2855.Valid := by decide +kernel
theorem sound2855 : certificate2855.Sound := rat_cut_bin_certificate_sound certificate2855 profilesValid2855 numericValid2855 valid2855

def certificates : List RatCutBinCertificate := [certificate2844,certificate2845,certificate2846,certificate2847,certificate2848,certificate2849,certificate2850,certificate2851,certificate2852,certificate2853,certificate2854,certificate2855]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2844,List.forall_mem_cons.mpr ⟨sound2845,List.forall_mem_cons.mpr ⟨sound2846,List.forall_mem_cons.mpr ⟨sound2847,List.forall_mem_cons.mpr ⟨sound2848,List.forall_mem_cons.mpr ⟨sound2849,List.forall_mem_cons.mpr ⟨sound2850,List.forall_mem_cons.mpr ⟨sound2851,List.forall_mem_cons.mpr ⟨sound2852,List.forall_mem_cons.mpr ⟨sound2853,List.forall_mem_cons.mpr ⟨sound2854,List.forall_mem_cons.mpr ⟨sound2855,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch237
