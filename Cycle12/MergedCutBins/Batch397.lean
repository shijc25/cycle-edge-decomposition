import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch079
import Cycle12.MergedCutProfiles.Batch080
import Cycle12.MergedCutProfiles.Batch081
import Cycle12.MergedCutProfiles.Batch672
import Cycle12.MergedCutProfiles.Batch673
import Cycle12.MergedCutProfiles.Batch674

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch397

def retention4764 : RatCutRetentionCertificate := ⟨(39/1000),(79/2000),(2274425670194083405/1619956233716477511356),(1155701869/1000000000),(11/4),(380391701897785319/160000000000000000),true,MergedCutProfiles.Batch672.profile26893,![MergedCutProfiles.Batch672.profile26893,MergedCutProfiles.Batch672.profile26889,MergedCutProfiles.Batch672.profile26897,MergedCutProfiles.Batch672.profile26901,MergedCutProfiles.Batch672.profile26902,MergedCutProfiles.Batch672.profile26903,MergedCutProfiles.Batch672.profile26904,MergedCutProfiles.Batch672.profile26905,MergedCutProfiles.Batch672.profile26906,MergedCutProfiles.Batch672.profile26907,MergedCutProfiles.Batch672.profile26908,MergedCutProfiles.Batch672.profile26909,MergedCutProfiles.Batch672.profile26910,MergedCutProfiles.Batch672.profile26911,MergedCutProfiles.Batch672.profile26912,MergedCutProfiles.Batch672.profile26913]⟩
theorem profilesValid4764 : retention4764.ProfilesValid := by
  change ∀ j : Fin 16, (retention4764.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch672.valid26893
  · exact MergedCutProfiles.Batch672.valid26889
  · exact MergedCutProfiles.Batch672.valid26897
  · exact MergedCutProfiles.Batch672.valid26901
  · exact MergedCutProfiles.Batch672.valid26902
  · exact MergedCutProfiles.Batch672.valid26903
  · exact MergedCutProfiles.Batch672.valid26904
  · exact MergedCutProfiles.Batch672.valid26905
  · exact MergedCutProfiles.Batch672.valid26906
  · exact MergedCutProfiles.Batch672.valid26907
  · exact MergedCutProfiles.Batch672.valid26908
  · exact MergedCutProfiles.Batch672.valid26909
  · exact MergedCutProfiles.Batch672.valid26910
  · exact MergedCutProfiles.Batch672.valid26911
  · exact MergedCutProfiles.Batch672.valid26912
  · exact MergedCutProfiles.Batch672.valid26913
theorem numericValid4764 : retention4764.NumericValid := by decide +kernel
def certificate4764 : RatCutBinCertificate := ⟨⟨retention4764,(941217283656937391/500000000000000000),(70986334890534179/1000000000000000000),(11180591871833216343/1000000000000000000),(36321210023289684453751/1000000000000000000),(2344580929171945731/1000000000000000000)⟩,(99995175076605437/100000000000000000),(437668501495930367/1000000000000000000),(40137688863627251/200000000000000000),(67451696711773063/500000000000000000)⟩
theorem valid4764 : certificate4764.Valid := by decide +kernel
theorem sound4764 : certificate4764.Sound := rat_cut_bin_certificate_sound certificate4764 profilesValid4764 numericValid4764 valid4764

def retention4765 : RatCutRetentionCertificate := ⟨(39/1000),(79/2000),(8000000000000000000/404989058429119377839),(454885134038816681/100000000000000000),(5/4),(158096169955493541847589806050648126191/72781621446210668960000000000000000000),true,MergedCutProfiles.Batch672.profile26911,![MergedCutProfiles.Batch672.profile26911,MergedCutProfiles.Batch672.profile26914,MergedCutProfiles.Batch672.profile26915,MergedCutProfiles.Batch672.profile26916,MergedCutProfiles.Batch672.profile26917,MergedCutProfiles.Batch672.profile26918,MergedCutProfiles.Batch672.profile26919,MergedCutProfiles.Batch673.profile26920,MergedCutProfiles.Batch673.profile26921,MergedCutProfiles.Batch673.profile26922,MergedCutProfiles.Batch079.profile3183,MergedCutProfiles.Batch673.profile26923,MergedCutProfiles.Batch673.profile26924,MergedCutProfiles.Batch673.profile26925,MergedCutProfiles.Batch673.profile26926,MergedCutProfiles.Batch080.profile3202]⟩
theorem profilesValid4765 : retention4765.ProfilesValid := by
  change ∀ j : Fin 16, (retention4765.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch672.valid26911
  · exact MergedCutProfiles.Batch672.valid26914
  · exact MergedCutProfiles.Batch672.valid26915
  · exact MergedCutProfiles.Batch672.valid26916
  · exact MergedCutProfiles.Batch672.valid26917
  · exact MergedCutProfiles.Batch672.valid26918
  · exact MergedCutProfiles.Batch672.valid26919
  · exact MergedCutProfiles.Batch673.valid26920
  · exact MergedCutProfiles.Batch673.valid26921
  · exact MergedCutProfiles.Batch673.valid26922
  · exact MergedCutProfiles.Batch079.valid3183
  · exact MergedCutProfiles.Batch673.valid26923
  · exact MergedCutProfiles.Batch673.valid26924
  · exact MergedCutProfiles.Batch673.valid26925
  · exact MergedCutProfiles.Batch673.valid26926
  · exact MergedCutProfiles.Batch080.valid3202
theorem numericValid4765 : retention4765.NumericValid := by decide +kernel
def certificate4765 : RatCutBinCertificate := ⟨⟨retention4765,(941217283656937391/500000000000000000),(70986334890534179/1000000000000000000),(11180591871833216343/1000000000000000000),(36321210023289684453751/1000000000000000000),(2157259427831002443/1000000000000000000)⟩,(99995175076605437/100000000000000000),(295359217261315869/1000000000000000000),(344405573209127999/1000000000000000000),(91191363463864847/200000000000000000)⟩
theorem valid4765 : certificate4765.Valid := by decide +kernel
theorem sound4765 : certificate4765.Sound := rat_cut_bin_certificate_sound certificate4765 profilesValid4765 numericValid4765 valid4765

def retention4766 : RatCutRetentionCertificate := ⟨(39/1000),(79/2000),(1/2),64,1,(255383261865984664571105957823832209879/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch081.profile3241,(fun _ => MergedCutProfiles.Batch081.profile3241)⟩
theorem profilesValid4766 : retention4766.ProfilesValid := by
  exact MergedCutProfiles.Batch081.valid3241
theorem numericValid4766 : retention4766.NumericValid := by decide +kernel
def certificate4766 : RatCutBinCertificate := ⟨⟨retention4766,(941217283656937391/500000000000000000),(70986334890534179/1000000000000000000),(11180591871833216343/1000000000000000000),(36321210023289684453751/1000000000000000000),(246409790440418857/250000000000000000)⟩,(99995175076605437/100000000000000000),(260793259294743243/500000000000000000),(69461582550187991/500000000000000000),(134844751507824831/1000000000000000000)⟩
theorem valid4766 : certificate4766.Valid := by decide +kernel
theorem sound4766 : certificate4766.Sound := rat_cut_bin_certificate_sound certificate4766 profilesValid4766 numericValid4766 valid4766

def retention4767 : RatCutRetentionCertificate := ⟨(39/1000),(79/2000),(8000000000000000000/404989058429119377839),(5984956242818387253/200000000000000000),1,(3236064421959948147796336638844905579/1477766973535404260000000000000000000),false,MergedCutProfiles.Batch673.profile26927,(fun _ => MergedCutProfiles.Batch673.profile26927)⟩
theorem profilesValid4767 : retention4767.ProfilesValid := by
  exact MergedCutProfiles.Batch673.valid26927
theorem numericValid4767 : retention4767.NumericValid := by decide +kernel
def certificate4767 : RatCutBinCertificate := ⟨⟨retention4767,(876976945156937391/500000000000000000),(70986334890534179/1000000000000000000),(11180591871833216343/1000000000000000000),(36321210023289684453751/1000000000000000000),(87147922693514551/40000000000000000)⟩,(499977521951523731/500000000000000000),(21157186199734411/1000000000000000000),(87049439300575611/100000000000000000),(220969329097304687/125000000000000000)⟩
theorem valid4767 : certificate4767.Valid := by decide +kernel
theorem sound4767 : certificate4767.Sound := rat_cut_bin_certificate_sound certificate4767 profilesValid4767 numericValid4767 valid4767

def retention4768 : RatCutRetentionCertificate := ⟨(39/1000),(79/2000),(1/2),64,1,(255383261865984664571105957823832209879/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch081.profile3241,(fun _ => MergedCutProfiles.Batch081.profile3241)⟩
theorem profilesValid4768 : retention4768.ProfilesValid := by
  exact MergedCutProfiles.Batch081.valid3241
theorem numericValid4768 : retention4768.NumericValid := by decide +kernel
def certificate4768 : RatCutBinCertificate := ⟨⟨retention4768,(876976945156937391/500000000000000000),(70986334890534179/1000000000000000000),(11180591871833216343/1000000000000000000),(36321210023289684453751/1000000000000000000),(986454894304956533/1000000000000000000)⟩,(499977521951523731/500000000000000000),(23364028578390659/500000000000000000),(797202951725751839/1000000000000000000),(3872162193837837/5000000000000000)⟩
theorem valid4768 : certificate4768.Valid := by decide +kernel
theorem sound4768 : certificate4768.Sound := rat_cut_bin_certificate_sound certificate4768 profilesValid4768 numericValid4768 valid4768

def retention4769 : RatCutRetentionCertificate := ⟨(39/1000),(79/2000),(687820040146050451/3239912467432955022712),(170252485184665953/250000000000000000),4,(2255857668341882455529570304063463/945847139914810850000000000000000),false,MergedCutProfiles.Batch673.profile26928,(fun _ => MergedCutProfiles.Batch673.profile26928)⟩
theorem profilesValid4769 : retention4769.ProfilesValid := by
  exact MergedCutProfiles.Batch673.valid26928
theorem numericValid4769 : retention4769.NumericValid := by decide +kernel
def certificate4769 : RatCutBinCertificate := ⟨⟨retention4769,(913835745156937391/500000000000000000),(70986334890534179/1000000000000000000),(11180591871833216343/1000000000000000000),(36321210023289684453751/1000000000000000000),(2338596866890357141/1000000000000000000)⟩,(499976577209730651/500000000000000000),(877086303752579567/1000000000000000000),(1970982417440921/250000000000000000),(758929424578937/200000000000000000)⟩
theorem valid4769 : certificate4769.Valid := by decide +kernel
theorem sound4769 : certificate4769.Sound := rat_cut_bin_certificate_sound certificate4769 profilesValid4769 numericValid4769 valid4769

def retention4770 : RatCutRetentionCertificate := ⟨(39/1000),(79/2000),(899812283065909607/3239912467432955022712),(687820040146050451/1000000000000000000),4,(1643129243217482061958791459401494843/687820040146050451000000000000000000),false,MergedCutProfiles.Batch673.profile26929,(fun _ => MergedCutProfiles.Batch673.profile26929)⟩
theorem profilesValid4770 : retention4770.ProfilesValid := by
  exact MergedCutProfiles.Batch673.valid26929
theorem numericValid4770 : retention4770.NumericValid := by decide +kernel
def certificate4770 : RatCutBinCertificate := ⟨⟨retention4770,(913835745156937391/500000000000000000),(70986334890534179/1000000000000000000),(11180591871833216343/1000000000000000000),(36321210023289684453751/1000000000000000000),(234247803764759123/100000000000000000)⟩,(499976577209730651/500000000000000000),(218343178640528981/250000000000000000),(8378839259120381/1000000000000000000),(2022725195468979/500000000000000000)⟩
theorem valid4770 : certificate4770.Valid := by decide +kernel
theorem sound4770 : certificate4770.Sound := rat_cut_bin_certificate_sound certificate4770 profilesValid4770 numericValid4770 valid4770

def retention4771 : RatCutRetentionCertificate := ⟨(39/1000),(79/2000),(3258932042676262685/1619956233716477511356),(899812283065909607/1000000000000000000),(18/5),(215325381291069937808700632543417134679/89981228306590960700000000000000000000),false,MergedCutProfiles.Batch673.profile26930,(fun _ => MergedCutProfiles.Batch673.profile26930)⟩
theorem profilesValid4771 : retention4771.ProfilesValid := by
  exact MergedCutProfiles.Batch673.valid26930
theorem numericValid4771 : retention4771.NumericValid := by decide +kernel
def certificate4771 : RatCutBinCertificate := ⟨⟨retention4771,(913835745156937391/500000000000000000),(70986334890534179/1000000000000000000),(11180591871833216343/1000000000000000000),(36321210023289684453751/1000000000000000000),(1175614447171071869/500000000000000000)⟩,(499976577209730651/500000000000000000),(817066822434015537/1000000000000000000),(17857574409467251/1000000000000000000),(4852810845513241/500000000000000000)⟩
theorem valid4771 : certificate4771.Valid := by decide +kernel
theorem sound4771 : certificate4771.Sound := rat_cut_bin_certificate_sound certificate4771 profilesValid4771 numericValid4771 valid4771

def retention4772 : RatCutRetentionCertificate := ⟨(39/1000),(79/2000),(1/40),(651786408535252537/100000000000000000),(13/10),(11463898709835773953312615308775237251/5214291268282020296000000000000000000),false,MergedCutProfiles.Batch673.profile26931,(fun _ => MergedCutProfiles.Batch673.profile26931)⟩
theorem profilesValid4772 : retention4772.ProfilesValid := by
  exact MergedCutProfiles.Batch673.valid26931
theorem numericValid4772 : retention4772.NumericValid := by decide +kernel
def certificate4772 : RatCutBinCertificate := ⟨⟨retention4772,(913835745156937391/500000000000000000),(70986334890534179/1000000000000000000),(11180591871833216343/1000000000000000000),(36321210023289684453751/1000000000000000000),(2183468358616874357/1000000000000000000)⟩,(499976577209730651/500000000000000000),(720067452786994807/1000000000000000000),(43454916422867391/1000000000000000000),(6090922449013171/100000000000000000)⟩
theorem valid4772 : certificate4772.Valid := by decide +kernel
theorem sound4772 : certificate4772.Sound := rat_cut_bin_certificate_sound certificate4772 profilesValid4772 numericValid4772 valid4772

def retention4773 : RatCutRetentionCertificate := ⟨(79/2000),(1/25),(19267293473163328/98467221350285359993),(580821184404415649/1000000000000000000),4,(64933367964333868079150378786452749/29041059220220782450000000000000000),true,MergedCutProfiles.Batch673.profile26932,![MergedCutProfiles.Batch673.profile26932,MergedCutProfiles.Batch673.profile26933,MergedCutProfiles.Batch673.profile26934,MergedCutProfiles.Batch673.profile26935,MergedCutProfiles.Batch673.profile26936,MergedCutProfiles.Batch673.profile26937,MergedCutProfiles.Batch673.profile26938,MergedCutProfiles.Batch673.profile26939,MergedCutProfiles.Batch673.profile26940,MergedCutProfiles.Batch673.profile26941,MergedCutProfiles.Batch673.profile26942,MergedCutProfiles.Batch673.profile26943,MergedCutProfiles.Batch673.profile26944,MergedCutProfiles.Batch673.profile26945,MergedCutProfiles.Batch673.profile26946,MergedCutProfiles.Batch673.profile26947]⟩
theorem profilesValid4773 : retention4773.ProfilesValid := by
  change ∀ j : Fin 16, (retention4773.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch673.valid26932
  · exact MergedCutProfiles.Batch673.valid26933
  · exact MergedCutProfiles.Batch673.valid26934
  · exact MergedCutProfiles.Batch673.valid26935
  · exact MergedCutProfiles.Batch673.valid26936
  · exact MergedCutProfiles.Batch673.valid26937
  · exact MergedCutProfiles.Batch673.valid26938
  · exact MergedCutProfiles.Batch673.valid26939
  · exact MergedCutProfiles.Batch673.valid26940
  · exact MergedCutProfiles.Batch673.valid26941
  · exact MergedCutProfiles.Batch673.valid26942
  · exact MergedCutProfiles.Batch673.valid26943
  · exact MergedCutProfiles.Batch673.valid26944
  · exact MergedCutProfiles.Batch673.valid26945
  · exact MergedCutProfiles.Batch673.valid26946
  · exact MergedCutProfiles.Batch673.valid26947
theorem numericValid4773 : retention4773.NumericValid := by decide +kernel
def certificate4773 : RatCutBinCertificate := ⟨⟨retention4773,(1885537524495224577/1000000000000000000),(1140020255178431/15625000000000000),(5633066575666683359/500000000000000000),(35594456451166953387459/1000000000000000000),(1093535870617505993/500000000000000000)⟩,(249987696843208519/250000000000000000),(352952709686006049/500000000000000000),(24123032171811493/500000000000000000),(10676319725557/500000000000000)⟩
theorem valid4773 : certificate4773.Valid := by decide +kernel
theorem sound4773 : certificate4773.Sound := rat_cut_bin_certificate_sound certificate4773 profilesValid4773 numericValid4773 valid4773

def retention4774 : RatCutRetentionCertificate := ⟨(79/2000),(1/25),(36162913781250000/98467221350285359993),(301051460518177/488281250000000),4,(14187708784654525185724355395889223/6165533911412264960000000000000000),true,MergedCutProfiles.Batch673.profile26948,![MergedCutProfiles.Batch673.profile26948,MergedCutProfiles.Batch673.profile26949,MergedCutProfiles.Batch673.profile26936,MergedCutProfiles.Batch673.profile26950,MergedCutProfiles.Batch673.profile26940,MergedCutProfiles.Batch673.profile26943,MergedCutProfiles.Batch673.profile26944,MergedCutProfiles.Batch673.profile26946,MergedCutProfiles.Batch673.profile26951,MergedCutProfiles.Batch673.profile26952,MergedCutProfiles.Batch673.profile26953,MergedCutProfiles.Batch673.profile26954,MergedCutProfiles.Batch673.profile26955,MergedCutProfiles.Batch673.profile26956,MergedCutProfiles.Batch673.profile26957,MergedCutProfiles.Batch673.profile26958]⟩
theorem profilesValid4774 : retention4774.ProfilesValid := by
  change ∀ j : Fin 16, (retention4774.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch673.valid26948
  · exact MergedCutProfiles.Batch673.valid26949
  · exact MergedCutProfiles.Batch673.valid26936
  · exact MergedCutProfiles.Batch673.valid26950
  · exact MergedCutProfiles.Batch673.valid26940
  · exact MergedCutProfiles.Batch673.valid26943
  · exact MergedCutProfiles.Batch673.valid26944
  · exact MergedCutProfiles.Batch673.valid26946
  · exact MergedCutProfiles.Batch673.valid26951
  · exact MergedCutProfiles.Batch673.valid26952
  · exact MergedCutProfiles.Batch673.valid26953
  · exact MergedCutProfiles.Batch673.valid26954
  · exact MergedCutProfiles.Batch673.valid26955
  · exact MergedCutProfiles.Batch673.valid26956
  · exact MergedCutProfiles.Batch673.valid26957
  · exact MergedCutProfiles.Batch673.valid26958
theorem numericValid4774 : retention4774.NumericValid := by decide +kernel
def certificate4774 : RatCutBinCertificate := ⟨⟨retention4774,(1885537524495224577/1000000000000000000),(1140020255178431/15625000000000000),(5633066575666683359/500000000000000000),(35594456451166953387459/1000000000000000000),(2252288005993991431/1000000000000000000)⟩,(249987696843208519/250000000000000000),(131749580010484071/200000000000000000),(66281262234334381/1000000000000000000),(15191108966777063/500000000000000000)⟩
theorem valid4774 : certificate4774.Valid := by decide +kernel
theorem sound4774 : certificate4774.Sound := rat_cut_bin_certificate_sound certificate4774 profilesValid4774 numericValid4774 valid4774

def retention4775 : RatCutRetentionCertificate := ⟨(79/2000),(1/25),(1309200199226407579/787737770802282879944),(1157213241/1000000000),(11/4),(305228793882084030658456952023699991/128579249000000000000000000000000000),true,MergedCutProfiles.Batch673.profile26939,![MergedCutProfiles.Batch673.profile26939,MergedCutProfiles.Batch673.profile26951,MergedCutProfiles.Batch673.profile26956,MergedCutProfiles.Batch673.profile26959,MergedCutProfiles.Batch674.profile26960,MergedCutProfiles.Batch674.profile26961,MergedCutProfiles.Batch674.profile26962,MergedCutProfiles.Batch674.profile26963,MergedCutProfiles.Batch674.profile26964,MergedCutProfiles.Batch674.profile26965,MergedCutProfiles.Batch674.profile26966,MergedCutProfiles.Batch674.profile26967,MergedCutProfiles.Batch674.profile26968,MergedCutProfiles.Batch674.profile26969,MergedCutProfiles.Batch674.profile26970,MergedCutProfiles.Batch674.profile26971]⟩
theorem profilesValid4775 : retention4775.ProfilesValid := by
  change ∀ j : Fin 16, (retention4775.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch673.valid26939
  · exact MergedCutProfiles.Batch673.valid26951
  · exact MergedCutProfiles.Batch673.valid26956
  · exact MergedCutProfiles.Batch673.valid26959
  · exact MergedCutProfiles.Batch674.valid26960
  · exact MergedCutProfiles.Batch674.valid26961
  · exact MergedCutProfiles.Batch674.valid26962
  · exact MergedCutProfiles.Batch674.valid26963
  · exact MergedCutProfiles.Batch674.valid26964
  · exact MergedCutProfiles.Batch674.valid26965
  · exact MergedCutProfiles.Batch674.valid26966
  · exact MergedCutProfiles.Batch674.valid26967
  · exact MergedCutProfiles.Batch674.valid26968
  · exact MergedCutProfiles.Batch674.valid26969
  · exact MergedCutProfiles.Batch674.valid26970
  · exact MergedCutProfiles.Batch674.valid26971
theorem numericValid4775 : retention4775.NumericValid := by decide +kernel
def certificate4775 : RatCutBinCertificate := ⟨⟨retention4775,(1885537524495224577/1000000000000000000),(1140020255178431/15625000000000000),(5633066575666683359/500000000000000000),(35594456451166953387459/1000000000000000000),(292534617855777533/125000000000000000)⟩,(249987696843208519/250000000000000000),(438704931115764863/1000000000000000000),(49958322264010909/250000000000000000),(134170909350273483/1000000000000000000)⟩
theorem valid4775 : certificate4775.Valid := by decide +kernel
theorem sound4775 : certificate4775.Sound := rat_cut_bin_certificate_sound certificate4775 profilesValid4775 numericValid4775 valid4775

def certificates : List RatCutBinCertificate := [certificate4764,certificate4765,certificate4766,certificate4767,certificate4768,certificate4769,certificate4770,certificate4771,certificate4772,certificate4773,certificate4774,certificate4775]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4764,List.forall_mem_cons.mpr ⟨sound4765,List.forall_mem_cons.mpr ⟨sound4766,List.forall_mem_cons.mpr ⟨sound4767,List.forall_mem_cons.mpr ⟨sound4768,List.forall_mem_cons.mpr ⟨sound4769,List.forall_mem_cons.mpr ⟨sound4770,List.forall_mem_cons.mpr ⟨sound4771,List.forall_mem_cons.mpr ⟨sound4772,List.forall_mem_cons.mpr ⟨sound4773,List.forall_mem_cons.mpr ⟨sound4774,List.forall_mem_cons.mpr ⟨sound4775,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch397
