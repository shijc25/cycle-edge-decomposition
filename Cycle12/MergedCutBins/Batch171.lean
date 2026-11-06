import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch023
import Cycle12.MergedCutProfiles.Batch024
import Cycle12.MergedCutProfiles.Batch025
import Cycle12.MergedCutProfiles.Batch320
import Cycle12.MergedCutProfiles.Batch321

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch171

def retention2052 : RatCutRetentionCertificate := ⟨(9/500),(19/1000),(1/2),64,1,(255370911039032911357452645744173379951/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch023.profile947,(fun _ => MergedCutProfiles.Batch023.profile947)⟩
theorem profilesValid2052 : retention2052.ProfilesValid := by
  exact MergedCutProfiles.Batch023.valid947
theorem numericValid2052 : retention2052.NumericValid := by decide +kernel
def certificate2052 : RatCutBinCertificate := ⟨⟨retention2052,(1892704313882366181/1000000000000000000),(15120529320228081/1000000000000000000),(8325279707217303457/1000000000000000000),(2597771268675315586621/1000000000000000000),(198821011164235653/200000000000000000)⟩,(999281257413213797/1000000000000000000),(142357744366093/320000000000000),(97399281894600669/500000000000000000),(47637523562243797/250000000000000000)⟩
theorem valid2052 : certificate2052.Valid := by decide +kernel
theorem sound2052 : certificate2052.Sound := rat_cut_bin_certificate_sound certificate2052 profilesValid2052 numericValid2052 valid2052

def retention2053 : RatCutRetentionCertificate := ⟨(9/500),(19/1000),(1600000000000000000/7764035718697559137),(1273427206644296749/250000000000000000),(11/10),(24868118340979876306586609305554514013/15917840083053709362500000000000000000),false,MergedCutProfiles.Batch320.profile12805,(fun _ => MergedCutProfiles.Batch320.profile12805)⟩
theorem profilesValid2053 : retention2053.ProfilesValid := by
  exact MergedCutProfiles.Batch320.valid12805
theorem numericValid2053 : retention2053.NumericValid := by decide +kernel
def certificate2053 : RatCutBinCertificate := ⟨⟨retention2053,(2180899965882366181/1000000000000000000),(15120529320228081/1000000000000000000),(8325279707217303457/1000000000000000000),(2597771268675315586621/1000000000000000000),(1557922599292934231/1000000000000000000)⟩,(499585907840160141/500000000000000000),(15502848635676489/100000000000000000),(69385902054309949/125000000000000000),(313493746642694281/500000000000000000)⟩
theorem valid2053 : certificate2053.Valid := by decide +kernel
theorem sound2053 : certificate2053.Sound := rat_cut_bin_certificate_sound certificate2053 profilesValid2053 numericValid2053 valid2053

def retention2054 : RatCutRetentionCertificate := ⟨(9/500),(19/1000),(1/2),64,1,(255370911039032911357452645744173379951/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch023.profile947,(fun _ => MergedCutProfiles.Batch023.profile947)⟩
theorem profilesValid2054 : retention2054.ProfilesValid := by
  exact MergedCutProfiles.Batch023.valid947
theorem numericValid2054 : retention2054.NumericValid := by decide +kernel
def certificate2054 : RatCutBinCertificate := ⟨⟨retention2054,(2180899965882366181/1000000000000000000),(15120529320228081/1000000000000000000),(8325279707217303457/1000000000000000000),(2597771268675315586621/1000000000000000000),(993581629419232209/1000000000000000000)⟩,(499585907840160141/500000000000000000),(243082576487001757/1000000000000000000),(206505683424707909/500000000000000000),(80750016277558307/200000000000000000)⟩
theorem valid2054 : certificate2054.Valid := by decide +kernel
theorem sound2054 : certificate2054.Sound := rat_cut_bin_certificate_sound certificate2054 profilesValid2054 numericValid2054 valid2054

def retention2055 : RatCutRetentionCertificate := ⟨(19/1000),(1/50),(630403369049402484/278951216698446561187),(124832350306812373/200000000000000000),4,(29133660196708223909/12800000000000000000),true,MergedCutProfiles.Batch320.profile12806,![MergedCutProfiles.Batch320.profile12806,MergedCutProfiles.Batch320.profile12807,MergedCutProfiles.Batch024.profile965,MergedCutProfiles.Batch320.profile12808,MergedCutProfiles.Batch320.profile12809,MergedCutProfiles.Batch024.profile966,MergedCutProfiles.Batch320.profile12810,MergedCutProfiles.Batch320.profile12811,MergedCutProfiles.Batch024.profile967,MergedCutProfiles.Batch320.profile12812,MergedCutProfiles.Batch320.profile12813,MergedCutProfiles.Batch024.profile968,MergedCutProfiles.Batch320.profile12814,MergedCutProfiles.Batch320.profile12815,MergedCutProfiles.Batch024.profile969,MergedCutProfiles.Batch320.profile12816]⟩
theorem profilesValid2055 : retention2055.ProfilesValid := by
  change ∀ j : Fin 16, (retention2055.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch320.valid12806
  · exact MergedCutProfiles.Batch320.valid12807
  · exact MergedCutProfiles.Batch024.valid965
  · exact MergedCutProfiles.Batch320.valid12808
  · exact MergedCutProfiles.Batch320.valid12809
  · exact MergedCutProfiles.Batch024.valid966
  · exact MergedCutProfiles.Batch320.valid12810
  · exact MergedCutProfiles.Batch320.valid12811
  · exact MergedCutProfiles.Batch024.valid967
  · exact MergedCutProfiles.Batch320.valid12812
  · exact MergedCutProfiles.Batch320.valid12813
  · exact MergedCutProfiles.Batch024.valid968
  · exact MergedCutProfiles.Batch320.valid12814
  · exact MergedCutProfiles.Batch320.valid12815
  · exact MergedCutProfiles.Batch024.valid969
  · exact MergedCutProfiles.Batch320.valid12816
theorem numericValid2055 : retention2055.NumericValid := by decide +kernel
def certificate2055 : RatCutBinCertificate := ⟨⟨retention2055,(237388975025591963/125000000000000000),(16814618099358171/1000000000000000000),(8434492387731276641/1000000000000000000),(295504222005520176937/125000000000000000),(56523080754111087/25000000000000000)⟩,(99920880191877409/100000000000000000),(16303703496574621/31250000000000000),(34709317524572689/250000000000000000),(31964387144156897/500000000000000000)⟩
theorem valid2055 : certificate2055.Valid := by decide +kernel
theorem sound2055 : certificate2055.Sound := rat_cut_bin_certificate_sound certificate2055 profilesValid2055 numericValid2055 valid2055

def retention2056 : RatCutRetentionCertificate := ⟨(19/1000),(1/50),(1213651935000000000/278951216698446561187),(157600842262350621/250000000000000000),4,(145117986997486916349/64000000000000000000),true,MergedCutProfiles.Batch320.profile12817,![MergedCutProfiles.Batch320.profile12817,MergedCutProfiles.Batch024.profile978,MergedCutProfiles.Batch320.profile12818,MergedCutProfiles.Batch320.profile12819,MergedCutProfiles.Batch024.profile991,MergedCutProfiles.Batch320.profile12820,MergedCutProfiles.Batch320.profile12821,MergedCutProfiles.Batch320.profile12822,MergedCutProfiles.Batch320.profile12823,MergedCutProfiles.Batch024.profile993,MergedCutProfiles.Batch320.profile12824,MergedCutProfiles.Batch023.profile959,MergedCutProfiles.Batch024.profile960,MergedCutProfiles.Batch024.profile961,MergedCutProfiles.Batch024.profile995,MergedCutProfiles.Batch320.profile12825]⟩
theorem profilesValid2056 : retention2056.ProfilesValid := by
  change ∀ j : Fin 16, (retention2056.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch320.valid12817
  · exact MergedCutProfiles.Batch024.valid978
  · exact MergedCutProfiles.Batch320.valid12818
  · exact MergedCutProfiles.Batch320.valid12819
  · exact MergedCutProfiles.Batch024.valid991
  · exact MergedCutProfiles.Batch320.valid12820
  · exact MergedCutProfiles.Batch320.valid12821
  · exact MergedCutProfiles.Batch320.valid12822
  · exact MergedCutProfiles.Batch320.valid12823
  · exact MergedCutProfiles.Batch024.valid993
  · exact MergedCutProfiles.Batch320.valid12824
  · exact MergedCutProfiles.Batch023.valid959
  · exact MergedCutProfiles.Batch024.valid960
  · exact MergedCutProfiles.Batch024.valid961
  · exact MergedCutProfiles.Batch024.valid995
  · exact MergedCutProfiles.Batch320.valid12825
theorem numericValid2056 : retention2056.NumericValid := by decide +kernel
def certificate2056 : RatCutBinCertificate := ⟨⟨retention2056,(237388975025591963/125000000000000000),(16814618099358171/1000000000000000000),(8434492387731276641/1000000000000000000),(295504222005520176937/125000000000000000),(90092982982380373/40000000000000000)⟩,(99920880191877409/100000000000000000),(520446580722509211/1000000000000000000),(139666373579359387/1000000000000000000),(64228064286536749/1000000000000000000)⟩
theorem valid2056 : certificate2056.Valid := by decide +kernel
theorem sound2056 : certificate2056.Sound := rat_cut_bin_certificate_sound certificate2056 profilesValid2056 numericValid2056 valid2056

def retention2057 : RatCutRetentionCertificate := ⟨(19/1000),(1/50),(1574653176044874420/278951216698446561187),(242730387/200000000),(49/20),(4527038978515851159/2000000000000000000),true,MergedCutProfiles.Batch320.profile12826,![MergedCutProfiles.Batch320.profile12826,MergedCutProfiles.Batch320.profile12809,MergedCutProfiles.Batch024.profile979,MergedCutProfiles.Batch320.profile12812,MergedCutProfiles.Batch023.profile954,MergedCutProfiles.Batch024.profile969,MergedCutProfiles.Batch320.profile12823,MergedCutProfiles.Batch320.profile12827,MergedCutProfiles.Batch024.profile981,MergedCutProfiles.Batch024.profile960,MergedCutProfiles.Batch320.profile12828,MergedCutProfiles.Batch024.profile972,MergedCutProfiles.Batch320.profile12829,MergedCutProfiles.Batch320.profile12830,MergedCutProfiles.Batch024.profile984,MergedCutProfiles.Batch320.profile12831]⟩
theorem profilesValid2057 : retention2057.ProfilesValid := by
  change ∀ j : Fin 16, (retention2057.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch320.valid12826
  · exact MergedCutProfiles.Batch320.valid12809
  · exact MergedCutProfiles.Batch024.valid979
  · exact MergedCutProfiles.Batch320.valid12812
  · exact MergedCutProfiles.Batch023.valid954
  · exact MergedCutProfiles.Batch024.valid969
  · exact MergedCutProfiles.Batch320.valid12823
  · exact MergedCutProfiles.Batch320.valid12827
  · exact MergedCutProfiles.Batch024.valid981
  · exact MergedCutProfiles.Batch024.valid960
  · exact MergedCutProfiles.Batch320.valid12828
  · exact MergedCutProfiles.Batch024.valid972
  · exact MergedCutProfiles.Batch320.valid12829
  · exact MergedCutProfiles.Batch320.valid12830
  · exact MergedCutProfiles.Batch024.valid984
  · exact MergedCutProfiles.Batch320.valid12831
theorem numericValid2057 : retention2057.NumericValid := by decide +kernel
def certificate2057 : RatCutBinCertificate := ⟨⟨retention2057,(237388975025591963/125000000000000000),(16814618099358171/1000000000000000000),(8434492387731276641/1000000000000000000),(295504222005520176937/125000000000000000),(450848762042895629/200000000000000000)⟩,(99920880191877409/100000000000000000),(363293030697553479/1000000000000000000),(67213065592263321/250000000000000000),(23592914435869359/125000000000000000)⟩
theorem valid2057 : certificate2057.Valid := by decide +kernel
theorem sound2057 : certificate2057.Sound := rat_cut_bin_certificate_sound certificate2057 profilesValid2057 numericValid2057 valid2057

def retention2058 : RatCutRetentionCertificate := ⟨(19/1000),(1/50),(20721477718600238232/278951216698446561187),(78732658802243721/50000000000000000),(21/10),(258452777133779099123369806084288923/131221098003739535000000000000000000),false,MergedCutProfiles.Batch320.profile12832,(fun _ => MergedCutProfiles.Batch320.profile12832)⟩
theorem profilesValid2058 : retention2058.ProfilesValid := by
  exact MergedCutProfiles.Batch320.valid12832
theorem numericValid2058 : retention2058.NumericValid := by decide +kernel
def certificate2058 : RatCutBinCertificate := ⟨⟨retention2058,(237388975025591963/125000000000000000),(16814618099358171/1000000000000000000),(8434492387731276641/1000000000000000000),(295504222005520176937/125000000000000000),(490411788189170623/250000000000000000)⟩,(99920880191877409/100000000000000000),(372857529378425577/1000000000000000000),(259293547719176367/1000000000000000000),(11793229835972303/62500000000000000)⟩
theorem valid2058 : certificate2058.Valid := by decide +kernel
theorem sound2058 : certificate2058.Sound := rat_cut_bin_certificate_sound certificate2058 profilesValid2058 numericValid2058 valid2058

def retention2059 : RatCutRetentionCertificate := ⟨(19/1000),(1/50),(64000000000000000000/278951216698446561187),(2590184714825029779/125000000000000000),1,(127617250988265393964963915080184402271/82885910874400952928000000000000000000),false,MergedCutProfiles.Batch320.profile12833,(fun _ => MergedCutProfiles.Batch320.profile12833)⟩
theorem profilesValid2059 : retention2059.ProfilesValid := by
  exact MergedCutProfiles.Batch320.valid12833
theorem numericValid2059 : retention2059.NumericValid := by decide +kernel
def certificate2059 : RatCutBinCertificate := ⟨⟨retention2059,(237388975025591963/125000000000000000),(16814618099358171/1000000000000000000),(8434492387731276641/1000000000000000000),(295504222005520176937/125000000000000000),(95992977680571213/62500000000000000)⟩,(99920880191877409/100000000000000000),(299169034502960657/1000000000000000000),(339786244621118623/1000000000000000000),(242733693546370219/500000000000000000)⟩
theorem valid2059 : certificate2059.Valid := by decide +kernel
theorem sound2059 : certificate2059.Sound := rat_cut_bin_certificate_sound certificate2059 profilesValid2059 numericValid2059 valid2059

def retention2060 : RatCutRetentionCertificate := ⟨(19/1000),(1/50),(1/2),64,1,(3990175631981414592578765135707307871/4000000000000000000000000000000000000),false,MergedCutProfiles.Batch025.profile1008,(fun _ => MergedCutProfiles.Batch025.profile1008)⟩
theorem profilesValid2060 : retention2060.ProfilesValid := by
  exact MergedCutProfiles.Batch025.valid1008
theorem numericValid2060 : retention2060.NumericValid := by decide +kernel
def certificate2060 : RatCutBinCertificate := ⟨⟨retention2060,(237388975025591963/125000000000000000),(16814618099358171/1000000000000000000),(8434492387731276641/1000000000000000000),(295504222005520176937/125000000000000000),(993757925184609401/1000000000000000000)⟩,(99920880191877409/100000000000000000),(447158512226473267/1000000000000000000),(192949170634197287/1000000000000000000),(188662342071400371/1000000000000000000)⟩
theorem valid2060 : certificate2060.Valid := by decide +kernel
theorem sound2060 : certificate2060.Sound := rat_cut_bin_certificate_sound certificate2060 profilesValid2060 numericValid2060 valid2060

def retention2061 : RatCutRetentionCertificate := ⟨(19/1000),(1/50),(64000000000000000000/278951216698446561187),(5160810676542461459/1000000000000000000),(11/10),(3128781950665285555776376819110096307039/2064324270616984583600000000000000000000),false,MergedCutProfiles.Batch320.profile12833,(fun _ => MergedCutProfiles.Batch320.profile12833)⟩
theorem profilesValid2061 : retention2061.ProfilesValid := by
  exact MergedCutProfiles.Batch320.valid12833
theorem numericValid2061 : retention2061.NumericValid := by decide +kernel
def certificate2061 : RatCutBinCertificate := ⟨⟨retention2061,(273508955150591963/125000000000000000),(16814618099358171/1000000000000000000),(8434492387731276641/1000000000000000000),(295504222005520176937/125000000000000000),(94427897430560603/62500000000000000)⟩,(999088415287834453/1000000000000000000),(39626092933690649/250000000000000000),(109743602233733509/200000000000000000),(1212500152532537/2000000000000000)⟩
theorem valid2061 : certificate2061.Valid := by decide +kernel
theorem sound2061 : certificate2061.Sound := rat_cut_bin_certificate_sound certificate2061 profilesValid2061 numericValid2061 valid2061

def retention2062 : RatCutRetentionCertificate := ⟨(19/1000),(1/50),(1/2),64,1,(3990175631981414592578765135707307871/4000000000000000000000000000000000000),false,MergedCutProfiles.Batch025.profile1008,(fun _ => MergedCutProfiles.Batch025.profile1008)⟩
theorem profilesValid2062 : retention2062.ProfilesValid := by
  exact MergedCutProfiles.Batch025.valid1008
theorem numericValid2062 : retention2062.NumericValid := by decide +kernel
def certificate2062 : RatCutBinCertificate := ⟨⟨retention2062,(273508955150591963/125000000000000000),(16814618099358171/1000000000000000000),(8434492387731276641/1000000000000000000),(295504222005520176937/125000000000000000),(496590934001543627/500000000000000000)⟩,(999088415287834453/1000000000000000000),(241119739111775033/1000000000000000000),(41579029543925797/100000000000000000),(406271495008416153/1000000000000000000)⟩
theorem valid2062 : certificate2062.Valid := by decide +kernel
theorem sound2062 : certificate2062.Sound := rat_cut_bin_certificate_sound certificate2062 profilesValid2062 numericValid2062 valid2062

def retention2063 : RatCutRetentionCertificate := ⟨(1/50),(21/1000),(321568044656931986/125904482924188692167),(315231883792698741/500000000000000000),4,(73029339353753759861/32000000000000000000),true,MergedCutProfiles.Batch320.profile12834,![MergedCutProfiles.Batch320.profile12834,MergedCutProfiles.Batch320.profile12835,MergedCutProfiles.Batch320.profile12836,MergedCutProfiles.Batch320.profile12837,MergedCutProfiles.Batch320.profile12838,MergedCutProfiles.Batch320.profile12839,MergedCutProfiles.Batch321.profile12840,MergedCutProfiles.Batch321.profile12841,MergedCutProfiles.Batch321.profile12842,MergedCutProfiles.Batch321.profile12843,MergedCutProfiles.Batch025.profile1028,MergedCutProfiles.Batch321.profile12844,MergedCutProfiles.Batch321.profile12845,MergedCutProfiles.Batch321.profile12846,MergedCutProfiles.Batch321.profile12847,MergedCutProfiles.Batch321.profile12848]⟩
theorem profilesValid2063 : retention2063.ProfilesValid := by
  change ∀ j : Fin 16, (retention2063.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch320.valid12834
  · exact MergedCutProfiles.Batch320.valid12835
  · exact MergedCutProfiles.Batch320.valid12836
  · exact MergedCutProfiles.Batch320.valid12837
  · exact MergedCutProfiles.Batch320.valid12838
  · exact MergedCutProfiles.Batch320.valid12839
  · exact MergedCutProfiles.Batch321.valid12840
  · exact MergedCutProfiles.Batch321.valid12841
  · exact MergedCutProfiles.Batch321.valid12842
  · exact MergedCutProfiles.Batch321.valid12843
  · exact MergedCutProfiles.Batch025.valid1028
  · exact MergedCutProfiles.Batch321.valid12844
  · exact MergedCutProfiles.Batch321.valid12845
  · exact MergedCutProfiles.Batch321.valid12846
  · exact MergedCutProfiles.Batch321.valid12847
  · exact MergedCutProfiles.Batch321.valid12848
theorem numericValid2063 : retention2063.NumericValid := by decide +kernel
def certificate2063 : RatCutBinCertificate := ⟨⟨retention2063,(1897335656472775499/1000000000000000000),(1860584005120499/100000000000000000),(8545922877877615579/1000000000000000000),(2162263568793696880991/1000000000000000000),(566410896619858989/250000000000000000)⟩,(499568632545310609/500000000000000000),(4131260935068031/8000000000000000),(142319800887149403/1000000000000000000),(6575991073844609/100000000000000000)⟩
theorem valid2063 : certificate2063.Valid := by decide +kernel
theorem sound2063 : certificate2063.Sound := rat_cut_bin_certificate_sound certificate2063 profilesValid2063 numericValid2063 valid2063

def certificates : List RatCutBinCertificate := [certificate2052,certificate2053,certificate2054,certificate2055,certificate2056,certificate2057,certificate2058,certificate2059,certificate2060,certificate2061,certificate2062,certificate2063]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2052,List.forall_mem_cons.mpr ⟨sound2053,List.forall_mem_cons.mpr ⟨sound2054,List.forall_mem_cons.mpr ⟨sound2055,List.forall_mem_cons.mpr ⟨sound2056,List.forall_mem_cons.mpr ⟨sound2057,List.forall_mem_cons.mpr ⟨sound2058,List.forall_mem_cons.mpr ⟨sound2059,List.forall_mem_cons.mpr ⟨sound2060,List.forall_mem_cons.mpr ⟨sound2061,List.forall_mem_cons.mpr ⟨sound2062,List.forall_mem_cons.mpr ⟨sound2063,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch171
