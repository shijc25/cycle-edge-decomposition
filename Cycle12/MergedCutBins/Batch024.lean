import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch047
import Cycle12.MergedCutProfiles.Batch048
import Cycle12.MergedCutProfiles.Batch049

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch024

def retention288 : RatCutRetentionCertificate := ⟨(31/1000),(4/125),(873846251729481477/51344512704105007463),(368928051175343753/500000000000000000),(71/20),(1414120138169813939281/640000000000000000000),true,MergedCutProfiles.Batch047.profile1892,![MergedCutProfiles.Batch047.profile1892,MergedCutProfiles.Batch047.profile1893,MergedCutProfiles.Batch047.profile1894,MergedCutProfiles.Batch047.profile1895,MergedCutProfiles.Batch047.profile1896,MergedCutProfiles.Batch047.profile1897,MergedCutProfiles.Batch047.profile1898,MergedCutProfiles.Batch047.profile1899,MergedCutProfiles.Batch047.profile1900,MergedCutProfiles.Batch047.profile1901,MergedCutProfiles.Batch047.profile1888,MergedCutProfiles.Batch047.profile1902,MergedCutProfiles.Batch047.profile1903,MergedCutProfiles.Batch047.profile1904,MergedCutProfiles.Batch047.profile1905,MergedCutProfiles.Batch047.profile1906]⟩
theorem profilesValid288 : retention288.ProfilesValid := by
  change ∀ j : Fin 16, (retention288.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch047.valid1892
  · exact MergedCutProfiles.Batch047.valid1893
  · exact MergedCutProfiles.Batch047.valid1894
  · exact MergedCutProfiles.Batch047.valid1895
  · exact MergedCutProfiles.Batch047.valid1896
  · exact MergedCutProfiles.Batch047.valid1897
  · exact MergedCutProfiles.Batch047.valid1898
  · exact MergedCutProfiles.Batch047.valid1899
  · exact MergedCutProfiles.Batch047.valid1900
  · exact MergedCutProfiles.Batch047.valid1901
  · exact MergedCutProfiles.Batch047.valid1888
  · exact MergedCutProfiles.Batch047.valid1902
  · exact MergedCutProfiles.Batch047.valid1903
  · exact MergedCutProfiles.Batch047.valid1904
  · exact MergedCutProfiles.Batch047.valid1905
  · exact MergedCutProfiles.Batch047.valid1906
theorem numericValid288 : retention288.NumericValid := by decide +kernel
def certificate288 : RatCutBinCertificate := ⟨⟨retention288,(2003128889937682127/1000000000000000000),(9018985876591161/200000000000000000),(9936799552501771471/1000000000000000000),(512812006704724266291/1000000000000000000),(2126259947447027/976562500000000)⟩,(249064460592379681/250000000000000000),(10916171864433/25000000000000),(201533787467219057/1000000000000000000),(24929073540215841/250000000000000000)⟩
theorem valid288 : certificate288.Valid := by decide +kernel
theorem sound288 : certificate288.Sound := rat_cut_bin_certificate_sound certificate288 profilesValid288 numericValid288 valid288

def retention289 : RatCutRetentionCertificate := ⟨(31/1000),(4/125),(1005547104000000000/51344512704105007463),(873846251729481477/1000000000000000000),(61/20),(2796298977413586511549/1280000000000000000000),true,MergedCutProfiles.Batch047.profile1907,![MergedCutProfiles.Batch047.profile1907,MergedCutProfiles.Batch047.profile1908,MergedCutProfiles.Batch047.profile1909,MergedCutProfiles.Batch047.profile1910,MergedCutProfiles.Batch047.profile1911,MergedCutProfiles.Batch047.profile1912,MergedCutProfiles.Batch047.profile1913,MergedCutProfiles.Batch047.profile1914,MergedCutProfiles.Batch047.profile1915,MergedCutProfiles.Batch047.profile1916,MergedCutProfiles.Batch047.profile1890,MergedCutProfiles.Batch047.profile1917,MergedCutProfiles.Batch047.profile1905,MergedCutProfiles.Batch047.profile1918,MergedCutProfiles.Batch047.profile1919,MergedCutProfiles.Batch048.profile1920]⟩
theorem profilesValid289 : retention289.ProfilesValid := by
  change ∀ j : Fin 16, (retention289.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch047.valid1907
  · exact MergedCutProfiles.Batch047.valid1908
  · exact MergedCutProfiles.Batch047.valid1909
  · exact MergedCutProfiles.Batch047.valid1910
  · exact MergedCutProfiles.Batch047.valid1911
  · exact MergedCutProfiles.Batch047.valid1912
  · exact MergedCutProfiles.Batch047.valid1913
  · exact MergedCutProfiles.Batch047.valid1914
  · exact MergedCutProfiles.Batch047.valid1915
  · exact MergedCutProfiles.Batch047.valid1916
  · exact MergedCutProfiles.Batch047.valid1890
  · exact MergedCutProfiles.Batch047.valid1917
  · exact MergedCutProfiles.Batch047.valid1905
  · exact MergedCutProfiles.Batch047.valid1918
  · exact MergedCutProfiles.Batch047.valid1919
  · exact MergedCutProfiles.Batch048.valid1920
theorem numericValid289 : retention289.NumericValid := by decide +kernel
def certificate289 : RatCutBinCertificate := ⟨⟨retention289,(2003128889937682127/1000000000000000000),(9018985876591161/200000000000000000),(9936799552501771471/1000000000000000000),(512812006704724266291/1000000000000000000),(431376297825717649/200000000000000000)⟩,(249064460592379681/250000000000000000),(405680744101715417/1000000000000000000),(228317512163714169/1000000000000000000),(12704840299678723/100000000000000000)⟩
theorem valid289 : certificate289.Valid := by decide +kernel
theorem sound289 : certificate289.Sound := rat_cut_bin_certificate_sound certificate289 profilesValid289 numericValid289 valid289

def retention290 : RatCutRetentionCertificate := ⟨(31/1000),(4/125),(1014508370024364893/51344512704105007463),(31423347/31250000),(27/10),(8692781384957171597/4000000000000000000),true,MergedCutProfiles.Batch047.profile1907,![MergedCutProfiles.Batch047.profile1907,MergedCutProfiles.Batch047.profile1908,MergedCutProfiles.Batch047.profile1909,MergedCutProfiles.Batch047.profile1910,MergedCutProfiles.Batch047.profile1911,MergedCutProfiles.Batch047.profile1898,MergedCutProfiles.Batch048.profile1921,MergedCutProfiles.Batch047.profile1886,MergedCutProfiles.Batch048.profile1922,MergedCutProfiles.Batch048.profile1923,MergedCutProfiles.Batch048.profile1924,MergedCutProfiles.Batch047.profile1904,MergedCutProfiles.Batch048.profile1925,MergedCutProfiles.Batch048.profile1926,MergedCutProfiles.Batch048.profile1927,MergedCutProfiles.Batch048.profile1928]⟩
theorem profilesValid290 : retention290.ProfilesValid := by
  change ∀ j : Fin 16, (retention290.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch047.valid1907
  · exact MergedCutProfiles.Batch047.valid1908
  · exact MergedCutProfiles.Batch047.valid1909
  · exact MergedCutProfiles.Batch047.valid1910
  · exact MergedCutProfiles.Batch047.valid1911
  · exact MergedCutProfiles.Batch047.valid1898
  · exact MergedCutProfiles.Batch048.valid1921
  · exact MergedCutProfiles.Batch047.valid1886
  · exact MergedCutProfiles.Batch048.valid1922
  · exact MergedCutProfiles.Batch048.valid1923
  · exact MergedCutProfiles.Batch048.valid1924
  · exact MergedCutProfiles.Batch047.valid1904
  · exact MergedCutProfiles.Batch048.valid1925
  · exact MergedCutProfiles.Batch048.valid1926
  · exact MergedCutProfiles.Batch048.valid1927
  · exact MergedCutProfiles.Batch048.valid1928
theorem numericValid290 : retention290.NumericValid := by decide +kernel
def certificate290 : RatCutBinCertificate := ⟨⟨retention290,(2003128889937682127/1000000000000000000),(9018985876591161/200000000000000000),(9936799552501771471/1000000000000000000),(512812006704724266291/1000000000000000000),(2148650070967797831/1000000000000000000)⟩,(249064460592379681/250000000000000000),(382197442964625739/1000000000000000000),(125097955545476197/500000000000000000),(153307825801531321/1000000000000000000)⟩
theorem valid290 : certificate290.Valid := by decide +kernel
theorem sound290 : certificate290.Sound := rat_cut_bin_certificate_sound certificate290 profilesValid290 numericValid290 valid290

def retention291 : RatCutRetentionCertificate := ⟨(31/1000),(4/125),(1131854875863208379/51344512704105007463),(1014508370024364893/1000000000000000000),(27/10),(2772731698234942460129/1280000000000000000000),true,MergedCutProfiles.Batch048.profile1929,![MergedCutProfiles.Batch048.profile1929,MergedCutProfiles.Batch048.profile1930,MergedCutProfiles.Batch048.profile1931,MergedCutProfiles.Batch048.profile1932,MergedCutProfiles.Batch048.profile1933,MergedCutProfiles.Batch048.profile1934,MergedCutProfiles.Batch048.profile1935,MergedCutProfiles.Batch048.profile1922,MergedCutProfiles.Batch048.profile1936,MergedCutProfiles.Batch047.profile1903,MergedCutProfiles.Batch048.profile1937,MergedCutProfiles.Batch048.profile1938,MergedCutProfiles.Batch048.profile1939,MergedCutProfiles.Batch048.profile1940,MergedCutProfiles.Batch048.profile1941,MergedCutProfiles.Batch048.profile1942]⟩
theorem profilesValid291 : retention291.ProfilesValid := by
  change ∀ j : Fin 16, (retention291.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch048.valid1929
  · exact MergedCutProfiles.Batch048.valid1930
  · exact MergedCutProfiles.Batch048.valid1931
  · exact MergedCutProfiles.Batch048.valid1932
  · exact MergedCutProfiles.Batch048.valid1933
  · exact MergedCutProfiles.Batch048.valid1934
  · exact MergedCutProfiles.Batch048.valid1935
  · exact MergedCutProfiles.Batch048.valid1922
  · exact MergedCutProfiles.Batch048.valid1936
  · exact MergedCutProfiles.Batch047.valid1903
  · exact MergedCutProfiles.Batch048.valid1937
  · exact MergedCutProfiles.Batch048.valid1938
  · exact MergedCutProfiles.Batch048.valid1939
  · exact MergedCutProfiles.Batch048.valid1940
  · exact MergedCutProfiles.Batch048.valid1941
  · exact MergedCutProfiles.Batch048.valid1942
theorem numericValid291 : retention291.NumericValid := by decide +kernel
def certificate291 : RatCutBinCertificate := ⟨⟨retention291,(2003128889937682127/1000000000000000000),(9018985876591161/200000000000000000),(9936799552501771471/1000000000000000000),(512812006704724266291/1000000000000000000),(2141651370996716931/1000000000000000000)⟩,(249064460592379681/250000000000000000),(190987112050885857/500000000000000000),(31301332130421883/125000000000000000),(153359454920058209/1000000000000000000)⟩
theorem valid291 : certificate291.Valid := by decide +kernel
theorem sound291 : certificate291.Sound := rat_cut_bin_certificate_sound certificate291 profilesValid291 numericValid291 valid291

def retention292 : RatCutRetentionCertificate := ⟨(31/1000),(4/125),(2884030717080300666/51344512704105007463),(1131854875863208379/1000000000000000000),(49/20),(649762805474178994717/320000000000000000000),true,MergedCutProfiles.Batch048.profile1943,![MergedCutProfiles.Batch048.profile1943,MergedCutProfiles.Batch048.profile1944,MergedCutProfiles.Batch048.profile1945,MergedCutProfiles.Batch048.profile1946,MergedCutProfiles.Batch048.profile1947,MergedCutProfiles.Batch048.profile1948,MergedCutProfiles.Batch048.profile1949,MergedCutProfiles.Batch048.profile1950,MergedCutProfiles.Batch048.profile1951,MergedCutProfiles.Batch048.profile1952,MergedCutProfiles.Batch048.profile1953,MergedCutProfiles.Batch048.profile1954,MergedCutProfiles.Batch048.profile1955,MergedCutProfiles.Batch048.profile1956,MergedCutProfiles.Batch048.profile1957,MergedCutProfiles.Batch048.profile1958]⟩
theorem profilesValid292 : retention292.ProfilesValid := by
  change ∀ j : Fin 16, (retention292.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch048.valid1943
  · exact MergedCutProfiles.Batch048.valid1944
  · exact MergedCutProfiles.Batch048.valid1945
  · exact MergedCutProfiles.Batch048.valid1946
  · exact MergedCutProfiles.Batch048.valid1947
  · exact MergedCutProfiles.Batch048.valid1948
  · exact MergedCutProfiles.Batch048.valid1949
  · exact MergedCutProfiles.Batch048.valid1950
  · exact MergedCutProfiles.Batch048.valid1951
  · exact MergedCutProfiles.Batch048.valid1952
  · exact MergedCutProfiles.Batch048.valid1953
  · exact MergedCutProfiles.Batch048.valid1954
  · exact MergedCutProfiles.Batch048.valid1955
  · exact MergedCutProfiles.Batch048.valid1956
  · exact MergedCutProfiles.Batch048.valid1957
  · exact MergedCutProfiles.Batch048.valid1958
theorem numericValid292 : retention292.NumericValid := by decide +kernel
def certificate292 : RatCutBinCertificate := ⟨⟨retention292,(2003128889937682127/1000000000000000000),(9018985876591161/200000000000000000),(9936799552501771471/1000000000000000000),(512812006704724266291/1000000000000000000),(80329448704562559/40000000000000000)⟩,(249064460592379681/250000000000000000),(97271387403032943/250000000000000000),(243632930518159921/1000000000000000000),(15347626062007253/100000000000000000)⟩
theorem valid292 : certificate292.Valid := by decide +kernel
theorem sound292 : certificate292.Sound := rat_cut_bin_certificate_sound certificate292 profilesValid292 numericValid292 valid292

def retention293 : RatCutRetentionCertificate := ⟨(31/1000),(4/125),(16783519641791992158/51344512704105007463),(1442015358540150333/500000000000000000),(27/20),(1553477198848895311434595588025804730479/1153612286832120266400000000000000000000),false,MergedCutProfiles.Batch048.profile1959,(fun _ => MergedCutProfiles.Batch048.profile1959)⟩
theorem profilesValid293 : retention293.ProfilesValid := by
  exact MergedCutProfiles.Batch048.valid1959
theorem numericValid293 : retention293.NumericValid := by decide +kernel
def certificate293 : RatCutBinCertificate := ⟨⟨retention293,(2003128889937682127/1000000000000000000),(9018985876591161/200000000000000000),(9936799552501771471/1000000000000000000),(512812006704724266291/1000000000000000000),(266869465529226807/200000000000000000)⟩,(249064460592379681/250000000000000000),(220600585601639511/500000000000000000),(197783685805906659/1000000000000000000),(155261909265358589/1000000000000000000)⟩
theorem valid293 : certificate293.Valid := by decide +kernel
theorem sound293 : certificate293.Sound := rat_cut_bin_certificate_sound certificate293 profilesValid293 numericValid293 valid293

def retention294 : RatCutRetentionCertificate := ⟨(31/1000),(4/125),(24988373716629664885/51344512704105007463),(8391759820895996079/500000000000000000),1,(66377016526466058087078045681860423/65560623600749969367187500000000000),false,MergedCutProfiles.Batch049.profile1960,(fun _ => MergedCutProfiles.Batch049.profile1960)⟩
theorem profilesValid294 : retention294.ProfilesValid := by
  exact MergedCutProfiles.Batch049.valid1960
theorem numericValid294 : retention294.NumericValid := by decide +kernel
def certificate294 : RatCutBinCertificate := ⟨⟨retention294,(2003128889937682127/1000000000000000000),(9018985876591161/200000000000000000),(9936799552501771471/1000000000000000000),(512812006704724266291/1000000000000000000),(1003361892832732397/1000000000000000000)⟩,(249064460592379681/250000000000000000),(242010573215779269/500000000000000000),(82380053051706513/500000000000000000),(77693505229154167/500000000000000000)⟩
theorem valid294 : certificate294.Valid := by decide +kernel
theorem sound294 : certificate294.Sound := rat_cut_bin_certificate_sound certificate294 profilesValid294 numericValid294 valid294

def retention295 : RatCutRetentionCertificate := ⟨(31/1000),(4/125),(25490640028333921150/51344512704105007463),(4997674743325932977/200000000000000000),1,(199586226630677125203895434085714653/199906989733037319080000000000000000),false,MergedCutProfiles.Batch049.profile1961,(fun _ => MergedCutProfiles.Batch049.profile1961)⟩
theorem profilesValid295 : retention295.ProfilesValid := by
  exact MergedCutProfiles.Batch049.valid1961
theorem numericValid295 : retention295.NumericValid := by decide +kernel
def certificate295 : RatCutBinCertificate := ⟨⟨retention295,(2003128889937682127/1000000000000000000),(9018985876591161/200000000000000000),(9936799552501771471/1000000000000000000),(512812006704724266291/1000000000000000000),(989304858038643941/1000000000000000000)⟩,(249064460592379681/250000000000000000),(6047509921428323/12500000000000000),(82460024700125347/500000000000000000),(156343133755222427/1000000000000000000)⟩
theorem valid295 : certificate295.Valid := by decide +kernel
theorem sound295 : certificate295.Sound := rat_cut_bin_certificate_sound certificate295 profilesValid295 numericValid295 valid295

def retention296 : RatCutRetentionCertificate := ⟨(31/1000),(4/125),(1/2),(509812800566678423/20000000000000000),1,(101110992214163829095915579427669373599/101962560113335684600000000000000000000),false,MergedCutProfiles.Batch049.profile1962,(fun _ => MergedCutProfiles.Batch049.profile1962)⟩
theorem profilesValid296 : retention296.ProfilesValid := by
  exact MergedCutProfiles.Batch049.valid1962
theorem numericValid296 : retention296.NumericValid := by decide +kernel
def certificate296 : RatCutBinCertificate := ⟨⟨retention296,(2003128889937682127/1000000000000000000),(9018985876591161/200000000000000000),(9936799552501771471/1000000000000000000),(512812006704724266291/1000000000000000000),(491278824954372781/500000000000000000)⟩,(249064460592379681/250000000000000000),(486835000173172523/1000000000000000000),(162726470370795213/1000000000000000000),(76682945917578391/500000000000000000)⟩
theorem valid296 : certificate296.Valid := by decide +kernel
theorem sound296 : certificate296.Sound := rat_cut_bin_certificate_sound certificate296 profilesValid296 numericValid296 valid296

def retention297 : RatCutRetentionCertificate := ⟨(31/1000),(4/125),(21773924546765350914/51344512704105007463),(374156723765451957/100000000000000000),(5/4),(68946160405920489639784299850774668599/59865075802472313120000000000000000000),false,MergedCutProfiles.Batch049.profile1963,(fun _ => MergedCutProfiles.Batch049.profile1963)⟩
theorem profilesValid297 : retention297.ProfilesValid := by
  exact MergedCutProfiles.Batch049.valid1963
theorem numericValid297 : retention297.NumericValid := by decide +kernel
def certificate297 : RatCutBinCertificate := ⟨⟨retention297,(2388549821937682127/1000000000000000000),(9018985876591161/200000000000000000),(9936799552501771471/1000000000000000000),(512812006704724266291/1000000000000000000),(1138142702258133161/1000000000000000000)⟩,(995537674501680959/1000000000000000000),(350092149391572237/1000000000000000000),(282459731262842389/1000000000000000000),(214234793608269067/1000000000000000000)⟩
theorem valid297 : certificate297.Valid := by decide +kernel
theorem sound297 : certificate297.Sound := rat_cut_bin_certificate_sound certificate297 profilesValid297 numericValid297 valid297

def retention298 : RatCutRetentionCertificate := ⟨(31/1000),(4/125),(25531638939716971659/51344512704105007463),(10886962273382675457/500000000000000000),1,(86688932851599284824214024482913787383/87095698187061403656000000000000000000),false,MergedCutProfiles.Batch049.profile1964,(fun _ => MergedCutProfiles.Batch049.profile1964)⟩
theorem profilesValid298 : retention298.ProfilesValid := by
  exact MergedCutProfiles.Batch049.valid1964
theorem numericValid298 : retention298.NumericValid := by decide +kernel
def certificate298 : RatCutBinCertificate := ⟨⟨retention298,(2388549821937682127/1000000000000000000),(9018985876591161/200000000000000000),(9936799552501771471/1000000000000000000),(512812006704724266291/1000000000000000000),(984489974194783113/1000000000000000000)⟩,(995537674501680959/1000000000000000000),(202366116157647671/500000000000000000),(114587162671673953/500000000000000000),(107438668758818801/500000000000000000)⟩
theorem valid298 : certificate298.Valid := by decide +kernel
theorem sound298 : certificate298.Sound := rat_cut_bin_certificate_sound certificate298 profilesValid298 numericValid298 valid298

def retention299 : RatCutRetentionCertificate := ⟨(31/1000),(4/125),(1/2),(25531638939716971659/1000000000000000000),1,(101275231376666420041559772113551144163/102126555758867886636000000000000000000),false,MergedCutProfiles.Batch049.profile1962,(fun _ => MergedCutProfiles.Batch049.profile1962)⟩
theorem profilesValid299 : retention299.ProfilesValid := by
  exact MergedCutProfiles.Batch049.valid1962
theorem numericValid299 : retention299.NumericValid := by decide +kernel
def certificate299 : RatCutBinCertificate := ⟨⟨retention299,(2388549821937682127/1000000000000000000),(9018985876591161/200000000000000000),(9936799552501771471/1000000000000000000),(512812006704724266291/1000000000000000000),(980824332329625877/1000000000000000000)⟩,(995537674501680959/1000000000000000000),(406244841011930833/1000000000000000000),(227809001593508217/1000000000000000000),(107098874053391839/500000000000000000)⟩
theorem valid299 : certificate299.Valid := by decide +kernel
theorem sound299 : certificate299.Sound := rat_cut_bin_certificate_sound certificate299 profilesValid299 numericValid299 valid299

def certificates : List RatCutBinCertificate := [certificate288,certificate289,certificate290,certificate291,certificate292,certificate293,certificate294,certificate295,certificate296,certificate297,certificate298,certificate299]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound288,List.forall_mem_cons.mpr ⟨sound289,List.forall_mem_cons.mpr ⟨sound290,List.forall_mem_cons.mpr ⟨sound291,List.forall_mem_cons.mpr ⟨sound292,List.forall_mem_cons.mpr ⟨sound293,List.forall_mem_cons.mpr ⟨sound294,List.forall_mem_cons.mpr ⟨sound295,List.forall_mem_cons.mpr ⟨sound296,List.forall_mem_cons.mpr ⟨sound297,List.forall_mem_cons.mpr ⟨sound298,List.forall_mem_cons.mpr ⟨sound299,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch024
