import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch045
import Cycle12.MergedCutProfiles.Batch046
import Cycle12.MergedCutProfiles.Batch047

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch023

def retention276 : RatCutRetentionCertificate := ⟨(3/100),(31/1000),(863312810182342579/54990570427380060659),(728961901444145483/1000000000000000000),(18/5),(2837712938169404341327/1280000000000000000000),true,MergedCutProfiles.Batch045.profile1813,![MergedCutProfiles.Batch045.profile1813,MergedCutProfiles.Batch045.profile1814,MergedCutProfiles.Batch045.profile1815,MergedCutProfiles.Batch045.profile1816,MergedCutProfiles.Batch045.profile1817,MergedCutProfiles.Batch045.profile1818,MergedCutProfiles.Batch045.profile1819,MergedCutProfiles.Batch045.profile1820,MergedCutProfiles.Batch045.profile1821,MergedCutProfiles.Batch045.profile1822,MergedCutProfiles.Batch045.profile1809,MergedCutProfiles.Batch045.profile1823,MergedCutProfiles.Batch045.profile1824,MergedCutProfiles.Batch045.profile1825,MergedCutProfiles.Batch045.profile1826,MergedCutProfiles.Batch045.profile1827]⟩
theorem profilesValid276 : retention276.ProfilesValid := by
  change ∀ j : Fin 16, (retention276.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch045.valid1813
  · exact MergedCutProfiles.Batch045.valid1814
  · exact MergedCutProfiles.Batch045.valid1815
  · exact MergedCutProfiles.Batch045.valid1816
  · exact MergedCutProfiles.Batch045.valid1817
  · exact MergedCutProfiles.Batch045.valid1818
  · exact MergedCutProfiles.Batch045.valid1819
  · exact MergedCutProfiles.Batch045.valid1820
  · exact MergedCutProfiles.Batch045.valid1821
  · exact MergedCutProfiles.Batch045.valid1822
  · exact MergedCutProfiles.Batch045.valid1809
  · exact MergedCutProfiles.Batch045.valid1823
  · exact MergedCutProfiles.Batch045.valid1824
  · exact MergedCutProfiles.Batch045.valid1825
  · exact MergedCutProfiles.Batch045.valid1826
  · exact MergedCutProfiles.Batch045.valid1827
theorem numericValid276 : retention276.NumericValid := by decide +kernel
def certificate276 : RatCutBinCertificate := ⟨⟨retention276,(499557047732608841/250000000000000000),(42146381475855499/1000000000000000000),(2449118668530467497/250000000000000000),(33840943074420866071/62500000000000000),(2186013925325916423/1000000000000000000)⟩,(249113519363578313/250000000000000000),(110131253023565377/250000000000000000),(24792183267801659/125000000000000000),(97399707840610431/1000000000000000000)⟩
theorem valid276 : certificate276.Valid := by decide +kernel
theorem sound276 : certificate276.Sound := rat_cut_bin_certificate_sound certificate276 profilesValid276 numericValid276 valid276

def retention277 : RatCutRetentionCertificate := ⟨(3/100),(31/1000),(1019093328000000000/54990570427380060659),(863312810182342579/1000000000000000000),(31/10),(2806758517466063160671/1280000000000000000000),true,MergedCutProfiles.Batch045.profile1828,![MergedCutProfiles.Batch045.profile1828,MergedCutProfiles.Batch045.profile1829,MergedCutProfiles.Batch045.profile1830,MergedCutProfiles.Batch045.profile1831,MergedCutProfiles.Batch045.profile1803,MergedCutProfiles.Batch045.profile1832,MergedCutProfiles.Batch045.profile1833,MergedCutProfiles.Batch045.profile1834,MergedCutProfiles.Batch045.profile1835,MergedCutProfiles.Batch045.profile1810,MergedCutProfiles.Batch045.profile1824,MergedCutProfiles.Batch045.profile1836,MergedCutProfiles.Batch045.profile1837,MergedCutProfiles.Batch045.profile1838,MergedCutProfiles.Batch045.profile1839,MergedCutProfiles.Batch046.profile1840]⟩
theorem profilesValid277 : retention277.ProfilesValid := by
  change ∀ j : Fin 16, (retention277.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch045.valid1828
  · exact MergedCutProfiles.Batch045.valid1829
  · exact MergedCutProfiles.Batch045.valid1830
  · exact MergedCutProfiles.Batch045.valid1831
  · exact MergedCutProfiles.Batch045.valid1803
  · exact MergedCutProfiles.Batch045.valid1832
  · exact MergedCutProfiles.Batch045.valid1833
  · exact MergedCutProfiles.Batch045.valid1834
  · exact MergedCutProfiles.Batch045.valid1835
  · exact MergedCutProfiles.Batch045.valid1810
  · exact MergedCutProfiles.Batch045.valid1824
  · exact MergedCutProfiles.Batch045.valid1836
  · exact MergedCutProfiles.Batch045.valid1837
  · exact MergedCutProfiles.Batch045.valid1838
  · exact MergedCutProfiles.Batch045.valid1839
  · exact MergedCutProfiles.Batch046.valid1840
theorem numericValid277 : retention277.NumericValid := by decide +kernel
def certificate277 : RatCutBinCertificate := ⟨⟨retention277,(499557047732608841/250000000000000000),(42146381475855499/1000000000000000000),(2449118668530467497/250000000000000000),(33840943074420866071/62500000000000000),(270766164307434079/125000000000000000)⟩,(249113519363578313/250000000000000000),(204360128837182491/500000000000000000),(4511735117389987/20000000000000000),(62239847361066359/500000000000000000)⟩
theorem valid277 : certificate277.Valid := by decide +kernel
theorem sound277 : certificate277.Sound := rat_cut_bin_certificate_sound certificate277 profilesValid277 numericValid277 valid277

def retention278 : RatCutRetentionCertificate := ⟨(3/100),(31/1000),(1063939749267423947/54990570427380060659),(63693333/62500000),(27/10),(34865796581342760923/16000000000000000000),true,MergedCutProfiles.Batch046.profile1841,![MergedCutProfiles.Batch046.profile1841,MergedCutProfiles.Batch046.profile1842,MergedCutProfiles.Batch046.profile1843,MergedCutProfiles.Batch046.profile1844,MergedCutProfiles.Batch046.profile1845,MergedCutProfiles.Batch046.profile1846,MergedCutProfiles.Batch046.profile1847,MergedCutProfiles.Batch046.profile1848,MergedCutProfiles.Batch046.profile1849,MergedCutProfiles.Batch046.profile1850,MergedCutProfiles.Batch046.profile1851,MergedCutProfiles.Batch046.profile1852,MergedCutProfiles.Batch045.profile1827,MergedCutProfiles.Batch046.profile1853,MergedCutProfiles.Batch046.profile1854,MergedCutProfiles.Batch046.profile1855]⟩
theorem profilesValid278 : retention278.ProfilesValid := by
  change ∀ j : Fin 16, (retention278.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch046.valid1841
  · exact MergedCutProfiles.Batch046.valid1842
  · exact MergedCutProfiles.Batch046.valid1843
  · exact MergedCutProfiles.Batch046.valid1844
  · exact MergedCutProfiles.Batch046.valid1845
  · exact MergedCutProfiles.Batch046.valid1846
  · exact MergedCutProfiles.Batch046.valid1847
  · exact MergedCutProfiles.Batch046.valid1848
  · exact MergedCutProfiles.Batch046.valid1849
  · exact MergedCutProfiles.Batch046.valid1850
  · exact MergedCutProfiles.Batch046.valid1851
  · exact MergedCutProfiles.Batch046.valid1852
  · exact MergedCutProfiles.Batch045.valid1827
  · exact MergedCutProfiles.Batch046.valid1853
  · exact MergedCutProfiles.Batch046.valid1854
  · exact MergedCutProfiles.Batch046.valid1855
theorem numericValid278 : retention278.NumericValid := by decide +kernel
def certificate278 : RatCutBinCertificate := ⟨⟨retention278,(499557047732608841/250000000000000000),(42146381475855499/1000000000000000000),(2449118668530467497/250000000000000000),(33840943074420866071/62500000000000000),(2155900337469287143/1000000000000000000)⟩,(249113519363578313/250000000000000000),(380785563997697037/1000000000000000000),(125778197592827611/500000000000000000),(19381020466283463/125000000000000000)⟩
theorem valid278 : certificate278.Valid := by decide +kernel
theorem sound278 : certificate278.Sound := rat_cut_bin_certificate_sound certificate278 profilesValid278 numericValid278 valid278

def retention279 : RatCutRetentionCertificate := ⟨(3/100),(31/1000),(1749789168169806392/54990570427380060659),(1063939749267423947/1000000000000000000),(13/5),(679620342613299867183/320000000000000000000),true,MergedCutProfiles.Batch046.profile1856,![MergedCutProfiles.Batch046.profile1856,MergedCutProfiles.Batch046.profile1857,MergedCutProfiles.Batch046.profile1858,MergedCutProfiles.Batch046.profile1859,MergedCutProfiles.Batch045.profile1808,MergedCutProfiles.Batch046.profile1860,MergedCutProfiles.Batch045.profile1836,MergedCutProfiles.Batch046.profile1861,MergedCutProfiles.Batch046.profile1862,MergedCutProfiles.Batch046.profile1863,MergedCutProfiles.Batch046.profile1864,MergedCutProfiles.Batch046.profile1865,MergedCutProfiles.Batch046.profile1866,MergedCutProfiles.Batch046.profile1867,MergedCutProfiles.Batch046.profile1868,MergedCutProfiles.Batch046.profile1869]⟩
theorem profilesValid279 : retention279.ProfilesValid := by
  change ∀ j : Fin 16, (retention279.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch046.valid1856
  · exact MergedCutProfiles.Batch046.valid1857
  · exact MergedCutProfiles.Batch046.valid1858
  · exact MergedCutProfiles.Batch046.valid1859
  · exact MergedCutProfiles.Batch045.valid1808
  · exact MergedCutProfiles.Batch046.valid1860
  · exact MergedCutProfiles.Batch045.valid1836
  · exact MergedCutProfiles.Batch046.valid1861
  · exact MergedCutProfiles.Batch046.valid1862
  · exact MergedCutProfiles.Batch046.valid1863
  · exact MergedCutProfiles.Batch046.valid1864
  · exact MergedCutProfiles.Batch046.valid1865
  · exact MergedCutProfiles.Batch046.valid1866
  · exact MergedCutProfiles.Batch046.valid1867
  · exact MergedCutProfiles.Batch046.valid1868
  · exact MergedCutProfiles.Batch046.valid1869
theorem numericValid279 : retention279.NumericValid := by decide +kernel
def certificate279 : RatCutBinCertificate := ⟨⟨retention279,(499557047732608841/250000000000000000),(42146381475855499/1000000000000000000),(2449118668530467497/250000000000000000),(33840943074420866071/62500000000000000),(131341332935617681/62500000000000000)⟩,(249113519363578313/250000000000000000),(95872679571462791/250000000000000000),(24895428723860639/100000000000000000),(3101670960774463/20000000000000000)⟩
theorem valid279 : certificate279.Valid := by decide +kernel
theorem sound279 : certificate279.Sound := rat_cut_bin_certificate_sound certificate279 profilesValid279 numericValid279 valid279

def retention280 : RatCutRetentionCertificate := ⟨(3/100),(31/1000),(10596303244479044136/54990570427380060659),(218723646021225799/125000000000000000),(37/20),(18089673814192857420466768433618600539/10936182301061289950000000000000000000),false,MergedCutProfiles.Batch046.profile1870,(fun _ => MergedCutProfiles.Batch046.profile1870)⟩
theorem profilesValid280 : retention280.ProfilesValid := by
  exact MergedCutProfiles.Batch046.valid1870
theorem numericValid280 : retention280.NumericValid := by decide +kernel
def certificate280 : RatCutBinCertificate := ⟨⟨retention280,(499557047732608841/250000000000000000),(42146381475855499/1000000000000000000),(2449118668530467497/250000000000000000),(33840943074420866071/62500000000000000),(32764157963484183/20000000000000000)⟩,(249113519363578313/250000000000000000),(205067824986297893/500000000000000000),(224322861696950797/1000000000000000000),(606831442820761/3906250000000000)⟩
theorem valid280 : certificate280.Valid := by decide +kernel
theorem sound280 : certificate280.Sound := rat_cut_bin_certificate_sound certificate280 profilesValid280 numericValid280 valid280

def retention281 : RatCutRetentionCertificate := ⟨(3/100),(31/1000),(25689558767242658800/54990570427380060659),(1324537905559880517/125000000000000000),(21/20),(280977371479867639717885674762962190431/264907581111976103400000000000000000000),false,MergedCutProfiles.Batch046.profile1871,(fun _ => MergedCutProfiles.Batch046.profile1871)⟩
theorem profilesValid281 : retention281.ProfilesValid := by
  exact MergedCutProfiles.Batch046.valid1871
theorem numericValid281 : retention281.NumericValid := by decide +kernel
def certificate281 : RatCutBinCertificate := ⟨⟨retention281,(499557047732608841/250000000000000000),(42146381475855499/1000000000000000000),(2449118668530467497/250000000000000000),(33840943074420866071/62500000000000000),(10516351974312603/10000000000000000)⟩,(249113519363578313/250000000000000000),(3790960908304759/8000000000000000),(34446625330331367/200000000000000000),(31533830636681809/200000000000000000)⟩
theorem valid281 : certificate281.Valid := by decide +kernel
theorem sound281 : certificate281.Sound := rat_cut_bin_certificate_sound certificate281 profilesValid281 numericValid281 valid281

def retention282 : RatCutRetentionCertificate := ⟨(3/100),(31/1000),(27269984291476667077/54990570427380060659),(64223896918106647/2500000000000000),1,(8218775772909991806449664453856059/8220658805517650816000000000000000),false,MergedCutProfiles.Batch046.profile1872,(fun _ => MergedCutProfiles.Batch046.profile1872)⟩
theorem profilesValid282 : retention282.ProfilesValid := by
  exact MergedCutProfiles.Batch046.valid1872
theorem numericValid282 : retention282.NumericValid := by decide +kernel
def certificate282 : RatCutBinCertificate := ⟨⟨retention282,(499557047732608841/250000000000000000),(42146381475855499/1000000000000000000),(2449118668530467497/250000000000000000),(33840943074420866071/62500000000000000),(198234827603049197/200000000000000000)⟩,(249113519363578313/250000000000000000),(60303547662771311/125000000000000000),(165918477480609301/1000000000000000000),(31554365696925219/200000000000000000)⟩
theorem valid282 : certificate282.Valid := by decide +kernel
theorem sound282 : certificate282.Sound := rat_cut_bin_certificate_sound certificate282 profilesValid282 numericValid282 valid282

def retention283 : RatCutRetentionCertificate := ⟨(3/100),(31/1000),(1/2),(27269984291476667077/1000000000000000000),1,(27059667492594312241909048520718831829/27269984291476667077000000000000000000),false,MergedCutProfiles.Batch046.profile1873,(fun _ => MergedCutProfiles.Batch046.profile1873)⟩
theorem profilesValid283 : retention283.ProfilesValid := by
  exact MergedCutProfiles.Batch046.valid1873
theorem numericValid283 : retention283.NumericValid := by decide +kernel
def certificate283 : RatCutBinCertificate := ⟨⟨retention283,(499557047732608841/250000000000000000),(42146381475855499/1000000000000000000),(2449118668530467497/250000000000000000),(33840943074420866071/62500000000000000),(983690808918682367/1000000000000000000)⟩,(249113519363578313/250000000000000000),(485264218941741051/1000000000000000000),(4096492453627509/25000000000000000),(155013066782467089/1000000000000000000)⟩
theorem valid283 : certificate283.Valid := by decide +kernel
theorem sound283 : certificate283.Sound := rat_cut_bin_certificate_sound certificate283 profilesValid283 numericValid283 valid283

def retention284 : RatCutRetentionCertificate := ⟨(3/100),(31/1000),(23063210542398128414/54990570427380060659),(7219664673498009/1953125000000000),(5/4),(119163130443631368618995456017653071/102679675356416128000000000000000000),false,MergedCutProfiles.Batch046.profile1874,(fun _ => MergedCutProfiles.Batch046.profile1874)⟩
theorem profilesValid284 : retention284.ProfilesValid := by
  exact MergedCutProfiles.Batch046.valid1874
theorem numericValid284 : retention284.NumericValid := by decide +kernel
def certificate284 : RatCutBinCertificate := ⟨⟨retention284,(596314580732608841/250000000000000000),(42146381475855499/1000000000000000000),(2449118668530467497/250000000000000000),(33840943074420866071/62500000000000000),(286926314437274203/250000000000000000)⟩,(995767160629374451/1000000000000000000),(14010392978902219/40000000000000000),(35285476753296471/125000000000000000),(107613783739482213/500000000000000000)⟩
theorem valid284 : certificate284.Valid := by decide +kernel
theorem sound284 : certificate284.Sound := rat_cut_bin_certificate_sound certificate284 profilesValid284 numericValid284 valid284

def retention285 : RatCutRetentionCertificate := ⟨(3/100),(31/1000),(27313862447049106942/54990570427380060659),(11531605271199064207/500000000000000000),1,(1957088592261147886530300332781114129/1962826429140266248000000000000000000),false,MergedCutProfiles.Batch046.profile1875,(fun _ => MergedCutProfiles.Batch046.profile1875)⟩
theorem profilesValid285 : retention285.ProfilesValid := by
  exact MergedCutProfiles.Batch046.valid1875
theorem numericValid285 : retention285.NumericValid := by decide +kernel
def certificate285 : RatCutBinCertificate := ⟨⟨retention285,(596314580732608841/250000000000000000),(42146381475855499/1000000000000000000),(2449118668530467497/250000000000000000),(33840943074420866071/62500000000000000),(98681485759554197/100000000000000000)⟩,(995767160629374451/1000000000000000000),(101841555949239221/250000000000000000),(226800444601604117/1000000000000000000),(213701075725496097/1000000000000000000)⟩
theorem valid285 : certificate285.Valid := by decide +kernel
theorem sound285 : certificate285.Sound := rat_cut_bin_certificate_sound certificate285 profilesValid285 numericValid285 valid285

def retention286 : RatCutRetentionCertificate := ⟨(3/100),(31/1000),(1/2),(13656931223524553471/500000000000000000),1,(27103610693022919073871631288583296339/27313862447049106942000000000000000000),false,MergedCutProfiles.Batch046.profile1873,(fun _ => MergedCutProfiles.Batch046.profile1873)⟩
theorem profilesValid286 : retention286.ProfilesValid := by
  exact MergedCutProfiles.Batch046.valid1873
theorem numericValid286 : retention286.NumericValid := by decide +kernel
def certificate286 : RatCutBinCertificate := ⟨⟨retention286,(596314580732608841/250000000000000000),(42146381475855499/1000000000000000000),(2449118668530467497/250000000000000000),(33840943074420866071/62500000000000000),(491020247274783253/500000000000000000)⟩,(995767160629374451/1000000000000000000),(409346706532515399/1000000000000000000),(11251337814835409/50000000000000000),(106199203733843971/500000000000000000)⟩
theorem valid286 : certificate286.Valid := by decide +kernel
theorem sound286 : certificate286.Sound := rat_cut_bin_certificate_sound certificate286 profilesValid286 numericValid286 valid286

def retention287 : RatCutRetentionCertificate := ⟨(31/1000),(4/125),(737856102350687506/51344512704105007463),(45659412274176207/62500000000000000),(71/20),(44375172673357594563/20000000000000000000),true,MergedCutProfiles.Batch046.profile1876,![MergedCutProfiles.Batch046.profile1876,MergedCutProfiles.Batch046.profile1877,MergedCutProfiles.Batch046.profile1878,MergedCutProfiles.Batch046.profile1879,MergedCutProfiles.Batch047.profile1880,MergedCutProfiles.Batch047.profile1881,MergedCutProfiles.Batch047.profile1882,MergedCutProfiles.Batch047.profile1883,MergedCutProfiles.Batch047.profile1884,MergedCutProfiles.Batch047.profile1885,MergedCutProfiles.Batch047.profile1886,MergedCutProfiles.Batch047.profile1887,MergedCutProfiles.Batch047.profile1888,MergedCutProfiles.Batch047.profile1889,MergedCutProfiles.Batch047.profile1890,MergedCutProfiles.Batch047.profile1891]⟩
theorem profilesValid287 : retention287.ProfilesValid := by
  change ∀ j : Fin 16, (retention287.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch046.valid1876
  · exact MergedCutProfiles.Batch046.valid1877
  · exact MergedCutProfiles.Batch046.valid1878
  · exact MergedCutProfiles.Batch046.valid1879
  · exact MergedCutProfiles.Batch047.valid1880
  · exact MergedCutProfiles.Batch047.valid1881
  · exact MergedCutProfiles.Batch047.valid1882
  · exact MergedCutProfiles.Batch047.valid1883
  · exact MergedCutProfiles.Batch047.valid1884
  · exact MergedCutProfiles.Batch047.valid1885
  · exact MergedCutProfiles.Batch047.valid1886
  · exact MergedCutProfiles.Batch047.valid1887
  · exact MergedCutProfiles.Batch047.valid1888
  · exact MergedCutProfiles.Batch047.valid1889
  · exact MergedCutProfiles.Batch047.valid1890
  · exact MergedCutProfiles.Batch047.valid1891
theorem numericValid287 : retention287.NumericValid := by decide +kernel
def certificate287 : RatCutBinCertificate := ⟨⟨retention287,(2003128889937682127/1000000000000000000),(9018985876591161/200000000000000000),(9936799552501771471/1000000000000000000),(512812006704724266291/1000000000000000000),(437297218625864719/200000000000000000)⟩,(249064460592379681/250000000000000000),(109258801115452149/250000000000000000),(100606091712545583/500000000000000000),(99707330646307471/1000000000000000000)⟩
theorem valid287 : certificate287.Valid := by decide +kernel
theorem sound287 : certificate287.Sound := rat_cut_bin_certificate_sound certificate287 profilesValid287 numericValid287 valid287

def certificates : List RatCutBinCertificate := [certificate276,certificate277,certificate278,certificate279,certificate280,certificate281,certificate282,certificate283,certificate284,certificate285,certificate286,certificate287]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound276,List.forall_mem_cons.mpr ⟨sound277,List.forall_mem_cons.mpr ⟨sound278,List.forall_mem_cons.mpr ⟨sound279,List.forall_mem_cons.mpr ⟨sound280,List.forall_mem_cons.mpr ⟨sound281,List.forall_mem_cons.mpr ⟨sound282,List.forall_mem_cons.mpr ⟨sound283,List.forall_mem_cons.mpr ⟨sound284,List.forall_mem_cons.mpr ⟨sound285,List.forall_mem_cons.mpr ⟨sound286,List.forall_mem_cons.mpr ⟨sound287,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch023
