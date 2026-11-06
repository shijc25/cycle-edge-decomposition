import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch293
import Cycle12.MergedCutProfiles.Batch294
import Cycle12.MergedCutProfiles.Batch295

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch154

def retention1848 : RatCutRetentionCertificate := ⟨(529/8000),(53/800),(4889734438604139461/9849714429867475514),(4841321226340732139/1000000000000000000),(11/10),(1926032014179526279319999802174026901559/1936528490536292855600000000000000000000),false,MergedCutProfiles.Batch293.profile11753,(fun _ => MergedCutProfiles.Batch293.profile11753)⟩
theorem profilesValid1848 : retention1848.ProfilesValid := by
  exact MergedCutProfiles.Batch293.valid11753
theorem numericValid1848 : retention1848.NumericValid := by decide +kernel
def certificate1848 : RatCutBinCertificate := ⟨⟨retention1848,(2717485569064180813/1000000000000000000),(231439924742735297/1000000000000000000),(4449992263997118281/250000000000000000),(21933068711334907873/125000000000000000),(955703303459243961/1000000000000000000)⟩,(988035810505703587/1000000000000000000),(49313457910230679/125000000000000000),(238552578995020771/1000000000000000000),(175855811291752123/1000000000000000000)⟩
theorem valid1848 : certificate1848.Valid := by decide +kernel
theorem sound1848 : certificate1848.Sound := rat_cut_bin_certificate_sound certificate1848 profilesValid1848 numericValid1848 valid1848

def retention1849 : RatCutRetentionCertificate := ⟨(529/8000),(53/800),(1/2),(4889734438604139461/1000000000000000000),(11/10),(1932831725657715687167277313688305286839/1955893775441655784400000000000000000000),false,MergedCutProfiles.Batch293.profile11750,(fun _ => MergedCutProfiles.Batch293.profile11750)⟩
theorem profilesValid1849 : retention1849.ProfilesValid := by
  exact MergedCutProfiles.Batch293.valid11750
theorem numericValid1849 : retention1849.NumericValid := by decide +kernel
def certificate1849 : RatCutBinCertificate := ⟨⟨retention1849,(2717485569064180813/1000000000000000000),(231439924742735297/1000000000000000000),(4449992263997118281/250000000000000000),(21933068711334907873/125000000000000000),(949332598465487031/1000000000000000000)⟩,(988035810505703587/1000000000000000000),(397155093639348741/1000000000000000000),(23609914462244139/100000000000000000),(173289570420512741/1000000000000000000)⟩
theorem valid1849 : certificate1849.Valid := by decide +kernel
theorem sound1849 : certificate1849.Sound := rat_cut_bin_certificate_sound certificate1849 profilesValid1849 numericValid1849 valid1849

def retention1850 : RatCutRetentionCertificate := ⟨(53/800),(531/8000),(1363107406512688819/9804817947003524195),(915535368188158949/1000000000000000000),(12/5),(572258437112939150889/320000000000000000000),true,MergedCutProfiles.Batch293.profile11754,![MergedCutProfiles.Batch293.profile11754,MergedCutProfiles.Batch293.profile11755,MergedCutProfiles.Batch293.profile11756,MergedCutProfiles.Batch293.profile11757,MergedCutProfiles.Batch293.profile11758,MergedCutProfiles.Batch293.profile11759,MergedCutProfiles.Batch294.profile11760,MergedCutProfiles.Batch294.profile11761,MergedCutProfiles.Batch294.profile11762,MergedCutProfiles.Batch294.profile11763,MergedCutProfiles.Batch294.profile11764,MergedCutProfiles.Batch294.profile11765,MergedCutProfiles.Batch294.profile11766,MergedCutProfiles.Batch294.profile11767,MergedCutProfiles.Batch294.profile11768,MergedCutProfiles.Batch294.profile11769]⟩
theorem profilesValid1850 : retention1850.ProfilesValid := by
  change ∀ j : Fin 16, (retention1850.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch293.valid11754
  · exact MergedCutProfiles.Batch293.valid11755
  · exact MergedCutProfiles.Batch293.valid11756
  · exact MergedCutProfiles.Batch293.valid11757
  · exact MergedCutProfiles.Batch293.valid11758
  · exact MergedCutProfiles.Batch293.valid11759
  · exact MergedCutProfiles.Batch294.valid11760
  · exact MergedCutProfiles.Batch294.valid11761
  · exact MergedCutProfiles.Batch294.valid11762
  · exact MergedCutProfiles.Batch294.valid11763
  · exact MergedCutProfiles.Batch294.valid11764
  · exact MergedCutProfiles.Batch294.valid11765
  · exact MergedCutProfiles.Batch294.valid11766
  · exact MergedCutProfiles.Batch294.valid11767
  · exact MergedCutProfiles.Batch294.valid11768
  · exact MergedCutProfiles.Batch294.valid11769
theorem numericValid1850 : retention1850.NumericValid := by decide +kernel
def certificate1850 : RatCutBinCertificate := ⟨⟨retention1850,(2409485405931971847/1000000000000000000),(232508037148497093/1000000000000000000),(17843180077170847979/1000000000000000000),(175088892166243367219/1000000000000000000),(856454476693712579/500000000000000000)⟩,(19787756596528779/20000000000000000),(165671805956976797/500000000000000000),(302644650474437937/1000000000000000000),(160919682716378697/1000000000000000000)⟩
theorem valid1850 : certificate1850.Valid := by decide +kernel
theorem sound1850 : certificate1850.Sound := rat_cut_bin_certificate_sound certificate1850 profilesValid1850 numericValid1850 valid1850

def retention1851 : RatCutRetentionCertificate := ⟨(53/800),(531/8000),(2762788350683880059/9804817947003524195),(1363107406512688819/1000000000000000000),(17/10),(1836298386176258134759/1280000000000000000000),true,MergedCutProfiles.Batch294.profile11770,![MergedCutProfiles.Batch294.profile11770,MergedCutProfiles.Batch294.profile11771,MergedCutProfiles.Batch294.profile11772,MergedCutProfiles.Batch294.profile11773,MergedCutProfiles.Batch294.profile11774,MergedCutProfiles.Batch294.profile11775,MergedCutProfiles.Batch294.profile11776,MergedCutProfiles.Batch294.profile11777,MergedCutProfiles.Batch294.profile11778,MergedCutProfiles.Batch294.profile11779,MergedCutProfiles.Batch294.profile11780,MergedCutProfiles.Batch294.profile11781,MergedCutProfiles.Batch294.profile11782,MergedCutProfiles.Batch294.profile11783,MergedCutProfiles.Batch294.profile11784,MergedCutProfiles.Batch294.profile11785]⟩
theorem profilesValid1851 : retention1851.ProfilesValid := by
  change ∀ j : Fin 16, (retention1851.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch294.valid11770
  · exact MergedCutProfiles.Batch294.valid11771
  · exact MergedCutProfiles.Batch294.valid11772
  · exact MergedCutProfiles.Batch294.valid11773
  · exact MergedCutProfiles.Batch294.valid11774
  · exact MergedCutProfiles.Batch294.valid11775
  · exact MergedCutProfiles.Batch294.valid11776
  · exact MergedCutProfiles.Batch294.valid11777
  · exact MergedCutProfiles.Batch294.valid11778
  · exact MergedCutProfiles.Batch294.valid11779
  · exact MergedCutProfiles.Batch294.valid11780
  · exact MergedCutProfiles.Batch294.valid11781
  · exact MergedCutProfiles.Batch294.valid11782
  · exact MergedCutProfiles.Batch294.valid11783
  · exact MergedCutProfiles.Batch294.valid11784
  · exact MergedCutProfiles.Batch294.valid11785
theorem numericValid1851 : retention1851.NumericValid := by decide +kernel
def certificate1851 : RatCutBinCertificate := ⟨⟨retention1851,(2409485405931971847/1000000000000000000),(232508037148497093/1000000000000000000),(17843180077170847979/1000000000000000000),(175088892166243367219/1000000000000000000),(43162574956856031/31250000000000000)⟩,(19787756596528779/20000000000000000),(4518327576830129/12500000000000000),(67676597895858187/250000000000000000),(643010401035721/4000000000000000)⟩
theorem valid1851 : certificate1851.Valid := by decide +kernel
theorem sound1851 : certificate1851.Sound := rat_cut_bin_certificate_sound certificate1851 profilesValid1851 numericValid1851 valid1851

def retention1852 : RatCutRetentionCertificate := ⟨(53/800),(531/8000),(4280436538092791746/9804817947003524195),(2762788350683880059/1000000000000000000),(11/10),(1390752816148592569967/1280000000000000000000),true,MergedCutProfiles.Batch294.profile11786,![MergedCutProfiles.Batch294.profile11786,MergedCutProfiles.Batch294.profile11787,MergedCutProfiles.Batch294.profile11788,MergedCutProfiles.Batch294.profile11789,MergedCutProfiles.Batch294.profile11790,MergedCutProfiles.Batch294.profile11791,MergedCutProfiles.Batch294.profile11792,MergedCutProfiles.Batch294.profile11793,MergedCutProfiles.Batch294.profile11794,MergedCutProfiles.Batch294.profile11795,MergedCutProfiles.Batch294.profile11796,MergedCutProfiles.Batch294.profile11797,MergedCutProfiles.Batch294.profile11798,MergedCutProfiles.Batch294.profile11799,MergedCutProfiles.Batch295.profile11800,MergedCutProfiles.Batch295.profile11801]⟩
theorem profilesValid1852 : retention1852.ProfilesValid := by
  change ∀ j : Fin 16, (retention1852.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch294.valid11786
  · exact MergedCutProfiles.Batch294.valid11787
  · exact MergedCutProfiles.Batch294.valid11788
  · exact MergedCutProfiles.Batch294.valid11789
  · exact MergedCutProfiles.Batch294.valid11790
  · exact MergedCutProfiles.Batch294.valid11791
  · exact MergedCutProfiles.Batch294.valid11792
  · exact MergedCutProfiles.Batch294.valid11793
  · exact MergedCutProfiles.Batch294.valid11794
  · exact MergedCutProfiles.Batch294.valid11795
  · exact MergedCutProfiles.Batch294.valid11796
  · exact MergedCutProfiles.Batch294.valid11797
  · exact MergedCutProfiles.Batch294.valid11798
  · exact MergedCutProfiles.Batch294.valid11799
  · exact MergedCutProfiles.Batch295.valid11800
  · exact MergedCutProfiles.Batch295.valid11801
theorem numericValid1852 : retention1852.NumericValid := by decide +kernel
def certificate1852 : RatCutBinCertificate := ⟨⟨retention1852,(2409485405931971847/1000000000000000000),(232508037148497093/1000000000000000000),(17843180077170847979/1000000000000000000),(175088892166243367219/1000000000000000000),(525986849345529279/500000000000000000)⟩,(19787756596528779/20000000000000000),(407304674120520729/1000000000000000000),(22685572146256921/100000000000000000),(162980874767824867/1000000000000000000)⟩
theorem valid1852 : certificate1852.Valid := by decide +kernel
theorem sound1852 : certificate1852.Sound := rat_cut_bin_certificate_sound certificate1852 profilesValid1852 numericValid1852 valid1852

def retention1853 : RatCutRetentionCertificate := ⟨(53/800),(531/8000),(955109511091959252/1960963589400704839),(2140218269046395873/500000000000000000),1,(125338591846829513993/128000000000000000000),true,MergedCutProfiles.Batch295.profile11802,![MergedCutProfiles.Batch295.profile11802,MergedCutProfiles.Batch294.profile11760,MergedCutProfiles.Batch295.profile11803,MergedCutProfiles.Batch294.profile11767,MergedCutProfiles.Batch295.profile11804,MergedCutProfiles.Batch295.profile11805,MergedCutProfiles.Batch295.profile11806,MergedCutProfiles.Batch295.profile11807,MergedCutProfiles.Batch295.profile11808,MergedCutProfiles.Batch295.profile11809,MergedCutProfiles.Batch295.profile11810,MergedCutProfiles.Batch295.profile11811,MergedCutProfiles.Batch295.profile11812,MergedCutProfiles.Batch295.profile11813,MergedCutProfiles.Batch295.profile11814,MergedCutProfiles.Batch295.profile11815]⟩
theorem profilesValid1853 : retention1853.ProfilesValid := by
  change ∀ j : Fin 16, (retention1853.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch295.valid11802
  · exact MergedCutProfiles.Batch294.valid11760
  · exact MergedCutProfiles.Batch295.valid11803
  · exact MergedCutProfiles.Batch294.valid11767
  · exact MergedCutProfiles.Batch295.valid11804
  · exact MergedCutProfiles.Batch295.valid11805
  · exact MergedCutProfiles.Batch295.valid11806
  · exact MergedCutProfiles.Batch295.valid11807
  · exact MergedCutProfiles.Batch295.valid11808
  · exact MergedCutProfiles.Batch295.valid11809
  · exact MergedCutProfiles.Batch295.valid11810
  · exact MergedCutProfiles.Batch295.valid11811
  · exact MergedCutProfiles.Batch295.valid11812
  · exact MergedCutProfiles.Batch295.valid11813
  · exact MergedCutProfiles.Batch295.valid11814
  · exact MergedCutProfiles.Batch295.valid11815
theorem numericValid1853 : retention1853.NumericValid := by decide +kernel
def certificate1853 : RatCutBinCertificate := ⟨⟨retention1853,(2409485405931971847/1000000000000000000),(232508037148497093/1000000000000000000),(17843180077170847979/1000000000000000000),(175088892166243367219/1000000000000000000),(947800873942913603/1000000000000000000)⟩,(19787756596528779/20000000000000000),(213142201000270869/500000000000000000),(42048845175219401/200000000000000000),(40298705130785593/250000000000000000)⟩
theorem valid1853 : certificate1853.Valid := by decide +kernel
theorem sound1853 : certificate1853.Sound := rat_cut_bin_certificate_sound certificate1853 profilesValid1853 numericValid1853 valid1853

def retention1854 : RatCutRetentionCertificate := ⟨(53/800),(531/8000),(4871536061324538166/9804817947003524195),(238777377772989813/50000000000000000),(11/10),(6324297381621922961526846454897635837/6367396740613061680000000000000000000),false,MergedCutProfiles.Batch295.profile11816,(fun _ => MergedCutProfiles.Batch295.profile11816)⟩
theorem profilesValid1854 : retention1854.ProfilesValid := by
  exact MergedCutProfiles.Batch295.valid11816
theorem numericValid1854 : retention1854.NumericValid := by decide +kernel
def certificate1854 : RatCutBinCertificate := ⟨⟨retention1854,(2409485405931971847/1000000000000000000),(232508037148497093/1000000000000000000),(17843180077170847979/1000000000000000000),(175088892166243367219/1000000000000000000),(958685664918971487/1000000000000000000)⟩,(19787756596528779/20000000000000000),(4166327087058343/10000000000000000),(218583616096674329/1000000000000000000),(80736549031658293/500000000000000000)⟩
theorem valid1854 : certificate1854.Valid := by decide +kernel
theorem sound1854 : certificate1854.Sound := rat_cut_bin_certificate_sound certificate1854 profilesValid1854 numericValid1854 valid1854

def retention1855 : RatCutRetentionCertificate := ⟨(53/800),(531/8000),(1/2),(2435768030662269083/500000000000000000),(11/10),(120334691556110961346869812324155750789/121788401533113454150000000000000000000),false,MergedCutProfiles.Batch295.profile11817,(fun _ => MergedCutProfiles.Batch295.profile11817)⟩
theorem profilesValid1855 : retention1855.ProfilesValid := by
  exact MergedCutProfiles.Batch295.valid11817
theorem numericValid1855 : retention1855.NumericValid := by decide +kernel
def certificate1855 : RatCutBinCertificate := ⟨⟨retention1855,(2409485405931971847/1000000000000000000),(232508037148497093/1000000000000000000),(17843180077170847979/1000000000000000000),(175088892166243367219/1000000000000000000),(95351823545899797/100000000000000000)⟩,(19787756596528779/20000000000000000),(418066467028028827/1000000000000000000),(43466157598757149/200000000000000000),(80127528877653981/500000000000000000)⟩
theorem valid1855 : certificate1855.Valid := by decide +kernel
theorem sound1855 : certificate1855.Sound := rat_cut_bin_certificate_sound certificate1855 profilesValid1855 numericValid1855 valid1855

def retention1856 : RatCutRetentionCertificate := ⟨(53/800),(531/8000),(1/2),64,1,(255418557898207655611292900453024111599/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch295.profile11817,(fun _ => MergedCutProfiles.Batch295.profile11817)⟩
theorem profilesValid1856 : retention1856.ProfilesValid := by
  exact MergedCutProfiles.Batch295.valid11817
theorem numericValid1856 : retention1856.NumericValid := by decide +kernel
def certificate1856 : RatCutBinCertificate := ⟨⟨retention1856,(2409485405931971847/1000000000000000000),(232508037148497093/1000000000000000000),(17843180077170847979/1000000000000000000),(175088892166243367219/1000000000000000000),(241582738992146873/250000000000000000)⟩,(19787756596528779/20000000000000000),(375145811452348643/1000000000000000000),(12852161250243247/50000000000000000),(242071012741538737/1000000000000000000)⟩
theorem valid1856 : certificate1856.Valid := by decide +kernel
theorem sound1856 : certificate1856.Sound := rat_cut_bin_certificate_sound certificate1856 profilesValid1856 numericValid1856 valid1856

def retention1857 : RatCutRetentionCertificate := ⟨(53/800),(531/8000),(898715202693660778/1960963589400704839),(2900358258425279053/1000000000000000000),(5/4),(199459848237041799208371065541515967391/185622928539217859392000000000000000000),false,MergedCutProfiles.Batch295.profile11818,(fun _ => MergedCutProfiles.Batch295.profile11818)⟩
theorem profilesValid1857 : retention1857.ProfilesValid := by
  exact MergedCutProfiles.Batch295.valid11818
theorem numericValid1857 : retention1857.NumericValid := by decide +kernel
def certificate1857 : RatCutBinCertificate := ⟨⟨retention1857,(2719172083931971847/1000000000000000000),(232508037148497093/1000000000000000000),(17843180077170847979/1000000000000000000),(175088892166243367219/1000000000000000000),(1030236250177013169/1000000000000000000)⟩,(98801895000489983/100000000000000000),(364729191769962173/1000000000000000000),(133700540093557497/500000000000000000),(4428320931661877/25000000000000000)⟩
theorem valid1857 : certificate1857.Valid := by decide +kernel
theorem sound1857 : certificate1857.Sound := rat_cut_bin_certificate_sound certificate1857 profilesValid1857 numericValid1857 valid1857

def retention1858 : RatCutRetentionCertificate := ⟨(53/800),(531/8000),(4817721701419454304/9804817947003524195),(449357601346830389/100000000000000000),(11/10),(17990887259224753618349381684998641799/17974304053873215560000000000000000000),false,MergedCutProfiles.Batch295.profile11819,(fun _ => MergedCutProfiles.Batch295.profile11819)⟩
theorem profilesValid1858 : retention1858.ProfilesValid := by
  exact MergedCutProfiles.Batch295.valid11819
theorem numericValid1858 : retention1858.NumericValid := by decide +kernel
def certificate1858 : RatCutBinCertificate := ⟨⟨retention1858,(2719172083931971847/1000000000000000000),(232508037148497093/1000000000000000000),(17843180077170847979/1000000000000000000),(175088892166243367219/1000000000000000000),(961936330609111733/1000000000000000000)⟩,(98801895000489983/100000000000000000),(195312944787751051/500000000000000000),(242182046198307123/1000000000000000000),(7103048179651701/40000000000000000)⟩
theorem valid1858 : certificate1858.Valid := by decide +kernel
theorem sound1858 : certificate1858.Sound := rat_cut_bin_certificate_sound certificate1858 profilesValid1858 numericValid1858 valid1858

def retention1859 : RatCutRetentionCertificate := ⟨(53/800),(531/8000),(4865898918433648848/9804817947003524195),(150553803169357947/31250000000000000),(11/10),(479209793585242120419830899982920104551/481772170141945430400000000000000000000),false,MergedCutProfiles.Batch295.profile11820,(fun _ => MergedCutProfiles.Batch295.profile11820)⟩
theorem profilesValid1859 : retention1859.ProfilesValid := by
  exact MergedCutProfiles.Batch295.valid11820
theorem numericValid1859 : retention1859.NumericValid := by decide +kernel
def certificate1859 : RatCutBinCertificate := ⟨⟨retention1859,(2719172083931971847/1000000000000000000),(232508037148497093/1000000000000000000),(17843180077170847979/1000000000000000000),(175088892166243367219/1000000000000000000),(119461972616641371/125000000000000000)⟩,(98801895000489983/100000000000000000),(393176617869227469/1000000000000000000),(29974098730551429/125000000000000000),(176643026676065253/1000000000000000000)⟩
theorem valid1859 : certificate1859.Valid := by decide +kernel
theorem sound1859 : certificate1859.Sound := rat_cut_bin_certificate_sound certificate1859 profilesValid1859 numericValid1859 valid1859

def certificates : List RatCutBinCertificate := [certificate1848,certificate1849,certificate1850,certificate1851,certificate1852,certificate1853,certificate1854,certificate1855,certificate1856,certificate1857,certificate1858,certificate1859]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1848,List.forall_mem_cons.mpr ⟨sound1849,List.forall_mem_cons.mpr ⟨sound1850,List.forall_mem_cons.mpr ⟨sound1851,List.forall_mem_cons.mpr ⟨sound1852,List.forall_mem_cons.mpr ⟨sound1853,List.forall_mem_cons.mpr ⟨sound1854,List.forall_mem_cons.mpr ⟨sound1855,List.forall_mem_cons.mpr ⟨sound1856,List.forall_mem_cons.mpr ⟨sound1857,List.forall_mem_cons.mpr ⟨sound1858,List.forall_mem_cons.mpr ⟨sound1859,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch154
