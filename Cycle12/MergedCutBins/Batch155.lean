import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch295
import Cycle12.MergedCutProfiles.Batch296
import Cycle12.MergedCutProfiles.Batch297

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch155

def retention1860 : RatCutRetentionCertificate := ⟨(53/800),(531/8000),(1/2),(304118682402103053/62500000000000000),(11/10),(480759613670927492373949586808162461159/486589891843364884800000000000000000000),false,MergedCutProfiles.Batch295.profile11817,(fun _ => MergedCutProfiles.Batch295.profile11817)⟩
theorem profilesValid1860 : retention1860.ProfilesValid := by
  exact MergedCutProfiles.Batch295.valid11817
theorem numericValid1860 : retention1860.NumericValid := by decide +kernel
def certificate1860 : RatCutBinCertificate := ⟨⟨retention1860,(2719172083931971847/1000000000000000000),(232508037148497093/1000000000000000000),(17843180077170847979/1000000000000000000),(175088892166243367219/1000000000000000000),(189806522339472273/200000000000000000)⟩,(98801895000489983/100000000000000000),(395937115571961431/1000000000000000000),(118612837460790731/500000000000000000),(173946801443908977/1000000000000000000)⟩
theorem valid1860 : certificate1860.Valid := by decide +kernel
theorem sound1860 : certificate1860.Sound := rat_cut_bin_certificate_sound certificate1860 profilesValid1860 numericValid1860 valid1860

def retention1861 : RatCutRetentionCertificate := ⟨(531/8000),(133/2000),(1203798080898944377/9760188529515390503),(223281346151771371/250000000000000000),(49/20),(146264129950398293883/80000000000000000000),true,MergedCutProfiles.Batch295.profile11821,![MergedCutProfiles.Batch295.profile11821,MergedCutProfiles.Batch295.profile11822,MergedCutProfiles.Batch295.profile11823,MergedCutProfiles.Batch295.profile11824,MergedCutProfiles.Batch295.profile11825,MergedCutProfiles.Batch295.profile11826,MergedCutProfiles.Batch295.profile11827,MergedCutProfiles.Batch295.profile11828,MergedCutProfiles.Batch295.profile11829,MergedCutProfiles.Batch295.profile11830,MergedCutProfiles.Batch295.profile11831,MergedCutProfiles.Batch295.profile11832,MergedCutProfiles.Batch295.profile11833,MergedCutProfiles.Batch295.profile11834,MergedCutProfiles.Batch295.profile11835,MergedCutProfiles.Batch295.profile11836]⟩
theorem profilesValid1861 : retention1861.ProfilesValid := by
  change ∀ j : Fin 16, (retention1861.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch295.valid11821
  · exact MergedCutProfiles.Batch295.valid11822
  · exact MergedCutProfiles.Batch295.valid11823
  · exact MergedCutProfiles.Batch295.valid11824
  · exact MergedCutProfiles.Batch295.valid11825
  · exact MergedCutProfiles.Batch295.valid11826
  · exact MergedCutProfiles.Batch295.valid11827
  · exact MergedCutProfiles.Batch295.valid11828
  · exact MergedCutProfiles.Batch295.valid11829
  · exact MergedCutProfiles.Batch295.valid11830
  · exact MergedCutProfiles.Batch295.valid11831
  · exact MergedCutProfiles.Batch295.valid11832
  · exact MergedCutProfiles.Batch295.valid11833
  · exact MergedCutProfiles.Batch295.valid11834
  · exact MergedCutProfiles.Batch295.valid11835
  · exact MergedCutProfiles.Batch295.valid11836
theorem numericValid1861 : retention1861.NumericValid := by decide +kernel
def certificate1861 : RatCutBinCertificate := ⟨⟨retention1861,(2414873725277091579/1000000000000000000),(233579791654726571/1000000000000000000),(17886548852311850759/1000000000000000000),(2183945909433927173/12500000000000000),(875495917754948361/500000000000000000)⟩,(494677930439098337/500000000000000000),(66280650811684817/200000000000000000),(302578791355215081/1000000000000000000),(32175779757297843/200000000000000000)⟩
theorem valid1861 : certificate1861.Valid := by decide +kernel
theorem sound1861 : certificate1861.Sound := rat_cut_bin_certificate_sound certificate1861 profilesValid1861 numericValid1861 valid1861

def retention1862 : RatCutRetentionCertificate := ⟨(531/8000),(133/2000),(2298491714197038475/9760188529515390503),(1203798080898944377/1000000000000000000),(19/10),(1976288308069474068629/1280000000000000000000),true,MergedCutProfiles.Batch295.profile11837,![MergedCutProfiles.Batch295.profile11837,MergedCutProfiles.Batch295.profile11838,MergedCutProfiles.Batch295.profile11839,MergedCutProfiles.Batch296.profile11840,MergedCutProfiles.Batch296.profile11841,MergedCutProfiles.Batch296.profile11842,MergedCutProfiles.Batch296.profile11843,MergedCutProfiles.Batch296.profile11844,MergedCutProfiles.Batch296.profile11845,MergedCutProfiles.Batch296.profile11846,MergedCutProfiles.Batch296.profile11847,MergedCutProfiles.Batch296.profile11848,MergedCutProfiles.Batch296.profile11849,MergedCutProfiles.Batch296.profile11850,MergedCutProfiles.Batch296.profile11851,MergedCutProfiles.Batch296.profile11852]⟩
theorem profilesValid1862 : retention1862.ProfilesValid := by
  change ∀ j : Fin 16, (retention1862.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch295.valid11837
  · exact MergedCutProfiles.Batch295.valid11838
  · exact MergedCutProfiles.Batch295.valid11839
  · exact MergedCutProfiles.Batch296.valid11840
  · exact MergedCutProfiles.Batch296.valid11841
  · exact MergedCutProfiles.Batch296.valid11842
  · exact MergedCutProfiles.Batch296.valid11843
  · exact MergedCutProfiles.Batch296.valid11844
  · exact MergedCutProfiles.Batch296.valid11845
  · exact MergedCutProfiles.Batch296.valid11846
  · exact MergedCutProfiles.Batch296.valid11847
  · exact MergedCutProfiles.Batch296.valid11848
  · exact MergedCutProfiles.Batch296.valid11849
  · exact MergedCutProfiles.Batch296.valid11850
  · exact MergedCutProfiles.Batch296.valid11851
  · exact MergedCutProfiles.Batch296.valid11852
theorem numericValid1862 : retention1862.NumericValid := by decide +kernel
def certificate1862 : RatCutBinCertificate := ⟨⟨retention1862,(2414873725277091579/1000000000000000000),(233579791654726571/1000000000000000000),(17886548852311850759/1000000000000000000),(2183945909433927173/12500000000000000),(148402229604527501/100000000000000000)⟩,(494677930439098337/500000000000000000),(70415056179905807/200000000000000000),(280384241446325733/1000000000000000000),(80569042760486077/500000000000000000)⟩
theorem valid1862 : certificate1862.Valid := by decide +kernel
theorem sound1862 : certificate1862.Sound := rat_cut_bin_certificate_sound certificate1862 profilesValid1862 numericValid1862 valid1862

def retention1863 : RatCutRetentionCertificate := ⟨(531/8000),(133/2000),(3972999409911804763/9760188529515390503),(91939668567881539/40000000000000000),(6/5),(59077853649417157119/51200000000000000000),true,MergedCutProfiles.Batch296.profile11853,![MergedCutProfiles.Batch296.profile11853,MergedCutProfiles.Batch296.profile11854,MergedCutProfiles.Batch296.profile11855,MergedCutProfiles.Batch296.profile11856,MergedCutProfiles.Batch296.profile11857,MergedCutProfiles.Batch296.profile11858,MergedCutProfiles.Batch296.profile11859,MergedCutProfiles.Batch296.profile11860,MergedCutProfiles.Batch296.profile11861,MergedCutProfiles.Batch296.profile11862,MergedCutProfiles.Batch296.profile11863,MergedCutProfiles.Batch296.profile11864,MergedCutProfiles.Batch296.profile11865,MergedCutProfiles.Batch296.profile11866,MergedCutProfiles.Batch296.profile11867,MergedCutProfiles.Batch296.profile11868]⟩
theorem profilesValid1863 : retention1863.ProfilesValid := by
  change ∀ j : Fin 16, (retention1863.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch296.valid11853
  · exact MergedCutProfiles.Batch296.valid11854
  · exact MergedCutProfiles.Batch296.valid11855
  · exact MergedCutProfiles.Batch296.valid11856
  · exact MergedCutProfiles.Batch296.valid11857
  · exact MergedCutProfiles.Batch296.valid11858
  · exact MergedCutProfiles.Batch296.valid11859
  · exact MergedCutProfiles.Batch296.valid11860
  · exact MergedCutProfiles.Batch296.valid11861
  · exact MergedCutProfiles.Batch296.valid11862
  · exact MergedCutProfiles.Batch296.valid11863
  · exact MergedCutProfiles.Batch296.valid11864
  · exact MergedCutProfiles.Batch296.valid11865
  · exact MergedCutProfiles.Batch296.valid11866
  · exact MergedCutProfiles.Batch296.valid11867
  · exact MergedCutProfiles.Batch296.valid11868
theorem numericValid1863 : retention1863.NumericValid := by decide +kernel
def certificate1863 : RatCutBinCertificate := ⟨⟨retention1863,(2414873725277091579/1000000000000000000),(233579791654726571/1000000000000000000),(17886548852311850759/1000000000000000000),(2183945909433927173/12500000000000000),(279000772119751681/250000000000000000)⟩,(494677930439098337/500000000000000000),(198634572094290379/500000000000000000),(235993848511864809/1000000000000000000),(81036397542242369/500000000000000000)⟩
theorem valid1863 : certificate1863.Valid := by decide +kernel
theorem sound1863 : certificate1863.Sound := rat_cut_bin_certificate_sound certificate1863 profilesValid1863 numericValid1863 valid1863

def retention1864 : RatCutRetentionCertificate := ⟨(531/8000),(133/2000),(4705240807000608254/9760188529515390503),(3972999409911804763/1000000000000000000),1,(252998033793686903323/256000000000000000000),true,MergedCutProfiles.Batch296.profile11869,![MergedCutProfiles.Batch296.profile11869,MergedCutProfiles.Batch296.profile11870,MergedCutProfiles.Batch296.profile11871,MergedCutProfiles.Batch296.profile11872,MergedCutProfiles.Batch296.profile11873,MergedCutProfiles.Batch296.profile11874,MergedCutProfiles.Batch296.profile11875,MergedCutProfiles.Batch296.profile11876,MergedCutProfiles.Batch296.profile11877,MergedCutProfiles.Batch296.profile11878,MergedCutProfiles.Batch296.profile11879,MergedCutProfiles.Batch297.profile11880,MergedCutProfiles.Batch297.profile11881,MergedCutProfiles.Batch297.profile11882,MergedCutProfiles.Batch297.profile11883,MergedCutProfiles.Batch297.profile11884]⟩
theorem profilesValid1864 : retention1864.ProfilesValid := by
  change ∀ j : Fin 16, (retention1864.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch296.valid11869
  · exact MergedCutProfiles.Batch296.valid11870
  · exact MergedCutProfiles.Batch296.valid11871
  · exact MergedCutProfiles.Batch296.valid11872
  · exact MergedCutProfiles.Batch296.valid11873
  · exact MergedCutProfiles.Batch296.valid11874
  · exact MergedCutProfiles.Batch296.valid11875
  · exact MergedCutProfiles.Batch296.valid11876
  · exact MergedCutProfiles.Batch296.valid11877
  · exact MergedCutProfiles.Batch296.valid11878
  · exact MergedCutProfiles.Batch296.valid11879
  · exact MergedCutProfiles.Batch297.valid11880
  · exact MergedCutProfiles.Batch297.valid11881
  · exact MergedCutProfiles.Batch297.valid11882
  · exact MergedCutProfiles.Batch297.valid11883
  · exact MergedCutProfiles.Batch297.valid11884
theorem numericValid1864 : retention1864.NumericValid := by decide +kernel
def certificate1864 : RatCutBinCertificate := ⟨⟨retention1864,(2414873725277091579/1000000000000000000),(233579791654726571/1000000000000000000),(17886548852311850759/1000000000000000000),(2183945909433927173/12500000000000000),(478363604741956781/500000000000000000)⟩,(494677930439098337/500000000000000000),(212535340623781603/500000000000000000),(52820202343724573/250000000000000000),(80470999569673427/500000000000000000)⟩
theorem valid1864 : certificate1864.Valid := by decide +kernel
theorem sound1864 : certificate1864.Sound := rat_cut_bin_certificate_sound certificate1864 profilesValid1864 numericValid1864 valid1864

def retention1865 : RatCutRetentionCertificate := ⟨(531/8000),(133/2000),(4847814308693533686/9760188529515390503),(2352620403500304127/500000000000000000),(11/10),(58398679299163637227391142590510167607/58815510087507603175000000000000000000),false,MergedCutProfiles.Batch297.profile11885,(fun _ => MergedCutProfiles.Batch297.profile11885)⟩
theorem profilesValid1865 : retention1865.ProfilesValid := by
  exact MergedCutProfiles.Batch297.valid11885
theorem numericValid1865 : retention1865.NumericValid := by decide +kernel
def certificate1865 : RatCutBinCertificate := ⟨⟨retention1865,(2414873725277091579/1000000000000000000),(233579791654726571/1000000000000000000),(17886548852311850759/1000000000000000000),(2183945909433927173/12500000000000000),(479107313504735359/500000000000000000)⟩,(494677930439098337/500000000000000000),(208117264130234771/500000000000000000),(218932423380163941/1000000000000000000),(20163944611745333/125000000000000000)⟩
theorem valid1865 : certificate1865.Valid := by decide +kernel
theorem sound1865 : certificate1865.Sound := rat_cut_bin_certificate_sound certificate1865 profilesValid1865 numericValid1865 valid1865

def retention1866 : RatCutRetentionCertificate := ⟨(531/8000),(133/2000),(1/2),(2423907154346766843/500000000000000000),(11/10),(59862739800152755553288813670001240477/60597678858669171075000000000000000000),false,MergedCutProfiles.Batch297.profile11886,(fun _ => MergedCutProfiles.Batch297.profile11886)⟩
theorem profilesValid1866 : retention1866.ProfilesValid := by
  exact MergedCutProfiles.Batch297.valid11886
theorem numericValid1866 : retention1866.NumericValid := by decide +kernel
def certificate1866 : RatCutBinCertificate := ⟨⟨retention1866,(2414873725277091579/1000000000000000000),(233579791654726571/1000000000000000000),(17886548852311850759/1000000000000000000),(2183945909433927173/12500000000000000),(953173808328579233/1000000000000000000)⟩,(494677930439098337/500000000000000000),(83424830640732801/200000000000000000),(218153633702602107/1000000000000000000),(6427832060594167/40000000000000000)⟩
theorem valid1866 : certificate1866.Valid := by decide +kernel
theorem sound1866 : certificate1866.Sound := rat_cut_bin_certificate_sound certificate1866 profilesValid1866 numericValid1866 valid1866

def retention1867 : RatCutRetentionCertificate := ⟨(531/8000),(133/2000),(1/2),64,1,(255418779663936458807337973009705307071/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch297.profile11886,(fun _ => MergedCutProfiles.Batch297.profile11886)⟩
theorem profilesValid1867 : retention1867.ProfilesValid := by
  exact MergedCutProfiles.Batch297.valid11886
theorem numericValid1867 : retention1867.NumericValid := by decide +kernel
def certificate1867 : RatCutBinCertificate := ⟨⟨retention1867,(2414873725277091579/1000000000000000000),(233579791654726571/1000000000000000000),(17886548852311850759/1000000000000000000),(2183945909433927173/12500000000000000),(483096600527882911/500000000000000000)⟩,(494677930439098337/500000000000000000),(372035183566413503/1000000000000000000),(52021134937601831/200000000000000000),(244912686311607941/1000000000000000000)⟩
theorem valid1867 : certificate1867.Valid := by decide +kernel
theorem sound1867 : certificate1867.Sound := rat_cut_bin_certificate_sound certificate1867 profilesValid1867 numericValid1867 valid1867

def retention1868 : RatCutRetentionCertificate := ⟨(531/8000),(133/2000),(4509760704371231443/9760188529515390503),(2881984746303996301/1000000000000000000),(5/4),(196812222105262998697245028815911470799/184447023763455763264000000000000000000),false,MergedCutProfiles.Batch297.profile11887,(fun _ => MergedCutProfiles.Batch297.profile11887)⟩
theorem profilesValid1868 : retention1868.ProfilesValid := by
  exact MergedCutProfiles.Batch297.valid11887
theorem numericValid1868 : retention1868.NumericValid := by decide +kernel
def certificate1868 : RatCutBinCertificate := ⟨⟨retention1868,(2722440657277091579/1000000000000000000),(233579791654726571/1000000000000000000),(17886548852311850759/1000000000000000000),(2183945909433927173/12500000000000000),(1022582485220188789/1000000000000000000)⟩,(987995258818487597/1000000000000000000),(93656707139555579/250000000000000000),(257552372890953291/1000000000000000000),(84684615502567523/500000000000000000)⟩
theorem valid1868 : certificate1868.Valid := by decide +kernel
theorem sound1868 : certificate1868.Sound := rat_cut_bin_certificate_sound certificate1868 profilesValid1868 numericValid1868 valid1868

def retention1869 : RatCutRetentionCertificate := ⟨(531/8000),(133/2000),(4835073880699407658/9760188529515390503),(4509760704371231443/1000000000000000000),(11/10),(1792208292178350802978456047188459237911/1803904281748492577200000000000000000000),false,MergedCutProfiles.Batch297.profile11888,(fun _ => MergedCutProfiles.Batch297.profile11888)⟩
theorem profilesValid1869 : retention1869.ProfilesValid := by
  exact MergedCutProfiles.Batch297.valid11888
theorem numericValid1869 : retention1869.NumericValid := by decide +kernel
def certificate1869 : RatCutBinCertificate := ⟨⟨retention1869,(2722440657277091579/1000000000000000000),(233579791654726571/1000000000000000000),(17886548852311850759/1000000000000000000),(2183945909433927173/12500000000000000),(477199136522135499/500000000000000000)⟩,(987995258818487597/1000000000000000000),(200695477033545823/500000000000000000),(232210315920796611/1000000000000000000),(169215958910306641/1000000000000000000)⟩
theorem valid1869 : certificate1869.Valid := by decide +kernel
theorem sound1869 : certificate1869.Sound := rat_cut_bin_certificate_sound certificate1869 profilesValid1869 numericValid1869 valid1869

def retention1870 : RatCutRetentionCertificate := ⟨(531/8000),(133/2000),(1/2),(2417536940349703829/500000000000000000),(11/10),(119398202222606967105698199783485463901/120876847017485191450000000000000000000),false,MergedCutProfiles.Batch297.profile11886,(fun _ => MergedCutProfiles.Batch297.profile11886)⟩
theorem profilesValid1870 : retention1870.ProfilesValid := by
  exact MergedCutProfiles.Batch297.valid11886
theorem numericValid1870 : retention1870.NumericValid := by decide +kernel
def certificate1870 : RatCutBinCertificate := ⟨⟨retention1870,(2722440657277091579/1000000000000000000),(233579791654726571/1000000000000000000),(17886548852311850759/1000000000000000000),(2183945909433927173/12500000000000000),(948650035452446593/1000000000000000000)⟩,(987995258818487597/1000000000000000000),(201911568576770341/500000000000000000),(45999523572058537/200000000000000000),(10527096404556869/62500000000000000)⟩
theorem valid1870 : certificate1870.Valid := by decide +kernel
theorem sound1870 : certificate1870.Sound := rat_cut_bin_certificate_sound certificate1870 profilesValid1870 numericValid1870 valid1870

def retention1871 : RatCutRetentionCertificate := ⟨(133/2000),(533/8000),(1136649052689879810/9715824122799784559),(886323062046346751/1000000000000000000),(5/2),(118311039016625891043/64000000000000000000),true,MergedCutProfiles.Batch297.profile11889,![MergedCutProfiles.Batch297.profile11889,MergedCutProfiles.Batch297.profile11890,MergedCutProfiles.Batch297.profile11891,MergedCutProfiles.Batch297.profile11892,MergedCutProfiles.Batch297.profile11893,MergedCutProfiles.Batch297.profile11894,MergedCutProfiles.Batch297.profile11895,MergedCutProfiles.Batch297.profile11896,MergedCutProfiles.Batch297.profile11897,MergedCutProfiles.Batch297.profile11898,MergedCutProfiles.Batch297.profile11899,MergedCutProfiles.Batch297.profile11900,MergedCutProfiles.Batch297.profile11901,MergedCutProfiles.Batch297.profile11902,MergedCutProfiles.Batch297.profile11903,MergedCutProfiles.Batch297.profile11904]⟩
theorem profilesValid1871 : retention1871.ProfilesValid := by
  change ∀ j : Fin 16, (retention1871.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch297.valid11889
  · exact MergedCutProfiles.Batch297.valid11890
  · exact MergedCutProfiles.Batch297.valid11891
  · exact MergedCutProfiles.Batch297.valid11892
  · exact MergedCutProfiles.Batch297.valid11893
  · exact MergedCutProfiles.Batch297.valid11894
  · exact MergedCutProfiles.Batch297.valid11895
  · exact MergedCutProfiles.Batch297.valid11896
  · exact MergedCutProfiles.Batch297.valid11897
  · exact MergedCutProfiles.Batch297.valid11898
  · exact MergedCutProfiles.Batch297.valid11899
  · exact MergedCutProfiles.Batch297.valid11900
  · exact MergedCutProfiles.Batch297.valid11901
  · exact MergedCutProfiles.Batch297.valid11902
  · exact MergedCutProfiles.Batch297.valid11903
  · exact MergedCutProfiles.Batch297.valid11904
theorem numericValid1871 : retention1871.NumericValid := by decide +kernel
def certificate1871 : RatCutBinCertificate := ⟨⟨retention1871,(2417909638712551331/1000000000000000000),(29331900029289919/125000000000000000),(8965038059610232297/500000000000000000),(43586218850587268037/250000000000000000),(17694525257522083/10000000000000000)⟩,(494667213896005769/500000000000000000),(82436707467919397/250000000000000000),(152205932788597791/500000000000000000),(805804214766441/5000000000000000)⟩
theorem valid1871 : certificate1871.Valid := by decide +kernel
theorem sound1871 : certificate1871.Sound := rat_cut_bin_certificate_sound certificate1871 profilesValid1871 numericValid1871 valid1871

def certificates : List RatCutBinCertificate := [certificate1860,certificate1861,certificate1862,certificate1863,certificate1864,certificate1865,certificate1866,certificate1867,certificate1868,certificate1869,certificate1870,certificate1871]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1860,List.forall_mem_cons.mpr ⟨sound1861,List.forall_mem_cons.mpr ⟨sound1862,List.forall_mem_cons.mpr ⟨sound1863,List.forall_mem_cons.mpr ⟨sound1864,List.forall_mem_cons.mpr ⟨sound1865,List.forall_mem_cons.mpr ⟨sound1866,List.forall_mem_cons.mpr ⟨sound1867,List.forall_mem_cons.mpr ⟨sound1868,List.forall_mem_cons.mpr ⟨sound1869,List.forall_mem_cons.mpr ⟨sound1870,List.forall_mem_cons.mpr ⟨sound1871,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch155
