import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch148
import Cycle12.MergedCutProfiles.Batch149
import Cycle12.MergedCutProfiles.Batch150

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch073

def retention876 : RatCutRetentionCertificate := ⟨(197/4000),(99/2000),(743775834209659001/9760316133501427926),(461334700204588299/500000000000000000),(27/10),(315614688526719467747/160000000000000000000),true,MergedCutProfiles.Batch148.profile5947,![MergedCutProfiles.Batch148.profile5947,MergedCutProfiles.Batch148.profile5948,MergedCutProfiles.Batch148.profile5949,MergedCutProfiles.Batch148.profile5950,MergedCutProfiles.Batch148.profile5951,MergedCutProfiles.Batch148.profile5952,MergedCutProfiles.Batch148.profile5953,MergedCutProfiles.Batch148.profile5954,MergedCutProfiles.Batch148.profile5955,MergedCutProfiles.Batch148.profile5956,MergedCutProfiles.Batch148.profile5957,MergedCutProfiles.Batch148.profile5958,MergedCutProfiles.Batch148.profile5959,MergedCutProfiles.Batch149.profile5960,MergedCutProfiles.Batch149.profile5961,MergedCutProfiles.Batch149.profile5962]⟩
theorem profilesValid876 : retention876.ProfilesValid := by
  change ∀ j : Fin 16, (retention876.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch148.valid5947
  · exact MergedCutProfiles.Batch148.valid5948
  · exact MergedCutProfiles.Batch148.valid5949
  · exact MergedCutProfiles.Batch148.valid5950
  · exact MergedCutProfiles.Batch148.valid5951
  · exact MergedCutProfiles.Batch148.valid5952
  · exact MergedCutProfiles.Batch148.valid5953
  · exact MergedCutProfiles.Batch148.valid5954
  · exact MergedCutProfiles.Batch148.valid5955
  · exact MergedCutProfiles.Batch148.valid5956
  · exact MergedCutProfiles.Batch148.valid5957
  · exact MergedCutProfiles.Batch148.valid5958
  · exact MergedCutProfiles.Batch148.valid5959
  · exact MergedCutProfiles.Batch149.valid5960
  · exact MergedCutProfiles.Batch149.valid5961
  · exact MergedCutProfiles.Batch149.valid5962
theorem numericValid876 : retention876.NumericValid := by decide +kernel
def certificate876 : RatCutBinCertificate := ⟨⟨retention876,(134770246555588883/62500000000000000),(7315173282470881/62500000000000000),(13154822491454154077/1000000000000000000),(128578448836555681817/500000000000000000),(1920781430598460983/1000000000000000000)⟩,(496288820713863167/500000000000000000),(94482451624867973/250000000000000000),(127162104545066009/500000000000000000),(69750913608896129/500000000000000000)⟩
theorem valid876 : certificate876.Valid := by decide +kernel
theorem sound876 : certificate876.Sound := rat_cut_bin_certificate_sound certificate876 profilesValid876 numericValid876 valid876

def retention877 : RatCutRetentionCertificate := ⟨(197/4000),(99/2000),(4624967343929083181/19520632267002855852),(743775834209659001/500000000000000000),(37/20),(990116526274316671073/640000000000000000000),true,MergedCutProfiles.Batch149.profile5963,![MergedCutProfiles.Batch149.profile5963,MergedCutProfiles.Batch148.profile5941,MergedCutProfiles.Batch148.profile5945,MergedCutProfiles.Batch149.profile5964,MergedCutProfiles.Batch149.profile5965,MergedCutProfiles.Batch149.profile5966,MergedCutProfiles.Batch149.profile5967,MergedCutProfiles.Batch149.profile5968,MergedCutProfiles.Batch149.profile5969,MergedCutProfiles.Batch149.profile5970,MergedCutProfiles.Batch149.profile5971,MergedCutProfiles.Batch149.profile5972,MergedCutProfiles.Batch149.profile5973,MergedCutProfiles.Batch149.profile5974,MergedCutProfiles.Batch149.profile5975,MergedCutProfiles.Batch149.profile5976]⟩
theorem profilesValid877 : retention877.ProfilesValid := by
  change ∀ j : Fin 16, (retention877.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch149.valid5963
  · exact MergedCutProfiles.Batch148.valid5941
  · exact MergedCutProfiles.Batch148.valid5945
  · exact MergedCutProfiles.Batch149.valid5964
  · exact MergedCutProfiles.Batch149.valid5965
  · exact MergedCutProfiles.Batch149.valid5966
  · exact MergedCutProfiles.Batch149.valid5967
  · exact MergedCutProfiles.Batch149.valid5968
  · exact MergedCutProfiles.Batch149.valid5969
  · exact MergedCutProfiles.Batch149.valid5970
  · exact MergedCutProfiles.Batch149.valid5971
  · exact MergedCutProfiles.Batch149.valid5972
  · exact MergedCutProfiles.Batch149.valid5973
  · exact MergedCutProfiles.Batch149.valid5974
  · exact MergedCutProfiles.Batch149.valid5975
  · exact MergedCutProfiles.Batch149.valid5976
theorem numericValid877 : retention877.NumericValid := by decide +kernel
def certificate877 : RatCutBinCertificate := ⟨⟨retention877,(134770246555588883/62500000000000000),(7315173282470881/62500000000000000),(13154822491454154077/1000000000000000000),(128578448836555681817/500000000000000000),(60462319477682241/40000000000000000)⟩,(496288820713863167/500000000000000000),(409541447553231691/1000000000000000000),(224852867363420617/1000000000000000000),(28087166401788571/200000000000000000)⟩
theorem valid877 : certificate877.Valid := by decide +kernel
theorem sound877 : certificate877.Sound := rat_cut_bin_certificate_sound certificate877 profilesValid877 numericValid877 valid877

def retention878 : RatCutRetentionCertificate := ⟨(197/4000),(99/2000),(4371662205643030025/9760316133501427926),(4624967343929083181/1000000000000000000),(21/20),(1369020881263860569829/1280000000000000000000),true,MergedCutProfiles.Batch149.profile5977,![MergedCutProfiles.Batch149.profile5977,MergedCutProfiles.Batch149.profile5978,MergedCutProfiles.Batch149.profile5979,MergedCutProfiles.Batch149.profile5980,MergedCutProfiles.Batch149.profile5981,MergedCutProfiles.Batch149.profile5982,MergedCutProfiles.Batch149.profile5983,MergedCutProfiles.Batch149.profile5984,MergedCutProfiles.Batch149.profile5985,MergedCutProfiles.Batch149.profile5986,MergedCutProfiles.Batch149.profile5987,MergedCutProfiles.Batch149.profile5988,MergedCutProfiles.Batch149.profile5989,MergedCutProfiles.Batch149.profile5990,MergedCutProfiles.Batch149.profile5991,MergedCutProfiles.Batch149.profile5992]⟩
theorem profilesValid878 : retention878.ProfilesValid := by
  change ∀ j : Fin 16, (retention878.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch149.valid5977
  · exact MergedCutProfiles.Batch149.valid5978
  · exact MergedCutProfiles.Batch149.valid5979
  · exact MergedCutProfiles.Batch149.valid5980
  · exact MergedCutProfiles.Batch149.valid5981
  · exact MergedCutProfiles.Batch149.valid5982
  · exact MergedCutProfiles.Batch149.valid5983
  · exact MergedCutProfiles.Batch149.valid5984
  · exact MergedCutProfiles.Batch149.valid5985
  · exact MergedCutProfiles.Batch149.valid5986
  · exact MergedCutProfiles.Batch149.valid5987
  · exact MergedCutProfiles.Batch149.valid5988
  · exact MergedCutProfiles.Batch149.valid5989
  · exact MergedCutProfiles.Batch149.valid5990
  · exact MergedCutProfiles.Batch149.valid5991
  · exact MergedCutProfiles.Batch149.valid5992
theorem numericValid878 : retention878.NumericValid := by decide +kernel
def certificate878 : RatCutBinCertificate := ⟨⟨retention878,(134770246555588883/62500000000000000),(7315173282470881/62500000000000000),(13154822491454154077/1000000000000000000),(128578448836555681817/500000000000000000),(524700438807240361/500000000000000000)⟩,(496288820713863167/500000000000000000),(477057946978589127/1000000000000000000),(2123288676257993/12500000000000000),(17455193769958273/125000000000000000)⟩
theorem valid878 : certificate878.Valid := by decide +kernel
theorem sound878 : certificate878.Sound := rat_cut_bin_certificate_sound certificate878 profilesValid878 numericValid878 valid878

def retention879 : RatCutRetentionCertificate := ⟨(197/4000),(99/2000),(9658069594354476071/19520632267002855852),(174866488225721201/20000000000000000),(21/20),(2862383356458887075965755339832373631/2854963073072999200000000000000000000),false,MergedCutProfiles.Batch149.profile5993,(fun _ => MergedCutProfiles.Batch149.profile5993)⟩
theorem profilesValid879 : retention879.ProfilesValid := by
  exact MergedCutProfiles.Batch149.valid5993
theorem numericValid879 : retention879.NumericValid := by decide +kernel
def certificate879 : RatCutBinCertificate := ⟨⟨retention879,(134770246555588883/62500000000000000),(7315173282470881/62500000000000000),(13154822491454154077/1000000000000000000),(128578448836555681817/500000000000000000),(49122664276840783/50000000000000000)⟩,(496288820713863167/500000000000000000),(3016543751659653/6250000000000000),(165759171366870113/1000000000000000000),(69822784185774539/500000000000000000)⟩
theorem valid879 : certificate879.Valid := by decide +kernel
theorem sound879 : certificate879.Sound := rat_cut_bin_certificate_sound certificate879 profilesValid879 numericValid879 valid879

def retention880 : RatCutRetentionCertificate := ⟨(197/4000),(99/2000),(812887524191501736/1626719355583571321),(9658069594354476071/1000000000000000000),(21/20),(2196858546589288111262714577449694343097/2207558764423880244800000000000000000000),false,MergedCutProfiles.Batch149.profile5994,(fun _ => MergedCutProfiles.Batch149.profile5994)⟩
theorem profilesValid880 : retention880.ProfilesValid := by
  exact MergedCutProfiles.Batch149.valid5994
theorem numericValid880 : retention880.NumericValid := by decide +kernel
def certificate880 : RatCutBinCertificate := ⟨⟨retention880,(134770246555588883/62500000000000000),(7315173282470881/62500000000000000),(13154822491454154077/1000000000000000000),(128578448836555681817/500000000000000000),(975007216274213967/1000000000000000000)⟩,(496288820713863167/500000000000000000),(6043098024751469/12500000000000000),(4129411224826319/25000000000000000),(17426863829447819/125000000000000000)⟩
theorem valid880 : certificate880.Valid := by decide +kernel
theorem sound880 : certificate880.Sound := rat_cut_bin_certificate_sound certificate880 profilesValid880 numericValid880 valid880

def retention881 : RatCutRetentionCertificate := ⟨(197/4000),(99/2000),(1/2),(304832821571813151/31250000000000000),(21/20),(970376847427932937906085885511893419751/975465029029802083200000000000000000000),false,MergedCutProfiles.Batch149.profile5995,(fun _ => MergedCutProfiles.Batch149.profile5995)⟩
theorem profilesValid881 : retention881.ProfilesValid := by
  exact MergedCutProfiles.Batch149.valid5995
theorem numericValid881 : retention881.NumericValid := by decide +kernel
def certificate881 : RatCutBinCertificate := ⟨⟨retention881,(134770246555588883/62500000000000000),(7315173282470881/62500000000000000),(13154822491454154077/1000000000000000000),(128578448836555681817/500000000000000000),(974638147057616893/1000000000000000000)⟩,(496288820713863167/500000000000000000),(483357773439997623/1000000000000000000),(165241919982849147/1000000000000000000),(139538155678403349/1000000000000000000)⟩
theorem valid881 : certificate881.Valid := by decide +kernel
theorem sound881 : certificate881.Sound := rat_cut_bin_certificate_sound certificate881 profilesValid881 numericValid881 valid881

def retention882 : RatCutRetentionCertificate := ⟨(197/4000),(99/2000),(1/2),64,1,(255393713058328124527378149748559929711/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch149.profile5995,(fun _ => MergedCutProfiles.Batch149.profile5995)⟩
theorem profilesValid882 : retention882.ProfilesValid := by
  exact MergedCutProfiles.Batch149.valid5995
theorem numericValid882 : retention882.NumericValid := by decide +kernel
def certificate882 : RatCutBinCertificate := ⟨⟨retention882,(134770246555588883/62500000000000000),(7315173282470881/62500000000000000),(13154822491454154077/1000000000000000000),(128578448836555681817/500000000000000000),(97844603344971001/100000000000000000)⟩,(496288820713863167/500000000000000000),(458416091160988443/1000000000000000000),(23003653279891349/125000000000000000),(3520461408711659/20000000000000000)⟩
theorem valid882 : certificate882.Valid := by decide +kernel
theorem sound882 : certificate882.Sound := rat_cut_bin_certificate_sound certificate882 profilesValid882 numericValid882 valid882

def retention883 : RatCutRetentionCertificate := ⟨(197/4000),(99/2000),(1471898781410177171/3253438711167142642),(3715948419915760893/1000000000000000000),(6/5),(50585196004831496443211456032153534567/46449355248947011162500000000000000000),false,MergedCutProfiles.Batch149.profile5996,(fun _ => MergedCutProfiles.Batch149.profile5996)⟩
theorem profilesValid883 : retention883.ProfilesValid := by
  exact MergedCutProfiles.Batch149.valid5996
theorem numericValid883 : retention883.NumericValid := by decide +kernel
def certificate883 : RatCutBinCertificate := ⟨⟨retention883,(158335299555588883/62500000000000000),(7315173282470881/62500000000000000),(13154822491454154077/1000000000000000000),(128578448836555681817/500000000000000000),(33187150436953259/31250000000000000)⟩,(991278335015233257/1000000000000000000),(381027265486814907/1000000000000000000),(3141539018572257/12500000000000000),(183816767894060961/1000000000000000000)⟩
theorem valid883 : certificate883.Valid := by decide +kernel
theorem sound883 : certificate883.Sound := rat_cut_bin_certificate_sound certificate883 profilesValid883 numericValid883 valid883

def retention884 : RatCutRetentionCertificate := ⟨(197/4000),(99/2000),(9658764120662208839/19520632267002855852),(4415696344230531513/500000000000000000),(21/20),(3542331775298414015005671419835629404151/3532557075384425210400000000000000000000),false,MergedCutProfiles.Batch149.profile5997,(fun _ => MergedCutProfiles.Batch149.profile5997)⟩
theorem profilesValid884 : retention884.ProfilesValid := by
  exact MergedCutProfiles.Batch149.valid5997
theorem numericValid884 : retention884.NumericValid := by decide +kernel
def certificate884 : RatCutBinCertificate := ⟨⟨retention884,(158335299555588883/62500000000000000),(7315173282470881/62500000000000000),(13154822491454154077/1000000000000000000),(128578448836555681817/500000000000000000),(244774670992212547/250000000000000000)⟩,(991278335015233257/1000000000000000000),(413284891905965527/1000000000000000000),(110764098233822279/500000000000000000),(18597835585203519/100000000000000000)⟩
theorem valid884 : certificate884.Valid := by decide +kernel
theorem sound884 : certificate884.Sound := rat_cut_bin_certificate_sound certificate884 profilesValid884 numericValid884 valid884

def retention885 : RatCutRetentionCertificate := ⟨(197/4000),(99/2000),(2438837940467207732/4880158066750713963),(9658764120662208839/1000000000000000000),(21/20),(15378055285653923102342645601370933022519/15454022593059534142400000000000000000000),false,MergedCutProfiles.Batch149.profile5998,(fun _ => MergedCutProfiles.Batch149.profile5998)⟩
theorem profilesValid885 : retention885.ProfilesValid := by
  exact MergedCutProfiles.Batch149.valid5998
theorem numericValid885 : retention885.NumericValid := by decide +kernel
def certificate885 : RatCutBinCertificate := ⟨⟨retention885,(158335299555588883/62500000000000000),(7315173282470881/62500000000000000),(13154822491454154077/1000000000000000000),(128578448836555681817/500000000000000000),(971416053102292863/1000000000000000000)⟩,(991278335015233257/1000000000000000000),(13017294844889987/31250000000000000),(109326514865416733/500000000000000000),(91844202581665261/500000000000000000)⟩
theorem valid885 : certificate885.Valid := by decide +kernel
theorem sound885 : certificate885.Sound := rat_cut_bin_certificate_sound certificate885 profilesValid885 numericValid885 valid885

def retention886 : RatCutRetentionCertificate := ⟨(197/4000),(99/2000),(1/2),(609709485116801933/62500000000000000),(21/20),(970448004357626771907419092136787166911/975535176186883092800000000000000000000),false,MergedCutProfiles.Batch149.profile5995,(fun _ => MergedCutProfiles.Batch149.profile5995)⟩
theorem profilesValid886 : retention886.ProfilesValid := by
  exact MergedCutProfiles.Batch149.valid5995
theorem numericValid886 : retention886.NumericValid := by decide +kernel
def certificate886 : RatCutBinCertificate := ⟨⟨retention886,(158335299555588883/62500000000000000),(7315173282470881/62500000000000000),(13154822491454154077/1000000000000000000),(128578448836555681817/500000000000000000),(485558505909847087/500000000000000000)⟩,(991278335015233257/1000000000000000000),(26042606660956469/62500000000000000),(109270360054004569/500000000000000000),(183694918236302941/1000000000000000000)⟩
theorem valid886 : certificate886.Valid := by decide +kernel
theorem sound886 : certificate886.Sound := rat_cut_bin_certificate_sound certificate886 profilesValid886 numericValid886 valid886

def retention887 : RatCutRetentionCertificate := ⟨(99/2000),(199/4000),(868468599062609361/19297355914231360480),(842927066034692153/1000000000000000000),(29/10),(165584504995846661279/80000000000000000000),true,MergedCutProfiles.Batch149.profile5999,![MergedCutProfiles.Batch149.profile5999,MergedCutProfiles.Batch150.profile6000,MergedCutProfiles.Batch150.profile6001,MergedCutProfiles.Batch150.profile6002,MergedCutProfiles.Batch150.profile6003,MergedCutProfiles.Batch150.profile6004,MergedCutProfiles.Batch150.profile6005,MergedCutProfiles.Batch150.profile6006,MergedCutProfiles.Batch150.profile6007,MergedCutProfiles.Batch150.profile6008,MergedCutProfiles.Batch150.profile6009,MergedCutProfiles.Batch150.profile6010,MergedCutProfiles.Batch150.profile6011,MergedCutProfiles.Batch150.profile6012,MergedCutProfiles.Batch150.profile6013,MergedCutProfiles.Batch150.profile6014]⟩
theorem profilesValid887 : retention887.ProfilesValid := by
  change ∀ j : Fin 16, (retention887.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch149.valid5999
  · exact MergedCutProfiles.Batch150.valid6000
  · exact MergedCutProfiles.Batch150.valid6001
  · exact MergedCutProfiles.Batch150.valid6002
  · exact MergedCutProfiles.Batch150.valid6003
  · exact MergedCutProfiles.Batch150.valid6004
  · exact MergedCutProfiles.Batch150.valid6005
  · exact MergedCutProfiles.Batch150.valid6006
  · exact MergedCutProfiles.Batch150.valid6007
  · exact MergedCutProfiles.Batch150.valid6008
  · exact MergedCutProfiles.Batch150.valid6009
  · exact MergedCutProfiles.Batch150.valid6010
  · exact MergedCutProfiles.Batch150.valid6011
  · exact MergedCutProfiles.Batch150.valid6012
  · exact MergedCutProfiles.Batch150.valid6013
  · exact MergedCutProfiles.Batch150.valid6014
theorem numericValid887 : retention887.NumericValid := by decide +kernel
def certificate887 : RatCutBinCertificate := ⟨⟨retention887,(1071187279941295167/500000000000000000),(29595609602345631/250000000000000000),(3302378788223152359/250000000000000000),(255273060558360408829/1000000000000000000),(10070582223042341/5000000000000000)⟩,(248145578385063119/250000000000000000),(93591090723359699/250000000000000000),(12890506906543157/50000000000000000),(34552418101708827/250000000000000000)⟩
theorem valid887 : certificate887.Valid := by decide +kernel
theorem sound887 : certificate887.Sound := rat_cut_bin_certificate_sound certificate887 profilesValid887 numericValid887 valid887

def certificates : List RatCutBinCertificate := [certificate876,certificate877,certificate878,certificate879,certificate880,certificate881,certificate882,certificate883,certificate884,certificate885,certificate886,certificate887]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound876,List.forall_mem_cons.mpr ⟨sound877,List.forall_mem_cons.mpr ⟨sound878,List.forall_mem_cons.mpr ⟨sound879,List.forall_mem_cons.mpr ⟨sound880,List.forall_mem_cons.mpr ⟨sound881,List.forall_mem_cons.mpr ⟨sound882,List.forall_mem_cons.mpr ⟨sound883,List.forall_mem_cons.mpr ⟨sound884,List.forall_mem_cons.mpr ⟨sound885,List.forall_mem_cons.mpr ⟨sound886,List.forall_mem_cons.mpr ⟨sound887,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch073
