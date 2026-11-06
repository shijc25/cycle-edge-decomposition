import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch381
import Cycle12.MergedCutProfiles.Batch382
import Cycle12.MergedCutProfiles.Batch498
import Cycle12.MergedCutProfiles.Batch499
import Cycle12.MergedCutProfiles.Batch613
import Cycle12.MergedCutProfiles.Batch614
import Cycle12.MergedCutProfiles.Batch698
import Cycle12.MergedCutProfiles.Batch699

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch417

def retention5004 : RatCutRetentionCertificate := ⟨(51/1000),(13/250),(10318274047289888517/435902475717329878669),(3569514077661618261/1000000000000000000),(31/20),(4227446706753588448742147142778672186653/1903740841419529739200000000000000000000),false,MergedCutProfiles.Batch698.profile27941,(fun _ => MergedCutProfiles.Batch698.profile27941)⟩
theorem profilesValid5004 : retention5004.ProfilesValid := by
  exact MergedCutProfiles.Batch698.valid27941
theorem numericValid5004 : retention5004.NumericValid := by decide +kernel
def certificate5004 : RatCutBinCertificate := ⟨⟨retention5004,(954973606390364433/500000000000000000),(65444215677591123/500000000000000000),(3387039325050602467/250000000000000000),(11879850903099233585143/500000000000000000),(547999833138969453/250000000000000000)⟩,(499964839993540811/500000000000000000),(90540374385171317/125000000000000000),(42069902393373783/1000000000000000000),(23689940226902933/500000000000000000)⟩
theorem valid5004 : certificate5004.Valid := by decide +kernel
theorem sound5004 : certificate5004.Sound := rat_cut_bin_certificate_sound certificate5004 profilesValid5004 numericValid5004 valid5004

def retention5005 : RatCutRetentionCertificate := ⟨(51/1000),(13/250),(1/40),(10318274047289888517/250000000000000000),(21/20),(572063847730714900271388280507173240881/257956851182247212925000000000000000000),false,MergedCutProfiles.Batch698.profile27942,(fun _ => MergedCutProfiles.Batch698.profile27942)⟩
theorem profilesValid5005 : retention5005.ProfilesValid := by
  exact MergedCutProfiles.Batch698.valid27942
theorem numericValid5005 : retention5005.NumericValid := by decide +kernel
def certificate5005 : RatCutBinCertificate := ⟨⟨retention5005,(954973606390364433/500000000000000000),(65444215677591123/500000000000000000),(3387039325050602467/250000000000000000),(11879850903099233585143/500000000000000000),(549574517753408577/250000000000000000)⟩,(499964839993540811/500000000000000000),(136934253344481883/200000000000000000),(55963988762242529/1000000000000000000),(55879825473871037/500000000000000000)⟩
theorem valid5005 : certificate5005.Valid := by decide +kernel
theorem sound5005 : certificate5005.Sound := rat_cut_bin_certificate_sound certificate5005 profilesValid5005 numericValid5005 valid5005

def retention5006 : RatCutRetentionCertificate := ⟨(13/250),(53/1000),(623283541052079814/1668693111133782522381),(120990572862120839/200000000000000000),4,(5546186940738016441661224812531471111/2419811457242416780000000000000000000),true,MergedCutProfiles.Batch698.profile27943,![MergedCutProfiles.Batch698.profile27943,MergedCutProfiles.Batch698.profile27944,MergedCutProfiles.Batch698.profile27945,MergedCutProfiles.Batch698.profile27946,MergedCutProfiles.Batch698.profile27947,MergedCutProfiles.Batch698.profile27948,MergedCutProfiles.Batch698.profile27949,MergedCutProfiles.Batch698.profile27950,MergedCutProfiles.Batch614.profile24560,MergedCutProfiles.Batch698.profile27951,MergedCutProfiles.Batch613.profile24550,MergedCutProfiles.Batch698.profile27952,MergedCutProfiles.Batch698.profile27953,MergedCutProfiles.Batch698.profile27954,MergedCutProfiles.Batch614.profile24570,MergedCutProfiles.Batch613.profile24551]⟩
theorem profilesValid5006 : retention5006.ProfilesValid := by
  change ∀ j : Fin 16, (retention5006.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch698.valid27943
  · exact MergedCutProfiles.Batch698.valid27944
  · exact MergedCutProfiles.Batch698.valid27945
  · exact MergedCutProfiles.Batch698.valid27946
  · exact MergedCutProfiles.Batch698.valid27947
  · exact MergedCutProfiles.Batch698.valid27948
  · exact MergedCutProfiles.Batch698.valid27949
  · exact MergedCutProfiles.Batch698.valid27950
  · exact MergedCutProfiles.Batch614.valid24560
  · exact MergedCutProfiles.Batch698.valid27951
  · exact MergedCutProfiles.Batch613.valid24550
  · exact MergedCutProfiles.Batch698.valid27952
  · exact MergedCutProfiles.Batch698.valid27953
  · exact MergedCutProfiles.Batch698.valid27954
  · exact MergedCutProfiles.Batch614.valid24570
  · exact MergedCutProfiles.Batch613.valid24551
theorem numericValid5006 : retention5006.NumericValid := by decide +kernel
def certificate5006 : RatCutBinCertificate := ⟨⟨retention5006,(964681634682956873/500000000000000000),(136712609017002193/1000000000000000000),(13779447163723159963/1000000000000000000),(23127892970843726925201/1000000000000000000),(540874647420561/244140625000000)⟩,(499963748313443067/500000000000000000),(698112656875065179/1000000000000000000),(51003253860187657/1000000000000000000),(2298502494154611/100000000000000000)⟩
theorem valid5006 : certificate5006.Valid := by decide +kernel
theorem sound5006 : certificate5006.Sound := rat_cut_bin_certificate_sound certificate5006 profilesValid5006 numericValid5006 valid5006

def retention5007 : RatCutRetentionCertificate := ⟨(13/250),(53/1000),(1093441681000000000/1668693111133782522381),(311641770526039907/500000000000000000),4,(59379914383850544871/25600000000000000000),true,MergedCutProfiles.Batch698.profile27944,![MergedCutProfiles.Batch698.profile27944,MergedCutProfiles.Batch698.profile27955,MergedCutProfiles.Batch698.profile27947,MergedCutProfiles.Batch698.profile27949,MergedCutProfiles.Batch614.profile24560,MergedCutProfiles.Batch613.profile24550,MergedCutProfiles.Batch698.profile27952,MergedCutProfiles.Batch698.profile27954,MergedCutProfiles.Batch613.profile24551,MergedCutProfiles.Batch614.profile24561,MergedCutProfiles.Batch698.profile27956,MergedCutProfiles.Batch698.profile27957,MergedCutProfiles.Batch698.profile27958,MergedCutProfiles.Batch698.profile27959,MergedCutProfiles.Batch498.profile19957,MergedCutProfiles.Batch699.profile27960]⟩
theorem profilesValid5007 : retention5007.ProfilesValid := by
  change ∀ j : Fin 16, (retention5007.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch698.valid27944
  · exact MergedCutProfiles.Batch698.valid27955
  · exact MergedCutProfiles.Batch698.valid27947
  · exact MergedCutProfiles.Batch698.valid27949
  · exact MergedCutProfiles.Batch614.valid24560
  · exact MergedCutProfiles.Batch613.valid24550
  · exact MergedCutProfiles.Batch698.valid27952
  · exact MergedCutProfiles.Batch698.valid27954
  · exact MergedCutProfiles.Batch613.valid24551
  · exact MergedCutProfiles.Batch614.valid24561
  · exact MergedCutProfiles.Batch698.valid27956
  · exact MergedCutProfiles.Batch698.valid27957
  · exact MergedCutProfiles.Batch698.valid27958
  · exact MergedCutProfiles.Batch698.valid27959
  · exact MergedCutProfiles.Batch498.valid19957
  · exact MergedCutProfiles.Batch699.valid27960
theorem numericValid5007 : retention5007.NumericValid := by decide +kernel
def certificate5007 : RatCutBinCertificate := ⟨⟨retention5007,(964681634682956873/500000000000000000),(136712609017002193/1000000000000000000),(13779447163723159963/1000000000000000000),(23127892970843726925201/1000000000000000000),(1121479555975600217/500000000000000000)⟩,(499963748313443067/500000000000000000),(135244188649643967/200000000000000000),(59217473866230609/1000000000000000000),(13553058459737953/500000000000000000)⟩
theorem valid5007 : certificate5007.Valid := by decide +kernel
theorem sound5007 : certificate5007.Sound := rat_cut_bin_certificate_sound certificate5007 profilesValid5007 numericValid5007 valid5007

def retention5008 : RatCutRetentionCertificate := ⟨(13/250),(53/1000),(2077647598796668802/1668693111133782522381),(1093441681/1000000000),(29/10),(2631389081100123593840627777282344991/1093441681000000000000000000000000000),true,MergedCutProfiles.Batch698.profile27955,![MergedCutProfiles.Batch698.profile27955,MergedCutProfiles.Batch699.profile27961,MergedCutProfiles.Batch698.profile27951,MergedCutProfiles.Batch699.profile27962,MergedCutProfiles.Batch699.profile27963,MergedCutProfiles.Batch699.profile27964,MergedCutProfiles.Batch698.profile27958,MergedCutProfiles.Batch613.profile24553,MergedCutProfiles.Batch699.profile27965,MergedCutProfiles.Batch699.profile27966,MergedCutProfiles.Batch614.profile24562,MergedCutProfiles.Batch699.profile27967,MergedCutProfiles.Batch613.profile24555,MergedCutProfiles.Batch699.profile27968,MergedCutProfiles.Batch499.profile19994,MergedCutProfiles.Batch613.profile24556]⟩
theorem profilesValid5008 : retention5008.ProfilesValid := by
  change ∀ j : Fin 16, (retention5008.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch698.valid27955
  · exact MergedCutProfiles.Batch699.valid27961
  · exact MergedCutProfiles.Batch698.valid27951
  · exact MergedCutProfiles.Batch699.valid27962
  · exact MergedCutProfiles.Batch699.valid27963
  · exact MergedCutProfiles.Batch699.valid27964
  · exact MergedCutProfiles.Batch698.valid27958
  · exact MergedCutProfiles.Batch613.valid24553
  · exact MergedCutProfiles.Batch699.valid27965
  · exact MergedCutProfiles.Batch699.valid27966
  · exact MergedCutProfiles.Batch614.valid24562
  · exact MergedCutProfiles.Batch699.valid27967
  · exact MergedCutProfiles.Batch613.valid24555
  · exact MergedCutProfiles.Batch699.valid27968
  · exact MergedCutProfiles.Batch499.valid19994
  · exact MergedCutProfiles.Batch613.valid24556
theorem numericValid5008 : retention5008.NumericValid := by decide +kernel
def certificate5008 : RatCutBinCertificate := ⟨⟨retention5008,(964681634682956873/500000000000000000),(136712609017002193/1000000000000000000),(13779447163723159963/1000000000000000000),(23127892970843726925201/1000000000000000000),(587751869041096633/250000000000000000)⟩,(499963748313443067/500000000000000000),(464800659223453159/1000000000000000000),(179093699458209549/1000000000000000000),(115618542542888079/1000000000000000000)⟩
theorem valid5008 : certificate5008.Valid := by decide +kernel
theorem sound5008 : certificate5008.Sound := rat_cut_bin_certificate_sound certificate5008 profilesValid5008 numericValid5008 valid5008

def retention5009 : RatCutRetentionCertificate := ⟨(13/250),(53/1000),(64000000000000000000/1668693111133782522381),(1038823799398334401/500000000000000000),(37/20),(1366047862573281562873/640000000000000000000),true,MergedCutProfiles.Batch614.profile24573,![MergedCutProfiles.Batch614.profile24573,MergedCutProfiles.Batch699.profile27969,MergedCutProfiles.Batch699.profile27970,MergedCutProfiles.Batch699.profile27971,MergedCutProfiles.Batch499.profile19980,MergedCutProfiles.Batch381.profile15268,MergedCutProfiles.Batch382.profile15280,MergedCutProfiles.Batch699.profile27972,MergedCutProfiles.Batch699.profile27973,MergedCutProfiles.Batch699.profile27974,MergedCutProfiles.Batch699.profile27975,MergedCutProfiles.Batch381.profile15275,MergedCutProfiles.Batch699.profile27976,MergedCutProfiles.Batch382.profile15282,MergedCutProfiles.Batch699.profile27977,MergedCutProfiles.Batch699.profile27978]⟩
theorem profilesValid5009 : retention5009.ProfilesValid := by
  change ∀ j : Fin 16, (retention5009.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch614.valid24573
  · exact MergedCutProfiles.Batch699.valid27969
  · exact MergedCutProfiles.Batch699.valid27970
  · exact MergedCutProfiles.Batch699.valid27971
  · exact MergedCutProfiles.Batch499.valid19980
  · exact MergedCutProfiles.Batch381.valid15268
  · exact MergedCutProfiles.Batch382.valid15280
  · exact MergedCutProfiles.Batch699.valid27972
  · exact MergedCutProfiles.Batch699.valid27973
  · exact MergedCutProfiles.Batch699.valid27974
  · exact MergedCutProfiles.Batch699.valid27975
  · exact MergedCutProfiles.Batch381.valid15275
  · exact MergedCutProfiles.Batch699.valid27976
  · exact MergedCutProfiles.Batch382.valid15282
  · exact MergedCutProfiles.Batch699.valid27977
  · exact MergedCutProfiles.Batch699.valid27978
theorem numericValid5009 : retention5009.NumericValid := by decide +kernel
def certificate5009 : RatCutBinCertificate := ⟨⟨retention5009,(964681634682956873/500000000000000000),(136712609017002193/1000000000000000000),(13779447163723159963/1000000000000000000),(23127892970843726925201/1000000000000000000),(131189796731304273/62500000000000000)⟩,(499963748313443067/500000000000000000),(393746760157206949/1000000000000000000),(239261005289758069/1000000000000000000),(26197526793826367/125000000000000000)⟩
theorem valid5009 : certificate5009.Valid := by decide +kernel
theorem sound5009 : certificate5009.Sound := rat_cut_bin_certificate_sound certificate5009 profilesValid5009 numericValid5009 valid5009

def retention5010 : RatCutRetentionCertificate := ⟨(13/250),(53/1000),(1/2),64,1,(15962312511554171806365804663307544671/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch382.profile15294,(fun _ => MergedCutProfiles.Batch382.profile15294)⟩
theorem profilesValid5010 : retention5010.ProfilesValid := by
  exact MergedCutProfiles.Batch382.valid15294
theorem numericValid5010 : retention5010.NumericValid := by decide +kernel
def certificate5010 : RatCutBinCertificate := ⟨⟨retention5010,(964681634682956873/500000000000000000),(136712609017002193/1000000000000000000),(13779447163723159963/1000000000000000000),(23127892970843726925201/1000000000000000000),(978502377172694601/1000000000000000000)⟩,(499963748313443067/500000000000000000),(27607449473837081/50000000000000000),(11990908984320553/100000000000000000),(115555986795311239/1000000000000000000)⟩
theorem valid5010 : certificate5010.Valid := by decide +kernel
theorem sound5010 : certificate5010.Sound := rat_cut_bin_certificate_sound certificate5010 profilesValid5010 numericValid5010 valid5010

def retention5011 : RatCutRetentionCertificate := ⟨(13/250),(53/1000),(64000000000000000000/1668693111133782522381),(9734184480236888221/250000000000000000),1,(375467885557226943578101967723154493/176985172367943422200000000000000000),false,MergedCutProfiles.Batch699.profile27979,(fun _ => MergedCutProfiles.Batch699.profile27979)⟩
theorem profilesValid5011 : retention5011.ProfilesValid := by
  exact MergedCutProfiles.Batch699.valid27979
theorem numericValid5011 : retention5011.NumericValid := by decide +kernel
def certificate5011 : RatCutBinCertificate := ⟨⟨retention5011,(868607811182956873/500000000000000000),(136712609017002193/1000000000000000000),(13779447163723159963/1000000000000000000),(23127892970843726925201/1000000000000000000),(32878585047520491/15625000000000000)⟩,(499967358698727103/500000000000000000),(1769320951870337/100000000000000000),(440522211117729267/500000000000000000),(879374779158786873/500000000000000000)⟩
theorem valid5011 : certificate5011.Valid := by decide +kernel
theorem sound5011 : certificate5011.Sound := rat_cut_bin_certificate_sound certificate5011 profilesValid5011 numericValid5011 valid5011

def retention5012 : RatCutRetentionCertificate := ⟨(13/250),(53/1000),(1/2),64,1,(15962312511554171806365804663307544671/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch382.profile15294,(fun _ => MergedCutProfiles.Batch382.profile15294)⟩
theorem profilesValid5012 : retention5012.ProfilesValid := by
  exact MergedCutProfiles.Batch382.valid15294
theorem numericValid5012 : retention5012.NumericValid := by decide +kernel
def certificate5012 : RatCutBinCertificate := ⟨⟨retention5012,(868607811182956873/500000000000000000),(136712609017002193/1000000000000000000),(13779447163723159963/1000000000000000000),(23127892970843726925201/1000000000000000000),(122551095971749957/125000000000000000)⟩,(499967358698727103/500000000000000000),(4746817556477713/125000000000000000),(821422687709770253/1000000000000000000),(198281749762247903/250000000000000000)⟩
theorem valid5012 : certificate5012.Valid := by decide +kernel
theorem sound5012 : certificate5012.Sound := rat_cut_bin_certificate_sound certificate5012 profilesValid5012 numericValid5012 valid5012

def retention5013 : RatCutRetentionCertificate := ⟨(13/250),(53/1000),(730483739911840732/1668693111133782522381),(723251227635485873/1000000000000000000),4,(1756106584356909704503113991938877587/723251227635485873000000000000000000),false,MergedCutProfiles.Batch699.profile27980,(fun _ => MergedCutProfiles.Batch699.profile27980)⟩
theorem profilesValid5013 : retention5013.ProfilesValid := by
  exact MergedCutProfiles.Batch699.valid27980
theorem numericValid5013 : retention5013.NumericValid := by decide +kernel
def certificate5013 : RatCutBinCertificate := ⟨⟨retention5013,(959159135682956873/500000000000000000),(136712609017002193/1000000000000000000),(13779447163723159963/1000000000000000000),(23127892970843726925201/1000000000000000000),(2351942295753607009/1000000000000000000)⟩,(499963955845201769/500000000000000000),(822008983444364607/1000000000000000000),(2109250571643357/125000000000000000),(412252911485283/50000000000000000)⟩
theorem valid5013 : certificate5013.Valid := by decide +kernel
theorem sound5013 : certificate5013.Sound := rat_cut_bin_certificate_sound certificate5013 profilesValid5013 numericValid5013 valid5013

def retention5014 : RatCutRetentionCertificate := ⟨(13/250),(53/1000),(873766281525702541/1668693111133782522381),(182620934977960183/250000000000000000),4,(1774900180018625562160296175961717271/730483739911840732000000000000000000),false,MergedCutProfiles.Batch699.profile27981,(fun _ => MergedCutProfiles.Batch699.profile27981)⟩
theorem profilesValid5014 : retention5014.ProfilesValid := by
  exact MergedCutProfiles.Batch699.valid27981
theorem numericValid5014 : retention5014.NumericValid := by decide +kernel
def certificate5014 : RatCutBinCertificate := ⟨⟨retention5014,(959159135682956873/500000000000000000),(136712609017002193/1000000000000000000),(13779447163723159963/1000000000000000000),(23127892970843726925201/1000000000000000000),(470725915243403393/200000000000000000)⟩,(499963955845201769/500000000000000000),(819564620350677177/1000000000000000000),(216959341870093/12500000000000000),(8500219570734887/1000000000000000000)⟩
theorem valid5014 : certificate5014.Valid := by decide +kernel
theorem sound5014 : certificate5014.Sound := rat_cut_bin_certificate_sound certificate5014 profilesValid5014 numericValid5014 valid5014

def retention5015 : RatCutRetentionCertificate := ⟨(13/250),(53/1000),(3381443348407215257/1668693111133782522381),(873766281525702541/1000000000000000000),(73/20),(3373522688189900682222269545095499489711/1398026050441124065600000000000000000000),false,MergedCutProfiles.Batch699.profile27982,(fun _ => MergedCutProfiles.Batch699.profile27982)⟩
theorem profilesValid5015 : retention5015.ProfilesValid := by
  exact MergedCutProfiles.Batch699.valid27982
theorem numericValid5015 : retention5015.NumericValid := by decide +kernel
def certificate5015 : RatCutBinCertificate := ⟨⟨retention5015,(959159135682956873/500000000000000000),(136712609017002193/1000000000000000000),(13779447163723159963/1000000000000000000),(23127892970843726925201/1000000000000000000),(2343592382536382797/1000000000000000000)⟩,(499963955845201769/500000000000000000),(792524326402022631/1000000000000000000),(23188345172496091/1000000000000000000),(12392559464902659/1000000000000000000)⟩
theorem valid5015 : certificate5015.Valid := by decide +kernel
theorem sound5015 : certificate5015.Sound := rat_cut_bin_certificate_sound certificate5015 profilesValid5015 numericValid5015 valid5015

def certificates : List RatCutBinCertificate := [certificate5004,certificate5005,certificate5006,certificate5007,certificate5008,certificate5009,certificate5010,certificate5011,certificate5012,certificate5013,certificate5014,certificate5015]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound5004,List.forall_mem_cons.mpr ⟨sound5005,List.forall_mem_cons.mpr ⟨sound5006,List.forall_mem_cons.mpr ⟨sound5007,List.forall_mem_cons.mpr ⟨sound5008,List.forall_mem_cons.mpr ⟨sound5009,List.forall_mem_cons.mpr ⟨sound5010,List.forall_mem_cons.mpr ⟨sound5011,List.forall_mem_cons.mpr ⟨sound5012,List.forall_mem_cons.mpr ⟨sound5013,List.forall_mem_cons.mpr ⟨sound5014,List.forall_mem_cons.mpr ⟨sound5015,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch417
