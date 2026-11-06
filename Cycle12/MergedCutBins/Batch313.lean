import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch015
import Cycle12.MergedCutProfiles.Batch016
import Cycle12.MergedCutProfiles.Batch315
import Cycle12.MergedCutProfiles.Batch450
import Cycle12.MergedCutProfiles.Batch572
import Cycle12.MergedCutProfiles.Batch573

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch313

def retention3756 : RatCutRetentionCertificate := ⟨(13/1000),(7/500),(622580160456842530/5855369243723004773617),(70451712189030483/125000000000000000),4,(4929110024813714442810311332523488607/2254454790048975456000000000000000000),true,MergedCutProfiles.Batch572.profile22886,![MergedCutProfiles.Batch572.profile22886,MergedCutProfiles.Batch572.profile22887,MergedCutProfiles.Batch572.profile22888,MergedCutProfiles.Batch450.profile18013,MergedCutProfiles.Batch572.profile22889,MergedCutProfiles.Batch572.profile22890,MergedCutProfiles.Batch572.profile22891,MergedCutProfiles.Batch450.profile18014,MergedCutProfiles.Batch450.profile18025,MergedCutProfiles.Batch315.profile12608,MergedCutProfiles.Batch450.profile18015,MergedCutProfiles.Batch572.profile22892,MergedCutProfiles.Batch572.profile22893,MergedCutProfiles.Batch572.profile22893,MergedCutProfiles.Batch450.profile18016,MergedCutProfiles.Batch450.profile18026]⟩
theorem profilesValid3756 : retention3756.ProfilesValid := by
  change ∀ j : Fin 16, (retention3756.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch572.valid22886
  · exact MergedCutProfiles.Batch572.valid22887
  · exact MergedCutProfiles.Batch572.valid22888
  · exact MergedCutProfiles.Batch450.valid18013
  · exact MergedCutProfiles.Batch572.valid22889
  · exact MergedCutProfiles.Batch572.valid22890
  · exact MergedCutProfiles.Batch572.valid22891
  · exact MergedCutProfiles.Batch450.valid18014
  · exact MergedCutProfiles.Batch450.valid18025
  · exact MergedCutProfiles.Batch315.valid12608
  · exact MergedCutProfiles.Batch450.valid18015
  · exact MergedCutProfiles.Batch572.valid22892
  · exact MergedCutProfiles.Batch572.valid22893
  · exact MergedCutProfiles.Batch572.valid22893
  · exact MergedCutProfiles.Batch450.valid18016
  · exact MergedCutProfiles.Batch450.valid18026
theorem numericValid3756 : retention3756.NumericValid := by decide +kernel
def certificate3756 : RatCutBinCertificate := ⟨⟨retention3756,(1799555487422594913/1000000000000000000),(1008381335301397/125000000000000000),(7810502051399865481/1000000000000000000),(11486023224795442248733/250000000000000000),(544738016264714911/250000000000000000)⟩,(999961103136177459/1000000000000000000),(655497197009519987/1000000000000000000),(67646186173896143/1000000000000000000),(29676960683654327/1000000000000000000)⟩
theorem valid3756 : certificate3756.Valid := by decide +kernel
theorem sound3756 : certificate3756.Sound := rat_cut_bin_certificate_sound certificate3756 profilesValid3756 numericValid3756 valid3756

def retention3757 : RatCutRetentionCertificate := ⟨(13/1000),(7/500),(1271214302000000000/5855369243723004773617),(62258016045684253/100000000000000000),4,(293914103137788391313/128000000000000000000),true,MergedCutProfiles.Batch572.profile22887,![MergedCutProfiles.Batch572.profile22887,MergedCutProfiles.Batch450.profile18013,MergedCutProfiles.Batch572.profile22891,MergedCutProfiles.Batch450.profile18025,MergedCutProfiles.Batch315.profile12608,MergedCutProfiles.Batch572.profile22892,MergedCutProfiles.Batch572.profile22893,MergedCutProfiles.Batch450.profile18026,MergedCutProfiles.Batch450.profile18017,MergedCutProfiles.Batch015.profile611,MergedCutProfiles.Batch450.profile18018,MergedCutProfiles.Batch450.profile18027,MergedCutProfiles.Batch450.profile18019,MergedCutProfiles.Batch315.profile12609,MergedCutProfiles.Batch572.profile22894,MergedCutProfiles.Batch450.profile18020]⟩
theorem profilesValid3757 : retention3757.ProfilesValid := by
  change ∀ j : Fin 16, (retention3757.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch572.valid22887
  · exact MergedCutProfiles.Batch450.valid18013
  · exact MergedCutProfiles.Batch572.valid22891
  · exact MergedCutProfiles.Batch450.valid18025
  · exact MergedCutProfiles.Batch315.valid12608
  · exact MergedCutProfiles.Batch572.valid22892
  · exact MergedCutProfiles.Batch572.valid22893
  · exact MergedCutProfiles.Batch450.valid18026
  · exact MergedCutProfiles.Batch450.valid18017
  · exact MergedCutProfiles.Batch015.valid611
  · exact MergedCutProfiles.Batch450.valid18018
  · exact MergedCutProfiles.Batch450.valid18027
  · exact MergedCutProfiles.Batch450.valid18019
  · exact MergedCutProfiles.Batch315.valid12609
  · exact MergedCutProfiles.Batch572.valid22894
  · exact MergedCutProfiles.Batch450.valid18020
theorem numericValid3757 : retention3757.NumericValid := by decide +kernel
def certificate3757 : RatCutBinCertificate := ⟨⟨retention3757,(1799555487422594913/1000000000000000000),(1008381335301397/125000000000000000),(7810502051399865481/1000000000000000000),(11486023224795442248733/250000000000000000),(572192317748475047/250000000000000000)⟩,(999961103136177459/1000000000000000000),(583134836389608401/1000000000000000000),(102359062144218469/1000000000000000000),(47623975851811161/1000000000000000000)⟩
theorem valid3757 : certificate3757.Valid := by decide +kernel
theorem sound3757 : certificate3757.Sound := rat_cut_bin_certificate_sound certificate3757 profilesValid3757 numericValid3757 valid3757

def retention3758 : RatCutRetentionCertificate := ⟨(13/1000),(7/500),(3962513917792279619/5855369243723004773617),(635607151/500000000),(5/2),(9398969041720197077/4000000000000000000),true,MergedCutProfiles.Batch572.profile22891,![MergedCutProfiles.Batch572.profile22891,MergedCutProfiles.Batch572.profile22892,MergedCutProfiles.Batch015.profile611,MergedCutProfiles.Batch450.profile18027,MergedCutProfiles.Batch572.profile22894,MergedCutProfiles.Batch450.profile18021,MergedCutProfiles.Batch315.profile12620,MergedCutProfiles.Batch315.profile12610,MergedCutProfiles.Batch450.profile18024,MergedCutProfiles.Batch315.profile12621,MergedCutProfiles.Batch315.profile12612,MergedCutProfiles.Batch572.profile22895,MergedCutProfiles.Batch572.profile22896,MergedCutProfiles.Batch315.profile12613,MergedCutProfiles.Batch572.profile22897,MergedCutProfiles.Batch015.profile615]⟩
theorem profilesValid3758 : retention3758.ProfilesValid := by
  change ∀ j : Fin 16, (retention3758.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch572.valid22891
  · exact MergedCutProfiles.Batch572.valid22892
  · exact MergedCutProfiles.Batch015.valid611
  · exact MergedCutProfiles.Batch450.valid18027
  · exact MergedCutProfiles.Batch572.valid22894
  · exact MergedCutProfiles.Batch450.valid18021
  · exact MergedCutProfiles.Batch315.valid12620
  · exact MergedCutProfiles.Batch315.valid12610
  · exact MergedCutProfiles.Batch450.valid18024
  · exact MergedCutProfiles.Batch315.valid12621
  · exact MergedCutProfiles.Batch315.valid12612
  · exact MergedCutProfiles.Batch572.valid22895
  · exact MergedCutProfiles.Batch572.valid22896
  · exact MergedCutProfiles.Batch315.valid12613
  · exact MergedCutProfiles.Batch572.valid22897
  · exact MergedCutProfiles.Batch015.valid615
theorem numericValid3758 : retention3758.NumericValid := by decide +kernel
def certificate3758 : RatCutBinCertificate := ⟨⟨retention3758,(1799555487422594913/1000000000000000000),(1008381335301397/125000000000000000),(7810502051399865481/1000000000000000000),(11486023224795442248733/250000000000000000),(117254779907232517/50000000000000000)⟩,(999961103136177459/1000000000000000000),(374395798727729169/1000000000000000000),(257779255583348511/1000000000000000000),(186691654883993229/1000000000000000000)⟩
theorem valid3758 : certificate3758.Valid := by decide +kernel
theorem sound3758 : certificate3758.Sound := rat_cut_bin_certificate_sound certificate3758 profilesValid3758 numericValid3758 valid3758

def retention3759 : RatCutRetentionCertificate := ⟨(13/1000),(7/500),(64000000000000000000/5855369243723004773617),(3962513917792279619/1000000000000000000),(13/10),(703085100035520710403/320000000000000000000),true,MergedCutProfiles.Batch015.profile615,![MergedCutProfiles.Batch015.profile615,MergedCutProfiles.Batch016.profile640,MergedCutProfiles.Batch315.profile12624,MergedCutProfiles.Batch016.profile643,MergedCutProfiles.Batch572.profile22898,MergedCutProfiles.Batch016.profile645,MergedCutProfiles.Batch572.profile22899,MergedCutProfiles.Batch016.profile648,MergedCutProfiles.Batch572.profile22900,MergedCutProfiles.Batch016.profile651,MergedCutProfiles.Batch572.profile22901,MergedCutProfiles.Batch450.profile18037,MergedCutProfiles.Batch572.profile22902,MergedCutProfiles.Batch572.profile22903,MergedCutProfiles.Batch572.profile22904,MergedCutProfiles.Batch450.profile18038]⟩
theorem profilesValid3759 : retention3759.ProfilesValid := by
  change ∀ j : Fin 16, (retention3759.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch015.valid615
  · exact MergedCutProfiles.Batch016.valid640
  · exact MergedCutProfiles.Batch315.valid12624
  · exact MergedCutProfiles.Batch016.valid643
  · exact MergedCutProfiles.Batch572.valid22898
  · exact MergedCutProfiles.Batch016.valid645
  · exact MergedCutProfiles.Batch572.valid22899
  · exact MergedCutProfiles.Batch016.valid648
  · exact MergedCutProfiles.Batch572.valid22900
  · exact MergedCutProfiles.Batch016.valid651
  · exact MergedCutProfiles.Batch572.valid22901
  · exact MergedCutProfiles.Batch450.valid18037
  · exact MergedCutProfiles.Batch572.valid22902
  · exact MergedCutProfiles.Batch572.valid22903
  · exact MergedCutProfiles.Batch572.valid22904
  · exact MergedCutProfiles.Batch450.valid18038
theorem numericValid3759 : retention3759.NumericValid := by decide +kernel
def certificate3759 : RatCutBinCertificate := ⟨⟨retention3759,(1799555487422594913/1000000000000000000),(1008381335301397/125000000000000000),(7810502051399865481/1000000000000000000),(11486023224795442248733/250000000000000000),(2194724673273731727/1000000000000000000)⟩,(999961103136177459/1000000000000000000),(52880317381363249/200000000000000000),(383809990590111649/1000000000000000000),(48800396297766677/100000000000000000)⟩
theorem valid3759 : certificate3759.Valid := by decide +kernel
theorem sound3759 : certificate3759.Sound := rat_cut_bin_certificate_sound certificate3759 profilesValid3759 numericValid3759 valid3759

def retention3760 : RatCutRetentionCertificate := ⟨(13/1000),(7/500),(1/2),64,1,(255369632393373974456752157088663284991/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch016.profile655,(fun _ => MergedCutProfiles.Batch016.profile655)⟩
theorem profilesValid3760 : retention3760.ProfilesValid := by
  exact MergedCutProfiles.Batch016.valid655
theorem numericValid3760 : retention3760.NumericValid := by decide +kernel
def certificate3760 : RatCutBinCertificate := ⟨⟨retention3760,(1799555487422594913/1000000000000000000),(1008381335301397/125000000000000000),(7810502051399865481/1000000000000000000),(11486023224795442248733/250000000000000000),(995678961720048089/1000000000000000000)⟩,(999961103136177459/1000000000000000000),(90064421689678127/200000000000000000),(47603542463333941/250000000000000000),(186679678356641353/1000000000000000000)⟩
theorem valid3760 : certificate3760.Valid := by decide +kernel
theorem sound3760 : certificate3760.Sound := rat_cut_bin_certificate_sound certificate3760 profilesValid3760 numericValid3760 valid3760

def retention3761 : RatCutRetentionCertificate := ⟨(13/1000),(7/500),(64000000000000000000/5855369243723004773617),(2131843478987705177/125000000000000000),1,(149417106128276348711066628817637096199/68218991327606565664000000000000000000),false,MergedCutProfiles.Batch572.profile22905,(fun _ => MergedCutProfiles.Batch572.profile22905)⟩
theorem profilesValid3761 : retention3761.ProfilesValid := by
  exact MergedCutProfiles.Batch572.valid22905
theorem numericValid3761 : retention3761.NumericValid := by decide +kernel
def certificate3761 : RatCutBinCertificate := ⟨⟨retention3761,(1773036194422594913/1000000000000000000),(1008381335301397/125000000000000000),(7810502051399865481/1000000000000000000),(11486023224795442248733/250000000000000000),(437685094797954867/200000000000000000)⟩,(249990419085766881/250000000000000000),(16351313685944653/500000000000000000),(836435040930594423/1000000000000000000),(811120646611236647/500000000000000000)⟩
theorem valid3761 : certificate3761.Valid := by decide +kernel
theorem sound3761 : certificate3761.Sound := rat_cut_bin_certificate_sound certificate3761 profilesValid3761 numericValid3761 valid3761

def retention3762 : RatCutRetentionCertificate := ⟨(13/1000),(7/500),(1/2),64,1,(255369632393373974456752157088663284991/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch016.profile655,(fun _ => MergedCutProfiles.Batch016.profile655)⟩
theorem profilesValid3762 : retention3762.ProfilesValid := by
  exact MergedCutProfiles.Batch016.valid655
theorem numericValid3762 : retention3762.NumericValid := by decide +kernel
def certificate3762 : RatCutBinCertificate := ⟨⟨retention3762,(1773036194422594913/1000000000000000000),(1008381335301397/125000000000000000),(7810502051399865481/1000000000000000000),(11486023224795442248733/250000000000000000),(124463294010299063/125000000000000000)⟩,(249990419085766881/250000000000000000),(561530253885251/7812500000000000),(366070535541601677/500000000000000000),(717801833571762829/1000000000000000000)⟩
theorem valid3762 : certificate3762.Valid := by decide +kernel
theorem sound3762 : certificate3762.Sound := rat_cut_bin_certificate_sound certificate3762 profilesValid3762 numericValid3762 valid3762

def retention3763 : RatCutRetentionCertificate := ⟨(7/500),(29/2000),(580907865820714025/5445927406376945481761),(112764690283851811/200000000000000000),4,(1233191168163800299001773653231201171/563823451419259055000000000000000000),true,MergedCutProfiles.Batch572.profile22906,![MergedCutProfiles.Batch572.profile22906,MergedCutProfiles.Batch572.profile22907,MergedCutProfiles.Batch572.profile22908,MergedCutProfiles.Batch572.profile22909,MergedCutProfiles.Batch572.profile22910,MergedCutProfiles.Batch572.profile22911,MergedCutProfiles.Batch572.profile22912,MergedCutProfiles.Batch572.profile22913,MergedCutProfiles.Batch572.profile22914,MergedCutProfiles.Batch572.profile22915,MergedCutProfiles.Batch572.profile22916,MergedCutProfiles.Batch572.profile22917,MergedCutProfiles.Batch572.profile22918,MergedCutProfiles.Batch572.profile22918,MergedCutProfiles.Batch572.profile22919,MergedCutProfiles.Batch573.profile22920]⟩
theorem profilesValid3763 : retention3763.ProfilesValid := by
  change ∀ j : Fin 16, (retention3763.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch572.valid22906
  · exact MergedCutProfiles.Batch572.valid22907
  · exact MergedCutProfiles.Batch572.valid22908
  · exact MergedCutProfiles.Batch572.valid22909
  · exact MergedCutProfiles.Batch572.valid22910
  · exact MergedCutProfiles.Batch572.valid22911
  · exact MergedCutProfiles.Batch572.valid22912
  · exact MergedCutProfiles.Batch572.valid22913
  · exact MergedCutProfiles.Batch572.valid22914
  · exact MergedCutProfiles.Batch572.valid22915
  · exact MergedCutProfiles.Batch572.valid22916
  · exact MergedCutProfiles.Batch572.valid22917
  · exact MergedCutProfiles.Batch572.valid22918
  · exact MergedCutProfiles.Batch572.valid22918
  · exact MergedCutProfiles.Batch572.valid22919
  · exact MergedCutProfiles.Batch573.valid22920
theorem numericValid3763 : retention3763.NumericValid := by decide +kernel
def certificate3763 : RatCutBinCertificate := ⟨⟨retention3763,(1802076669453891259/1000000000000000000),(4334189134333581/500000000000000000),(395473373618377527/50000000000000000),(43173931529598022123071/1000000000000000000),(217929387734628729/100000000000000000)⟩,(24998964919475563/25000000000000000),(131820865195041643/200000000000000000),(33066290671034071/500000000000000000),(29018608484572237/1000000000000000000)⟩
theorem valid3763 : certificate3763.Valid := by decide +kernel
theorem sound3763 : certificate3763.Sound := rat_cut_bin_certificate_sound certificate3763 profilesValid3763 numericValid3763 valid3763

def retention3764 : RatCutRetentionCertificate := ⟨(7/500),(29/2000),(1271606070000000000/5445927406376945481761),(23236314632828561/40000000000000000),4,(568964836097861886121/256000000000000000000),true,MergedCutProfiles.Batch572.profile22907,![MergedCutProfiles.Batch572.profile22907,MergedCutProfiles.Batch572.profile22910,MergedCutProfiles.Batch572.profile22912,MergedCutProfiles.Batch572.profile22914,MergedCutProfiles.Batch572.profile22916,MergedCutProfiles.Batch572.profile22918,MergedCutProfiles.Batch572.profile22919,MergedCutProfiles.Batch573.profile22921,MergedCutProfiles.Batch573.profile22922,MergedCutProfiles.Batch573.profile22923,MergedCutProfiles.Batch573.profile22924,MergedCutProfiles.Batch573.profile22925,MergedCutProfiles.Batch573.profile22926,MergedCutProfiles.Batch573.profile22927,MergedCutProfiles.Batch573.profile22928,MergedCutProfiles.Batch573.profile22929]⟩
theorem profilesValid3764 : retention3764.ProfilesValid := by
  change ∀ j : Fin 16, (retention3764.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch572.valid22907
  · exact MergedCutProfiles.Batch572.valid22910
  · exact MergedCutProfiles.Batch572.valid22912
  · exact MergedCutProfiles.Batch572.valid22914
  · exact MergedCutProfiles.Batch572.valid22916
  · exact MergedCutProfiles.Batch572.valid22918
  · exact MergedCutProfiles.Batch572.valid22919
  · exact MergedCutProfiles.Batch573.valid22921
  · exact MergedCutProfiles.Batch573.valid22922
  · exact MergedCutProfiles.Batch573.valid22923
  · exact MergedCutProfiles.Batch573.valid22924
  · exact MergedCutProfiles.Batch573.valid22925
  · exact MergedCutProfiles.Batch573.valid22926
  · exact MergedCutProfiles.Batch573.valid22927
  · exact MergedCutProfiles.Batch573.valid22928
  · exact MergedCutProfiles.Batch573.valid22929
theorem numericValid3764 : retention3764.NumericValid := by decide +kernel
def certificate3764 : RatCutBinCertificate := ⟨⟨retention3764,(1802076669453891259/1000000000000000000),(4334189134333581/500000000000000000),(395473373618377527/50000000000000000),(43173931529598022123071/1000000000000000000),(1107309474498809433/500000000000000000)⟩,(24998964919475563/25000000000000000),(635397086938387177/1000000000000000000),(38223533438510209/500000000000000000),(17089624846747631/500000000000000000)⟩
theorem valid3764 : certificate3764.Valid := by decide +kernel
theorem sound3764 : certificate3764.Sound := rat_cut_bin_certificate_sound certificate3764 profilesValid3764 numericValid3764 valid3764

def retention3765 : RatCutRetentionCertificate := ⟨(7/500),(29/2000),(5134381270479107056/5445927406376945481761),(127160607/100000000),(5/2),(37516109035421840531/16000000000000000000),true,MergedCutProfiles.Batch572.profile22914,![MergedCutProfiles.Batch572.profile22914,MergedCutProfiles.Batch573.profile22921,MergedCutProfiles.Batch573.profile22925,MergedCutProfiles.Batch573.profile22929,MergedCutProfiles.Batch573.profile22930,MergedCutProfiles.Batch573.profile22931,MergedCutProfiles.Batch573.profile22932,MergedCutProfiles.Batch573.profile22933,MergedCutProfiles.Batch573.profile22934,MergedCutProfiles.Batch573.profile22935,MergedCutProfiles.Batch573.profile22936,MergedCutProfiles.Batch573.profile22937,MergedCutProfiles.Batch573.profile22938,MergedCutProfiles.Batch573.profile22939,MergedCutProfiles.Batch573.profile22940,MergedCutProfiles.Batch573.profile22941]⟩
theorem profilesValid3765 : retention3765.ProfilesValid := by
  change ∀ j : Fin 16, (retention3765.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch572.valid22914
  · exact MergedCutProfiles.Batch573.valid22921
  · exact MergedCutProfiles.Batch573.valid22925
  · exact MergedCutProfiles.Batch573.valid22929
  · exact MergedCutProfiles.Batch573.valid22930
  · exact MergedCutProfiles.Batch573.valid22931
  · exact MergedCutProfiles.Batch573.valid22932
  · exact MergedCutProfiles.Batch573.valid22933
  · exact MergedCutProfiles.Batch573.valid22934
  · exact MergedCutProfiles.Batch573.valid22935
  · exact MergedCutProfiles.Batch573.valid22936
  · exact MergedCutProfiles.Batch573.valid22937
  · exact MergedCutProfiles.Batch573.valid22938
  · exact MergedCutProfiles.Batch573.valid22939
  · exact MergedCutProfiles.Batch573.valid22940
  · exact MergedCutProfiles.Batch573.valid22941
theorem numericValid3765 : retention3765.NumericValid := by decide +kernel
def certificate3765 : RatCutBinCertificate := ⟨⟨retention3765,(1802076669453891259/1000000000000000000),(4334189134333581/500000000000000000),(395473373618377527/50000000000000000),(43173931529598022123071/1000000000000000000),(2339819351072625753/1000000000000000000)⟩,(24998964919475563/25000000000000000),(188770464383748339/500000000000000000),(127351387816710621/500000000000000000),(11509709267627403/62500000000000000)⟩
theorem valid3765 : certificate3765.Valid := by decide +kernel
theorem sound3765 : certificate3765.Sound := rat_cut_bin_certificate_sound certificate3765 profilesValid3765 numericValid3765 valid3765

def retention3766 : RatCutRetentionCertificate := ⟨(7/500),(29/2000),(64000000000000000000/5445927406376945481761),(320898829404944191/62500000000000000),(6/5),(1124865960203632144711323959629157497359/513438127047910705600000000000000000000),true,MergedCutProfiles.Batch573.profile22942,![MergedCutProfiles.Batch573.profile22942,MergedCutProfiles.Batch573.profile22943,MergedCutProfiles.Batch573.profile22944,MergedCutProfiles.Batch573.profile22945,MergedCutProfiles.Batch573.profile22946,MergedCutProfiles.Batch573.profile22947,MergedCutProfiles.Batch573.profile22948,MergedCutProfiles.Batch573.profile22949,MergedCutProfiles.Batch573.profile22950,MergedCutProfiles.Batch573.profile22951,MergedCutProfiles.Batch573.profile22952,MergedCutProfiles.Batch573.profile22953,MergedCutProfiles.Batch573.profile22954,MergedCutProfiles.Batch573.profile22955,MergedCutProfiles.Batch573.profile22956,MergedCutProfiles.Batch573.profile22957]⟩
theorem profilesValid3766 : retention3766.ProfilesValid := by
  change ∀ j : Fin 16, (retention3766.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch573.valid22942
  · exact MergedCutProfiles.Batch573.valid22943
  · exact MergedCutProfiles.Batch573.valid22944
  · exact MergedCutProfiles.Batch573.valid22945
  · exact MergedCutProfiles.Batch573.valid22946
  · exact MergedCutProfiles.Batch573.valid22947
  · exact MergedCutProfiles.Batch573.valid22948
  · exact MergedCutProfiles.Batch573.valid22949
  · exact MergedCutProfiles.Batch573.valid22950
  · exact MergedCutProfiles.Batch573.valid22951
  · exact MergedCutProfiles.Batch573.valid22952
  · exact MergedCutProfiles.Batch573.valid22953
  · exact MergedCutProfiles.Batch573.valid22954
  · exact MergedCutProfiles.Batch573.valid22955
  · exact MergedCutProfiles.Batch573.valid22956
  · exact MergedCutProfiles.Batch573.valid22957
theorem numericValid3766 : retention3766.NumericValid := by decide +kernel
def certificate3766 : RatCutBinCertificate := ⟨⟨retention3766,(1802076669453891259/1000000000000000000),(4334189134333581/500000000000000000),(395473373618377527/50000000000000000),(43173931529598022123071/1000000000000000000),(547120023643814547/250000000000000000)⟩,(24998964919475563/25000000000000000),(126104449589772413/500000000000000000),(50036715430536221/125000000000000000),(563268957015266179/1000000000000000000)⟩
theorem valid3766 : certificate3766.Valid := by decide +kernel
theorem sound3766 : certificate3766.Sound := rat_cut_bin_certificate_sound certificate3766 profilesValid3766 numericValid3766 valid3766

def retention3767 : RatCutRetentionCertificate := ⟨(7/500),(29/2000),(1/2),64,1,(15960618230641953517588502271429102831/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch573.profile22958,(fun _ => MergedCutProfiles.Batch573.profile22958)⟩
theorem profilesValid3767 : retention3767.ProfilesValid := by
  exact MergedCutProfiles.Batch573.valid22958
theorem numericValid3767 : retention3767.NumericValid := by decide +kernel
def certificate3767 : RatCutBinCertificate := ⟨⟨retention3767,(1802076669453891259/1000000000000000000),(4334189134333581/500000000000000000),(395473373618377527/50000000000000000),(43173931529598022123071/1000000000000000000),(995563654077165313/1000000000000000000)⟩,(24998964919475563/25000000000000000),(453616390985411441/1000000000000000000),(187798065558716263/1000000000000000000),(18409342148048287/100000000000000000)⟩
theorem valid3767 : certificate3767.Valid := by decide +kernel
theorem sound3767 : certificate3767.Sound := rat_cut_bin_certificate_sound certificate3767 profilesValid3767 numericValid3767 valid3767

def certificates : List RatCutBinCertificate := [certificate3756,certificate3757,certificate3758,certificate3759,certificate3760,certificate3761,certificate3762,certificate3763,certificate3764,certificate3765,certificate3766,certificate3767]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3756,List.forall_mem_cons.mpr ⟨sound3757,List.forall_mem_cons.mpr ⟨sound3758,List.forall_mem_cons.mpr ⟨sound3759,List.forall_mem_cons.mpr ⟨sound3760,List.forall_mem_cons.mpr ⟨sound3761,List.forall_mem_cons.mpr ⟨sound3762,List.forall_mem_cons.mpr ⟨sound3763,List.forall_mem_cons.mpr ⟨sound3764,List.forall_mem_cons.mpr ⟨sound3765,List.forall_mem_cons.mpr ⟨sound3766,List.forall_mem_cons.mpr ⟨sound3767,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch313
