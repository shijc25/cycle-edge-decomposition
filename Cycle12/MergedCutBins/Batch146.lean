import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch279
import Cycle12.MergedCutProfiles.Batch280
import Cycle12.MergedCutProfiles.Batch281

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch146

def retention1752 : RatCutRetentionCertificate := ⟨(521/8000),(261/4000),(1/2),(254704340694625849/50000000000000000),(11/10),(5041868817241733413563967886746779919/5094086813892516980000000000000000000),false,MergedCutProfiles.Batch279.profile11198,(fun _ => MergedCutProfiles.Batch279.profile11198)⟩
theorem profilesValid1752 : retention1752.ProfilesValid := by
  exact MergedCutProfiles.Batch279.valid11198
theorem numericValid1752 : retention1752.NumericValid := by decide +kernel
def certificate1752 : RatCutBinCertificate := ⟨⟨retention1752,(1194938032328947707/500000000000000000),(223024722628732191/1000000000000000000),(17459872792263231209/1000000000000000000),(2789993129168606837/15625000000000000),(29880058145623777/31250000000000000)⟩,(989554301967784457/1000000000000000000),(106029802665715863/250000000000000000),(21209583914242773/100000000000000000),(78883927791417233/500000000000000000)⟩
theorem valid1752 : certificate1752.Valid := by decide +kernel
theorem sound1752 : certificate1752.Sound := rat_cut_bin_certificate_sound certificate1752 profilesValid1752 numericValid1752 valid1752

def retention1753 : RatCutRetentionCertificate := ⟨(521/8000),(261/4000),(1/2),64,1,(2494302634053916259762552721939439/2500000000000000000000000000000000),false,MergedCutProfiles.Batch279.profile11198,(fun _ => MergedCutProfiles.Batch279.profile11198)⟩
theorem profilesValid1753 : retention1753.ProfilesValid := by
  exact MergedCutProfiles.Batch279.valid11198
theorem numericValid1753 : retention1753.NumericValid := by decide +kernel
def certificate1753 : RatCutBinCertificate := ⟨⟨retention1753,(1194938032328947707/500000000000000000),(223024722628732191/1000000000000000000),(17459872792263231209/1000000000000000000),(2789993129168606837/15625000000000000),(96719323392813589/100000000000000000)⟩,(989554301967784457/1000000000000000000),(38289988312384983/100000000000000000),(62380245929577653/250000000000000000),(47046751372476859/200000000000000000)⟩
theorem valid1753 : certificate1753.Valid := by decide +kernel
theorem sound1753 : certificate1753.Sound := rat_cut_bin_certificate_sound certificate1753 profilesValid1753 numericValid1753 valid1753

def retention1754 : RatCutRetentionCertificate := ⟨(521/8000),(261/4000),(4742709507660844082/10218753817620470541),(3030851824129145953/1000000000000000000),(5/4),(206716425727863764840695549748770539671/193974516744265340992000000000000000000),false,MergedCutProfiles.Batch279.profile11199,(fun _ => MergedCutProfiles.Batch279.profile11199)⟩
theorem profilesValid1754 : retention1754.ProfilesValid := by
  exact MergedCutProfiles.Batch279.valid11199
theorem numericValid1754 : retention1754.NumericValid := by decide +kernel
def certificate1754 : RatCutBinCertificate := ⟨⟨retention1754,(1352121360828947707/500000000000000000),(223024722628732191/1000000000000000000),(17459872792263231209/1000000000000000000),(2789993129168606837/15625000000000000),(1022495830318913879/1000000000000000000)⟩,(98817563202672433/100000000000000000),(378765171662902777/1000000000000000000),(253512345233687483/1000000000000000000),(84139721021142237/500000000000000000)⟩
theorem valid1754 : certificate1754.Valid := by decide +kernel
theorem sound1754 : certificate1754.Sound := rat_cut_bin_certificate_sound certificate1754 profilesValid1754 numericValid1754 valid1754

def retention1755 : RatCutRetentionCertificate := ⟨(521/8000),(261/4000),(5034481710828933776/10218753817620470541),(2371354753830422041/500000000000000000),(11/10),(474674083463537196052138012930473126719/474270950766084408200000000000000000000),false,MergedCutProfiles.Batch280.profile11200,(fun _ => MergedCutProfiles.Batch280.profile11200)⟩
theorem profilesValid1755 : retention1755.ProfilesValid := by
  exact MergedCutProfiles.Batch280.valid11200
theorem numericValid1755 : retention1755.NumericValid := by decide +kernel
def certificate1755 : RatCutBinCertificate := ⟨⟨retention1755,(1352121360828947707/500000000000000000),(223024722628732191/1000000000000000000),(17459872792263231209/1000000000000000000),(2789993129168606837/15625000000000000),(192568764474104197/200000000000000000)⟩,(98817563202672433/100000000000000000),(201115590969804567/500000000000000000),(46288850182628787/200000000000000000),(171233748694214207/1000000000000000000)⟩
theorem valid1755 : certificate1755.Valid := by decide +kernel
theorem sound1755 : certificate1755.Sound := rat_cut_bin_certificate_sound certificate1755 profilesValid1755 numericValid1755 valid1755

def retention1756 : RatCutRetentionCertificate := ⟨(521/8000),(261/4000),(5084826527937223114/10218753817620470541),(314655106926808361/62500000000000000),(11/10),(31273274765712923617877960957828236111/31465510692680836100000000000000000000),false,MergedCutProfiles.Batch280.profile11201,(fun _ => MergedCutProfiles.Batch280.profile11201)⟩
theorem profilesValid1756 : retention1756.ProfilesValid := by
  exact MergedCutProfiles.Batch280.valid11201
theorem numericValid1756 : retention1756.NumericValid := by decide +kernel
def certificate1756 : RatCutBinCertificate := ⟨⟨retention1756,(1352121360828947707/500000000000000000),(223024722628732191/1000000000000000000),(17459872792263231209/1000000000000000000),(2789993129168606837/15625000000000000),(477942463758935433/500000000000000000)⟩,(98817563202672433/100000000000000000),(405159447069642361/1000000000000000000),(45757627485345361/200000000000000000),(169633024013718981/1000000000000000000)⟩
theorem valid1756 : certificate1756.Valid := by decide +kernel
theorem sound1756 : certificate1756.Sound := rat_cut_bin_certificate_sound certificate1756 profilesValid1756 numericValid1756 valid1756

def retention1757 : RatCutRetentionCertificate := ⟨(521/8000),(261/4000),(1/2),(2542413263968611557/500000000000000000),(11/10),(503236521865595747534151974080506013351/508482652793722311400000000000000000000),false,MergedCutProfiles.Batch279.profile11198,(fun _ => MergedCutProfiles.Batch279.profile11198)⟩
theorem profilesValid1757 : retention1757.ProfilesValid := by
  exact MergedCutProfiles.Batch279.valid11198
theorem numericValid1757 : retention1757.NumericValid := by decide +kernel
def certificate1757 : RatCutBinCertificate := ⟨⟨retention1757,(1352121360828947707/500000000000000000),(223024722628732191/1000000000000000000),(17459872792263231209/1000000000000000000),(2789993129168606837/15625000000000000),(29739912576631171/31250000000000000)⟩,(98817563202672433/100000000000000000),(406950810314066553/1000000000000000000),(113586850889888511/500000000000000000),(33604194804213039/200000000000000000)⟩
theorem valid1757 : certificate1757.Valid := by decide +kernel
theorem sound1757 : certificate1757.Sound := rat_cut_bin_certificate_sound certificate1757 profilesValid1757 numericValid1757 valid1757

def retention1758 : RatCutRetentionCertificate := ⟨(261/4000),(523/8000),(739416376055719605/5085822214685245478),(231608503966701341/250000000000000000),(12/5),(567329480830128435897/320000000000000000000),true,MergedCutProfiles.Batch280.profile11202,![MergedCutProfiles.Batch280.profile11202,MergedCutProfiles.Batch280.profile11203,MergedCutProfiles.Batch280.profile11204,MergedCutProfiles.Batch280.profile11205,MergedCutProfiles.Batch280.profile11206,MergedCutProfiles.Batch280.profile11207,MergedCutProfiles.Batch280.profile11208,MergedCutProfiles.Batch280.profile11209,MergedCutProfiles.Batch280.profile11210,MergedCutProfiles.Batch280.profile11211,MergedCutProfiles.Batch280.profile11212,MergedCutProfiles.Batch280.profile11213,MergedCutProfiles.Batch280.profile11214,MergedCutProfiles.Batch280.profile11215,MergedCutProfiles.Batch280.profile11216,MergedCutProfiles.Batch280.profile11217]⟩
theorem profilesValid1758 : retention1758.ProfilesValid := by
  change ∀ j : Fin 16, (retention1758.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch280.valid11202
  · exact MergedCutProfiles.Batch280.valid11203
  · exact MergedCutProfiles.Batch280.valid11204
  · exact MergedCutProfiles.Batch280.valid11205
  · exact MergedCutProfiles.Batch280.valid11206
  · exact MergedCutProfiles.Batch280.valid11207
  · exact MergedCutProfiles.Batch280.valid11208
  · exact MergedCutProfiles.Batch280.valid11209
  · exact MergedCutProfiles.Batch280.valid11210
  · exact MergedCutProfiles.Batch280.valid11211
  · exact MergedCutProfiles.Batch280.valid11212
  · exact MergedCutProfiles.Batch280.valid11213
  · exact MergedCutProfiles.Batch280.valid11214
  · exact MergedCutProfiles.Batch280.valid11215
  · exact MergedCutProfiles.Batch280.valid11216
  · exact MergedCutProfiles.Batch280.valid11217
theorem numericValid1758 : retention1758.NumericValid := by decide +kernel
def certificate1758 : RatCutBinCertificate := ⟨⟨retention1758,(2389621610354379771/1000000000000000000),(56016030656085903/250000000000000000),(17501847871039495223/1000000000000000000),(178163800970004532923/1000000000000000000),(849720330465498099/500000000000000000)⟩,(494772959013836839/500000000000000000),(83922011957676767/250000000000000000),(148937630690454153/500000000000000000),(157931725494184033/1000000000000000000)⟩
theorem valid1758 : certificate1758.Valid := by decide +kernel
theorem sound1758 : certificate1758.Sound := rat_cut_bin_certificate_sound certificate1758 profilesValid1758 numericValid1758 valid1758

def retention1759 : RatCutRetentionCertificate := ⟨(261/4000),(523/8000),(3088166591500595961/10171644429370490956),(147883275211143921/100000000000000000),(33/20),(177872023305708065097/128000000000000000000),true,MergedCutProfiles.Batch280.profile11218,![MergedCutProfiles.Batch280.profile11218,MergedCutProfiles.Batch280.profile11219,MergedCutProfiles.Batch280.profile11220,MergedCutProfiles.Batch280.profile11221,MergedCutProfiles.Batch280.profile11222,MergedCutProfiles.Batch280.profile11223,MergedCutProfiles.Batch280.profile11224,MergedCutProfiles.Batch280.profile11225,MergedCutProfiles.Batch280.profile11226,MergedCutProfiles.Batch280.profile11227,MergedCutProfiles.Batch280.profile11228,MergedCutProfiles.Batch280.profile11229,MergedCutProfiles.Batch280.profile11230,MergedCutProfiles.Batch280.profile11231,MergedCutProfiles.Batch280.profile11232,MergedCutProfiles.Batch280.profile11233]⟩
theorem profilesValid1759 : retention1759.ProfilesValid := by
  change ∀ j : Fin 16, (retention1759.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch280.valid11218
  · exact MergedCutProfiles.Batch280.valid11219
  · exact MergedCutProfiles.Batch280.valid11220
  · exact MergedCutProfiles.Batch280.valid11221
  · exact MergedCutProfiles.Batch280.valid11222
  · exact MergedCutProfiles.Batch280.valid11223
  · exact MergedCutProfiles.Batch280.valid11224
  · exact MergedCutProfiles.Batch280.valid11225
  · exact MergedCutProfiles.Batch280.valid11226
  · exact MergedCutProfiles.Batch280.valid11227
  · exact MergedCutProfiles.Batch280.valid11228
  · exact MergedCutProfiles.Batch280.valid11229
  · exact MergedCutProfiles.Batch280.valid11230
  · exact MergedCutProfiles.Batch280.valid11231
  · exact MergedCutProfiles.Batch280.valid11232
  · exact MergedCutProfiles.Batch280.valid11233
theorem numericValid1759 : retention1759.NumericValid := by decide +kernel
def certificate1759 : RatCutBinCertificate := ⟨⟨retention1759,(2389621610354379771/1000000000000000000),(56016030656085903/250000000000000000),(17501847871039495223/1000000000000000000),(178163800970004532923/1000000000000000000),(1339121239826044177/1000000000000000000)⟩,(494772959013836839/500000000000000000),(184807333549154389/500000000000000000),(32813333398660993/125000000000000000),(78932382430847551/500000000000000000)⟩
theorem valid1759 : certificate1759.Valid := by decide +kernel
theorem sound1759 : certificate1759.Sound := rat_cut_bin_certificate_sound certificate1759 profilesValid1759 numericValid1759 valid1759

def retention1760 : RatCutRetentionCertificate := ⟨(261/4000),(523/8000),(4597859241363987453/10171644429370490956),(3088166591500595961/1000000000000000000),(21/20),(1345890511935711927249/1280000000000000000000),true,MergedCutProfiles.Batch280.profile11234,![MergedCutProfiles.Batch280.profile11234,MergedCutProfiles.Batch280.profile11235,MergedCutProfiles.Batch280.profile11236,MergedCutProfiles.Batch280.profile11237,MergedCutProfiles.Batch280.profile11238,MergedCutProfiles.Batch280.profile11239,MergedCutProfiles.Batch281.profile11240,MergedCutProfiles.Batch281.profile11241,MergedCutProfiles.Batch281.profile11242,MergedCutProfiles.Batch281.profile11243,MergedCutProfiles.Batch281.profile11244,MergedCutProfiles.Batch281.profile11245,MergedCutProfiles.Batch281.profile11246,MergedCutProfiles.Batch281.profile11247,MergedCutProfiles.Batch281.profile11248,MergedCutProfiles.Batch281.profile11249]⟩
theorem profilesValid1760 : retention1760.ProfilesValid := by
  change ∀ j : Fin 16, (retention1760.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch280.valid11234
  · exact MergedCutProfiles.Batch280.valid11235
  · exact MergedCutProfiles.Batch280.valid11236
  · exact MergedCutProfiles.Batch280.valid11237
  · exact MergedCutProfiles.Batch280.valid11238
  · exact MergedCutProfiles.Batch280.valid11239
  · exact MergedCutProfiles.Batch281.valid11240
  · exact MergedCutProfiles.Batch281.valid11241
  · exact MergedCutProfiles.Batch281.valid11242
  · exact MergedCutProfiles.Batch281.valid11243
  · exact MergedCutProfiles.Batch281.valid11244
  · exact MergedCutProfiles.Batch281.valid11245
  · exact MergedCutProfiles.Batch281.valid11246
  · exact MergedCutProfiles.Batch281.valid11247
  · exact MergedCutProfiles.Batch281.valid11248
  · exact MergedCutProfiles.Batch281.valid11249
theorem numericValid1760 : retention1760.NumericValid := by decide +kernel
def certificate1760 : RatCutBinCertificate := ⟨⟨retention1760,(2389621610354379771/1000000000000000000),(56016030656085903/250000000000000000),(17501847871039495223/1000000000000000000),(178163800970004532923/1000000000000000000),(509671093772598013/500000000000000000)⟩,(494772959013836839/500000000000000000),(420812886612884479/1000000000000000000),(214944659420183657/1000000000000000000),(79324860353231691/500000000000000000)⟩
theorem valid1760 : certificate1760.Valid := by decide +kernel
theorem sound1760 : certificate1760.Sound := rat_cut_bin_certificate_sound certificate1760 profilesValid1760 numericValid1760 valid1760

def retention1761 : RatCutRetentionCertificate := ⟨(261/4000),(523/8000),(1244705677761257764/2542911107342622739),(4597859241363987453/1000000000000000000),1,(250004714805461618253/256000000000000000000),true,MergedCutProfiles.Batch281.profile11250,![MergedCutProfiles.Batch281.profile11250,MergedCutProfiles.Batch281.profile11251,MergedCutProfiles.Batch281.profile11252,MergedCutProfiles.Batch281.profile11253,MergedCutProfiles.Batch281.profile11254,MergedCutProfiles.Batch281.profile11255,MergedCutProfiles.Batch281.profile11256,MergedCutProfiles.Batch281.profile11257,MergedCutProfiles.Batch281.profile11258,MergedCutProfiles.Batch281.profile11259,MergedCutProfiles.Batch281.profile11260,MergedCutProfiles.Batch281.profile11261,MergedCutProfiles.Batch281.profile11262,MergedCutProfiles.Batch281.profile11263,MergedCutProfiles.Batch281.profile11264,MergedCutProfiles.Batch281.profile11265]⟩
theorem profilesValid1761 : retention1761.ProfilesValid := by
  change ∀ j : Fin 16, (retention1761.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch281.valid11250
  · exact MergedCutProfiles.Batch281.valid11251
  · exact MergedCutProfiles.Batch281.valid11252
  · exact MergedCutProfiles.Batch281.valid11253
  · exact MergedCutProfiles.Batch281.valid11254
  · exact MergedCutProfiles.Batch281.valid11255
  · exact MergedCutProfiles.Batch281.valid11256
  · exact MergedCutProfiles.Batch281.valid11257
  · exact MergedCutProfiles.Batch281.valid11258
  · exact MergedCutProfiles.Batch281.valid11259
  · exact MergedCutProfiles.Batch281.valid11260
  · exact MergedCutProfiles.Batch281.valid11261
  · exact MergedCutProfiles.Batch281.valid11262
  · exact MergedCutProfiles.Batch281.valid11263
  · exact MergedCutProfiles.Batch281.valid11264
  · exact MergedCutProfiles.Batch281.valid11265
theorem numericValid1761 : retention1761.NumericValid := by decide +kernel
def certificate1761 : RatCutBinCertificate := ⟨⟨retention1761,(2389621610354379771/1000000000000000000),(56016030656085903/250000000000000000),(17501847871039495223/1000000000000000000),(178163800970004532923/1000000000000000000),(472989933579893369/500000000000000000)⟩,(494772959013836839/500000000000000000),(432394786759750477/1000000000000000000),(2050779056790697/10000000000000000),(795077114024967/5000000000000000)⟩
theorem valid1761 : certificate1761.Valid := by decide +kernel
theorem sound1761 : certificate1761.Sound := rat_cut_bin_certificate_sound certificate1761 profilesValid1761 numericValid1761 valid1761

def retention1762 : RatCutRetentionCertificate := ⟨(261/4000),(523/8000),(5028610938155481367/10171644429370490956),(311176419440314441/62500000000000000),(11/10),(497682478168945652240177869294811068111/497882271104503105600000000000000000000),false,MergedCutProfiles.Batch281.profile11266,(fun _ => MergedCutProfiles.Batch281.profile11266)⟩
theorem profilesValid1762 : retention1762.ProfilesValid := by
  exact MergedCutProfiles.Batch281.valid11266
theorem numericValid1762 : retention1762.NumericValid := by decide +kernel
def certificate1762 : RatCutBinCertificate := ⟨⟨retention1762,(2389621610354379771/1000000000000000000),(56016030656085903/250000000000000000),(17501847871039495223/1000000000000000000),(178163800970004532923/1000000000000000000),(193187807303189359/200000000000000000)⟩,(494772959013836839/500000000000000000),(52529141382321513/125000000000000000),(26930857912346553/125000000000000000),(80583319514727329/500000000000000000)⟩
theorem valid1762 : certificate1762.Valid := by decide +kernel
theorem sound1762 : certificate1762.Sound := rat_cut_bin_certificate_sound certificate1762 profilesValid1762 numericValid1762 valid1762

def retention1763 : RatCutRetentionCertificate := ⟨(261/4000),(523/8000),(5078897047537036181/10171644429370490956),(5028610938155481367/1000000000000000000),(11/10),(1992474400237068572396058302350441333631/2011444375262192546800000000000000000000),false,MergedCutProfiles.Batch281.profile11267,(fun _ => MergedCutProfiles.Batch281.profile11267)⟩
theorem profilesValid1763 : retention1763.ProfilesValid := by
  exact MergedCutProfiles.Batch281.valid11267
theorem numericValid1763 : retention1763.NumericValid := by decide +kernel
def certificate1763 : RatCutBinCertificate := ⟨⟨retention1763,(2389621610354379771/1000000000000000000),(56016030656085903/250000000000000000),(17501847871039495223/1000000000000000000),(178163800970004532923/1000000000000000000),(478454688543625117/500000000000000000)⟩,(494772959013836839/500000000000000000),(211904652253776309/500000000000000000),(21236176527500359/100000000000000000),(157792724886390241/1000000000000000000)⟩
theorem valid1763 : certificate1763.Valid := by decide +kernel
theorem sound1763 : certificate1763.Sound := rat_cut_bin_certificate_sound certificate1763 profilesValid1763 numericValid1763 valid1763

def certificates : List RatCutBinCertificate := [certificate1752,certificate1753,certificate1754,certificate1755,certificate1756,certificate1757,certificate1758,certificate1759,certificate1760,certificate1761,certificate1762,certificate1763]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1752,List.forall_mem_cons.mpr ⟨sound1753,List.forall_mem_cons.mpr ⟨sound1754,List.forall_mem_cons.mpr ⟨sound1755,List.forall_mem_cons.mpr ⟨sound1756,List.forall_mem_cons.mpr ⟨sound1757,List.forall_mem_cons.mpr ⟨sound1758,List.forall_mem_cons.mpr ⟨sound1759,List.forall_mem_cons.mpr ⟨sound1760,List.forall_mem_cons.mpr ⟨sound1761,List.forall_mem_cons.mpr ⟨sound1762,List.forall_mem_cons.mpr ⟨sound1763,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch146
