import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch281
import Cycle12.MergedCutProfiles.Batch282
import Cycle12.MergedCutProfiles.Batch283

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch147

def retention1764 : RatCutRetentionCertificate := ⟨(261/4000),(523/8000),(1/2),(5078897047537036181/1000000000000000000),(11/10),(2010513532213726131451634523385094797039/2031558819014814472400000000000000000000),false,MergedCutProfiles.Batch281.profile11268,(fun _ => MergedCutProfiles.Batch281.profile11268)⟩
theorem profilesValid1764 : retention1764.ProfilesValid := by
  exact MergedCutProfiles.Batch281.valid11268
theorem numericValid1764 : retention1764.NumericValid := by decide +kernel
def certificate1764 : RatCutBinCertificate := ⟨⟨retention1764,(2389621610354379771/1000000000000000000),(56016030656085903/250000000000000000),(17501847871039495223/1000000000000000000),(178163800970004532923/1000000000000000000),(477990646323685721/500000000000000000)⟩,(494772959013836839/500000000000000000),(84766992942469189/200000000000000000),(212339738011970941/1000000000000000000),(789288846195859/5000000000000000)⟩
theorem valid1764 : certificate1764.Valid := by decide +kernel
theorem sound1764 : certificate1764.Sound := rat_cut_bin_certificate_sound certificate1764 profilesValid1764 numericValid1764 valid1764

def retention1765 : RatCutRetentionCertificate := ⟨(261/4000),(523/8000),(1/2),64,1,(2554168059628887584971769426064464719/2560000000000000000000000000000000000),false,MergedCutProfiles.Batch281.profile11268,(fun _ => MergedCutProfiles.Batch281.profile11268)⟩
theorem profilesValid1765 : retention1765.ProfilesValid := by
  exact MergedCutProfiles.Batch281.valid11268
theorem numericValid1765 : retention1765.NumericValid := by decide +kernel
def certificate1765 : RatCutBinCertificate := ⟨⟨retention1765,(2389621610354379771/1000000000000000000),(56016030656085903/250000000000000000),(17501847871039495223/1000000000000000000),(178163800970004532923/1000000000000000000),(967128614949364093/1000000000000000000)⟩,(494772959013836839/500000000000000000),(76768486165907733/200000000000000000),(124308687991424493/500000000000000000),(5859110001728193/25000000000000000)⟩
theorem valid1765 : certificate1765.Valid := by decide +kernel
theorem sound1765 : certificate1765.Sound := rat_cut_bin_certificate_sound certificate1765 profilesValid1765 numericValid1765 valid1765

def retention1766 : RatCutRetentionCertificate := ⟨(261/4000),(523/8000),(4719334502051789265/10171644429370490956),(3015913911892523449/1000000000000000000),(5/4),(205707024742553975436989273656529948311/193018490361121500736000000000000000000),false,MergedCutProfiles.Batch281.profile11269,(fun _ => MergedCutProfiles.Batch281.profile11269)⟩
theorem profilesValid1766 : retention1766.ProfilesValid := by
  exact MergedCutProfiles.Batch281.valid11269
theorem numericValid1766 : retention1766.NumericValid := by decide +kernel
def certificate1766 : RatCutBinCertificate := ⟨⟨retention1766,(2705941767354379771/1000000000000000000),(56016030656085903/250000000000000000),(17501847871039495223/1000000000000000000),(178163800970004532923/1000000000000000000),(1022420068182725487/1000000000000000000)⟩,(1929994891448271/1953125000000000),(5899110425128759/15625000000000000),(254700692799957269/1000000000000000000),(8445223424859863/50000000000000000)⟩
theorem valid1766 : certificate1766.Valid := by decide +kernel
theorem sound1766 : certificate1766.Sound := rat_cut_bin_certificate_sound certificate1766 profilesValid1766 numericValid1766 valid1766

def retention1767 : RatCutRetentionCertificate := ⟨(261/4000),(523/8000),(5009668671354510687/10171644429370490956),(943866900410357853/200000000000000000),(11/10),(75580170579120052140606930441093799271/75509352032828628240000000000000000000),false,MergedCutProfiles.Batch281.profile11270,(fun _ => MergedCutProfiles.Batch281.profile11270)⟩
theorem profilesValid1767 : retention1767.ProfilesValid := by
  exact MergedCutProfiles.Batch281.valid11270
theorem numericValid1767 : retention1767.NumericValid := by decide +kernel
def certificate1767 : RatCutBinCertificate := ⟨⟨retention1767,(2705941767354379771/1000000000000000000),(56016030656085903/250000000000000000),(17501847871039495223/1000000000000000000),(178163800970004532923/1000000000000000000),(48141105169361313/50000000000000000)⟩,(1929994891448271/1953125000000000),(80182539881247557/200000000000000000),(7270223194939697/31250000000000000),(171993378637090213/1000000000000000000)⟩
theorem valid1767 : certificate1767.Valid := by decide +kernel
theorem sound1767 : certificate1767.Sound := rat_cut_bin_certificate_sound certificate1767 profilesValid1767 numericValid1767 valid1767

def retention1768 : RatCutRetentionCertificate := ⟨(261/4000),(523/8000),(2529882679034027897/5085822214685245478),(5009668671354510687/1000000000000000000),(11/10),(663953034929804645144888163294085057077/667955822847268091600000000000000000000),false,MergedCutProfiles.Batch281.profile11271,(fun _ => MergedCutProfiles.Batch281.profile11271)⟩
theorem profilesValid1768 : retention1768.ProfilesValid := by
  exact MergedCutProfiles.Batch281.valid11271
theorem numericValid1768 : retention1768.NumericValid := by decide +kernel
def certificate1768 : RatCutBinCertificate := ⟨⟨retention1768,(2705941767354379771/1000000000000000000),(56016030656085903/250000000000000000),(17501847871039495223/1000000000000000000),(178163800970004532923/1000000000000000000),(477946083397540723/500000000000000000)⟩,(1929994891448271/1953125000000000),(403819198363317781/1000000000000000000),(230001189345317499/1000000000000000000),(85207279539857/500000000000000)⟩
theorem valid1768 : certificate1768.Valid := by decide +kernel
theorem sound1768 : certificate1768.Sound := rat_cut_bin_certificate_sound certificate1768 profilesValid1768 numericValid1768 valid1768

def retention1769 : RatCutRetentionCertificate := ⟨(261/4000),(523/8000),(1/2),(2529882679034027897/500000000000000000),(11/10),(500664751650895185172010624272398863191/505976535806805579400000000000000000000),false,MergedCutProfiles.Batch281.profile11268,(fun _ => MergedCutProfiles.Batch281.profile11268)⟩
theorem profilesValid1769 : retention1769.ProfilesValid := by
  exact MergedCutProfiles.Batch281.valid11268
theorem numericValid1769 : retention1769.NumericValid := by decide +kernel
def certificate1769 : RatCutBinCertificate := ⟨⟨retention1769,(2705941767354379771/1000000000000000000),(56016030656085903/250000000000000000),(17501847871039495223/1000000000000000000),(178163800970004532923/1000000000000000000),(11892334534125859/12500000000000000)⟩,(1929994891448271/1953125000000000),(81146306347439537/200000000000000000),(45654339412188469/200000000000000000),(84336050779045737/500000000000000000)⟩
theorem valid1769 : certificate1769.Valid := by decide +kernel
theorem sound1769 : certificate1769.Sound := rat_cut_bin_certificate_sound certificate1769 profilesValid1769 numericValid1769 valid1769

def retention1770 : RatCutRetentionCertificate := ⟨(523/8000),(131/2000),(1245240123106853699/10124819273238357312),(448350620586136831/500000000000000000),(5/2),(11740852140612095359/6400000000000000000),true,MergedCutProfiles.Batch281.profile11272,![MergedCutProfiles.Batch281.profile11272,MergedCutProfiles.Batch281.profile11273,MergedCutProfiles.Batch281.profile11274,MergedCutProfiles.Batch281.profile11275,MergedCutProfiles.Batch281.profile11276,MergedCutProfiles.Batch281.profile11277,MergedCutProfiles.Batch281.profile11278,MergedCutProfiles.Batch281.profile11279,MergedCutProfiles.Batch282.profile11280,MergedCutProfiles.Batch282.profile11281,MergedCutProfiles.Batch282.profile11282,MergedCutProfiles.Batch282.profile11283,MergedCutProfiles.Batch282.profile11284,MergedCutProfiles.Batch282.profile11285,MergedCutProfiles.Batch282.profile11286,MergedCutProfiles.Batch282.profile11287]⟩
theorem profilesValid1770 : retention1770.ProfilesValid := by
  change ∀ j : Fin 16, (retention1770.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch281.valid11272
  · exact MergedCutProfiles.Batch281.valid11273
  · exact MergedCutProfiles.Batch281.valid11274
  · exact MergedCutProfiles.Batch281.valid11275
  · exact MergedCutProfiles.Batch281.valid11276
  · exact MergedCutProfiles.Batch281.valid11277
  · exact MergedCutProfiles.Batch281.valid11278
  · exact MergedCutProfiles.Batch281.valid11279
  · exact MergedCutProfiles.Batch282.valid11280
  · exact MergedCutProfiles.Batch282.valid11281
  · exact MergedCutProfiles.Batch282.valid11282
  · exact MergedCutProfiles.Batch282.valid11283
  · exact MergedCutProfiles.Batch282.valid11284
  · exact MergedCutProfiles.Batch282.valid11285
  · exact MergedCutProfiles.Batch282.valid11286
  · exact MergedCutProfiles.Batch282.valid11287
theorem numericValid1770 : retention1770.NumericValid := by decide +kernel
def certificate1770 : RatCutBinCertificate := ⟨⟨retention1770,(479253603809882821/200000000000000000),(225107070921290071/1000000000000000000),(17543974942373782039/1000000000000000000),(35554122786682429017/200000000000000000),(35151966572584077/20000000000000000)⟩,(494753692033902929/500000000000000000),(167199870824158461/500000000000000000),(149641849878441481/500000000000000000),(19765185272712007/125000000000000000)⟩
theorem valid1770 : certificate1770.Valid := by decide +kernel
theorem sound1770 : certificate1770.Sound := rat_cut_bin_certificate_sound certificate1770 profilesValid1770 numericValid1770 valid1770

def retention1771 : RatCutRetentionCertificate := ⟨(523/8000),(131/2000),(2474160657333655513/10124819273238357312),(1245240123106853699/1000000000000000000),(37/20),(1948041320120644823627/1280000000000000000000),true,MergedCutProfiles.Batch281.profile11273,![MergedCutProfiles.Batch281.profile11273,MergedCutProfiles.Batch282.profile11288,MergedCutProfiles.Batch282.profile11289,MergedCutProfiles.Batch282.profile11290,MergedCutProfiles.Batch282.profile11291,MergedCutProfiles.Batch282.profile11292,MergedCutProfiles.Batch282.profile11293,MergedCutProfiles.Batch282.profile11294,MergedCutProfiles.Batch282.profile11295,MergedCutProfiles.Batch282.profile11296,MergedCutProfiles.Batch282.profile11297,MergedCutProfiles.Batch282.profile11298,MergedCutProfiles.Batch282.profile11299,MergedCutProfiles.Batch282.profile11300,MergedCutProfiles.Batch282.profile11301,MergedCutProfiles.Batch282.profile11302]⟩
theorem profilesValid1771 : retention1771.ProfilesValid := by
  change ∀ j : Fin 16, (retention1771.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch281.valid11273
  · exact MergedCutProfiles.Batch282.valid11288
  · exact MergedCutProfiles.Batch282.valid11289
  · exact MergedCutProfiles.Batch282.valid11290
  · exact MergedCutProfiles.Batch282.valid11291
  · exact MergedCutProfiles.Batch282.valid11292
  · exact MergedCutProfiles.Batch282.valid11293
  · exact MergedCutProfiles.Batch282.valid11294
  · exact MergedCutProfiles.Batch282.valid11295
  · exact MergedCutProfiles.Batch282.valid11296
  · exact MergedCutProfiles.Batch282.valid11297
  · exact MergedCutProfiles.Batch282.valid11298
  · exact MergedCutProfiles.Batch282.valid11299
  · exact MergedCutProfiles.Batch282.valid11300
  · exact MergedCutProfiles.Batch282.valid11301
  · exact MergedCutProfiles.Batch282.valid11302
theorem numericValid1771 : retention1771.NumericValid := by decide +kernel
def certificate1771 : RatCutBinCertificate := ⟨⟨retention1771,(479253603809882821/200000000000000000),(225107070921290071/1000000000000000000),(17543974942373782039/1000000000000000000),(35554122786682429017/200000000000000000),(1464994879672433221/1000000000000000000)⟩,(494753692033902929/500000000000000000),(358435334131649353/1000000000000000000),(68450732122682193/250000000000000000),(9956569686851491/62500000000000000)⟩
theorem valid1771 : certificate1771.Valid := by decide +kernel
theorem sound1771 : certificate1771.Sound := rat_cut_bin_certificate_sound certificate1771 profilesValid1771 numericValid1771 valid1771

def retention1772 : RatCutRetentionCertificate := ⟨(523/8000),(131/2000),(4192380643975430423/10124819273238357312),(2474160657333655513/1000000000000000000),(6/5),(1463445276914895293373/1280000000000000000000),true,MergedCutProfiles.Batch282.profile11303,![MergedCutProfiles.Batch282.profile11303,MergedCutProfiles.Batch282.profile11304,MergedCutProfiles.Batch282.profile11305,MergedCutProfiles.Batch282.profile11306,MergedCutProfiles.Batch282.profile11307,MergedCutProfiles.Batch282.profile11308,MergedCutProfiles.Batch282.profile11309,MergedCutProfiles.Batch282.profile11310,MergedCutProfiles.Batch282.profile11311,MergedCutProfiles.Batch282.profile11312,MergedCutProfiles.Batch282.profile11313,MergedCutProfiles.Batch282.profile11314,MergedCutProfiles.Batch282.profile11315,MergedCutProfiles.Batch282.profile11316,MergedCutProfiles.Batch282.profile11317,MergedCutProfiles.Batch282.profile11318]⟩
theorem profilesValid1772 : retention1772.ProfilesValid := by
  change ∀ j : Fin 16, (retention1772.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch282.valid11303
  · exact MergedCutProfiles.Batch282.valid11304
  · exact MergedCutProfiles.Batch282.valid11305
  · exact MergedCutProfiles.Batch282.valid11306
  · exact MergedCutProfiles.Batch282.valid11307
  · exact MergedCutProfiles.Batch282.valid11308
  · exact MergedCutProfiles.Batch282.valid11309
  · exact MergedCutProfiles.Batch282.valid11310
  · exact MergedCutProfiles.Batch282.valid11311
  · exact MergedCutProfiles.Batch282.valid11312
  · exact MergedCutProfiles.Batch282.valid11313
  · exact MergedCutProfiles.Batch282.valid11314
  · exact MergedCutProfiles.Batch282.valid11315
  · exact MergedCutProfiles.Batch282.valid11316
  · exact MergedCutProfiles.Batch282.valid11317
  · exact MergedCutProfiles.Batch282.valid11318
theorem numericValid1772 : retention1772.NumericValid := by decide +kernel
def certificate1772 : RatCutBinCertificate := ⟨⟨retention1772,(479253603809882821/200000000000000000),(225107070921290071/1000000000000000000),(17543974942373782039/1000000000000000000),(35554122786682429017/200000000000000000),(138300626836248569/125000000000000000)⟩,(494753692033902929/500000000000000000),(20113164470983053/50000000000000000),(231415012229768463/1000000000000000000),(160811293684319653/1000000000000000000)⟩
theorem valid1772 : certificate1772.Valid := by decide +kernel
theorem sound1772 : certificate1772.Sound := rat_cut_bin_certificate_sound certificate1772 profilesValid1772 numericValid1772 valid1772

def retention1773 : RatCutRetentionCertificate := ⟨(523/8000),(131/2000),(4867223776749557209/10124819273238357312),(4192380643975430423/1000000000000000000),1,(253870779547457808503/256000000000000000000),true,MergedCutProfiles.Batch282.profile11319,![MergedCutProfiles.Batch282.profile11319,MergedCutProfiles.Batch283.profile11320,MergedCutProfiles.Batch283.profile11321,MergedCutProfiles.Batch283.profile11322,MergedCutProfiles.Batch283.profile11323,MergedCutProfiles.Batch283.profile11324,MergedCutProfiles.Batch283.profile11325,MergedCutProfiles.Batch283.profile11326,MergedCutProfiles.Batch283.profile11327,MergedCutProfiles.Batch283.profile11328,MergedCutProfiles.Batch283.profile11329,MergedCutProfiles.Batch283.profile11330,MergedCutProfiles.Batch283.profile11331,MergedCutProfiles.Batch283.profile11332,MergedCutProfiles.Batch283.profile11333,MergedCutProfiles.Batch283.profile11334]⟩
theorem profilesValid1773 : retention1773.ProfilesValid := by
  change ∀ j : Fin 16, (retention1773.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch282.valid11319
  · exact MergedCutProfiles.Batch283.valid11320
  · exact MergedCutProfiles.Batch283.valid11321
  · exact MergedCutProfiles.Batch283.valid11322
  · exact MergedCutProfiles.Batch283.valid11323
  · exact MergedCutProfiles.Batch283.valid11324
  · exact MergedCutProfiles.Batch283.valid11325
  · exact MergedCutProfiles.Batch283.valid11326
  · exact MergedCutProfiles.Batch283.valid11327
  · exact MergedCutProfiles.Batch283.valid11328
  · exact MergedCutProfiles.Batch283.valid11329
  · exact MergedCutProfiles.Batch283.valid11330
  · exact MergedCutProfiles.Batch283.valid11331
  · exact MergedCutProfiles.Batch283.valid11332
  · exact MergedCutProfiles.Batch283.valid11333
  · exact MergedCutProfiles.Batch283.valid11334
theorem numericValid1773 : retention1773.NumericValid := by decide +kernel
def certificate1773 : RatCutBinCertificate := ⟨⟨retention1773,(479253603809882821/200000000000000000),(225107070921290071/1000000000000000000),(17543974942373782039/1000000000000000000),(35554122786682429017/200000000000000000),(96092688601861907/100000000000000000)⟩,(494753692033902929/500000000000000000),(428572359738440143/1000000000000000000),(208299572625848179/1000000000000000000),(80455733995321033/500000000000000000)⟩
theorem valid1773 : certificate1773.Valid := by decide +kernel
theorem sound1773 : certificate1773.Sound := rat_cut_bin_certificate_sound certificate1773 profilesValid1773 numericValid1773 valid1773

def retention1774 : RatCutRetentionCertificate := ⟨(523/8000),(131/2000),(208946063517035231/421867469718264888),(4867223776749557209/1000000000000000000),(11/10),(1940979323446921126630478961185431518679/1946889510699822883600000000000000000000),false,MergedCutProfiles.Batch283.profile11335,(fun _ => MergedCutProfiles.Batch283.profile11335)⟩
theorem profilesValid1774 : retention1774.ProfilesValid := by
  exact MergedCutProfiles.Batch283.valid11335
theorem numericValid1774 : retention1774.NumericValid := by decide +kernel
def certificate1774 : RatCutBinCertificate := ⟨⟨retention1774,(479253603809882821/200000000000000000),(225107070921290071/1000000000000000000),(17543974942373782039/1000000000000000000),(35554122786682429017/200000000000000000),(481567538731262899/500000000000000000)⟩,(494753692033902929/500000000000000000),(420699486966219973/1000000000000000000),(107521413589014613/500000000000000000),(159945988816493323/1000000000000000000)⟩
theorem valid1774 : certificate1774.Valid := by decide +kernel
theorem sound1774 : certificate1774.Sound := rat_cut_bin_certificate_sound certificate1774 profilesValid1774 numericValid1774 valid1774

def retention1775 : RatCutRetentionCertificate := ⟨(523/8000),(131/2000),(1/2),(626838190551105693/125000000000000000),(11/10),(165346533482910167846950797156021266997/167156850813628184800000000000000000000),false,MergedCutProfiles.Batch283.profile11336,(fun _ => MergedCutProfiles.Batch283.profile11336)⟩
theorem profilesValid1775 : retention1775.ProfilesValid := by
  exact MergedCutProfiles.Batch283.valid11336
theorem numericValid1775 : retention1775.NumericValid := by decide +kernel
def certificate1775 : RatCutBinCertificate := ⟨⟨retention1775,(479253603809882821/200000000000000000),(225107070921290071/1000000000000000000),(17543974942373782039/1000000000000000000),(35554122786682429017/200000000000000000),(238835242158546407/250000000000000000)⟩,(494753692033902929/500000000000000000),(422862585939537723/1000000000000000000),(213175535108424943/1000000000000000000),(31621273318839381/200000000000000000)⟩
theorem valid1775 : certificate1775.Valid := by decide +kernel
theorem sound1775 : certificate1775.Sound := rat_cut_bin_certificate_sound certificate1775 profilesValid1775 numericValid1775 valid1775

def certificates : List RatCutBinCertificate := [certificate1764,certificate1765,certificate1766,certificate1767,certificate1768,certificate1769,certificate1770,certificate1771,certificate1772,certificate1773,certificate1774,certificate1775]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1764,List.forall_mem_cons.mpr ⟨sound1765,List.forall_mem_cons.mpr ⟨sound1766,List.forall_mem_cons.mpr ⟨sound1767,List.forall_mem_cons.mpr ⟨sound1768,List.forall_mem_cons.mpr ⟨sound1769,List.forall_mem_cons.mpr ⟨sound1770,List.forall_mem_cons.mpr ⟨sound1771,List.forall_mem_cons.mpr ⟨sound1772,List.forall_mem_cons.mpr ⟨sound1773,List.forall_mem_cons.mpr ⟨sound1774,List.forall_mem_cons.mpr ⟨sound1775,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch147
