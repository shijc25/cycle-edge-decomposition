import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch215
import Cycle12.MergedCutProfiles.Batch216
import Cycle12.MergedCutProfiles.Batch217

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch110

def retention1320 : RatCutRetentionCertificate := ⟨(117/2000),(47/800),(1/2),(3275368903791034531/500000000000000000),(21/20),(2579047240060635056290908374331253525919/2620295123032827624800000000000000000000),false,MergedCutProfiles.Batch215.profile8617,(fun _ => MergedCutProfiles.Batch215.profile8617)⟩
theorem profilesValid1320 : retention1320.ProfilesValid := by
  exact MergedCutProfiles.Batch215.valid8617
theorem numericValid1320 : retention1320.NumericValid := by decide +kernel
def certificate1320 : RatCutBinCertificate := ⟨⟨retention1320,(1283445517804849/488281250000000),(86798448590065447/500000000000000000),(15435416906887000289/1000000000000000000),(12679638681241212941/62500000000000000),(953214547055151009/1000000000000000000)⟩,(247311424294230257/250000000000000000),(419163686532639077/1000000000000000000),(216375351070018853/1000000000000000000),(85766449775880039/500000000000000000)⟩
theorem valid1320 : certificate1320.Valid := by decide +kernel
theorem sound1320 : certificate1320.Sound := rat_cut_bin_certificate_sound certificate1320 profilesValid1320 numericValid1320 valid1320

def retention1321 : RatCutRetentionCertificate := ⟨(47/800),(471/8000),(1100870457514910349/13057946946642478085),(108376035377524809/125000000000000000),(27/10),(311294058318605173127/160000000000000000000),true,MergedCutProfiles.Batch215.profile8621,![MergedCutProfiles.Batch215.profile8621,MergedCutProfiles.Batch215.profile8622,MergedCutProfiles.Batch215.profile8623,MergedCutProfiles.Batch215.profile8624,MergedCutProfiles.Batch215.profile8625,MergedCutProfiles.Batch215.profile8626,MergedCutProfiles.Batch215.profile8627,MergedCutProfiles.Batch215.profile8628,MergedCutProfiles.Batch215.profile8629,MergedCutProfiles.Batch215.profile8630,MergedCutProfiles.Batch215.profile8631,MergedCutProfiles.Batch215.profile8632,MergedCutProfiles.Batch215.profile8633,MergedCutProfiles.Batch215.profile8634,MergedCutProfiles.Batch215.profile8635,MergedCutProfiles.Batch215.profile8636]⟩
theorem profilesValid1321 : retention1321.ProfilesValid := by
  change ∀ j : Fin 16, (retention1321.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch215.valid8621
  · exact MergedCutProfiles.Batch215.valid8622
  · exact MergedCutProfiles.Batch215.valid8623
  · exact MergedCutProfiles.Batch215.valid8624
  · exact MergedCutProfiles.Batch215.valid8625
  · exact MergedCutProfiles.Batch215.valid8626
  · exact MergedCutProfiles.Batch215.valid8627
  · exact MergedCutProfiles.Batch215.valid8628
  · exact MergedCutProfiles.Batch215.valid8629
  · exact MergedCutProfiles.Batch215.valid8630
  · exact MergedCutProfiles.Batch215.valid8631
  · exact MergedCutProfiles.Batch215.valid8632
  · exact MergedCutProfiles.Batch215.valid8633
  · exact MergedCutProfiles.Batch215.valid8634
  · exact MergedCutProfiles.Batch215.valid8635
  · exact MergedCutProfiles.Batch215.valid8636
theorem numericValid1321 : retention1321.NumericValid := by decide +kernel
def certificate1321 : RatCutBinCertificate := ⟨⟨retention1321,(2298757406178528191/1000000000000000000),(174466420515893047/1000000000000000000),(15505262415654835759/1000000000000000000),(50655134347720589667/250000000000000000),(1875724523466370689/1000000000000000000)⟩,(990605105400324533/1000000000000000000),(354876530383982451/1000000000000000000),(69367880694727313/250000000000000000),(146969275885796293/1000000000000000000)⟩
theorem valid1321 : certificate1321.Valid := by decide +kernel
theorem sound1321 : certificate1321.Sound := rat_cut_bin_certificate_sound certificate1321 profilesValid1321 numericValid1321 valid1321

def retention1322 : RatCutRetentionCertificate := ⟨(47/800),(471/8000),(2253591156290129439/13057946946642478085),(1100870457514910349/1000000000000000000),(11/5),(2177756579721977592849/1280000000000000000000),true,MergedCutProfiles.Batch215.profile8637,![MergedCutProfiles.Batch215.profile8637,MergedCutProfiles.Batch215.profile8638,MergedCutProfiles.Batch215.profile8639,MergedCutProfiles.Batch216.profile8640,MergedCutProfiles.Batch216.profile8641,MergedCutProfiles.Batch216.profile8642,MergedCutProfiles.Batch216.profile8643,MergedCutProfiles.Batch216.profile8644,MergedCutProfiles.Batch216.profile8645,MergedCutProfiles.Batch216.profile8646,MergedCutProfiles.Batch216.profile8647,MergedCutProfiles.Batch216.profile8648,MergedCutProfiles.Batch216.profile8649,MergedCutProfiles.Batch216.profile8650,MergedCutProfiles.Batch216.profile8651,MergedCutProfiles.Batch216.profile8652]⟩
theorem profilesValid1322 : retention1322.ProfilesValid := by
  change ∀ j : Fin 16, (retention1322.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch215.valid8637
  · exact MergedCutProfiles.Batch215.valid8638
  · exact MergedCutProfiles.Batch215.valid8639
  · exact MergedCutProfiles.Batch216.valid8640
  · exact MergedCutProfiles.Batch216.valid8641
  · exact MergedCutProfiles.Batch216.valid8642
  · exact MergedCutProfiles.Batch216.valid8643
  · exact MergedCutProfiles.Batch216.valid8644
  · exact MergedCutProfiles.Batch216.valid8645
  · exact MergedCutProfiles.Batch216.valid8646
  · exact MergedCutProfiles.Batch216.valid8647
  · exact MergedCutProfiles.Batch216.valid8648
  · exact MergedCutProfiles.Batch216.valid8649
  · exact MergedCutProfiles.Batch216.valid8650
  · exact MergedCutProfiles.Batch216.valid8651
  · exact MergedCutProfiles.Batch216.valid8652
theorem numericValid1322 : retention1322.NumericValid := by decide +kernel
def certificate1322 : RatCutBinCertificate := ⟨⟨retention1322,(2298757406178528191/1000000000000000000),(174466420515893047/1000000000000000000),(15505262415654835759/1000000000000000000),(50655134347720589667/250000000000000000),(1644447342593680193/1000000000000000000)⟩,(990605105400324533/1000000000000000000),(370789072828591391/1000000000000000000),(130669881429056037/500000000000000000),(147600038640054517/1000000000000000000)⟩
theorem valid1322 : certificate1322.Valid := by decide +kernel
theorem sound1322 : certificate1322.Sound := rat_cut_bin_certificate_sound certificate1322 profilesValid1322 numericValid1322 valid1322

def retention1323 : RatCutRetentionCertificate := ⟨(47/800),(471/8000),(979427469754481038/2611589389328495617),(2253591156290129439/1000000000000000000),(13/10),(1573175827583673564531/1280000000000000000000),true,MergedCutProfiles.Batch216.profile8653,![MergedCutProfiles.Batch216.profile8653,MergedCutProfiles.Batch216.profile8654,MergedCutProfiles.Batch216.profile8655,MergedCutProfiles.Batch216.profile8656,MergedCutProfiles.Batch216.profile8657,MergedCutProfiles.Batch216.profile8658,MergedCutProfiles.Batch216.profile8659,MergedCutProfiles.Batch216.profile8660,MergedCutProfiles.Batch216.profile8661,MergedCutProfiles.Batch216.profile8662,MergedCutProfiles.Batch216.profile8663,MergedCutProfiles.Batch216.profile8664,MergedCutProfiles.Batch216.profile8665,MergedCutProfiles.Batch216.profile8666,MergedCutProfiles.Batch216.profile8667,MergedCutProfiles.Batch216.profile8668]⟩
theorem profilesValid1323 : retention1323.ProfilesValid := by
  change ∀ j : Fin 16, (retention1323.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch216.valid8653
  · exact MergedCutProfiles.Batch216.valid8654
  · exact MergedCutProfiles.Batch216.valid8655
  · exact MergedCutProfiles.Batch216.valid8656
  · exact MergedCutProfiles.Batch216.valid8657
  · exact MergedCutProfiles.Batch216.valid8658
  · exact MergedCutProfiles.Batch216.valid8659
  · exact MergedCutProfiles.Batch216.valid8660
  · exact MergedCutProfiles.Batch216.valid8661
  · exact MergedCutProfiles.Batch216.valid8662
  · exact MergedCutProfiles.Batch216.valid8663
  · exact MergedCutProfiles.Batch216.valid8664
  · exact MergedCutProfiles.Batch216.valid8665
  · exact MergedCutProfiles.Batch216.valid8666
  · exact MergedCutProfiles.Batch216.valid8667
  · exact MergedCutProfiles.Batch216.valid8668
theorem numericValid1323 : retention1323.NumericValid := by decide +kernel
def certificate1323 : RatCutBinCertificate := ⟨⟨retention1323,(2298757406178528191/1000000000000000000),(174466420515893047/1000000000000000000),(15505262415654835759/1000000000000000000),(50655134347720589667/250000000000000000),(597704097949294121/500000000000000000)⟩,(990605105400324533/1000000000000000000),(105345697033699661/250000000000000000),(8578070788463939/40000000000000000),(74226813425515577/500000000000000000)⟩
theorem valid1323 : certificate1323.Valid := by decide +kernel
theorem sound1323 : certificate1323.Sound := rat_cut_bin_certificate_sound certificate1323 profilesValid1323 numericValid1323 valid1323

def retention1324 : RatCutRetentionCertificate := ⟨(47/800),(471/8000),(6218064970356041358/13057946946642478085),(489713734877240519/100000000000000000),1,(25652407406198096591/25600000000000000000),true,MergedCutProfiles.Batch216.profile8669,![MergedCutProfiles.Batch216.profile8669,MergedCutProfiles.Batch216.profile8670,MergedCutProfiles.Batch216.profile8671,MergedCutProfiles.Batch216.profile8672,MergedCutProfiles.Batch216.profile8673,MergedCutProfiles.Batch216.profile8674,MergedCutProfiles.Batch216.profile8675,MergedCutProfiles.Batch216.profile8676,MergedCutProfiles.Batch216.profile8677,MergedCutProfiles.Batch216.profile8678,MergedCutProfiles.Batch216.profile8679,MergedCutProfiles.Batch217.profile8680,MergedCutProfiles.Batch217.profile8681,MergedCutProfiles.Batch217.profile8682,MergedCutProfiles.Batch217.profile8683,MergedCutProfiles.Batch217.profile8684]⟩
theorem profilesValid1324 : retention1324.ProfilesValid := by
  change ∀ j : Fin 16, (retention1324.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch216.valid8669
  · exact MergedCutProfiles.Batch216.valid8670
  · exact MergedCutProfiles.Batch216.valid8671
  · exact MergedCutProfiles.Batch216.valid8672
  · exact MergedCutProfiles.Batch216.valid8673
  · exact MergedCutProfiles.Batch216.valid8674
  · exact MergedCutProfiles.Batch216.valid8675
  · exact MergedCutProfiles.Batch216.valid8676
  · exact MergedCutProfiles.Batch216.valid8677
  · exact MergedCutProfiles.Batch216.valid8678
  · exact MergedCutProfiles.Batch216.valid8679
  · exact MergedCutProfiles.Batch217.valid8680
  · exact MergedCutProfiles.Batch217.valid8681
  · exact MergedCutProfiles.Batch217.valid8682
  · exact MergedCutProfiles.Batch217.valid8683
  · exact MergedCutProfiles.Batch217.valid8684
theorem numericValid1324 : retention1324.NumericValid := by decide +kernel
def certificate1324 : RatCutBinCertificate := ⟨⟨retention1324,(2298757406178528191/1000000000000000000),(174466420515893047/1000000000000000000),(15505262415654835759/1000000000000000000),(50655134347720589667/250000000000000000),(97617681899257727/100000000000000000)⟩,(990605105400324533/1000000000000000000),(46002760348730243/100000000000000000),(18277512230648541/100000000000000000),(9201388188753083/62500000000000000)⟩
theorem valid1324 : certificate1324.Valid := by decide +kernel
theorem sound1324 : certificate1324.Sound := rat_cut_bin_certificate_sound certificate1324 profilesValid1324 numericValid1324 valid1324

def retention1325 : RatCutRetentionCertificate := ⟨(47/800),(471/8000),(6470543342593027766/13057946946642478085),(3109032485178020679/500000000000000000),(11/10),(208199999256559753014832430414112525093/207268832345201378600000000000000000000),false,MergedCutProfiles.Batch217.profile8685,(fun _ => MergedCutProfiles.Batch217.profile8685)⟩
theorem profilesValid1325 : retention1325.ProfilesValid := by
  exact MergedCutProfiles.Batch217.valid8685
theorem numericValid1325 : retention1325.NumericValid := by decide +kernel
def certificate1325 : RatCutBinCertificate := ⟨⟨retention1325,(2298757406178528191/1000000000000000000),(174466420515893047/1000000000000000000),(15505262415654835759/1000000000000000000),(50655134347720589667/250000000000000000),(488018298720039423/500000000000000000)⟩,(990605105400324533/1000000000000000000),(224976297569521001/500000000000000000),(190709112962205149/1000000000000000000),(148266896008339861/1000000000000000000)⟩
theorem valid1325 : certificate1325.Valid := by decide +kernel
theorem sound1325 : certificate1325.Sound := rat_cut_bin_certificate_sound certificate1325 profilesValid1325 numericValid1325 valid1325

def retention1326 : RatCutRetentionCertificate := ⟨(47/800),(471/8000),(1/2),(3235271671296513883/500000000000000000),(21/20),(2546379695382647986252102124504272484351/2588217337037211106400000000000000000000),false,MergedCutProfiles.Batch217.profile8686,(fun _ => MergedCutProfiles.Batch217.profile8686)⟩
theorem profilesValid1326 : retention1326.ProfilesValid := by
  exact MergedCutProfiles.Batch217.valid8686
theorem numericValid1326 : retention1326.NumericValid := by decide +kernel
def certificate1326 : RatCutBinCertificate := ⟨⟨retention1326,(2298757406178528191/1000000000000000000),(174466420515893047/1000000000000000000),(15505262415654835759/1000000000000000000),(50655134347720589667/250000000000000000),(191334563038368707/200000000000000000)⟩,(990605105400324533/1000000000000000000),(457563277858631583/1000000000000000000),(184695189562373737/1000000000000000000),(146875006804074643/1000000000000000000)⟩
theorem valid1326 : certificate1326.Valid := by decide +kernel
theorem sound1326 : certificate1326.Sound := rat_cut_bin_certificate_sound certificate1326 profilesValid1326 numericValid1326 valid1326

def retention1327 : RatCutRetentionCertificate := ⟨(47/800),(471/8000),(1/2),64,1,(63851586085245566050723143238003283991/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch217.profile8686,(fun _ => MergedCutProfiles.Batch217.profile8686)⟩
theorem profilesValid1327 : retention1327.ProfilesValid := by
  exact MergedCutProfiles.Batch217.valid8686
theorem numericValid1327 : retention1327.NumericValid := by decide +kernel
def certificate1327 : RatCutBinCertificate := ⟨⟨retention1327,(2298757406178528191/1000000000000000000),(174466420515893047/1000000000000000000),(15505262415654835759/1000000000000000000),(50655134347720589667/250000000000000000),(194362977437016703/200000000000000000)⟩,(990605105400324533/1000000000000000000),(417816009072630781/1000000000000000000),(43509857019366281/200000000000000000),(103140134630475291/500000000000000000)⟩
theorem valid1327 : certificate1327.Valid := by decide +kernel
theorem sound1327 : certificate1327.Sound := rat_cut_bin_certificate_sound certificate1327 profilesValid1327 numericValid1327 valid1327

def retention1328 : RatCutRetentionCertificate := ⟨(47/800),(471/8000),(6065632047247147167/13057946946642478085),(3579672135622291863/1000000000000000000),(6/5),(380929938791613961105634916864425230391/357967213562229186300000000000000000000),false,MergedCutProfiles.Batch217.profile8687,(fun _ => MergedCutProfiles.Batch217.profile8687)⟩
theorem profilesValid1328 : retention1328.ProfilesValid := by
  exact MergedCutProfiles.Batch217.valid8687
theorem numericValid1328 : retention1328.NumericValid := by decide +kernel
def certificate1328 : RatCutBinCertificate := ⟨⟨retention1328,(2631128462178528191/1000000000000000000),(174466420515893047/1000000000000000000),(15505262415654835759/1000000000000000000),(50655134347720589667/250000000000000000),(1028613649154953837/1000000000000000000)⟩,(989243655366097281/1000000000000000000),(193275275854590113/500000000000000000),(49206797370711639/200000000000000000),(173723728122276967/1000000000000000000)⟩
theorem valid1328 : certificate1328.Valid := by decide +kernel
theorem sound1328 : certificate1328.Sound := rat_cut_bin_certificate_sound certificate1328 profilesValid1328 numericValid1328 valid1328

def retention1329 : RatCutRetentionCertificate := ⟨(47/800),(471/8000),(6438790644284043612/13057946946642478085),(6065632047247147167/1000000000000000000),(21/20),(9652061741481603940946627427716086421111/9705011275595435467200000000000000000000),false,MergedCutProfiles.Batch217.profile8688,(fun _ => MergedCutProfiles.Batch217.profile8688)⟩
theorem profilesValid1329 : retention1329.ProfilesValid := by
  exact MergedCutProfiles.Batch217.valid8688
theorem numericValid1329 : retention1329.NumericValid := by decide +kernel
def certificate1329 : RatCutBinCertificate := ⟨⟨retention1329,(2631128462178528191/1000000000000000000),(174466420515893047/1000000000000000000),(15505262415654835759/1000000000000000000),(50655134347720589667/250000000000000000),(963453955580649321/1000000000000000000)⟩,(989243655366097281/1000000000000000000),(206346744062517423/500000000000000000),(222051178411203977/1000000000000000000),(88016996134394267/500000000000000000)⟩
theorem valid1329 : certificate1329.Valid := by decide +kernel
theorem sound1329 : certificate1329.Sound := rat_cut_bin_certificate_sound certificate1329 profilesValid1329 numericValid1329 valid1329

def retention1330 : RatCutRetentionCertificate := ⟨(47/800),(471/8000),(6503178550726884049/13057946946642478085),(1609697661071010903/250000000000000000),(21/20),(635774410067266244746777366597633789751/643879064428404361200000000000000000000),false,MergedCutProfiles.Batch217.profile8689,(fun _ => MergedCutProfiles.Batch217.profile8689)⟩
theorem profilesValid1330 : retention1330.ProfilesValid := by
  exact MergedCutProfiles.Batch217.valid8689
theorem numericValid1330 : retention1330.NumericValid := by decide +kernel
def certificate1330 : RatCutBinCertificate := ⟨⟨retention1330,(2631128462178528191/1000000000000000000),(174466420515893047/1000000000000000000),(15505262415654835759/1000000000000000000),(50655134347720589667/250000000000000000),(956322864590541943/1000000000000000000)⟩,(989243655366097281/1000000000000000000),(51971356680188923/125000000000000000),(21933908385266423/100000000000000000),(17402675250096973/100000000000000000)⟩
theorem valid1330 : certificate1330.Valid := by decide +kernel
theorem sound1330 : certificate1330.Sound := rat_cut_bin_certificate_sound certificate1330 profilesValid1330 numericValid1330 valid1330

def retention1331 : RatCutRetentionCertificate := ⟨(47/800),(471/8000),(1/2),(6503178550726884049/1000000000000000000),(21/20),(10238702746353072292140141183089146289039/10405085681163014478400000000000000000000),false,MergedCutProfiles.Batch217.profile8686,(fun _ => MergedCutProfiles.Batch217.profile8686)⟩
theorem profilesValid1331 : retention1331.ProfilesValid := by
  exact MergedCutProfiles.Batch217.valid8686
theorem numericValid1331 : retention1331.NumericValid := by decide +kernel
def certificate1331 : RatCutBinCertificate := ⟨⟨retention1331,(2631128462178528191/1000000000000000000),(174466420515893047/1000000000000000000),(15505262415654835759/1000000000000000000),(50655134347720589667/250000000000000000),(952919594925328927/1000000000000000000)⟩,(989243655366097281/1000000000000000000),(8345114859509159/20000000000000000),(21803859937015261/100000000000000000),(172655561433070353/1000000000000000000)⟩
theorem valid1331 : certificate1331.Valid := by decide +kernel
theorem sound1331 : certificate1331.Sound := rat_cut_bin_certificate_sound certificate1331 profilesValid1331 numericValid1331 valid1331

def certificates : List RatCutBinCertificate := [certificate1320,certificate1321,certificate1322,certificate1323,certificate1324,certificate1325,certificate1326,certificate1327,certificate1328,certificate1329,certificate1330,certificate1331]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1320,List.forall_mem_cons.mpr ⟨sound1321,List.forall_mem_cons.mpr ⟨sound1322,List.forall_mem_cons.mpr ⟨sound1323,List.forall_mem_cons.mpr ⟨sound1324,List.forall_mem_cons.mpr ⟨sound1325,List.forall_mem_cons.mpr ⟨sound1326,List.forall_mem_cons.mpr ⟨sound1327,List.forall_mem_cons.mpr ⟨sound1328,List.forall_mem_cons.mpr ⟨sound1329,List.forall_mem_cons.mpr ⟨sound1330,List.forall_mem_cons.mpr ⟨sound1331,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch110
