import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch213
import Cycle12.MergedCutProfiles.Batch214
import Cycle12.MergedCutProfiles.Batch215

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch109

def retention1308 : RatCutRetentionCertificate := ⟨(117/2000),(47/800),(911492599947105237/13123523113560400721),(850165604702613157/1000000000000000000),(11/4),(3973849848077273719/2000000000000000000),true,MergedCutProfiles.Batch213.profile8553,![MergedCutProfiles.Batch213.profile8553,MergedCutProfiles.Batch213.profile8554,MergedCutProfiles.Batch213.profile8555,MergedCutProfiles.Batch213.profile8556,MergedCutProfiles.Batch213.profile8557,MergedCutProfiles.Batch213.profile8558,MergedCutProfiles.Batch213.profile8559,MergedCutProfiles.Batch214.profile8560,MergedCutProfiles.Batch214.profile8561,MergedCutProfiles.Batch214.profile8562,MergedCutProfiles.Batch214.profile8563,MergedCutProfiles.Batch214.profile8564,MergedCutProfiles.Batch214.profile8565,MergedCutProfiles.Batch214.profile8566,MergedCutProfiles.Batch214.profile8567,MergedCutProfiles.Batch214.profile8568]⟩
theorem profilesValid1308 : retention1308.ProfilesValid := by
  change ∀ j : Fin 16, (retention1308.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch213.valid8553
  · exact MergedCutProfiles.Batch213.valid8554
  · exact MergedCutProfiles.Batch213.valid8555
  · exact MergedCutProfiles.Batch213.valid8556
  · exact MergedCutProfiles.Batch213.valid8557
  · exact MergedCutProfiles.Batch213.valid8558
  · exact MergedCutProfiles.Batch213.valid8559
  · exact MergedCutProfiles.Batch214.valid8560
  · exact MergedCutProfiles.Batch214.valid8561
  · exact MergedCutProfiles.Batch214.valid8562
  · exact MergedCutProfiles.Batch214.valid8563
  · exact MergedCutProfiles.Batch214.valid8564
  · exact MergedCutProfiles.Batch214.valid8565
  · exact MergedCutProfiles.Batch214.valid8566
  · exact MergedCutProfiles.Batch214.valid8567
  · exact MergedCutProfiles.Batch214.valid8568
theorem numericValid1308 : retention1308.NumericValid := by decide +kernel
def certificate1308 : RatCutBinCertificate := ⟨⟨retention1308,(4488709885672521/1953125000000000),(86798448590065447/500000000000000000),(15435416906887000289/1000000000000000000),(12679638681241212941/62500000000000000),(383163769762253197/200000000000000000)⟩,(15478119320647879/15625000000000000),(177431284017285227/500000000000000000),(277485985828402001/1000000000000000000),(147251439255877677/1000000000000000000)⟩
theorem valid1308 : certificate1308.Valid := by decide +kernel
theorem sound1308 : certificate1308.Sound := rat_cut_bin_certificate_sound certificate1308 profilesValid1308 numericValid1308 valid1308

def retention1309 : RatCutRetentionCertificate := ⟨(117/2000),(47/800),(1278438543749678361/13123523113560400721),(911492599947105237/1000000000000000000),(13/5),(610847080498664912233/320000000000000000000),true,MergedCutProfiles.Batch214.profile8569,![MergedCutProfiles.Batch214.profile8569,MergedCutProfiles.Batch214.profile8570,MergedCutProfiles.Batch214.profile8571,MergedCutProfiles.Batch214.profile8572,MergedCutProfiles.Batch213.profile8559,MergedCutProfiles.Batch214.profile8573,MergedCutProfiles.Batch214.profile8574,MergedCutProfiles.Batch214.profile8575,MergedCutProfiles.Batch214.profile8576,MergedCutProfiles.Batch214.profile8577,MergedCutProfiles.Batch214.profile8578,MergedCutProfiles.Batch214.profile8579,MergedCutProfiles.Batch214.profile8580,MergedCutProfiles.Batch214.profile8581,MergedCutProfiles.Batch214.profile8582,MergedCutProfiles.Batch214.profile8583]⟩
theorem profilesValid1309 : retention1309.ProfilesValid := by
  change ∀ j : Fin 16, (retention1309.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch214.valid8569
  · exact MergedCutProfiles.Batch214.valid8570
  · exact MergedCutProfiles.Batch214.valid8571
  · exact MergedCutProfiles.Batch214.valid8572
  · exact MergedCutProfiles.Batch213.valid8559
  · exact MergedCutProfiles.Batch214.valid8573
  · exact MergedCutProfiles.Batch214.valid8574
  · exact MergedCutProfiles.Batch214.valid8575
  · exact MergedCutProfiles.Batch214.valid8576
  · exact MergedCutProfiles.Batch214.valid8577
  · exact MergedCutProfiles.Batch214.valid8578
  · exact MergedCutProfiles.Batch214.valid8579
  · exact MergedCutProfiles.Batch214.valid8580
  · exact MergedCutProfiles.Batch214.valid8581
  · exact MergedCutProfiles.Batch214.valid8582
  · exact MergedCutProfiles.Batch214.valid8583
theorem numericValid1309 : retention1309.NumericValid := by decide +kernel
def certificate1309 : RatCutBinCertificate := ⟨⟨retention1309,(4488709885672521/1953125000000000),(86798448590065447/500000000000000000),(15435416906887000289/1000000000000000000),(12679638681241212941/62500000000000000),(1841669895867142427/1000000000000000000)⟩,(15478119320647879/15625000000000000),(89747580432552261/250000000000000000),(273234008861207583/1000000000000000000),(29465028662874979/200000000000000000)⟩
theorem valid1309 : certificate1309.Valid := by decide +kernel
theorem sound1309 : certificate1309.Sound := rat_cut_bin_certificate_sound certificate1309 profilesValid1309 numericValid1309 valid1309

def retention1310 : RatCutRetentionCertificate := ⟨(117/2000),(47/800),(2890896251078546939/13123523113560400721),(1278438543749678361/1000000000000000000),(39/20),(2025921646696988317641/1280000000000000000000),true,MergedCutProfiles.Batch214.profile8584,![MergedCutProfiles.Batch214.profile8584,MergedCutProfiles.Batch214.profile8585,MergedCutProfiles.Batch214.profile8586,MergedCutProfiles.Batch214.profile8587,MergedCutProfiles.Batch214.profile8588,MergedCutProfiles.Batch214.profile8589,MergedCutProfiles.Batch214.profile8590,MergedCutProfiles.Batch214.profile8591,MergedCutProfiles.Batch214.profile8592,MergedCutProfiles.Batch214.profile8593,MergedCutProfiles.Batch214.profile8594,MergedCutProfiles.Batch214.profile8595,MergedCutProfiles.Batch214.profile8596,MergedCutProfiles.Batch214.profile8597,MergedCutProfiles.Batch214.profile8598,MergedCutProfiles.Batch214.profile8599]⟩
theorem profilesValid1310 : retention1310.ProfilesValid := by
  change ∀ j : Fin 16, (retention1310.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch214.valid8584
  · exact MergedCutProfiles.Batch214.valid8585
  · exact MergedCutProfiles.Batch214.valid8586
  · exact MergedCutProfiles.Batch214.valid8587
  · exact MergedCutProfiles.Batch214.valid8588
  · exact MergedCutProfiles.Batch214.valid8589
  · exact MergedCutProfiles.Batch214.valid8590
  · exact MergedCutProfiles.Batch214.valid8591
  · exact MergedCutProfiles.Batch214.valid8592
  · exact MergedCutProfiles.Batch214.valid8593
  · exact MergedCutProfiles.Batch214.valid8594
  · exact MergedCutProfiles.Batch214.valid8595
  · exact MergedCutProfiles.Batch214.valid8596
  · exact MergedCutProfiles.Batch214.valid8597
  · exact MergedCutProfiles.Batch214.valid8598
  · exact MergedCutProfiles.Batch214.valid8599
theorem numericValid1310 : retention1310.NumericValid := by decide +kernel
def certificate1310 : RatCutBinCertificate := ⟨⟨retention1310,(4488709885672521/1953125000000000),(86798448590065447/500000000000000000),(15435416906887000289/1000000000000000000),(12679638681241212941/62500000000000000),(306466352381756329/200000000000000000)⟩,(15478119320647879/15625000000000000),(23929692955089177/62500000000000000),(1559654915196239/6250000000000000),(73716908204416191/500000000000000000)⟩
theorem valid1310 : certificate1310.Valid := by decide +kernel
theorem sound1310 : certificate1310.Sound := rat_cut_bin_certificate_sound certificate1310 profilesValid1310 numericValid1310 valid1310

def retention1311 : RatCutRetentionCertificate := ⟨(117/2000),(47/800),(5465129131285382781/13123523113560400721),(2890896251078546939/1000000000000000000),(6/5),(1465637121327015612519/1280000000000000000000),true,MergedCutProfiles.Batch213.profile8558,![MergedCutProfiles.Batch213.profile8558,MergedCutProfiles.Batch214.profile8564,MergedCutProfiles.Batch215.profile8600,MergedCutProfiles.Batch215.profile8601,MergedCutProfiles.Batch215.profile8602,MergedCutProfiles.Batch215.profile8603,MergedCutProfiles.Batch215.profile8604,MergedCutProfiles.Batch215.profile8605,MergedCutProfiles.Batch215.profile8606,MergedCutProfiles.Batch215.profile8607,MergedCutProfiles.Batch215.profile8608,MergedCutProfiles.Batch215.profile8609,MergedCutProfiles.Batch215.profile8610,MergedCutProfiles.Batch215.profile8611,MergedCutProfiles.Batch215.profile8612,MergedCutProfiles.Batch215.profile8613]⟩
theorem profilesValid1311 : retention1311.ProfilesValid := by
  change ∀ j : Fin 16, (retention1311.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch213.valid8558
  · exact MergedCutProfiles.Batch214.valid8564
  · exact MergedCutProfiles.Batch215.valid8600
  · exact MergedCutProfiles.Batch215.valid8601
  · exact MergedCutProfiles.Batch215.valid8602
  · exact MergedCutProfiles.Batch215.valid8603
  · exact MergedCutProfiles.Batch215.valid8604
  · exact MergedCutProfiles.Batch215.valid8605
  · exact MergedCutProfiles.Batch215.valid8606
  · exact MergedCutProfiles.Batch215.valid8607
  · exact MergedCutProfiles.Batch215.valid8608
  · exact MergedCutProfiles.Batch215.valid8609
  · exact MergedCutProfiles.Batch215.valid8610
  · exact MergedCutProfiles.Batch215.valid8611
  · exact MergedCutProfiles.Batch215.valid8612
  · exact MergedCutProfiles.Batch215.valid8613
theorem numericValid1311 : retention1311.NumericValid := by decide +kernel
def certificate1311 : RatCutBinCertificate := ⟨⟨retention1311,(4488709885672521/1953125000000000),(86798448590065447/500000000000000000),(15435416906887000289/1000000000000000000),(12679638681241212941/62500000000000000),(557002298459187909/500000000000000000)⟩,(15478119320647879/15625000000000000),(217028315703021969/500000000000000000),(203687802913864679/1000000000000000000),(147574016021164707/1000000000000000000)⟩
theorem valid1311 : certificate1311.Valid := by decide +kernel
theorem sound1311 : certificate1311.Sound := rat_cut_bin_certificate_sound certificate1311 profilesValid1311 numericValid1311 valid1311

def retention1312 : RatCutRetentionCertificate := ⟨(117/2000),(47/800),(6344845258510538434/13123523113560400721),(5465129131285382781/1000000000000000000),(11/10),(2238256008912450260589993386779203289799/2186051652514153112400000000000000000000),false,MergedCutProfiles.Batch215.profile8614,(fun _ => MergedCutProfiles.Batch215.profile8614)⟩
theorem profilesValid1312 : retention1312.ProfilesValid := by
  exact MergedCutProfiles.Batch215.valid8614
theorem numericValid1312 : retention1312.NumericValid := by decide +kernel
def certificate1312 : RatCutBinCertificate := ⟨⟨retention1312,(4488709885672521/1953125000000000),(86798448590065447/500000000000000000),(15435416906887000289/1000000000000000000),(12679638681241212941/62500000000000000),(248861147268487883/250000000000000000)⟩,(15478119320647879/15625000000000000),(223527724284740359/500000000000000000),(193032131458149417/1000000000000000000),(150275138350248109/1000000000000000000)⟩
theorem valid1312 : certificate1312.Valid := by decide +kernel
theorem sound1312 : certificate1312.Sound := rat_cut_bin_certificate_sound certificate1312 profilesValid1312 numericValid1312 valid1312

def retention1313 : RatCutRetentionCertificate := ⟨(117/2000),(47/800),(6472376648206600258/13123523113560400721),(3172422629255269217/500000000000000000),(21/20),(2527932481198251366729087678653938575311/2537938103404215373600000000000000000000),false,MergedCutProfiles.Batch215.profile8615,(fun _ => MergedCutProfiles.Batch215.profile8615)⟩
theorem profilesValid1313 : retention1313.ProfilesValid := by
  exact MergedCutProfiles.Batch215.valid8615
theorem numericValid1313 : retention1313.NumericValid := by decide +kernel
def certificate1313 : RatCutBinCertificate := ⟨⟨retention1313,(4488709885672521/1953125000000000),(86798448590065447/500000000000000000),(15435416906887000289/1000000000000000000),(12679638681241212941/62500000000000000),(121114304146206979/125000000000000000)⟩,(15478119320647879/15625000000000000),(453105836679716691/1000000000000000000),(188201943703932989/1000000000000000000),(30197931421178103/200000000000000000)⟩
theorem valid1313 : certificate1313.Valid := by decide +kernel
theorem sound1313 : certificate1313.Sound := rat_cut_bin_certificate_sound certificate1313 profilesValid1313 numericValid1313 valid1313

def retention1314 : RatCutRetentionCertificate := ⟨(117/2000),(47/800),(6537100414688666261/13123523113560400721),(3236188324103300129/500000000000000000),(21/20),(2556359130710326108770040366409989573959/2588950659282640103200000000000000000000),false,MergedCutProfiles.Batch215.profile8616,(fun _ => MergedCutProfiles.Batch215.profile8616)⟩
theorem profilesValid1314 : retention1314.ProfilesValid := by
  exact MergedCutProfiles.Batch215.valid8616
theorem numericValid1314 : retention1314.NumericValid := by decide +kernel
def certificate1314 : RatCutBinCertificate := ⟨⟨retention1314,(4488709885672521/1953125000000000),(86798448590065447/500000000000000000),(15435416906887000289/1000000000000000000),(12679638681241212941/62500000000000000),(240067055361939589/250000000000000000)⟩,(15478119320647879/15625000000000000),(18256839169471379/40000000000000000),(92794851550735001/500000000000000000),(148079668644826451/1000000000000000000)⟩
theorem valid1314 : certificate1314.Valid := by decide +kernel
theorem sound1314 : certificate1314.Sound := rat_cut_bin_certificate_sound certificate1314 profilesValid1314 numericValid1314 valid1314

def retention1315 : RatCutRetentionCertificate := ⟨(117/2000),(47/800),(1/2),(6537100414688666261/1000000000000000000),(21/20),(10293966373591845018466877883488138841239/10459360663501866017600000000000000000000),false,MergedCutProfiles.Batch215.profile8617,(fun _ => MergedCutProfiles.Batch215.profile8617)⟩
theorem profilesValid1315 : retention1315.ProfilesValid := by
  exact MergedCutProfiles.Batch215.valid8617
theorem numericValid1315 : retention1315.NumericValid := by decide +kernel
def certificate1315 : RatCutBinCertificate := ⟨⟨retention1315,(4488709885672521/1953125000000000),(86798448590065447/500000000000000000),(15435416906887000289/1000000000000000000),(12679638681241212941/62500000000000000),(239260979309884203/250000000000000000)⟩,(15478119320647879/15625000000000000),(228790385534537761/500000000000000000),(7387260525175903/40000000000000000),(73545961684133593/500000000000000000)⟩
theorem valid1315 : certificate1315.Valid := by decide +kernel
theorem sound1315 : certificate1315.Sound := rat_cut_bin_certificate_sound certificate1315 profilesValid1315 numericValid1315 valid1315

def retention1316 : RatCutRetentionCertificate := ⟨(117/2000),(47/800),(1/2),64,1,(63851490842319608675685978453670207791/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch215.profile8617,(fun _ => MergedCutProfiles.Batch215.profile8617)⟩
theorem profilesValid1316 : retention1316.ProfilesValid := by
  exact MergedCutProfiles.Batch215.valid8617
theorem numericValid1316 : retention1316.NumericValid := by decide +kernel
def certificate1316 : RatCutBinCertificate := ⟨⟨retention1316,(4488709885672521/1953125000000000),(86798448590065447/500000000000000000),(15435416906887000289/1000000000000000000),(12679638681241212941/62500000000000000),(971831904263448079/1000000000000000000)⟩,(15478119320647879/15625000000000000),(2086020304971841/5000000000000000),(54520943560526953/250000000000000000),(103394766969679301/500000000000000000)⟩
theorem valid1316 : certificate1316.Valid := by decide +kernel
theorem sound1316 : certificate1316.Sound := rat_cut_bin_certificate_sound certificate1316 profilesValid1316 numericValid1316 valid1316

def retention1317 : RatCutRetentionCertificate := ⟨(117/2000),(47/800),(6109991424784432325/13123523113560400721),(3570149614151003697/1000000000000000000),(6/5),(379145983673701066092255013167281235191/357014961415100369700000000000000000000),false,MergedCutProfiles.Batch215.profile8618,(fun _ => MergedCutProfiles.Batch215.profile8618)⟩
theorem profilesValid1317 : retention1317.ProfilesValid := by
  exact MergedCutProfiles.Batch215.valid8618
theorem numericValid1317 : retention1317.NumericValid := by decide +kernel
def certificate1317 : RatCutBinCertificate := ⟨⟨retention1317,(1283445517804849/488281250000000),(86798448590065447/500000000000000000),(15435416906887000289/1000000000000000000),(12679638681241212941/62500000000000000),(128313475852034281/125000000000000000)⟩,(247311424294230257/250000000000000000),(48654394168637017/125000000000000000),(24349174823601013/100000000000000000),(42889845771924829/250000000000000000)⟩
theorem valid1317 : certificate1317.Valid := by decide +kernel
theorem sound1317 : certificate1317.Sound := rat_cut_bin_certificate_sound certificate1317 profilesValid1317 numericValid1317 valid1317

def retention1318 : RatCutRetentionCertificate := ⟨(117/2000),(47/800),(6485879017407989170/13123523113560400721),(244399656991377293/40000000000000000),(21/20),(388184219716908687562367343175180060239/391039451186203668800000000000000000000),false,MergedCutProfiles.Batch215.profile8619,(fun _ => MergedCutProfiles.Batch215.profile8619)⟩
theorem profilesValid1318 : retention1318.ProfilesValid := by
  exact MergedCutProfiles.Batch215.valid8619
theorem numericValid1318 : retention1318.NumericValid := by decide +kernel
def certificate1318 : RatCutBinCertificate := ⟨⟨retention1318,(1283445517804849/488281250000000),(86798448590065447/500000000000000000),(15435416906887000289/1000000000000000000),(12679638681241212941/62500000000000000),(961654316554359303/1000000000000000000)⟩,(247311424294230257/250000000000000000),(415484979084572523/1000000000000000000),(219590064117978799/1000000000000000000),(86979446524251671/500000000000000000)⟩
theorem valid1318 : certificate1318.Valid := by decide +kernel
theorem sound1318 : certificate1318.Sound := rat_cut_bin_certificate_sound certificate1318 profilesValid1318 numericValid1318 valid1318

def retention1319 : RatCutRetentionCertificate := ⟨(117/2000),(47/800),(6550737807582069062/13123523113560400721),(648587901740798917/100000000000000000),(21/20),(102270470013280194613242616878040762511/103774064278527826720000000000000000000),false,MergedCutProfiles.Batch215.profile8620,(fun _ => MergedCutProfiles.Batch215.profile8620)⟩
theorem profilesValid1319 : retention1319.ProfilesValid := by
  exact MergedCutProfiles.Batch215.valid8620
theorem numericValid1319 : retention1319.NumericValid := by decide +kernel
def certificate1319 : RatCutBinCertificate := ⟨⟨retention1319,(1283445517804849/488281250000000),(86798448590065447/500000000000000000),(15435416906887000289/1000000000000000000),(12679638681241212941/62500000000000000),(238616771967832591/250000000000000000)⟩,(247311424294230257/250000000000000000),(418613620812496493/1000000000000000000),(108426988990468457/500000000000000000),(171910071139547/1000000000000000)⟩
theorem valid1319 : certificate1319.Valid := by decide +kernel
theorem sound1319 : certificate1319.Sound := rat_cut_bin_certificate_sound certificate1319 profilesValid1319 numericValid1319 valid1319

def certificates : List RatCutBinCertificate := [certificate1308,certificate1309,certificate1310,certificate1311,certificate1312,certificate1313,certificate1314,certificate1315,certificate1316,certificate1317,certificate1318,certificate1319]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1308,List.forall_mem_cons.mpr ⟨sound1309,List.forall_mem_cons.mpr ⟨sound1310,List.forall_mem_cons.mpr ⟨sound1311,List.forall_mem_cons.mpr ⟨sound1312,List.forall_mem_cons.mpr ⟨sound1313,List.forall_mem_cons.mpr ⟨sound1314,List.forall_mem_cons.mpr ⟨sound1315,List.forall_mem_cons.mpr ⟨sound1316,List.forall_mem_cons.mpr ⟨sound1317,List.forall_mem_cons.mpr ⟨sound1318,List.forall_mem_cons.mpr ⟨sound1319,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch109
