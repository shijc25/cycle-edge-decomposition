import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch212
import Cycle12.MergedCutProfiles.Batch213

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch108

def retention1296 : RatCutRetentionCertificate := ⟨(233/4000),(117/2000),(1400295320291140612/13256000331978180397),(931200739807056869/1000000000000000000),(51/20),(603162486606186238863/320000000000000000000),true,MergedCutProfiles.Batch212.profile8505,![MergedCutProfiles.Batch212.profile8505,MergedCutProfiles.Batch212.profile8491,MergedCutProfiles.Batch212.profile8506,MergedCutProfiles.Batch212.profile8494,MergedCutProfiles.Batch212.profile8507,MergedCutProfiles.Batch212.profile8497,MergedCutProfiles.Batch212.profile8508,MergedCutProfiles.Batch212.profile8500,MergedCutProfiles.Batch212.profile8509,MergedCutProfiles.Batch212.profile8510,MergedCutProfiles.Batch212.profile8511,MergedCutProfiles.Batch212.profile8512,MergedCutProfiles.Batch212.profile8513,MergedCutProfiles.Batch212.profile8514,MergedCutProfiles.Batch212.profile8515,MergedCutProfiles.Batch212.profile8516]⟩
theorem profilesValid1296 : retention1296.ProfilesValid := by
  change ∀ j : Fin 16, (retention1296.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch212.valid8505
  · exact MergedCutProfiles.Batch212.valid8491
  · exact MergedCutProfiles.Batch212.valid8506
  · exact MergedCutProfiles.Batch212.valid8494
  · exact MergedCutProfiles.Batch212.valid8507
  · exact MergedCutProfiles.Batch212.valid8497
  · exact MergedCutProfiles.Batch212.valid8508
  · exact MergedCutProfiles.Batch212.valid8500
  · exact MergedCutProfiles.Batch212.valid8509
  · exact MergedCutProfiles.Batch212.valid8510
  · exact MergedCutProfiles.Batch212.valid8511
  · exact MergedCutProfiles.Batch212.valid8512
  · exact MergedCutProfiles.Batch212.valid8513
  · exact MergedCutProfiles.Batch212.valid8514
  · exact MergedCutProfiles.Batch212.valid8515
  · exact MergedCutProfiles.Batch212.valid8516
theorem numericValid1296 : retention1296.NumericValid := by decide +kernel
def certificate1296 : RatCutBinCertificate := ⟨⟨retention1296,(1146738186914770071/500000000000000000),(42966716513336319/250000000000000000),(15366096952548243309/1000000000000000000),(204001344332391525971/1000000000000000000),(22743083967091513/12500000000000000)⟩,(990651851972591847/1000000000000000000),(361239557981117387/1000000000000000000),(135468534715592573/500000000000000000),(18373053704656403/125000000000000000)⟩
theorem valid1296 : certificate1296.Valid := by decide +kernel
theorem sound1296 : certificate1296.Sound := rat_cut_bin_certificate_sound certificate1296 profilesValid1296 numericValid1296 valid1296

def retention1297 : RatCutRetentionCertificate := ⟨(233/4000),(117/2000),(3262393994325749674/13256000331978180397),(350073830072785153/250000000000000000),(37/20),(488006005712090195869/320000000000000000000),true,MergedCutProfiles.Batch212.profile8517,![MergedCutProfiles.Batch212.profile8517,MergedCutProfiles.Batch212.profile8495,MergedCutProfiles.Batch212.profile8518,MergedCutProfiles.Batch212.profile8502,MergedCutProfiles.Batch212.profile8519,MergedCutProfiles.Batch212.profile8514,MergedCutProfiles.Batch213.profile8520,MergedCutProfiles.Batch213.profile8521,MergedCutProfiles.Batch213.profile8522,MergedCutProfiles.Batch213.profile8523,MergedCutProfiles.Batch213.profile8524,MergedCutProfiles.Batch213.profile8525,MergedCutProfiles.Batch213.profile8526,MergedCutProfiles.Batch213.profile8527,MergedCutProfiles.Batch213.profile8528,MergedCutProfiles.Batch213.profile8529]⟩
theorem profilesValid1297 : retention1297.ProfilesValid := by
  change ∀ j : Fin 16, (retention1297.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch212.valid8517
  · exact MergedCutProfiles.Batch212.valid8495
  · exact MergedCutProfiles.Batch212.valid8518
  · exact MergedCutProfiles.Batch212.valid8502
  · exact MergedCutProfiles.Batch212.valid8519
  · exact MergedCutProfiles.Batch212.valid8514
  · exact MergedCutProfiles.Batch213.valid8520
  · exact MergedCutProfiles.Batch213.valid8521
  · exact MergedCutProfiles.Batch213.valid8522
  · exact MergedCutProfiles.Batch213.valid8523
  · exact MergedCutProfiles.Batch213.valid8524
  · exact MergedCutProfiles.Batch213.valid8525
  · exact MergedCutProfiles.Batch213.valid8526
  · exact MergedCutProfiles.Batch213.valid8527
  · exact MergedCutProfiles.Batch213.valid8528
  · exact MergedCutProfiles.Batch213.valid8529
theorem numericValid1297 : retention1297.NumericValid := by decide +kernel
def certificate1297 : RatCutBinCertificate := ⟨⟨retention1297,(1146738186914770071/500000000000000000),(42966716513336319/250000000000000000),(15366096952548243309/1000000000000000000),(204001344332391525971/1000000000000000000),(1477546956515191671/1000000000000000000)⟩,(990651851972591847/1000000000000000000),(96819472379370883/250000000000000000),(122671692276710741/500000000000000000),(18515061524647433/125000000000000000)⟩
theorem valid1297 : certificate1297.Valid := by decide +kernel
theorem sound1297 : certificate1297.Sound := rat_cut_bin_certificate_sound certificate1297 profilesValid1297 numericValid1297 valid1297

def retention1298 : RatCutRetentionCertificate := ⟨(233/4000),(117/2000),(5752474664109716383/13256000331978180397),(1631196997162874837/500000000000000000),(11/10),(701675591615093689481/640000000000000000000),true,MergedCutProfiles.Batch213.profile8530,![MergedCutProfiles.Batch213.profile8530,MergedCutProfiles.Batch213.profile8531,MergedCutProfiles.Batch213.profile8532,MergedCutProfiles.Batch213.profile8533,MergedCutProfiles.Batch213.profile8534,MergedCutProfiles.Batch213.profile8535,MergedCutProfiles.Batch213.profile8536,MergedCutProfiles.Batch213.profile8537,MergedCutProfiles.Batch213.profile8538,MergedCutProfiles.Batch213.profile8539,MergedCutProfiles.Batch213.profile8540,MergedCutProfiles.Batch213.profile8541,MergedCutProfiles.Batch213.profile8542,MergedCutProfiles.Batch213.profile8543,MergedCutProfiles.Batch213.profile8544,MergedCutProfiles.Batch213.profile8545]⟩
theorem profilesValid1298 : retention1298.ProfilesValid := by
  change ∀ j : Fin 16, (retention1298.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch213.valid8530
  · exact MergedCutProfiles.Batch213.valid8531
  · exact MergedCutProfiles.Batch213.valid8532
  · exact MergedCutProfiles.Batch213.valid8533
  · exact MergedCutProfiles.Batch213.valid8534
  · exact MergedCutProfiles.Batch213.valid8535
  · exact MergedCutProfiles.Batch213.valid8536
  · exact MergedCutProfiles.Batch213.valid8537
  · exact MergedCutProfiles.Batch213.valid8538
  · exact MergedCutProfiles.Batch213.valid8539
  · exact MergedCutProfiles.Batch213.valid8540
  · exact MergedCutProfiles.Batch213.valid8541
  · exact MergedCutProfiles.Batch213.valid8542
  · exact MergedCutProfiles.Batch213.valid8543
  · exact MergedCutProfiles.Batch213.valid8544
  · exact MergedCutProfiles.Batch213.valid8545
theorem numericValid1298 : retention1298.NumericValid := by decide +kernel
def certificate1298 : RatCutBinCertificate := ⟨⟨retention1298,(1146738186914770071/500000000000000000),(42966716513336319/250000000000000000),(15366096952548243309/1000000000000000000),(204001344332391525971/1000000000000000000),(1068144181729726941/1000000000000000000)⟩,(990651851972591847/1000000000000000000),(445513351957663129/1000000000000000000),(194276278238231983/1000000000000000000),(146900128331684681/1000000000000000000)⟩
theorem valid1298 : certificate1298.Valid := by decide +kernel
theorem sound1298 : certificate1298.Sound := rat_cut_bin_certificate_sound certificate1298 profilesValid1298 numericValid1298 valid1298

def retention1299 : RatCutRetentionCertificate := ⟨(233/4000),(117/2000),(6482032436718823566/13256000331978180397),(5752474664109716383/1000000000000000000),(11/10),(2335388012713009879108332715660477769951/2300989865643886553200000000000000000000),false,MergedCutProfiles.Batch213.profile8546,(fun _ => MergedCutProfiles.Batch213.profile8546)⟩
theorem profilesValid1299 : retention1299.ProfilesValid := by
  exact MergedCutProfiles.Batch213.valid8546
theorem numericValid1299 : retention1299.NumericValid := by decide +kernel
def certificate1299 : RatCutBinCertificate := ⟨⟨retention1299,(1146738186914770071/500000000000000000),(42966716513336319/250000000000000000),(15366096952548243309/1000000000000000000),(204001344332391525971/1000000000000000000),(246682054908998089/250000000000000000)⟩,(990651851972591847/1000000000000000000),(225243983120896249/500000000000000000),(11892617614994993/62500000000000000),(147979009887768051/1000000000000000000)⟩
theorem valid1299 : certificate1299.Valid := by decide +kernel
theorem sound1299 : certificate1299.Sound := rat_cut_bin_certificate_sound certificate1299 profilesValid1299 numericValid1299 valid1299

def retention1300 : RatCutRetentionCertificate := ⟨(233/4000),(117/2000),(6546852761086011802/13256000331978180397),(3241016218359411783/500000000000000000),(21/20),(2581197107237898179641375679154551652911/2592812974687529426400000000000000000000),false,MergedCutProfiles.Batch213.profile8547,(fun _ => MergedCutProfiles.Batch213.profile8547)⟩
theorem profilesValid1300 : retention1300.ProfilesValid := by
  exact MergedCutProfiles.Batch213.valid8547
theorem numericValid1300 : retention1300.NumericValid := by decide +kernel
def certificate1300 : RatCutBinCertificate := ⟨⟨retention1300,(1146738186914770071/500000000000000000),(42966716513336319/250000000000000000),(15366096952548243309/1000000000000000000),(204001344332391525971/1000000000000000000),(24214548494773869/25000000000000000)⟩,(990651851972591847/1000000000000000000),(454152991102474687/1000000000000000000),(187374202938330239/1000000000000000000),(75339496114067523/500000000000000000)⟩
theorem valid1300 : certificate1300.Valid := by decide +kernel
theorem sound1300 : certificate1300.Sound := rat_cut_bin_certificate_sound certificate1300 profilesValid1300 numericValid1300 valid1300

def retention1301 : RatCutRetentionCertificate := ⟨(233/4000),(117/2000),(6612321288696871921/13256000331978180397),(3273426380543005901/500000000000000000),(21/20),(2583346484881709311622897347594252383119/2618741104434404720800000000000000000000),false,MergedCutProfiles.Batch213.profile8548,(fun _ => MergedCutProfiles.Batch213.profile8548)⟩
theorem profilesValid1301 : retention1301.ProfilesValid := by
  exact MergedCutProfiles.Batch213.valid8548
theorem numericValid1301 : retention1301.NumericValid := by decide +kernel
def certificate1301 : RatCutBinCertificate := ⟨⟨retention1301,(1146738186914770071/500000000000000000),(42966716513336319/250000000000000000),(15366096952548243309/1000000000000000000),(204001344332391525971/1000000000000000000),(47977305345404657/50000000000000000)⟩,(990651851972591847/1000000000000000000),(114513344444286507/250000000000000000),(92156137839779183/500000000000000000),(147171013486540097/1000000000000000000)⟩
theorem valid1301 : certificate1301.Valid := by decide +kernel
theorem sound1301 : certificate1301.Sound := rat_cut_bin_certificate_sound certificate1301 profilesValid1301 numericValid1301 valid1301

def retention1302 : RatCutRetentionCertificate := ⟨(233/4000),(117/2000),(1/2),(6612321288696871921/1000000000000000000),(21/20),(10416522062642666828993170306862501879799/10579714061914995073600000000000000000000),false,MergedCutProfiles.Batch213.profile8549,(fun _ => MergedCutProfiles.Batch213.profile8549)⟩
theorem profilesValid1302 : retention1302.ProfilesValid := by
  exact MergedCutProfiles.Batch213.valid8549
theorem numericValid1302 : retention1302.NumericValid := by decide +kernel
def certificate1302 : RatCutBinCertificate := ⟨⟨retention1302,(1146738186914770071/500000000000000000),(42966716513336319/250000000000000000),(15366096952548243309/1000000000000000000),(204001344332391525971/1000000000000000000),(478818519598993093/500000000000000000)⟩,(990651851972591847/1000000000000000000),(458593227385553249/1000000000000000000),(36778219867197701/200000000000000000),(73373955703308007/500000000000000000)⟩
theorem valid1302 : certificate1302.Valid := by decide +kernel
theorem sound1302 : certificate1302.Sound := rat_cut_bin_certificate_sound certificate1302 profilesValid1302 numericValid1302 valid1302

def retention1303 : RatCutRetentionCertificate := ⟨(233/4000),(117/2000),(1/2),64,1,(255405594066448641120890838352219611999/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch213.profile8549,(fun _ => MergedCutProfiles.Batch213.profile8549)⟩
theorem profilesValid1303 : retention1303.ProfilesValid := by
  exact MergedCutProfiles.Batch213.valid8549
theorem numericValid1303 : retention1303.NumericValid := by decide +kernel
def certificate1303 : RatCutBinCertificate := ⟨⟨retention1303,(1146738186914770071/500000000000000000),(42966716513336319/250000000000000000),(15366096952548243309/1000000000000000000),(204001344332391525971/1000000000000000000),(486012833988849341/500000000000000000)⟩,(990651851972591847/1000000000000000000),(418828147232220941/1000000000000000000),(216667226899875697/1000000000000000000),(205497657562681117/1000000000000000000)⟩
theorem valid1303 : certificate1303.Valid := by decide +kernel
theorem sound1303 : certificate1303.Sound := rat_cut_bin_certificate_sound certificate1303 profilesValid1303 numericValid1303 valid1303

def retention1304 : RatCutRetentionCertificate := ⟨(233/4000),(117/2000),(6164811676123755951/13256000331978180397),(3566516652835385047/1000000000000000000),(6/5),(47387226754696919378863894824655872877/44581458160442313087500000000000000000),false,MergedCutProfiles.Batch213.profile8550,(fun _ => MergedCutProfiles.Batch213.profile8550)⟩
theorem profilesValid1304 : retention1304.ProfilesValid := by
  exact MergedCutProfiles.Batch213.valid8550
theorem numericValid1304 : retention1304.NumericValid := by decide +kernel
def certificate1304 : RatCutBinCertificate := ⟨⟨retention1304,(1313254154914770071/500000000000000000),(42966716513336319/250000000000000000),(15366096952548243309/1000000000000000000),(204001344332391525971/1000000000000000000),(20553528822665087/20000000000000000)⟩,(989291443667091549/1000000000000000000),(97580249085991201/250000000000000000),(242468750057895171/1000000000000000000),(170980816876825557/1000000000000000000)⟩
theorem valid1304 : certificate1304.Valid := by decide +kernel
theorem sound1304 : certificate1304.Sound := rat_cut_bin_certificate_sound certificate1304 profilesValid1304 numericValid1304 valid1304

def retention1305 : RatCutRetentionCertificate := ⟨(233/4000),(117/2000),(6544071818865692657/13256000331978180397),(6164811676123755951/1000000000000000000),(21/20),(9805257172105116319033914959905910506919/9863698681798009521600000000000000000000),false,MergedCutProfiles.Batch213.profile8551,(fun _ => MergedCutProfiles.Batch213.profile8551)⟩
theorem profilesValid1305 : retention1305.ProfilesValid := by
  exact MergedCutProfiles.Batch213.valid8551
theorem numericValid1305 : retention1305.NumericValid := by decide +kernel
def certificate1305 : RatCutBinCertificate := ⟨⟨retention1305,(1313254154914770071/500000000000000000),(42966716513336319/250000000000000000),(15366096952548243309/1000000000000000000),(204001344332391525971/1000000000000000000),(963225232460073283/1000000000000000000)⟩,(989291443667091549/1000000000000000000),(416438107002121893/1000000000000000000),(54688510057577253/250000000000000000),(86873824723198163/500000000000000000)⟩
theorem valid1305 : certificate1305.Valid := by decide +kernel
theorem sound1305 : certificate1305.Sound := rat_cut_bin_certificate_sound certificate1305 profilesValid1305 numericValid1305 valid1305

def retention1306 : RatCutRetentionCertificate := ⟨(233/4000),(117/2000),(6609512537054349584/13256000331978180397),(6544071818865692657/1000000000000000000),(21/20),(10333059315709170478598313799089566716751/10470514910185108251200000000000000000000),false,MergedCutProfiles.Batch213.profile8552,(fun _ => MergedCutProfiles.Batch213.profile8552)⟩
theorem profilesValid1306 : retention1306.ProfilesValid := by
  exact MergedCutProfiles.Batch213.valid8552
theorem numericValid1306 : retention1306.NumericValid := by decide +kernel
def certificate1306 : RatCutBinCertificate := ⟨⟨retention1306,(1313254154914770071/500000000000000000),(42966716513336319/250000000000000000),(15366096952548243309/1000000000000000000),(204001344332391525971/1000000000000000000),(956022499948522689/1000000000000000000)⟩,(989291443667091549/1000000000000000000),(419575577399015561/1000000000000000000),(108008713173595123/500000000000000000),(171682970801612767/1000000000000000000)⟩
theorem valid1306 : certificate1306.Valid := by decide +kernel
theorem sound1306 : certificate1306.Sound := rat_cut_bin_certificate_sound certificate1306 profilesValid1306 numericValid1306 valid1306

def retention1307 : RatCutRetentionCertificate := ⟨(233/4000),(117/2000),(1/2),(413094533565896849/62500000000000000),(21/20),(650746593200103529568573388401628911519/660951253705434958400000000000000000000),false,MergedCutProfiles.Batch213.profile8549,(fun _ => MergedCutProfiles.Batch213.profile8549)⟩
theorem profilesValid1307 : retention1307.ProfilesValid := by
  exact MergedCutProfiles.Batch213.valid8549
theorem numericValid1307 : retention1307.NumericValid := by decide +kernel
def certificate1307 : RatCutBinCertificate := ⟨⟨retention1307,(1313254154914770071/500000000000000000),(42966716513336319/250000000000000000),(15366096952548243309/1000000000000000000),(204001344332391525971/1000000000000000000),(190742211327425997/200000000000000000)⟩,(989291443667091549/1000000000000000000),(420592473612238019/1000000000000000000),(4302709889561057/20000000000000000),(170815448611090963/1000000000000000000)⟩
theorem valid1307 : certificate1307.Valid := by decide +kernel
theorem sound1307 : certificate1307.Sound := rat_cut_bin_certificate_sound certificate1307 profilesValid1307 numericValid1307 valid1307

def certificates : List RatCutBinCertificate := [certificate1296,certificate1297,certificate1298,certificate1299,certificate1300,certificate1301,certificate1302,certificate1303,certificate1304,certificate1305,certificate1306,certificate1307]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1296,List.forall_mem_cons.mpr ⟨sound1297,List.forall_mem_cons.mpr ⟨sound1298,List.forall_mem_cons.mpr ⟨sound1299,List.forall_mem_cons.mpr ⟨sound1300,List.forall_mem_cons.mpr ⟨sound1301,List.forall_mem_cons.mpr ⟨sound1302,List.forall_mem_cons.mpr ⟨sound1303,List.forall_mem_cons.mpr ⟨sound1304,List.forall_mem_cons.mpr ⟨sound1305,List.forall_mem_cons.mpr ⟨sound1306,List.forall_mem_cons.mpr ⟨sound1307,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch108
