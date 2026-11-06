import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch337
import Cycle12.MergedCutProfiles.Batch338
import Cycle12.MergedCutProfiles.Batch465
import Cycle12.MergedCutProfiles.Batch466
import Cycle12.MergedCutProfiles.Batch597
import Cycle12.MergedCutProfiles.Batch598
import Cycle12.MergedCutProfiles.Batch656
import Cycle12.MergedCutProfiles.Batch657

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch385

def retention4620 : RatCutRetentionCertificate := ⟨(4/125),(33/1000),(6297787412783017922/4803249501802636639505),(593102819/500000000),(27/10),(2811713610195661372138346572391311439/1186205638000000000000000000000000000),true,MergedCutProfiles.Batch656.profile26275,![MergedCutProfiles.Batch656.profile26275,MergedCutProfiles.Batch465.profile18610,MergedCutProfiles.Batch597.profile23881,MergedCutProfiles.Batch465.profile18611,MergedCutProfiles.Batch465.profile18639,MergedCutProfiles.Batch657.profile26280,MergedCutProfiles.Batch337.profile13492,MergedCutProfiles.Batch657.profile26281,MergedCutProfiles.Batch338.profile13522,MergedCutProfiles.Batch657.profile26282,MergedCutProfiles.Batch465.profile18623,MergedCutProfiles.Batch597.profile23890,MergedCutProfiles.Batch657.profile26283,MergedCutProfiles.Batch597.profile23892,MergedCutProfiles.Batch465.profile18629,MergedCutProfiles.Batch657.profile26284]⟩
theorem profilesValid4620 : retention4620.ProfilesValid := by
  change ∀ j : Fin 16, (retention4620.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch656.valid26275
  · exact MergedCutProfiles.Batch465.valid18610
  · exact MergedCutProfiles.Batch597.valid23881
  · exact MergedCutProfiles.Batch465.valid18611
  · exact MergedCutProfiles.Batch465.valid18639
  · exact MergedCutProfiles.Batch657.valid26280
  · exact MergedCutProfiles.Batch337.valid13492
  · exact MergedCutProfiles.Batch657.valid26281
  · exact MergedCutProfiles.Batch338.valid13522
  · exact MergedCutProfiles.Batch657.valid26282
  · exact MergedCutProfiles.Batch465.valid18623
  · exact MergedCutProfiles.Batch597.valid23890
  · exact MergedCutProfiles.Batch657.valid26283
  · exact MergedCutProfiles.Batch597.valid23892
  · exact MergedCutProfiles.Batch465.valid18629
  · exact MergedCutProfiles.Batch657.valid26284
theorem numericValid4620 : retention4620.NumericValid := by decide +kernel
def certificate4620 : RatCutBinCertificate := ⟨⟨retention4620,(1860062754391343549/1000000000000000000),(481579510880593/10000000000000000),(10080661328367137021/1000000000000000000),(24334652116046352788149/500000000000000000),(2346350254957505941/1000000000000000000)⟩,(499981752498362213/500000000000000000),(211434142891305427/500000000000000000),(213170629364936139/1000000000000000000),(145706323309742793/1000000000000000000)⟩
theorem valid4620 : certificate4620.Valid := by decide +kernel
theorem sound4620 : certificate4620.Sound := rat_cut_bin_certificate_sound certificate4620 profilesValid4620 numericValid4620 valid4620

def retention4621 : RatCutRetentionCertificate := ⟨(4/125),(33/1000),(12800000000000000000/960649900360527327901),(3148893706391508961/500000000000000000),(23/20),(5547020720044462712427332480848524746871/2519114965113207168800000000000000000000),true,MergedCutProfiles.Batch465.profile18614,![MergedCutProfiles.Batch465.profile18614,MergedCutProfiles.Batch466.profile18641,MergedCutProfiles.Batch466.profile18642,MergedCutProfiles.Batch465.profile18633,MergedCutProfiles.Batch337.profile13484,MergedCutProfiles.Batch466.profile18644,MergedCutProfiles.Batch466.profile18646,MergedCutProfiles.Batch338.profile13529,MergedCutProfiles.Batch657.profile26285,MergedCutProfiles.Batch337.profile13504,MergedCutProfiles.Batch657.profile26286,MergedCutProfiles.Batch657.profile26287,MergedCutProfiles.Batch657.profile26288,MergedCutProfiles.Batch657.profile26289,MergedCutProfiles.Batch597.profile23896,MergedCutProfiles.Batch657.profile26290]⟩
theorem profilesValid4621 : retention4621.ProfilesValid := by
  change ∀ j : Fin 16, (retention4621.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch465.valid18614
  · exact MergedCutProfiles.Batch466.valid18641
  · exact MergedCutProfiles.Batch466.valid18642
  · exact MergedCutProfiles.Batch465.valid18633
  · exact MergedCutProfiles.Batch337.valid13484
  · exact MergedCutProfiles.Batch466.valid18644
  · exact MergedCutProfiles.Batch466.valid18646
  · exact MergedCutProfiles.Batch338.valid13529
  · exact MergedCutProfiles.Batch657.valid26285
  · exact MergedCutProfiles.Batch337.valid13504
  · exact MergedCutProfiles.Batch657.valid26286
  · exact MergedCutProfiles.Batch657.valid26287
  · exact MergedCutProfiles.Batch657.valid26288
  · exact MergedCutProfiles.Batch657.valid26289
  · exact MergedCutProfiles.Batch597.valid23896
  · exact MergedCutProfiles.Batch657.valid26290
theorem numericValid4621 : retention4621.NumericValid := by decide +kernel
def certificate4621 : RatCutBinCertificate := ⟨⟨retention4621,(1860062754391343549/1000000000000000000),(481579510880593/10000000000000000),(10080661328367137021/1000000000000000000),(24334652116046352788149/500000000000000000),(1095876566450444861/500000000000000000)⟩,(499981752498362213/500000000000000000),(266913944135866703/1000000000000000000),(190241712829602043/500000000000000000),(57405933689087339/100000000000000000)⟩
theorem valid4621 : certificate4621.Valid := by decide +kernel
theorem sound4621 : certificate4621.Sound := rat_cut_bin_certificate_sound certificate4621 profilesValid4621 numericValid4621 valid4621

def retention4622 : RatCutRetentionCertificate := ⟨(4/125),(33/1000),(1/2),64,1,(2553778241264668473974121578981079951/2560000000000000000000000000000000000),false,MergedCutProfiles.Batch338.profile13551,(fun _ => MergedCutProfiles.Batch338.profile13551)⟩
theorem profilesValid4622 : retention4622.ProfilesValid := by
  exact MergedCutProfiles.Batch338.valid13551
theorem numericValid4622 : retention4622.NumericValid := by decide +kernel
def certificate4622 : RatCutBinCertificate := ⟨⟨retention4622,(1860062754391343549/1000000000000000000),(481579510880593/10000000000000000),(10080661328367137021/1000000000000000000),(24334652116046352788149/500000000000000000),(988683619942018143/1000000000000000000)⟩,(499981752498362213/500000000000000000),(505535771248965883/1000000000000000000),(37404949050607961/250000000000000000),(72835422233446089/500000000000000000)⟩
theorem valid4622 : certificate4622.Valid := by decide +kernel
theorem sound4622 : certificate4622.Sound := rat_cut_bin_certificate_sound certificate4622 profilesValid4622 numericValid4622 valid4622

def retention4623 : RatCutRetentionCertificate := ⟨(4/125),(33/1000),(12800000000000000000/960649900360527327901),(5241874322976524153/200000000000000000),1,(232404122869049220383612637935485947451/104837486459530483060000000000000000000),false,MergedCutProfiles.Batch657.profile26291,(fun _ => MergedCutProfiles.Batch657.profile26291)⟩
theorem profilesValid4623 : retention4623.ProfilesValid := by
  exact MergedCutProfiles.Batch657.valid26291
theorem numericValid4623 : retention4623.NumericValid := by decide +kernel
def certificate4623 : RatCutBinCertificate := ⟨⟨retention4623,(1758280247391343549/1000000000000000000),(481579510880593/10000000000000000),(10080661328367137021/1000000000000000000),(24334652116046352788149/500000000000000000),(69012621501876491/31250000000000000)⟩,(124995687750508359/125000000000000000),(23202954824923749/1000000000000000000),(864337048303297439/1000000000000000000),(1760406038551281699/1000000000000000000)⟩
theorem valid4623 : certificate4623.Valid := by decide +kernel
theorem sound4623 : certificate4623.Sound := rat_cut_bin_certificate_sound certificate4623 profilesValid4623 numericValid4623 valid4623

def retention4624 : RatCutRetentionCertificate := ⟨(4/125),(33/1000),(1/2),64,1,(2553778241264668473974121578981079951/2560000000000000000000000000000000000),false,MergedCutProfiles.Batch338.profile13551,(fun _ => MergedCutProfiles.Batch338.profile13551)⟩
theorem profilesValid4624 : retention4624.ProfilesValid := by
  exact MergedCutProfiles.Batch338.valid13551
theorem numericValid4624 : retention4624.NumericValid := by decide +kernel
def certificate4624 : RatCutBinCertificate := ⟨⟨retention4624,(1758280247391343549/1000000000000000000),(481579510880593/10000000000000000),(10080661328367137021/1000000000000000000),(24334652116046352788149/500000000000000000),(494584930779745903/500000000000000000)⟩,(124995687750508359/125000000000000000),(51802524158042621/1000000000000000000),(391775158352634691/500000000000000000),(763240880845862119/1000000000000000000)⟩
theorem valid4624 : certificate4624.Valid := by decide +kernel
theorem sound4624 : certificate4624.Sound := rat_cut_bin_certificate_sound certificate4624 profilesValid4624 numericValid4624 valid4624

def retention4625 : RatCutRetentionCertificate := ⟨(4/125),(33/1000),(136014250574069866/960649900360527327901),(336668937064529371/500000000000000000),4,(99877778858106158440934683039533897/42083617133066171375000000000000000),false,MergedCutProfiles.Batch657.profile26292,(fun _ => MergedCutProfiles.Batch657.profile26292)⟩
theorem profilesValid4625 : retention4625.ProfilesValid := by
  exact MergedCutProfiles.Batch657.valid26292
theorem numericValid4625 : retention4625.NumericValid := by decide +kernel
def certificate4625 : RatCutBinCertificate := ⟨⟨retention4625,(1800198772391343549/1000000000000000000),(481579510880593/10000000000000000),(10080661328367137021/1000000000000000000),(24334652116046352788149/500000000000000000),(1169458631560774273/500000000000000000)⟩,(39998587181936827/40000000000000000),(867526871362980809/1000000000000000000),(9189932914623039/1000000000000000000),(13796610918503/3125000000000000)⟩
theorem valid4625 : certificate4625.Valid := by decide +kernel
theorem sound4625 : certificate4625.Sound := rat_cut_bin_certificate_sound certificate4625 profilesValid4625 numericValid4625 valid4625

def retention4626 : RatCutRetentionCertificate := ⟨(4/125),(33/1000),(982754966417161001/4803249501802636639505),(68007125287034933/100000000000000000),4,(64667214817675760632981933214575503/27202850114813973200000000000000000),false,MergedCutProfiles.Batch657.profile26293,(fun _ => MergedCutProfiles.Batch657.profile26293)⟩
theorem profilesValid4626 : retention4626.ProfilesValid := by
  exact MergedCutProfiles.Batch657.valid26293
theorem numericValid4626 : retention4626.NumericValid := by decide +kernel
def certificate4626 : RatCutBinCertificate := ⟨⟨retention4626,(1800198772391343549/1000000000000000000),(481579510880593/10000000000000000),(10080661328367137021/1000000000000000000),(24334652116046352788149/500000000000000000),(46856438967135803/20000000000000000)⟩,(39998587181936827/40000000000000000),(172740491268030191/200000000000000000),(9741858125033373/1000000000000000000),(4694785252486379/1000000000000000000)⟩
theorem valid4626 : certificate4626.Valid := by decide +kernel
theorem sound4626 : certificate4626.Sound := rat_cut_bin_certificate_sound certificate4626 profilesValid4626 numericValid4626 valid4626

def retention4627 : RatCutRetentionCertificate := ⟨(4/125),(33/1000),(13192399807008683429/4803249501802636639505),(982754966417161001/1000000000000000000),(67/20),(3727315300040971780106640949913254299871/1572407946267457601600000000000000000000),false,MergedCutProfiles.Batch657.profile26294,(fun _ => MergedCutProfiles.Batch657.profile26294)⟩
theorem profilesValid4627 : retention4627.ProfilesValid := by
  exact MergedCutProfiles.Batch657.valid26294
theorem numericValid4627 : retention4627.NumericValid := by decide +kernel
def certificate4627 : RatCutBinCertificate := ⟨⟨retention4627,(1800198772391343549/1000000000000000000),(481579510880593/10000000000000000),(10080661328367137021/1000000000000000000),(24334652116046352788149/500000000000000000),(234164048794725247/100000000000000000)⟩,(39998587181936827/40000000000000000),(790843293843393397/1000000000000000000),(5895255814281741/250000000000000000),(2719155676334893/200000000000000000)⟩
theorem valid4627 : certificate4627.Valid := by decide +kernel
theorem sound4627 : certificate4627.Sound := rat_cut_bin_certificate_sound certificate4627 profilesValid4627 numericValid4627 valid4627

def retention4628 : RatCutRetentionCertificate := ⟨(4/125),(33/1000),(1/40),(13192399807008683429/1000000000000000000),(23/20),(46264405285285075052153152951044857095551/21107839691213893486400000000000000000000),false,MergedCutProfiles.Batch657.profile26295,(fun _ => MergedCutProfiles.Batch657.profile26295)⟩
theorem profilesValid4628 : retention4628.ProfilesValid := by
  exact MergedCutProfiles.Batch657.valid26295
theorem numericValid4628 : retention4628.NumericValid := by decide +kernel
def certificate4628 : RatCutBinCertificate := ⟨⟨retention4628,(1800198772391343549/1000000000000000000),(481579510880593/10000000000000000),(10080661328367137021/1000000000000000000),(24334652116046352788149/500000000000000000),(2181921453662960069/1000000000000000000)⟩,(39998587181936827/40000000000000000),(685165383580192701/1000000000000000000),(13944246854986171/250000000000000000),(18811984661204623/200000000000000000)⟩
theorem valid4628 : certificate4628.Valid := by decide +kernel
theorem sound4628 : certificate4628.Sound := rat_cut_bin_certificate_sound certificate4628 profilesValid4628 numericValid4628 valid4628

def retention4629 : RatCutRetentionCertificate := ⟨(33/1000),(17/500),(621867221554335284/4501536247443668921467),(568597966056554031/1000000000000000000),4,(227842019419596246238765015995397/103306316507368101562500000000000),true,MergedCutProfiles.Batch657.profile26296,![MergedCutProfiles.Batch657.profile26296,MergedCutProfiles.Batch657.profile26297,MergedCutProfiles.Batch657.profile26298,MergedCutProfiles.Batch657.profile26299,MergedCutProfiles.Batch597.profile23910,MergedCutProfiles.Batch657.profile26300,MergedCutProfiles.Batch657.profile26301,MergedCutProfiles.Batch657.profile26302,MergedCutProfiles.Batch597.profile23911,MergedCutProfiles.Batch657.profile26303,MergedCutProfiles.Batch657.profile26303,MergedCutProfiles.Batch657.profile26304,MergedCutProfiles.Batch657.profile26305,MergedCutProfiles.Batch597.profile23912,MergedCutProfiles.Batch657.profile26306,MergedCutProfiles.Batch598.profile23933]⟩
theorem profilesValid4629 : retention4629.ProfilesValid := by
  change ∀ j : Fin 16, (retention4629.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch657.valid26296
  · exact MergedCutProfiles.Batch657.valid26297
  · exact MergedCutProfiles.Batch657.valid26298
  · exact MergedCutProfiles.Batch657.valid26299
  · exact MergedCutProfiles.Batch597.valid23910
  · exact MergedCutProfiles.Batch657.valid26300
  · exact MergedCutProfiles.Batch657.valid26301
  · exact MergedCutProfiles.Batch657.valid26302
  · exact MergedCutProfiles.Batch597.valid23911
  · exact MergedCutProfiles.Batch657.valid26303
  · exact MergedCutProfiles.Batch657.valid26303
  · exact MergedCutProfiles.Batch657.valid26304
  · exact MergedCutProfiles.Batch657.valid26305
  · exact MergedCutProfiles.Batch597.valid23912
  · exact MergedCutProfiles.Batch657.valid26306
  · exact MergedCutProfiles.Batch598.valid23933
theorem numericValid4629 : retention4629.NumericValid := by decide +kernel
def certificate4629 : RatCutBinCertificate := ⟨⟨retention4629,(4658249665960103/2500000000000000),(51337219122942991/1000000000000000000),(10227354861297963889/1000000000000000000),(46277353761204040216509/1000000000000000000),(2168087313331188699/1000000000000000000)⟩,(999961675194067381/1000000000000000000),(142165774330984017/200000000000000000),(46548483769719717/1000000000000000000),(20373751947703939/1000000000000000000)⟩
theorem valid4629 : certificate4629.Valid := by decide +kernel
theorem sound4629 : certificate4629.Sound := rat_cut_bin_certificate_sound certificate4629 profilesValid4629 numericValid4629 valid4629

def retention4630 : RatCutRetentionCertificate := ⟨(33/1000),(17/500),(1160508567000000000/4501536247443668921467),(155466805388583821/250000000000000000),4,(147634523628233679809/64000000000000000000),true,MergedCutProfiles.Batch657.profile26297,![MergedCutProfiles.Batch657.profile26297,MergedCutProfiles.Batch657.profile26307,MergedCutProfiles.Batch657.profile26300,MergedCutProfiles.Batch657.profile26308,MergedCutProfiles.Batch597.profile23911,MergedCutProfiles.Batch657.profile26304,MergedCutProfiles.Batch657.profile26305,MergedCutProfiles.Batch657.profile26306,MergedCutProfiles.Batch598.profile23933,MergedCutProfiles.Batch598.profile23922,MergedCutProfiles.Batch466.profile18650,MergedCutProfiles.Batch657.profile26309,MergedCutProfiles.Batch597.profile23914,MergedCutProfiles.Batch657.profile26310,MergedCutProfiles.Batch598.profile23923,MergedCutProfiles.Batch597.profile23915]⟩
theorem profilesValid4630 : retention4630.ProfilesValid := by
  change ∀ j : Fin 16, (retention4630.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch657.valid26297
  · exact MergedCutProfiles.Batch657.valid26307
  · exact MergedCutProfiles.Batch657.valid26300
  · exact MergedCutProfiles.Batch657.valid26308
  · exact MergedCutProfiles.Batch597.valid23911
  · exact MergedCutProfiles.Batch657.valid26304
  · exact MergedCutProfiles.Batch657.valid26305
  · exact MergedCutProfiles.Batch657.valid26306
  · exact MergedCutProfiles.Batch598.valid23933
  · exact MergedCutProfiles.Batch598.valid23922
  · exact MergedCutProfiles.Batch466.valid18650
  · exact MergedCutProfiles.Batch657.valid26309
  · exact MergedCutProfiles.Batch597.valid23914
  · exact MergedCutProfiles.Batch657.valid26310
  · exact MergedCutProfiles.Batch598.valid23923
  · exact MergedCutProfiles.Batch597.valid23915
theorem numericValid4630 : retention4630.NumericValid := by decide +kernel
def certificate4630 : RatCutBinCertificate := ⟨⟨retention4630,(4658249665960103/2500000000000000),(51337219122942991/1000000000000000000),(10227354861297963889/1000000000000000000),(46277353761204040216509/1000000000000000000),(2269377343232451573/1000000000000000000)⟩,(999961675194067381/1000000000000000000),(63952109119010269/100000000000000000),(74590164211483607/1000000000000000000),(8614328245586243/250000000000000000)⟩
theorem valid4630 : certificate4630.Valid := by decide +kernel
theorem sound4630 : certificate4630.Sound := rat_cut_bin_certificate_sound certificate4630 profilesValid4630 numericValid4630 valid4630

def retention4631 : RatCutRetentionCertificate := ⟨(33/1000),(17/500),(167945181461094923/643076606777666988781),(1160508567/1000000000),(11/4),(3712472803934562424917819069010727133/1547344756000000000000000000000000000),true,MergedCutProfiles.Batch657.profile26297,![MergedCutProfiles.Batch657.profile26297,MergedCutProfiles.Batch657.profile26307,MergedCutProfiles.Batch657.profile26300,MergedCutProfiles.Batch657.profile26308,MergedCutProfiles.Batch597.profile23911,MergedCutProfiles.Batch657.profile26304,MergedCutProfiles.Batch657.profile26305,MergedCutProfiles.Batch657.profile26306,MergedCutProfiles.Batch598.profile23933,MergedCutProfiles.Batch597.profile23913,MergedCutProfiles.Batch466.profile18650,MergedCutProfiles.Batch657.profile26309,MergedCutProfiles.Batch597.profile23914,MergedCutProfiles.Batch657.profile26310,MergedCutProfiles.Batch597.profile23915,MergedCutProfiles.Batch657.profile26311]⟩
theorem profilesValid4631 : retention4631.ProfilesValid := by
  change ∀ j : Fin 16, (retention4631.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch657.valid26297
  · exact MergedCutProfiles.Batch657.valid26307
  · exact MergedCutProfiles.Batch657.valid26300
  · exact MergedCutProfiles.Batch657.valid26308
  · exact MergedCutProfiles.Batch597.valid23911
  · exact MergedCutProfiles.Batch657.valid26304
  · exact MergedCutProfiles.Batch657.valid26305
  · exact MergedCutProfiles.Batch657.valid26306
  · exact MergedCutProfiles.Batch598.valid23933
  · exact MergedCutProfiles.Batch597.valid23913
  · exact MergedCutProfiles.Batch466.valid18650
  · exact MergedCutProfiles.Batch657.valid26309
  · exact MergedCutProfiles.Batch597.valid23914
  · exact MergedCutProfiles.Batch657.valid26310
  · exact MergedCutProfiles.Batch597.valid23915
  · exact MergedCutProfiles.Batch657.valid26311
theorem numericValid4631 : retention4631.NumericValid := by decide +kernel
def certificate4631 : RatCutBinCertificate := ⟨⟨retention4631,(4658249665960103/2500000000000000),(51337219122942991/1000000000000000000),(10227354861297963889/1000000000000000000),(46277353761204040216509/1000000000000000000),(2373533003471335441/1000000000000000000)⟩,(999961675194067381/1000000000000000000),(423967173206495441/1000000000000000000),(212226272055620057/1000000000000000000),(28834752394163549/200000000000000000)⟩
theorem valid4631 : certificate4631.Valid := by decide +kernel
theorem sound4631 : certificate4631.Sound := rat_cut_bin_certificate_sound certificate4631 profilesValid4631 numericValid4631 valid4631

def certificates : List RatCutBinCertificate := [certificate4620,certificate4621,certificate4622,certificate4623,certificate4624,certificate4625,certificate4626,certificate4627,certificate4628,certificate4629,certificate4630,certificate4631]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4620,List.forall_mem_cons.mpr ⟨sound4621,List.forall_mem_cons.mpr ⟨sound4622,List.forall_mem_cons.mpr ⟨sound4623,List.forall_mem_cons.mpr ⟨sound4624,List.forall_mem_cons.mpr ⟨sound4625,List.forall_mem_cons.mpr ⟨sound4626,List.forall_mem_cons.mpr ⟨sound4627,List.forall_mem_cons.mpr ⟨sound4628,List.forall_mem_cons.mpr ⟨sound4629,List.forall_mem_cons.mpr ⟨sound4630,List.forall_mem_cons.mpr ⟨sound4631,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch385
