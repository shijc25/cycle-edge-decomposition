import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch162
import Cycle12.MergedCutProfiles.Batch163
import Cycle12.MergedCutProfiles.Batch164

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch081

def retention972 : RatCutRetentionCertificate := ⟨(51/1000),(41/800),(1/2),(1797154591475572169/200000000000000000),(21/20),(571105622095812529163400966792655125791/575089469272183094080000000000000000000),false,MergedCutProfiles.Batch162.profile6515,(fun _ => MergedCutProfiles.Batch162.profile6515)⟩
theorem profilesValid972 : retention972.ProfilesValid := by
  exact MergedCutProfiles.Batch162.valid6515
theorem numericValid972 : retention972.NumericValid := by decide +kernel
def certificate972 : RatCutBinCertificate := ⟨⟨retention972,(2550378879450865399/1000000000000000000),(126628854218784741/1000000000000000000),(13545089729628503117/1000000000000000000),(244546577768143902817/1000000000000000000),(484018217810129569/500000000000000000)⟩,(198172956800622417/200000000000000000),(421248758113888971/1000000000000000000),(4291352373538269/20000000000000000),(89241524923467629/500000000000000000)⟩
theorem valid972 : certificate972.Valid := by decide +kernel
theorem sound972 : certificate972.Sound := rat_cut_bin_certificate_sound certificate972 profilesValid972 numericValid972 valid972

def retention973 : RatCutRetentionCertificate := ⟨(41/800),(103/2000),(313037245496718352/5942621241730892643),(170033120808722371/200000000000000000),(57/20),(523104418556674489419/256000000000000000000),true,MergedCutProfiles.Batch162.profile6519,![MergedCutProfiles.Batch162.profile6519,MergedCutProfiles.Batch163.profile6520,MergedCutProfiles.Batch163.profile6521,MergedCutProfiles.Batch163.profile6522,MergedCutProfiles.Batch163.profile6523,MergedCutProfiles.Batch163.profile6524,MergedCutProfiles.Batch163.profile6525,MergedCutProfiles.Batch163.profile6526,MergedCutProfiles.Batch163.profile6527,MergedCutProfiles.Batch163.profile6528,MergedCutProfiles.Batch163.profile6529,MergedCutProfiles.Batch163.profile6530,MergedCutProfiles.Batch163.profile6531,MergedCutProfiles.Batch163.profile6532,MergedCutProfiles.Batch163.profile6533,MergedCutProfiles.Batch163.profile6534]⟩
theorem profilesValid973 : retention973.ProfilesValid := by
  change ∀ j : Fin 16, (retention973.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch162.valid6519
  · exact MergedCutProfiles.Batch163.valid6520
  · exact MergedCutProfiles.Batch163.valid6521
  · exact MergedCutProfiles.Batch163.valid6522
  · exact MergedCutProfiles.Batch163.valid6523
  · exact MergedCutProfiles.Batch163.valid6524
  · exact MergedCutProfiles.Batch163.valid6525
  · exact MergedCutProfiles.Batch163.valid6526
  · exact MergedCutProfiles.Batch163.valid6527
  · exact MergedCutProfiles.Batch163.valid6528
  · exact MergedCutProfiles.Batch163.valid6529
  · exact MergedCutProfiles.Batch163.valid6530
  · exact MergedCutProfiles.Batch163.valid6531
  · exact MergedCutProfiles.Batch163.valid6532
  · exact MergedCutProfiles.Batch163.valid6533
  · exact MergedCutProfiles.Batch163.valid6534
theorem numericValid973 : retention973.NumericValid := by decide +kernel
def certificate973 : RatCutBinCertificate := ⟨⟨retention973,(2191989654154948687/1000000000000000000),(64019242937268319/500000000000000000),(3400570858551781727/250000000000000000),(48570040808067511363/200000000000000000),(992279567523679527/500000000000000000)⟩,(39684303381502337/40000000000000000),(369272363871878947/1000000000000000000),(262847485092635593/1000000000000000000),(35209597743004501/250000000000000000)⟩
theorem valid973 : certificate973.Valid := by decide +kernel
theorem sound973 : certificate973.Sound := rat_cut_bin_certificate_sound certificate973 profilesValid973 numericValid973 valid973

def retention974 : RatCutRetentionCertificate := ⟨(41/800),(103/2000),(1623277713759375427/17827863725192677929),(58694483530634691/62500000000000000),(13/5),(9622989159426664291/5000000000000000000),true,MergedCutProfiles.Batch163.profile6535,![MergedCutProfiles.Batch163.profile6535,MergedCutProfiles.Batch163.profile6536,MergedCutProfiles.Batch163.profile6537,MergedCutProfiles.Batch163.profile6538,MergedCutProfiles.Batch163.profile6539,MergedCutProfiles.Batch163.profile6540,MergedCutProfiles.Batch163.profile6541,MergedCutProfiles.Batch163.profile6542,MergedCutProfiles.Batch163.profile6543,MergedCutProfiles.Batch163.profile6544,MergedCutProfiles.Batch163.profile6545,MergedCutProfiles.Batch163.profile6546,MergedCutProfiles.Batch163.profile6547,MergedCutProfiles.Batch163.profile6548,MergedCutProfiles.Batch163.profile6549,MergedCutProfiles.Batch163.profile6550]⟩
theorem profilesValid974 : retention974.ProfilesValid := by
  change ∀ j : Fin 16, (retention974.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch163.valid6535
  · exact MergedCutProfiles.Batch163.valid6536
  · exact MergedCutProfiles.Batch163.valid6537
  · exact MergedCutProfiles.Batch163.valid6538
  · exact MergedCutProfiles.Batch163.valid6539
  · exact MergedCutProfiles.Batch163.valid6540
  · exact MergedCutProfiles.Batch163.valid6541
  · exact MergedCutProfiles.Batch163.valid6542
  · exact MergedCutProfiles.Batch163.valid6543
  · exact MergedCutProfiles.Batch163.valid6544
  · exact MergedCutProfiles.Batch163.valid6545
  · exact MergedCutProfiles.Batch163.valid6546
  · exact MergedCutProfiles.Batch163.valid6547
  · exact MergedCutProfiles.Batch163.valid6548
  · exact MergedCutProfiles.Batch163.valid6549
  · exact MergedCutProfiles.Batch163.valid6550
theorem numericValid974 : retention974.NumericValid := by decide +kernel
def certificate974 : RatCutBinCertificate := ⟨⟨retention974,(2191989654154948687/1000000000000000000),(64019242937268319/500000000000000000),(3400570858551781727/250000000000000000),(48570040808067511363/200000000000000000),(7308358793965573/3906250000000000)⟩,(39684303381502337/40000000000000000),(188355554406676537/500000000000000000),(51102386291409241/200000000000000000),(70341489098278861/500000000000000000)⟩
theorem valid974 : certificate974.Valid := by decide +kernel
theorem sound974 : certificate974.Sound := rat_cut_bin_certificate_sound certificate974 profilesValid974 numericValid974 valid974

def retention975 : RatCutRetentionCertificate := ⟨(41/800),(103/2000),(1600668188044146824/5942621241730892643),(1623277713759375427/1000000000000000000),(7/4),(377733657952577499271/256000000000000000000),true,MergedCutProfiles.Batch163.profile6551,![MergedCutProfiles.Batch163.profile6551,MergedCutProfiles.Batch163.profile6552,MergedCutProfiles.Batch163.profile6553,MergedCutProfiles.Batch163.profile6554,MergedCutProfiles.Batch163.profile6555,MergedCutProfiles.Batch163.profile6556,MergedCutProfiles.Batch163.profile6557,MergedCutProfiles.Batch163.profile6558,MergedCutProfiles.Batch163.profile6559,MergedCutProfiles.Batch164.profile6560,MergedCutProfiles.Batch164.profile6561,MergedCutProfiles.Batch164.profile6562,MergedCutProfiles.Batch164.profile6563,MergedCutProfiles.Batch164.profile6564,MergedCutProfiles.Batch164.profile6565,MergedCutProfiles.Batch164.profile6566]⟩
theorem profilesValid975 : retention975.ProfilesValid := by
  change ∀ j : Fin 16, (retention975.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch163.valid6551
  · exact MergedCutProfiles.Batch163.valid6552
  · exact MergedCutProfiles.Batch163.valid6553
  · exact MergedCutProfiles.Batch163.valid6554
  · exact MergedCutProfiles.Batch163.valid6555
  · exact MergedCutProfiles.Batch163.valid6556
  · exact MergedCutProfiles.Batch163.valid6557
  · exact MergedCutProfiles.Batch163.valid6558
  · exact MergedCutProfiles.Batch163.valid6559
  · exact MergedCutProfiles.Batch164.valid6560
  · exact MergedCutProfiles.Batch164.valid6561
  · exact MergedCutProfiles.Batch164.valid6562
  · exact MergedCutProfiles.Batch164.valid6563
  · exact MergedCutProfiles.Batch164.valid6564
  · exact MergedCutProfiles.Batch164.valid6565
  · exact MergedCutProfiles.Batch164.valid6566
theorem numericValid975 : retention975.NumericValid := by decide +kernel
def certificate975 : RatCutBinCertificate := ⟨⟨retention975,(2191989654154948687/1000000000000000000),(64019242937268319/500000000000000000),(3400570858551781727/250000000000000000),(48570040808067511363/200000000000000000),(719703624056746569/500000000000000000)⟩,(39684303381502337/40000000000000000),(205587471270505163/500000000000000000),(44679584184545441/200000000000000000),(141186480113266131/1000000000000000000)⟩
theorem valid975 : certificate975.Valid := by decide +kernel
theorem sound975 : certificate975.Sound := rat_cut_bin_certificate_sound certificate975 profilesValid975 numericValid975 valid975

def retention976 : RatCutRetentionCertificate := ⟨(41/800),(103/2000),(2685423286019829412/5942621241730892643),(600250570516555059/125000000000000000),1,(33546324240347141349/32000000000000000000),true,MergedCutProfiles.Batch164.profile6567,![MergedCutProfiles.Batch164.profile6567,MergedCutProfiles.Batch164.profile6568,MergedCutProfiles.Batch164.profile6569,MergedCutProfiles.Batch164.profile6570,MergedCutProfiles.Batch164.profile6571,MergedCutProfiles.Batch164.profile6572,MergedCutProfiles.Batch164.profile6573,MergedCutProfiles.Batch164.profile6574,MergedCutProfiles.Batch164.profile6575,MergedCutProfiles.Batch164.profile6576,MergedCutProfiles.Batch164.profile6577,MergedCutProfiles.Batch164.profile6578,MergedCutProfiles.Batch164.profile6579,MergedCutProfiles.Batch164.profile6580,MergedCutProfiles.Batch164.profile6581,MergedCutProfiles.Batch164.profile6582]⟩
theorem profilesValid976 : retention976.ProfilesValid := by
  change ∀ j : Fin 16, (retention976.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch164.valid6567
  · exact MergedCutProfiles.Batch164.valid6568
  · exact MergedCutProfiles.Batch164.valid6569
  · exact MergedCutProfiles.Batch164.valid6570
  · exact MergedCutProfiles.Batch164.valid6571
  · exact MergedCutProfiles.Batch164.valid6572
  · exact MergedCutProfiles.Batch164.valid6573
  · exact MergedCutProfiles.Batch164.valid6574
  · exact MergedCutProfiles.Batch164.valid6575
  · exact MergedCutProfiles.Batch164.valid6576
  · exact MergedCutProfiles.Batch164.valid6577
  · exact MergedCutProfiles.Batch164.valid6578
  · exact MergedCutProfiles.Batch164.valid6579
  · exact MergedCutProfiles.Batch164.valid6580
  · exact MergedCutProfiles.Batch164.valid6581
  · exact MergedCutProfiles.Batch164.valid6582
theorem numericValid976 : retention976.NumericValid := by decide +kernel
def certificate976 : RatCutBinCertificate := ⟨⟨retention976,(2191989654154948687/1000000000000000000),(64019242937268319/500000000000000000),(3400570858551781727/250000000000000000),(48570040808067511363/200000000000000000),(102768713756111661/100000000000000000)⟩,(39684303381502337/40000000000000000),(95206692313708313/200000000000000000),(21327803787597169/125000000000000000),(4474396613166221/31250000000000000)⟩
theorem valid976 : certificate976.Valid := by decide +kernel
theorem sound976 : certificate976.Sound := rat_cut_bin_certificate_sound certificate976 profilesValid976 numericValid976 valid976

def retention977 : RatCutRetentionCertificate := ⟨(41/800),(103/2000),(2937007898843529629/5942621241730892643),(2014067464514872059/250000000000000000),(21/20),(806893252421503591245583143361639908119/805626985805948823600000000000000000000),false,MergedCutProfiles.Batch164.profile6583,(fun _ => MergedCutProfiles.Batch164.profile6583)⟩
theorem profilesValid977 : retention977.ProfilesValid := by
  exact MergedCutProfiles.Batch164.valid6583
theorem numericValid977 : retention977.NumericValid := by decide +kernel
def certificate977 : RatCutBinCertificate := ⟨⟨retention977,(2191989654154948687/1000000000000000000),(64019242937268319/500000000000000000),(3400570858551781727/250000000000000000),(48570040808067511363/200000000000000000),(489952768236159181/500000000000000000)⟩,(39684303381502337/40000000000000000),(19105592785070283/40000000000000000),(16943279701919319/100000000000000000),(141216366562779681/1000000000000000000)⟩
theorem valid977 : certificate977.Valid := by decide +kernel
theorem sound977 : certificate977.Sound := rat_cut_bin_certificate_sound certificate977 profilesValid977 numericValid977 valid977

def retention978 : RatCutRetentionCertificate := ⟨(41/800),(103/2000),(8899133933495894776/17827863725192677929),(8811023696530588887/1000000000000000000),(21/20),(14016426596441012107867058550268102201631/14097637914448942219200000000000000000000),false,MergedCutProfiles.Batch164.profile6584,(fun _ => MergedCutProfiles.Batch164.profile6584)⟩
theorem profilesValid978 : retention978.ProfilesValid := by
  exact MergedCutProfiles.Batch164.valid6584
theorem numericValid978 : retention978.NumericValid := by decide +kernel
def certificate978 : RatCutBinCertificate := ⟨⟨retention978,(2191989654154948687/1000000000000000000),(64019242937268319/500000000000000000),(3400570858551781727/250000000000000000),(48570040808067511363/200000000000000000),(194514648269689757/200000000000000000)⟩,(39684303381502337/40000000000000000),(478489217309525639/1000000000000000000),(168805936454902993/1000000000000000000),(8808870408880039/62500000000000000)⟩
theorem valid978 : certificate978.Valid := by decide +kernel
theorem sound978 : certificate978.Sound := rat_cut_bin_certificate_sound certificate978 profilesValid978 numericValid978 valid978

def retention979 : RatCutRetentionCertificate := ⟨(41/800),(103/2000),(1/2),(1112391741686986847/125000000000000000),(21/20),(883556087521458888392105899168202814239/889913393349589477600000000000000000000),false,MergedCutProfiles.Batch164.profile6585,(fun _ => MergedCutProfiles.Batch164.profile6585)⟩
theorem profilesValid979 : retention979.ProfilesValid := by
  exact MergedCutProfiles.Batch164.valid6585
theorem numericValid979 : retention979.NumericValid := by decide +kernel
def certificate979 : RatCutBinCertificate := ⟨⟨retention979,(2191989654154948687/1000000000000000000),(64019242937268319/500000000000000000),(3400570858551781727/250000000000000000),(48570040808067511363/200000000000000000),(971190151140377031/1000000000000000000)⟩,(39684303381502337/40000000000000000),(5985992925262993/12500000000000000),(168518459787447043/1000000000000000000),(70323569507086569/500000000000000000)⟩
theorem valid979 : certificate979.Valid := by decide +kernel
theorem sound979 : certificate979.Sound := rat_cut_bin_certificate_sound certificate979 profilesValid979 numericValid979 valid979

def retention980 : RatCutRetentionCertificate := ⟨(41/800),(103/2000),(1/2),64,1,(408633796355205409622121959028668871/409600000000000000000000000000000000),false,MergedCutProfiles.Batch164.profile6585,(fun _ => MergedCutProfiles.Batch164.profile6585)⟩
theorem profilesValid980 : retention980.ProfilesValid := by
  exact MergedCutProfiles.Batch164.valid6585
theorem numericValid980 : retention980.NumericValid := by decide +kernel
def certificate980 : RatCutBinCertificate := ⟨⟨retention980,(2191989654154948687/1000000000000000000),(64019242937268319/500000000000000000),(3400570858551781727/250000000000000000),(48570040808067511363/200000000000000000),(244251926216458323/250000000000000000)⟩,(39684303381502337/40000000000000000),(451105601343510001/1000000000000000000),(189789793540004437/1000000000000000000),(181183487178943221/1000000000000000000)⟩
theorem valid980 : certificate980.Valid := by decide +kernel
theorem sound980 : certificate980.Sound := rat_cut_bin_certificate_sound certificate980 profilesValid980 numericValid980 valid980

def retention981 : RatCutRetentionCertificate := ⟨(41/800),(103/2000),(8069342033626990594/17827863725192677929),(1838313598144314721/500000000000000000),(6/5),(400083604031085923888806022043454608551/367662719628862944200000000000000000000),false,MergedCutProfiles.Batch164.profile6586,(fun _ => MergedCutProfiles.Batch164.profile6586)⟩
theorem profilesValid981 : retention981.ProfilesValid := by
  exact MergedCutProfiles.Batch164.valid6586
theorem numericValid981 : retention981.NumericValid := by decide +kernel
def certificate981 : RatCutBinCertificate := ⟨⟨retention981,(2552192377154948687/1000000000000000000),(64019242937268319/500000000000000000),(3400570858551781727/250000000000000000),(48570040808067511363/200000000000000000),(529674508412180149/500000000000000000)⟩,(990808921039043279/1000000000000000000),(383693477159117941/1000000000000000000),(248760021833725509/1000000000000000000),(36229326925271151/200000000000000000)⟩
theorem valid981 : certificate981.Valid := by decide +kernel
theorem sound981 : certificate981.Sound := rat_cut_bin_certificate_sound certificate981 profilesValid981 numericValid981 valid981

def retention982 : RatCutRetentionCertificate := ⟨(41/800),(103/2000),(8825320542430710542/17827863725192677929),(4034671016813495297/500000000000000000),(21/20),(3227954065951999230310019544113711434511/3227736813450796237600000000000000000000),false,MergedCutProfiles.Batch164.profile6587,(fun _ => MergedCutProfiles.Batch164.profile6587)⟩
theorem profilesValid982 : retention982.ProfilesValid := by
  exact MergedCutProfiles.Batch164.valid6587
theorem numericValid982 : retention982.NumericValid := by decide +kernel
def certificate982 : RatCutBinCertificate := ⟨⟨retention982,(2552192377154948687/1000000000000000000),(64019242937268319/500000000000000000),(3400570858551781727/250000000000000000),(48570040808067511363/200000000000000000),(97484072433923297/100000000000000000)⟩,(990808921039043279/1000000000000000000),(416955608892870427/1000000000000000000),(218301033906761191/1000000000000000000),(180890839534668929/1000000000000000000)⟩
theorem valid982 : certificate982.Valid := by decide +kernel
theorem sound982 : certificate982.Sound := rat_cut_bin_certificate_sound certificate982 profilesValid982 numericValid982 valid982

def retention983 : RatCutRetentionCertificate := ⟨(41/800),(103/2000),(8913573747855017648/17827863725192677929),(4412660271215355271/500000000000000000),(21/20),(3504378272248321818029556823979603349239/3530128216972284216800000000000000000000),false,MergedCutProfiles.Batch164.profile6588,(fun _ => MergedCutProfiles.Batch164.profile6588)⟩
theorem profilesValid983 : retention983.ProfilesValid := by
  exact MergedCutProfiles.Batch164.valid6588
theorem numericValid983 : retention983.NumericValid := by decide +kernel
def certificate983 : RatCutBinCertificate := ⟨⟨retention983,(2552192377154948687/1000000000000000000),(64019242937268319/500000000000000000),(3400570858551781727/250000000000000000),(48570040808067511363/200000000000000000),(30233725432500793/31250000000000000)⟩,(990808921039043279/1000000000000000000),(105032051845622801/250000000000000000),(86215134862601/400000000000000),(5590456264982391/31250000000000000)⟩
theorem valid983 : certificate983.Valid := by decide +kernel
theorem sound983 : certificate983.Sound := rat_cut_bin_certificate_sound certificate983 profilesValid983 numericValid983 valid983

def certificates : List RatCutBinCertificate := [certificate972,certificate973,certificate974,certificate975,certificate976,certificate977,certificate978,certificate979,certificate980,certificate981,certificate982,certificate983]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound972,List.forall_mem_cons.mpr ⟨sound973,List.forall_mem_cons.mpr ⟨sound974,List.forall_mem_cons.mpr ⟨sound975,List.forall_mem_cons.mpr ⟨sound976,List.forall_mem_cons.mpr ⟨sound977,List.forall_mem_cons.mpr ⟨sound978,List.forall_mem_cons.mpr ⟨sound979,List.forall_mem_cons.mpr ⟨sound980,List.forall_mem_cons.mpr ⟨sound981,List.forall_mem_cons.mpr ⟨sound982,List.forall_mem_cons.mpr ⟨sound983,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch081
