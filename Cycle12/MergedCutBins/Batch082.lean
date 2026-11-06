import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch164
import Cycle12.MergedCutProfiles.Batch165
import Cycle12.MergedCutProfiles.Batch166

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch082

def retention984 : RatCutRetentionCertificate := ⟨(41/800),(103/2000),(1/2),(557098359240938603/62500000000000000),(21/20),(885022400988358599935723842072934572631/891357374785501764800000000000000000000),false,MergedCutProfiles.Batch164.profile6585,(fun _ => MergedCutProfiles.Batch164.profile6585)⟩
theorem profilesValid984 : retention984.ProfilesValid := by
  exact MergedCutProfiles.Batch164.valid6585
theorem numericValid984 : retention984.NumericValid := by decide +kernel
def certificate984 : RatCutBinCertificate := ⟨⟨retention984,(2552192377154948687/1000000000000000000),(64019242937268319/500000000000000000),(3400570858551781727/250000000000000000),(48570040808067511363/200000000000000000),(967666456259862079/1000000000000000000)⟩,(990808921039043279/1000000000000000000),(105011728256414179/250000000000000000),(26951042659077299/125000000000000000),(89572903364781473/500000000000000000)⟩
theorem valid984 : certificate984.Valid := by decide +kernel
theorem sound984 : certificate984.Sound := rat_cut_bin_certificate_sound certificate984 profilesValid984 numericValid984 valid984

def retention985 : RatCutRetentionCertificate := ⟨(103/2000),(207/4000),(142000460112706978/2938417085802724847),(168713417955691459/200000000000000000),(57/20),(16419308486999311161/8000000000000000000),true,MergedCutProfiles.Batch164.profile6589,![MergedCutProfiles.Batch164.profile6589,MergedCutProfiles.Batch164.profile6590,MergedCutProfiles.Batch164.profile6591,MergedCutProfiles.Batch164.profile6592,MergedCutProfiles.Batch164.profile6593,MergedCutProfiles.Batch164.profile6594,MergedCutProfiles.Batch164.profile6595,MergedCutProfiles.Batch164.profile6596,MergedCutProfiles.Batch164.profile6597,MergedCutProfiles.Batch164.profile6598,MergedCutProfiles.Batch164.profile6599,MergedCutProfiles.Batch165.profile6600,MergedCutProfiles.Batch165.profile6601,MergedCutProfiles.Batch165.profile6602,MergedCutProfiles.Batch165.profile6603,MergedCutProfiles.Batch165.profile6604]⟩
theorem profilesValid985 : retention985.ProfilesValid := by
  change ∀ j : Fin 16, (retention985.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch164.valid6589
  · exact MergedCutProfiles.Batch164.valid6590
  · exact MergedCutProfiles.Batch164.valid6591
  · exact MergedCutProfiles.Batch164.valid6592
  · exact MergedCutProfiles.Batch164.valid6593
  · exact MergedCutProfiles.Batch164.valid6594
  · exact MergedCutProfiles.Batch164.valid6595
  · exact MergedCutProfiles.Batch164.valid6596
  · exact MergedCutProfiles.Batch164.valid6597
  · exact MergedCutProfiles.Batch164.valid6598
  · exact MergedCutProfiles.Batch164.valid6599
  · exact MergedCutProfiles.Batch165.valid6600
  · exact MergedCutProfiles.Batch165.valid6601
  · exact MergedCutProfiles.Batch165.valid6602
  · exact MergedCutProfiles.Batch165.valid6603
  · exact MergedCutProfiles.Batch165.valid6604
theorem numericValid985 : retention985.NumericValid := by decide +kernel
def certificate985 : RatCutBinCertificate := ⟨⟨retention985,(2190350807738488223/1000000000000000000),(16182290823511013/125000000000000000),(13659846689896458373/1000000000000000000),(241178661540697140603/1000000000000000000),(1993238371789074091/1000000000000000000)⟩,(992071477364650843/1000000000000000000),(9249535959574773/25000000000000000),(65535459713680239/250000000000000000),(140682549931663883/1000000000000000000)⟩
theorem valid985 : certificate985.Valid := by decide +kernel
theorem sound985 : certificate985.Sound := rat_cut_bin_certificate_sound certificate985 profilesValid985 numericValid985 valid985

def retention986 : RatCutRetentionCertificate := ⟨(103/2000),(207/4000),(461298451305952412/8815251257408174541),(213000690169060467/250000000000000000),(57/20),(654429311037605839603/320000000000000000000),true,MergedCutProfiles.Batch165.profile6605,![MergedCutProfiles.Batch165.profile6605,MergedCutProfiles.Batch165.profile6606,MergedCutProfiles.Batch165.profile6607,MergedCutProfiles.Batch165.profile6608,MergedCutProfiles.Batch165.profile6609,MergedCutProfiles.Batch165.profile6610,MergedCutProfiles.Batch165.profile6611,MergedCutProfiles.Batch165.profile6612,MergedCutProfiles.Batch165.profile6613,MergedCutProfiles.Batch165.profile6614,MergedCutProfiles.Batch165.profile6615,MergedCutProfiles.Batch165.profile6601,MergedCutProfiles.Batch165.profile6616,MergedCutProfiles.Batch165.profile6617,MergedCutProfiles.Batch165.profile6618,MergedCutProfiles.Batch165.profile6619]⟩
theorem profilesValid986 : retention986.ProfilesValid := by
  change ∀ j : Fin 16, (retention986.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch165.valid6605
  · exact MergedCutProfiles.Batch165.valid6606
  · exact MergedCutProfiles.Batch165.valid6607
  · exact MergedCutProfiles.Batch165.valid6608
  · exact MergedCutProfiles.Batch165.valid6609
  · exact MergedCutProfiles.Batch165.valid6610
  · exact MergedCutProfiles.Batch165.valid6611
  · exact MergedCutProfiles.Batch165.valid6612
  · exact MergedCutProfiles.Batch165.valid6613
  · exact MergedCutProfiles.Batch165.valid6614
  · exact MergedCutProfiles.Batch165.valid6615
  · exact MergedCutProfiles.Batch165.valid6601
  · exact MergedCutProfiles.Batch165.valid6616
  · exact MergedCutProfiles.Batch165.valid6617
  · exact MergedCutProfiles.Batch165.valid6618
  · exact MergedCutProfiles.Batch165.valid6619
theorem numericValid986 : retention986.NumericValid := by decide +kernel
def certificate986 : RatCutBinCertificate := ⟨⟨retention986,(2190350807738488223/1000000000000000000),(16182290823511013/125000000000000000),(13659846689896458373/1000000000000000000),(241178661540697140603/1000000000000000000),(1985916538688670243/1000000000000000000)⟩,(992071477364650843/1000000000000000000),(73967963062586227/200000000000000000),(131141334307785307/500000000000000000),(140671695277946049/1000000000000000000)⟩
theorem valid986 : certificate986.Valid := by decide +kernel
theorem sound986 : certificate986.Sound := rat_cut_bin_certificate_sound certificate986 profilesValid986 numericValid986 valid986

def retention987 : RatCutRetentionCertificate := ⟨(103/2000),(207/4000),(486042148018162243/5876834171605449694),(115324612826488103/125000000000000000),(53/20),(78007895817536284603/40000000000000000000),true,MergedCutProfiles.Batch165.profile6620,![MergedCutProfiles.Batch165.profile6620,MergedCutProfiles.Batch165.profile6621,MergedCutProfiles.Batch165.profile6622,MergedCutProfiles.Batch165.profile6623,MergedCutProfiles.Batch165.profile6624,MergedCutProfiles.Batch165.profile6625,MergedCutProfiles.Batch165.profile6600,MergedCutProfiles.Batch165.profile6626,MergedCutProfiles.Batch165.profile6627,MergedCutProfiles.Batch165.profile6628,MergedCutProfiles.Batch165.profile6629,MergedCutProfiles.Batch165.profile6630,MergedCutProfiles.Batch165.profile6631,MergedCutProfiles.Batch165.profile6632,MergedCutProfiles.Batch165.profile6633,MergedCutProfiles.Batch165.profile6634]⟩
theorem profilesValid987 : retention987.ProfilesValid := by
  change ∀ j : Fin 16, (retention987.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch165.valid6620
  · exact MergedCutProfiles.Batch165.valid6621
  · exact MergedCutProfiles.Batch165.valid6622
  · exact MergedCutProfiles.Batch165.valid6623
  · exact MergedCutProfiles.Batch165.valid6624
  · exact MergedCutProfiles.Batch165.valid6625
  · exact MergedCutProfiles.Batch165.valid6600
  · exact MergedCutProfiles.Batch165.valid6626
  · exact MergedCutProfiles.Batch165.valid6627
  · exact MergedCutProfiles.Batch165.valid6628
  · exact MergedCutProfiles.Batch165.valid6629
  · exact MergedCutProfiles.Batch165.valid6630
  · exact MergedCutProfiles.Batch165.valid6631
  · exact MergedCutProfiles.Batch165.valid6632
  · exact MergedCutProfiles.Batch165.valid6633
  · exact MergedCutProfiles.Batch165.valid6634
theorem numericValid987 : retention987.NumericValid := by decide +kernel
def certificate987 : RatCutBinCertificate := ⟨⟨retention987,(2190350807738488223/1000000000000000000),(16182290823511013/125000000000000000),(13659846689896458373/1000000000000000000),(241178661540697140603/1000000000000000000),(1895175055738298061/1000000000000000000)⟩,(992071477364650843/1000000000000000000),(375475079889340043/1000000000000000000),(31337960007663/122070312500000),(70354907357121783/500000000000000000)⟩
theorem valid987 : certificate987.Valid := by decide +kernel
theorem sound987 : certificate987.Sound := rat_cut_bin_certificate_sound certificate987 profilesValid987 numericValid987 valid987

def retention988 : RatCutRetentionCertificate := ⟨(103/2000),(207/4000),(2114229777701781056/8815251257408174541),(1458126444054486729/1000000000000000000),(37/20),(1970975557393793225217/1280000000000000000000),true,MergedCutProfiles.Batch165.profile6635,![MergedCutProfiles.Batch165.profile6635,MergedCutProfiles.Batch165.profile6636,MergedCutProfiles.Batch165.profile6637,MergedCutProfiles.Batch165.profile6638,MergedCutProfiles.Batch165.profile6639,MergedCutProfiles.Batch166.profile6640,MergedCutProfiles.Batch166.profile6641,MergedCutProfiles.Batch166.profile6642,MergedCutProfiles.Batch166.profile6643,MergedCutProfiles.Batch166.profile6644,MergedCutProfiles.Batch166.profile6645,MergedCutProfiles.Batch166.profile6646,MergedCutProfiles.Batch166.profile6647,MergedCutProfiles.Batch166.profile6648,MergedCutProfiles.Batch166.profile6649,MergedCutProfiles.Batch166.profile6650]⟩
theorem profilesValid988 : retention988.ProfilesValid := by
  change ∀ j : Fin 16, (retention988.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch165.valid6635
  · exact MergedCutProfiles.Batch165.valid6636
  · exact MergedCutProfiles.Batch165.valid6637
  · exact MergedCutProfiles.Batch165.valid6638
  · exact MergedCutProfiles.Batch165.valid6639
  · exact MergedCutProfiles.Batch166.valid6640
  · exact MergedCutProfiles.Batch166.valid6641
  · exact MergedCutProfiles.Batch166.valid6642
  · exact MergedCutProfiles.Batch166.valid6643
  · exact MergedCutProfiles.Batch166.valid6644
  · exact MergedCutProfiles.Batch166.valid6645
  · exact MergedCutProfiles.Batch166.valid6646
  · exact MergedCutProfiles.Batch166.valid6647
  · exact MergedCutProfiles.Batch166.valid6648
  · exact MergedCutProfiles.Batch166.valid6649
  · exact MergedCutProfiles.Batch166.valid6650
theorem numericValid988 : retention988.NumericValid := by decide +kernel
def certificate988 : RatCutBinCertificate := ⟨⟨retention988,(2190350807738488223/1000000000000000000),(16182290823511013/125000000000000000),(13659846689896458373/1000000000000000000),(241178661540697140603/1000000000000000000),(1501413621853147503/1000000000000000000)⟩,(992071477364650843/1000000000000000000),(101599690722325731/250000000000000000),(227670383256626591/1000000000000000000),(35180735303185183/250000000000000000)⟩
theorem valid988 : certificate988.Valid := by decide +kernel
theorem sound988 : certificate988.Sound := rat_cut_bin_certificate_sound certificate988 profilesValid988 numericValid988 valid988

def retention989 : RatCutRetentionCertificate := ⟨(103/2000),(207/4000),(3918116633725566124/8815251257408174541),(33034840276590329/7812500000000000),(21/20),(21460284270118563597/20000000000000000000),true,MergedCutProfiles.Batch166.profile6651,![MergedCutProfiles.Batch166.profile6651,MergedCutProfiles.Batch166.profile6652,MergedCutProfiles.Batch166.profile6653,MergedCutProfiles.Batch166.profile6654,MergedCutProfiles.Batch166.profile6655,MergedCutProfiles.Batch166.profile6656,MergedCutProfiles.Batch166.profile6657,MergedCutProfiles.Batch166.profile6658,MergedCutProfiles.Batch166.profile6659,MergedCutProfiles.Batch166.profile6660,MergedCutProfiles.Batch166.profile6661,MergedCutProfiles.Batch166.profile6662,MergedCutProfiles.Batch166.profile6663,MergedCutProfiles.Batch166.profile6664,MergedCutProfiles.Batch166.profile6665,MergedCutProfiles.Batch166.profile6666]⟩
theorem profilesValid989 : retention989.ProfilesValid := by
  change ∀ j : Fin 16, (retention989.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch166.valid6651
  · exact MergedCutProfiles.Batch166.valid6652
  · exact MergedCutProfiles.Batch166.valid6653
  · exact MergedCutProfiles.Batch166.valid6654
  · exact MergedCutProfiles.Batch166.valid6655
  · exact MergedCutProfiles.Batch166.valid6656
  · exact MergedCutProfiles.Batch166.valid6657
  · exact MergedCutProfiles.Batch166.valid6658
  · exact MergedCutProfiles.Batch166.valid6659
  · exact MergedCutProfiles.Batch166.valid6660
  · exact MergedCutProfiles.Batch166.valid6661
  · exact MergedCutProfiles.Batch166.valid6662
  · exact MergedCutProfiles.Batch166.valid6663
  · exact MergedCutProfiles.Batch166.valid6664
  · exact MergedCutProfiles.Batch166.valid6665
  · exact MergedCutProfiles.Batch166.valid6666
theorem numericValid989 : retention989.NumericValid := by decide +kernel
def certificate989 : RatCutBinCertificate := ⟨⟨retention989,(2190350807738488223/1000000000000000000),(16182290823511013/125000000000000000),(13659846689896458373/1000000000000000000),(241178661540697140603/1000000000000000000),(1051215059361340163/1000000000000000000)⟩,(992071477364650843/1000000000000000000),(471551243355458579/1000000000000000000),(43492645647685983/250000000000000000),(140875140383697567/1000000000000000000)⟩
theorem valid989 : certificate989.Valid := by decide +kernel
theorem sound989 : certificate989.Sound := rat_cut_bin_certificate_sound certificate989 profilesValid989 numericValid989 valid989

def retention990 : RatCutRetentionCertificate := ⟨(103/2000),(207/4000),(4328038323554928752/8815251257408174541),(979529158431391531/125000000000000000),(21/20),(789179546695876534199692261234674352391/783623326745113224800000000000000000000),false,MergedCutProfiles.Batch166.profile6667,(fun _ => MergedCutProfiles.Batch166.profile6667)⟩
theorem profilesValid990 : retention990.ProfilesValid := by
  exact MergedCutProfiles.Batch166.valid6667
theorem numericValid990 : retention990.NumericValid := by decide +kernel
def certificate990 : RatCutBinCertificate := ⟨⟨retention990,(2190350807738488223/1000000000000000000),(16182290823511013/125000000000000000),(13659846689896458373/1000000000000000000),(241178661540697140603/1000000000000000000),(7697597507137669/7812500000000000)⟩,(992071477364650843/1000000000000000000),(29684257549900989/62500000000000000),(42857319220434139/250000000000000000),(143178364597660179/1000000000000000000)⟩
theorem valid990 : certificate990.Valid := by decide +kernel
theorem sound990 : certificate990.Sound := rat_cut_bin_certificate_sound certificate990 profilesValid990 numericValid990 valid990

def retention991 : RatCutRetentionCertificate := ⟨(103/2000),(207/4000),(4371318706790478040/8815251257408174541),(270502395222183047/31250000000000000),(21/20),(123682895093741842599294156117289807697/123658237815855107200000000000000000000),false,MergedCutProfiles.Batch166.profile6668,(fun _ => MergedCutProfiles.Batch166.profile6668)⟩
theorem profilesValid991 : retention991.ProfilesValid := by
  exact MergedCutProfiles.Batch166.valid6668
theorem numericValid991 : retention991.NumericValid := by decide +kernel
def certificate991 : RatCutBinCertificate := ⟨⟨retention991,(2190350807738488223/1000000000000000000),(16182290823511013/125000000000000000),(13659846689896458373/1000000000000000000),(241178661540697140603/1000000000000000000),(489200796168171901/500000000000000000)⟩,(992071477364650843/1000000000000000000),(237572986953420957/500000000000000000),(171282007429526479/1000000000000000000),(143545938019135609/1000000000000000000)⟩
theorem valid991 : certificate991.Valid := by decide +kernel
theorem sound991 : certificate991.Sound := rat_cut_bin_certificate_sound certificate991 profilesValid991 numericValid991 valid991

def retention992 : RatCutRetentionCertificate := ⟨(103/2000),(207/4000),(1/2),(109282967669761951/12500000000000000),(21/20),(34706550629292042286913877283470951551/34970549654323824320000000000000000000),false,MergedCutProfiles.Batch166.profile6669,(fun _ => MergedCutProfiles.Batch166.profile6669)⟩
theorem profilesValid992 : retention992.ProfilesValid := by
  exact MergedCutProfiles.Batch166.valid6669
theorem numericValid992 : retention992.NumericValid := by decide +kernel
def certificate992 : RatCutBinCertificate := ⟨⟨retention992,(2190350807738488223/1000000000000000000),(16182290823511013/125000000000000000),(13659846689896458373/1000000000000000000),(241178661540697140603/1000000000000000000),(970653025036425051/1000000000000000000)⟩,(992071477364650843/1000000000000000000),(478638771919925281/1000000000000000000),(84347860220161699/500000000000000000),(140491121625418147/1000000000000000000)⟩
theorem valid992 : certificate992.Valid := by decide +kernel
theorem sound992 : certificate992.Sound := rat_cut_bin_certificate_sound certificate992 profilesValid992 numericValid992 valid992

def retention993 : RatCutRetentionCertificate := ⟨(103/2000),(207/4000),(1/2),64,1,(255396432938144484358685289014764520631/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch166.profile6669,(fun _ => MergedCutProfiles.Batch166.profile6669)⟩
theorem profilesValid993 : retention993.ProfilesValid := by
  exact MergedCutProfiles.Batch166.valid6669
theorem numericValid993 : retention993.NumericValid := by decide +kernel
def certificate993 : RatCutBinCertificate := ⟨⟨retention993,(2190350807738488223/1000000000000000000),(16182290823511013/125000000000000000),(13659846689896458373/1000000000000000000),(241178661540697140603/1000000000000000000),(976883552550126291/1000000000000000000)⟩,(992071477364650843/1000000000000000000),(28114425678626879/62500000000000000),(190806386846188699/1000000000000000000),(22765555762864229/125000000000000000)⟩
theorem valid993 : certificate993.Valid := by decide +kernel
theorem sound993 : certificate993.Sound := rat_cut_bin_certificate_sound certificate993 profilesValid993 numericValid993 valid993

def retention994 : RatCutRetentionCertificate := ⟨(103/2000),(207/4000),(4000011881504264971/8815251257408174541),(23009338821876071/6250000000000000),(6/5),(15618329367269532448381077840084911/14380836763672544375000000000000000),false,MergedCutProfiles.Batch166.profile6670,(fun _ => MergedCutProfiles.Batch166.profile6670)⟩
theorem profilesValid994 : retention994.ProfilesValid := by
  exact MergedCutProfiles.Batch166.valid6670
theorem numericValid994 : retention994.NumericValid := by decide +kernel
def certificate994 : RatCutBinCertificate := ⟨⟨retention994,(2555171518738488223/1000000000000000000),(16182290823511013/125000000000000000),(13659846689896458373/1000000000000000000),(241178661540697140603/1000000000000000000),(13212358123193309/12500000000000000)⟩,(990749124187380419/1000000000000000000),(383397492850981433/1000000000000000000),(249043643453992903/1000000000000000000),(45261010596933077/250000000000000000)⟩
theorem valid994 : certificate994.Valid := by decide +kernel
theorem sound994 : certificate994.Sound := rat_cut_bin_certificate_sound certificate994 profilesValid994 numericValid994 valid994

def retention995 : RatCutRetentionCertificate := ⟨(103/2000),(207/4000),(8749508170727351083/17630502514816349082),(4000011881504264971/500000000000000000),(21/20),(3191825781270838380381477390291503107959/3200009505203411976800000000000000000000),false,MergedCutProfiles.Batch166.profile6671,(fun _ => MergedCutProfiles.Batch166.profile6671)⟩
theorem profilesValid995 : retention995.ProfilesValid := by
  exact MergedCutProfiles.Batch166.valid6671
theorem numericValid995 : retention995.NumericValid := by decide +kernel
def certificate995 : RatCutBinCertificate := ⟨⟨retention995,(2555171518738488223/1000000000000000000),(16182290823511013/125000000000000000),(13659846689896458373/1000000000000000000),(241178661540697140603/1000000000000000000),(972014062857950947/1000000000000000000)⟩,(990749124187380419/1000000000000000000),(416914542506728493/1000000000000000000),(218336958778645799/1000000000000000000),(90140727060847419/500000000000000000)⟩
theorem valid995 : certificate995.Valid := by decide +kernel
theorem sound995 : certificate995.Sound := rat_cut_bin_certificate_sound certificate995 profilesValid995 numericValid995 valid995

def certificates : List RatCutBinCertificate := [certificate984,certificate985,certificate986,certificate987,certificate988,certificate989,certificate990,certificate991,certificate992,certificate993,certificate994,certificate995]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound984,List.forall_mem_cons.mpr ⟨sound985,List.forall_mem_cons.mpr ⟨sound986,List.forall_mem_cons.mpr ⟨sound987,List.forall_mem_cons.mpr ⟨sound988,List.forall_mem_cons.mpr ⟨sound989,List.forall_mem_cons.mpr ⟨sound990,List.forall_mem_cons.mpr ⟨sound991,List.forall_mem_cons.mpr ⟨sound992,List.forall_mem_cons.mpr ⟨sound993,List.forall_mem_cons.mpr ⟨sound994,List.forall_mem_cons.mpr ⟨sound995,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch082
