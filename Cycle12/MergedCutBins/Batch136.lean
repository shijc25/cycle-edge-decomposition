import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch261
import Cycle12.MergedCutProfiles.Batch262
import Cycle12.MergedCutProfiles.Batch263

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch136

def retention1632 : RatCutRetentionCertificate := ⟨(511/8000),(8/125),(1/2),64,1,(10216578426123802445343798178091951151/10240000000000000000000000000000000000),false,MergedCutProfiles.Batch261.profile10472,(fun _ => MergedCutProfiles.Batch261.profile10472)⟩
theorem profilesValid1632 : retention1632.ProfilesValid := by
  exact MergedCutProfiles.Batch261.valid10472
theorem numericValid1632 : retention1632.NumericValid := by decide +kernel
def certificate1632 : RatCutBinCertificate := ⟨⟨retention1632,(73996785269951413/31250000000000000),(106411689904918233/500000000000000000),(852416440356973433/50000000000000000),(36532513181200568633/200000000000000000),(96815247621441309/100000000000000000)⟩,(494876572380097603/500000000000000000),(391291767849571499/1000000000000000000),(60389179917291909/250000000000000000),(1781207440638781/7812500000000000)⟩
theorem valid1632 : certificate1632.Valid := by decide +kernel
theorem sound1632 : certificate1632.Sound := rat_cut_bin_certificate_sound certificate1632 profilesValid1632 numericValid1632 valid1632

def retention1633 : RatCutRetentionCertificate := ⟨(511/8000),(8/125),(4987292486482914679/10705984450122921257),(1593576889508627693/500000000000000000),(6/5),(336475073850368911787823960599650526639/318715377901725538600000000000000000000),false,MergedCutProfiles.Batch261.profile10473,(fun _ => MergedCutProfiles.Batch261.profile10473)⟩
theorem profilesValid1633 : retention1633.ProfilesValid := by
  exact MergedCutProfiles.Batch261.valid10473
theorem numericValid1633 : retention1633.NumericValid := by decide +kernel
def certificate1633 : RatCutBinCertificate := ⟨⟨retention1633,(83931523363701413/31250000000000000),(106411689904918233/500000000000000000),(852416440356973433/50000000000000000),(36532513181200568633/200000000000000000),(507738214700456313/500000000000000000)⟩,(494186557858825893/500000000000000000),(38533751984824989/100000000000000000),(123594398078396409/500000000000000000),(33809364588098303/200000000000000000)⟩
theorem valid1633 : certificate1633.Valid := by decide +kernel
theorem sound1633 : certificate1633.Sound := rat_cut_bin_certificate_sound certificate1633 profilesValid1633 numericValid1633 valid1633

def retention1634 : RatCutRetentionCertificate := ⟨(511/8000),(8/125),(5294111471342579350/10705984450122921257),(4987292486482914679/1000000000000000000),(11/10),(1993756994205187563227461937969594653199/1994916994593165871600000000000000000000),false,MergedCutProfiles.Batch261.profile10474,(fun _ => MergedCutProfiles.Batch261.profile10474)⟩
theorem profilesValid1634 : retention1634.ProfilesValid := by
  exact MergedCutProfiles.Batch261.valid10474
theorem numericValid1634 : retention1634.NumericValid := by decide +kernel
def certificate1634 : RatCutBinCertificate := ⟨⟨retention1634,(83931523363701413/31250000000000000),(106411689904918233/500000000000000000),(852416440356973433/50000000000000000),(36532513181200568633/200000000000000000),(962529468034010753/1000000000000000000)⟩,(494186557858825893/500000000000000000),(203267111171643403/500000000000000000),(227548439942961891/1000000000000000000),(21193246490153291/125000000000000000)⟩
theorem valid1634 : certificate1634.Valid := by decide +kernel
theorem sound1634 : certificate1634.Sound := rat_cut_bin_certificate_sound certificate1634 profilesValid1634 numericValid1634 valid1634

def retention1635 : RatCutRetentionCertificate := ⟨(511/8000),(8/125),(5347052586056005144/10705984450122921257),(105882229426851587/20000000000000000),(11/10),(5252623668411946527711153727254021061/5294111471342579350000000000000000000),false,MergedCutProfiles.Batch261.profile10475,(fun _ => MergedCutProfiles.Batch261.profile10475)⟩
theorem profilesValid1635 : retention1635.ProfilesValid := by
  exact MergedCutProfiles.Batch261.valid10475
theorem numericValid1635 : retention1635.NumericValid := by decide +kernel
def certificate1635 : RatCutBinCertificate := ⟨⟨retention1635,(83931523363701413/31250000000000000),(106411689904918233/500000000000000000),(852416440356973433/50000000000000000),(36532513181200568633/200000000000000000),(238818701466249171/250000000000000000)⟩,(494186557858825893/500000000000000000),(204810786575378587/500000000000000000),(112390674087248123/500000000000000000),(167731554704081963/1000000000000000000)⟩
theorem valid1635 : certificate1635.Valid := by decide +kernel
theorem sound1635 : certificate1635.Sound := rat_cut_bin_certificate_sound certificate1635 profilesValid1635 numericValid1635 valid1635

def retention1636 : RatCutRetentionCertificate := ⟨(511/8000),(8/125),(1/2),(668381573257000643/125000000000000000),(11/10),(530127252817897390829581125347254429991/534705258605600514400000000000000000000),false,MergedCutProfiles.Batch261.profile10472,(fun _ => MergedCutProfiles.Batch261.profile10472)⟩
theorem profilesValid1636 : retention1636.ProfilesValid := by
  exact MergedCutProfiles.Batch261.valid10472
theorem numericValid1636 : retention1636.NumericValid := by decide +kernel
def certificate1636 : RatCutBinCertificate := ⟨⟨retention1636,(83931523363701413/31250000000000000),(106411689904918233/500000000000000000),(852416440356973433/50000000000000000),(36532513181200568633/200000000000000000),(477274868039715017/500000000000000000)⟩,(494186557858825893/500000000000000000),(409932719039737001/1000000000000000000),(8980150857813737/40000000000000000),(41907608739417777/250000000000000000)⟩
theorem valid1636 : certificate1636.Valid := by decide +kernel
theorem sound1636 : certificate1636.Sound := rat_cut_bin_certificate_sound certificate1636 profilesValid1636 numericValid1636 valid1636

def retention1637 : RatCutRetentionCertificate := ⟨(8/125),(513/8000),(254949710241134883/2131181161457446298),(449931551304117903/500000000000000000),(51/20),(1182271996856060917887/640000000000000000000),true,MergedCutProfiles.Batch261.profile10476,![MergedCutProfiles.Batch261.profile10476,MergedCutProfiles.Batch261.profile10477,MergedCutProfiles.Batch261.profile10478,MergedCutProfiles.Batch261.profile10479,MergedCutProfiles.Batch262.profile10480,MergedCutProfiles.Batch262.profile10481,MergedCutProfiles.Batch262.profile10482,MergedCutProfiles.Batch262.profile10483,MergedCutProfiles.Batch262.profile10484,MergedCutProfiles.Batch262.profile10485,MergedCutProfiles.Batch262.profile10486,MergedCutProfiles.Batch262.profile10487,MergedCutProfiles.Batch262.profile10488,MergedCutProfiles.Batch262.profile10489,MergedCutProfiles.Batch262.profile10490,MergedCutProfiles.Batch262.profile10491]⟩
theorem profilesValid1637 : retention1637.ProfilesValid := by
  change ∀ j : Fin 16, (retention1637.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch261.valid10476
  · exact MergedCutProfiles.Batch261.valid10477
  · exact MergedCutProfiles.Batch261.valid10478
  · exact MergedCutProfiles.Batch261.valid10479
  · exact MergedCutProfiles.Batch262.valid10480
  · exact MergedCutProfiles.Batch262.valid10481
  · exact MergedCutProfiles.Batch262.valid10482
  · exact MergedCutProfiles.Batch262.valid10483
  · exact MergedCutProfiles.Batch262.valid10484
  · exact MergedCutProfiles.Batch262.valid10485
  · exact MergedCutProfiles.Batch262.valid10486
  · exact MergedCutProfiles.Batch262.valid10487
  · exact MergedCutProfiles.Batch262.valid10488
  · exact MergedCutProfiles.Batch262.valid10489
  · exact MergedCutProfiles.Batch262.valid10490
  · exact MergedCutProfiles.Batch262.valid10491
theorem numericValid1637 : retention1637.NumericValid := by decide +kernel
def certificate1637 : RatCutBinCertificate := ⟨⟨retention1637,(1185621024187517083/500000000000000000),(106913959738129263/500000000000000000),(17088822004878414449/1000000000000000000),(182240092104582146113/1000000000000000000),(1771600956387377573/1000000000000000000)⟩,(989727687633311561/1000000000000000000),(337887950732675387/1000000000000000000),(295481616549980517/1000000000000000000),(155607387889170741/1000000000000000000)⟩
theorem valid1637 : certificate1637.Valid := by decide +kernel
theorem sound1637 : certificate1637.Sound := rat_cut_bin_certificate_sound certificate1637 profilesValid1637 numericValid1637 valid1637

def retention1638 : RatCutRetentionCertificate := ⟨(8/125),(513/8000),(1330994286803738773/5327952903643615745),(254949710241134883/200000000000000000),(37/20),(386893288582908836619/256000000000000000000),true,MergedCutProfiles.Batch262.profile10492,![MergedCutProfiles.Batch262.profile10492,MergedCutProfiles.Batch262.profile10493,MergedCutProfiles.Batch262.profile10494,MergedCutProfiles.Batch262.profile10495,MergedCutProfiles.Batch262.profile10496,MergedCutProfiles.Batch262.profile10497,MergedCutProfiles.Batch262.profile10498,MergedCutProfiles.Batch262.profile10499,MergedCutProfiles.Batch262.profile10500,MergedCutProfiles.Batch262.profile10501,MergedCutProfiles.Batch262.profile10502,MergedCutProfiles.Batch262.profile10503,MergedCutProfiles.Batch262.profile10504,MergedCutProfiles.Batch262.profile10505,MergedCutProfiles.Batch262.profile10506,MergedCutProfiles.Batch262.profile10507]⟩
theorem profilesValid1638 : retention1638.ProfilesValid := by
  change ∀ j : Fin 16, (retention1638.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch262.valid10492
  · exact MergedCutProfiles.Batch262.valid10493
  · exact MergedCutProfiles.Batch262.valid10494
  · exact MergedCutProfiles.Batch262.valid10495
  · exact MergedCutProfiles.Batch262.valid10496
  · exact MergedCutProfiles.Batch262.valid10497
  · exact MergedCutProfiles.Batch262.valid10498
  · exact MergedCutProfiles.Batch262.valid10499
  · exact MergedCutProfiles.Batch262.valid10500
  · exact MergedCutProfiles.Batch262.valid10501
  · exact MergedCutProfiles.Batch262.valid10502
  · exact MergedCutProfiles.Batch262.valid10503
  · exact MergedCutProfiles.Batch262.valid10504
  · exact MergedCutProfiles.Batch262.valid10505
  · exact MergedCutProfiles.Batch262.valid10506
  · exact MergedCutProfiles.Batch262.valid10507
theorem numericValid1638 : retention1638.NumericValid := by decide +kernel
def certificate1638 : RatCutBinCertificate := ⟨⟨retention1638,(1185621024187517083/500000000000000000),(106913959738129263/500000000000000000),(17088822004878414449/1000000000000000000),(182240092104582146113/1000000000000000000),(291276751089298797/200000000000000000)⟩,(989727687633311561/1000000000000000000),(91415791534259167/250000000000000000),(266460369851970001/1000000000000000000),(38830221589578149/250000000000000000)⟩
theorem valid1638 : certificate1638.Valid := by decide +kernel
theorem sound1638 : certificate1638.Sound := rat_cut_bin_certificate_sound certificate1638 profilesValid1638 numericValid1638 valid1638

def retention1639 : RatCutRetentionCertificate := ⟨(8/125),(513/8000),(2255324313196115828/5327952903643615745),(1330994286803738773/500000000000000000),(23/20),(716592254721180743741/640000000000000000000),true,MergedCutProfiles.Batch262.profile10508,![MergedCutProfiles.Batch262.profile10508,MergedCutProfiles.Batch262.profile10509,MergedCutProfiles.Batch262.profile10510,MergedCutProfiles.Batch262.profile10511,MergedCutProfiles.Batch262.profile10512,MergedCutProfiles.Batch262.profile10513,MergedCutProfiles.Batch262.profile10514,MergedCutProfiles.Batch262.profile10515,MergedCutProfiles.Batch262.profile10516,MergedCutProfiles.Batch262.profile10517,MergedCutProfiles.Batch262.profile10518,MergedCutProfiles.Batch262.profile10519,MergedCutProfiles.Batch263.profile10520,MergedCutProfiles.Batch263.profile10521,MergedCutProfiles.Batch263.profile10522,MergedCutProfiles.Batch263.profile10523]⟩
theorem profilesValid1639 : retention1639.ProfilesValid := by
  change ∀ j : Fin 16, (retention1639.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch262.valid10508
  · exact MergedCutProfiles.Batch262.valid10509
  · exact MergedCutProfiles.Batch262.valid10510
  · exact MergedCutProfiles.Batch262.valid10511
  · exact MergedCutProfiles.Batch262.valid10512
  · exact MergedCutProfiles.Batch262.valid10513
  · exact MergedCutProfiles.Batch262.valid10514
  · exact MergedCutProfiles.Batch262.valid10515
  · exact MergedCutProfiles.Batch262.valid10516
  · exact MergedCutProfiles.Batch262.valid10517
  · exact MergedCutProfiles.Batch262.valid10518
  · exact MergedCutProfiles.Batch262.valid10519
  · exact MergedCutProfiles.Batch263.valid10520
  · exact MergedCutProfiles.Batch263.valid10521
  · exact MergedCutProfiles.Batch263.valid10522
  · exact MergedCutProfiles.Batch263.valid10523
theorem numericValid1639 : retention1639.NumericValid := by decide +kernel
def certificate1639 : RatCutBinCertificate := ⟨⟨retention1639,(1185621024187517083/500000000000000000),(106913959738129263/500000000000000000),(17088822004878414449/1000000000000000000),(182240092104582146113/1000000000000000000),(1085540985174701351/1000000000000000000)⟩,(989727687633311561/1000000000000000000),(82892385766953641/200000000000000000),(220489851820542909/1000000000000000000),(78590652633820491/500000000000000000)⟩
theorem valid1639 : certificate1639.Valid := by decide +kernel
theorem sound1639 : certificate1639.Sound := rat_cut_bin_certificate_sound certificate1639 profilesValid1639 numericValid1639 valid1639

def retention1640 : RatCutRetentionCertificate := ⟨(8/125),(513/8000),(1026707778418529163/2131181161457446298),(563831078299028957/125000000000000000),1,(31691365377844123817/32000000000000000000),true,MergedCutProfiles.Batch263.profile10524,![MergedCutProfiles.Batch263.profile10524,MergedCutProfiles.Batch263.profile10525,MergedCutProfiles.Batch263.profile10526,MergedCutProfiles.Batch263.profile10527,MergedCutProfiles.Batch263.profile10528,MergedCutProfiles.Batch263.profile10529,MergedCutProfiles.Batch263.profile10530,MergedCutProfiles.Batch263.profile10531,MergedCutProfiles.Batch263.profile10532,MergedCutProfiles.Batch263.profile10533,MergedCutProfiles.Batch263.profile10534,MergedCutProfiles.Batch263.profile10535,MergedCutProfiles.Batch263.profile10536,MergedCutProfiles.Batch263.profile10537,MergedCutProfiles.Batch263.profile10538,MergedCutProfiles.Batch263.profile10539]⟩
theorem profilesValid1640 : retention1640.ProfilesValid := by
  change ∀ j : Fin 16, (retention1640.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch263.valid10524
  · exact MergedCutProfiles.Batch263.valid10525
  · exact MergedCutProfiles.Batch263.valid10526
  · exact MergedCutProfiles.Batch263.valid10527
  · exact MergedCutProfiles.Batch263.valid10528
  · exact MergedCutProfiles.Batch263.valid10529
  · exact MergedCutProfiles.Batch263.valid10530
  · exact MergedCutProfiles.Batch263.valid10531
  · exact MergedCutProfiles.Batch263.valid10532
  · exact MergedCutProfiles.Batch263.valid10533
  · exact MergedCutProfiles.Batch263.valid10534
  · exact MergedCutProfiles.Batch263.valid10535
  · exact MergedCutProfiles.Batch263.valid10536
  · exact MergedCutProfiles.Batch263.valid10537
  · exact MergedCutProfiles.Batch263.valid10538
  · exact MergedCutProfiles.Batch263.valid10539
theorem numericValid1640 : retention1640.NumericValid := by decide +kernel
def certificate1640 : RatCutBinCertificate := ⟨⟨retention1640,(1185621024187517083/500000000000000000),(106913959738129263/500000000000000000),(17088822004878414449/1000000000000000000),(182240092104582146113/1000000000000000000),(480338362031962809/500000000000000000)⟩,(989727687633311561/1000000000000000000),(217969268781250851/500000000000000000),(202121302112763299/1000000000000000000),(158240863485484857/1000000000000000000)⟩
theorem valid1640 : certificate1640.Valid := by decide +kernel
theorem sound1640 : certificate1640.Sound := rat_cut_bin_certificate_sound certificate1640 profilesValid1640 numericValid1640 valid1640

def retention1641 : RatCutRetentionCertificate := ⟨(8/125),(513/8000),(5289090254061945077/10655905807287231490),(1026707778418529163/200000000000000000),(11/10),(81888700746013970028324339308530994951/82136622273482333040000000000000000000),false,MergedCutProfiles.Batch263.profile10540,(fun _ => MergedCutProfiles.Batch263.profile10540)⟩
theorem profilesValid1641 : retention1641.ProfilesValid := by
  exact MergedCutProfiles.Batch263.valid10540
theorem numericValid1641 : retention1641.NumericValid := by decide +kernel
def certificate1641 : RatCutBinCertificate := ⟨⟨retention1641,(1185621024187517083/500000000000000000),(106913959738129263/500000000000000000),(17088822004878414449/1000000000000000000),(182240092104582146113/1000000000000000000),(964337015685986473/1000000000000000000)⟩,(989727687633311561/1000000000000000000),(214322794894927409/500000000000000000),(208237532658956089/1000000000000000000),(156238692950025707/1000000000000000000)⟩
theorem valid1641 : certificate1641.Valid := by decide +kernel
theorem sound1641 : certificate1641.Sound := rat_cut_bin_certificate_sound certificate1641 profilesValid1641 numericValid1641 valid1641

def retention1642 : RatCutRetentionCertificate := ⟨(8/125),(513/8000),(1/2),(5289090254061945077/1000000000000000000),(11/10),(2096743276579129783629089611338216518551/2115636101624778030800000000000000000000),false,MergedCutProfiles.Batch263.profile10541,(fun _ => MergedCutProfiles.Batch263.profile10541)⟩
theorem profilesValid1642 : retention1642.ProfilesValid := by
  exact MergedCutProfiles.Batch263.valid10541
theorem numericValid1642 : retention1642.NumericValid := by decide +kernel
def certificate1642 : RatCutBinCertificate := ⟨⟨retention1642,(1185621024187517083/500000000000000000),(106913959738129263/500000000000000000),(17088822004878414449/1000000000000000000),(182240092104582146113/1000000000000000000),(958425527344606409/1000000000000000000)⟩,(989727687633311561/1000000000000000000),(53760155615391817/125000000000000000),(103511889839213553/500000000000000000),(6204674771651987/40000000000000000)⟩
theorem valid1642 : certificate1642.Valid := by decide +kernel
theorem sound1642 : certificate1642.Sound := rat_cut_bin_certificate_sound certificate1642 profilesValid1642 numericValid1642 valid1642

def retention1643 : RatCutRetentionCertificate := ⟨(8/125),(513/8000),(1/2),64,1,(255414670854333229344824896095944825151/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch263.profile10541,(fun _ => MergedCutProfiles.Batch263.profile10541)⟩
theorem profilesValid1643 : retention1643.ProfilesValid := by
  exact MergedCutProfiles.Batch263.valid10541
theorem numericValid1643 : retention1643.NumericValid := by decide +kernel
def certificate1643 : RatCutBinCertificate := ⟨⟨retention1643,(1185621024187517083/500000000000000000),(106913959738129263/500000000000000000),(17088822004878414449/1000000000000000000),(182240092104582146113/1000000000000000000),(484021144077841403/500000000000000000)⟩,(989727687633311561/1000000000000000000),(24349636226577063/62500000000000000),(6078829164140941/25000000000000000),(114734829468146433/500000000000000000)⟩
theorem valid1643 : certificate1643.Valid := by decide +kernel
theorem sound1643 : certificate1643.Sound := rat_cut_bin_certificate_sound certificate1643 profilesValid1643 numericValid1643 valid1643

def certificates : List RatCutBinCertificate := [certificate1632,certificate1633,certificate1634,certificate1635,certificate1636,certificate1637,certificate1638,certificate1639,certificate1640,certificate1641,certificate1642,certificate1643]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1632,List.forall_mem_cons.mpr ⟨sound1633,List.forall_mem_cons.mpr ⟨sound1634,List.forall_mem_cons.mpr ⟨sound1635,List.forall_mem_cons.mpr ⟨sound1636,List.forall_mem_cons.mpr ⟨sound1637,List.forall_mem_cons.mpr ⟨sound1638,List.forall_mem_cons.mpr ⟨sound1639,List.forall_mem_cons.mpr ⟨sound1640,List.forall_mem_cons.mpr ⟨sound1641,List.forall_mem_cons.mpr ⟨sound1642,List.forall_mem_cons.mpr ⟨sound1643,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch136
