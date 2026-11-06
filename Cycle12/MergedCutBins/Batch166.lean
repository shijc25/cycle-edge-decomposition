import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch012
import Cycle12.MergedCutProfiles.Batch013
import Cycle12.MergedCutProfiles.Batch014
import Cycle12.MergedCutProfiles.Batch313
import Cycle12.MergedCutProfiles.Batch314

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch166

def retention1992 : RatCutRetentionCertificate := ⟨(1/100),(11/1000),(16000000000000000000/240392192378436071551),(2402003004088827699/500000000000000000),(23/20),(3680661116634007249080892003676159939831/1921602403271062159200000000000000000000),false,MergedCutProfiles.Batch313.profile12521,(fun _ => MergedCutProfiles.Batch313.profile12521)⟩
theorem profilesValid1992 : retention1992.ProfilesValid := by
  exact MergedCutProfiles.Batch313.valid12521
theorem numericValid1992 : retention1992.NumericValid := by decide +kernel
def certificate1992 : RatCutBinCertificate := ⟨⟨retention1992,(528096720054981793/250000000000000000),(246507623072377/50000000000000000),(7524782997285624993/1000000000000000000),(908546141764463021387/125000000000000000),(382764161958578417/200000000000000000)⟩,(999710552566337041/1000000000000000000),(128836411422949859/1000000000000000000),(605477766120435987/1000000000000000000),(387063842962694537/500000000000000000)⟩
theorem valid1992 : certificate1992.Valid := by decide +kernel
theorem sound1992 : certificate1992.Sound := rat_cut_bin_certificate_sound certificate1992 profilesValid1992 numericValid1992 valid1992

def retention1993 : RatCutRetentionCertificate := ⟨(1/100),(11/1000),(1/2),64,1,(63842289268809469711650675485864946351/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch012.profile509,(fun _ => MergedCutProfiles.Batch012.profile509)⟩
theorem profilesValid1993 : retention1993.ProfilesValid := by
  exact MergedCutProfiles.Batch012.valid509
theorem numericValid1993 : retention1993.NumericValid := by decide +kernel
def certificate1993 : RatCutBinCertificate := ⟨⟨retention1993,(528096720054981793/250000000000000000),(246507623072377/50000000000000000),(7524782997285624993/1000000000000000000),(908546141764463021387/125000000000000000),(996151757888700209/1000000000000000000)⟩,(999710552566337041/1000000000000000000),(247522331098299677/1000000000000000000),(40678308414294099/100000000000000000),(398890848461793983/1000000000000000000)⟩
theorem valid1993 : certificate1993.Valid := by decide +kernel
theorem sound1993 : certificate1993.Sound := rat_cut_bin_certificate_sound certificate1993 profilesValid1993 numericValid1993 valid1993

def retention1994 : RatCutRetentionCertificate := ⟨(11/1000),(3/250),(305621279145706919/402160494138211081563),(587392084229440781/1000000000000000000),4,(65444860856294199704131960097102433/29369604211472039050000000000000000),true,MergedCutProfiles.Batch313.profile12522,![MergedCutProfiles.Batch313.profile12522,MergedCutProfiles.Batch012.profile510,MergedCutProfiles.Batch313.profile12523,MergedCutProfiles.Batch012.profile511,MergedCutProfiles.Batch313.profile12524,MergedCutProfiles.Batch012.profile512,MergedCutProfiles.Batch313.profile12525,MergedCutProfiles.Batch012.profile513,MergedCutProfiles.Batch313.profile12526,MergedCutProfiles.Batch012.profile514,MergedCutProfiles.Batch313.profile12527,MergedCutProfiles.Batch012.profile515,MergedCutProfiles.Batch313.profile12528,MergedCutProfiles.Batch012.profile516,MergedCutProfiles.Batch313.profile12529,MergedCutProfiles.Batch012.profile517]⟩
theorem profilesValid1994 : retention1994.ProfilesValid := by
  change ∀ j : Fin 16, (retention1994.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch313.valid12522
  · exact MergedCutProfiles.Batch012.valid510
  · exact MergedCutProfiles.Batch313.valid12523
  · exact MergedCutProfiles.Batch012.valid511
  · exact MergedCutProfiles.Batch313.valid12524
  · exact MergedCutProfiles.Batch012.valid512
  · exact MergedCutProfiles.Batch313.valid12525
  · exact MergedCutProfiles.Batch012.valid513
  · exact MergedCutProfiles.Batch313.valid12526
  · exact MergedCutProfiles.Batch012.valid514
  · exact MergedCutProfiles.Batch313.valid12527
  · exact MergedCutProfiles.Batch012.valid515
  · exact MergedCutProfiles.Batch313.valid12528
  · exact MergedCutProfiles.Batch012.valid516
  · exact MergedCutProfiles.Batch313.valid12529
  · exact MergedCutProfiles.Batch012.valid517
theorem numericValid1994 : retention1994.NumericValid := by decide +kernel
def certificate1994 : RatCutBinCertificate := ⟨⟨retention1994,(1845333152726590187/1000000000000000000),(5886872707676009/1000000000000000000),(7618205815286770169/1000000000000000000),(3077697513182770252021/500000000000000000),(2222615634590811389/1000000000000000000)⟩,(999701686392685649/1000000000000000000),(564456529580409827/1000000000000000000),(112735345865836353/1000000000000000000),(25321486019864559/500000000000000000)⟩
theorem valid1994 : certificate1994.Valid := by decide +kernel
theorem sound1994 : certificate1994.Sound := rat_cut_bin_certificate_sound certificate1994 profilesValid1994 numericValid1994 valid1994

def retention1995 : RatCutRetentionCertificate := ⟨(11/1000),(3/250),(631381455500000000/402160494138211081563),(305621279145706919/500000000000000000),4,(57853216565044308259/25600000000000000000),true,MergedCutProfiles.Batch313.profile12530,![MergedCutProfiles.Batch313.profile12530,MergedCutProfiles.Batch012.profile511,MergedCutProfiles.Batch313.profile12531,MergedCutProfiles.Batch013.profile526,MergedCutProfiles.Batch313.profile12532,MergedCutProfiles.Batch013.profile527,MergedCutProfiles.Batch313.profile12533,MergedCutProfiles.Batch013.profile528,MergedCutProfiles.Batch313.profile12534,MergedCutProfiles.Batch313.profile12535,MergedCutProfiles.Batch013.profile542,MergedCutProfiles.Batch313.profile12536,MergedCutProfiles.Batch313.profile12537,MergedCutProfiles.Batch013.profile529,MergedCutProfiles.Batch313.profile12538,MergedCutProfiles.Batch313.profile12539]⟩
theorem profilesValid1995 : retention1995.ProfilesValid := by
  change ∀ j : Fin 16, (retention1995.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch313.valid12530
  · exact MergedCutProfiles.Batch012.valid511
  · exact MergedCutProfiles.Batch313.valid12531
  · exact MergedCutProfiles.Batch013.valid526
  · exact MergedCutProfiles.Batch313.valid12532
  · exact MergedCutProfiles.Batch013.valid527
  · exact MergedCutProfiles.Batch313.valid12533
  · exact MergedCutProfiles.Batch013.valid528
  · exact MergedCutProfiles.Batch313.valid12534
  · exact MergedCutProfiles.Batch313.valid12535
  · exact MergedCutProfiles.Batch013.valid542
  · exact MergedCutProfiles.Batch313.valid12536
  · exact MergedCutProfiles.Batch313.valid12537
  · exact MergedCutProfiles.Batch013.valid529
  · exact MergedCutProfiles.Batch313.valid12538
  · exact MergedCutProfiles.Batch313.valid12539
theorem numericValid1995 : retention1995.NumericValid := by decide +kernel
def certificate1995 : RatCutBinCertificate := ⟨⟨retention1995,(1845333152726590187/1000000000000000000),(5886872707676009/1000000000000000000),(7618205815286770169/1000000000000000000),(3077697513182770252021/500000000000000000),(225418743792210213/100000000000000000)⟩,(999701686392685649/1000000000000000000),(542104665102830283/1000000000000000000),(25193340958008231/200000000000000000),(57670500949738287/1000000000000000000)⟩
theorem valid1995 : certificate1995.Valid := by decide +kernel
theorem sound1995 : certificate1995.Sound := rat_cut_bin_certificate_sound certificate1995 profilesValid1995 numericValid1995 valid1995

def retention1996 : RatCutRetentionCertificate := ⟨(11/1000),(3/250),(1620720835994127571/804320988276422163126),(1262762911/1000000000),(49/20),(9242460171700226951/4000000000000000000),true,MergedCutProfiles.Batch313.profile12540,![MergedCutProfiles.Batch313.profile12540,MergedCutProfiles.Batch313.profile12541,MergedCutProfiles.Batch012.profile513,MergedCutProfiles.Batch313.profile12532,MergedCutProfiles.Batch313.profile12542,MergedCutProfiles.Batch012.profile517,MergedCutProfiles.Batch313.profile12534,MergedCutProfiles.Batch313.profile12543,MergedCutProfiles.Batch313.profile12544,MergedCutProfiles.Batch313.profile12545,MergedCutProfiles.Batch313.profile12546,MergedCutProfiles.Batch013.profile525,MergedCutProfiles.Batch013.profile543,MergedCutProfiles.Batch013.profile531,MergedCutProfiles.Batch313.profile12547,MergedCutProfiles.Batch313.profile12548]⟩
theorem profilesValid1996 : retention1996.ProfilesValid := by
  change ∀ j : Fin 16, (retention1996.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch313.valid12540
  · exact MergedCutProfiles.Batch313.valid12541
  · exact MergedCutProfiles.Batch012.valid513
  · exact MergedCutProfiles.Batch313.valid12532
  · exact MergedCutProfiles.Batch313.valid12542
  · exact MergedCutProfiles.Batch012.valid517
  · exact MergedCutProfiles.Batch313.valid12534
  · exact MergedCutProfiles.Batch313.valid12543
  · exact MergedCutProfiles.Batch313.valid12544
  · exact MergedCutProfiles.Batch313.valid12545
  · exact MergedCutProfiles.Batch313.valid12546
  · exact MergedCutProfiles.Batch013.valid525
  · exact MergedCutProfiles.Batch013.valid543
  · exact MergedCutProfiles.Batch013.valid531
  · exact MergedCutProfiles.Batch313.valid12547
  · exact MergedCutProfiles.Batch313.valid12548
theorem numericValid1996 : retention1996.NumericValid := by decide +kernel
def certificate1996 : RatCutBinCertificate := ⟨⟨retention1996,(1845333152726590187/1000000000000000000),(5886872707676009/1000000000000000000),(7618205815286770169/1000000000000000000),(3077697513182770252021/500000000000000000),(1153560722397400299/500000000000000000)⟩,(999701686392685649/1000000000000000000),(350313350237978757/1000000000000000000),(141113837025720483/500000000000000000),(101840985015374851/500000000000000000)⟩
theorem valid1996 : certificate1996.Valid := by decide +kernel
theorem sound1996 : certificate1996.Sound := rat_cut_bin_certificate_sound certificate1996 profilesValid1996 numericValid1996 valid1996

def retention1997 : RatCutRetentionCertificate := ⟨(11/1000),(3/250),(8118331829282046412/134053498046070360521),(1620720835994127571/1000000000000000000),(21/10),(2577559377811448351703/1280000000000000000000),true,MergedCutProfiles.Batch013.profile550,![MergedCutProfiles.Batch013.profile550,MergedCutProfiles.Batch313.profile12549,MergedCutProfiles.Batch313.profile12550,MergedCutProfiles.Batch313.profile12551,MergedCutProfiles.Batch313.profile12552,MergedCutProfiles.Batch313.profile12553,MergedCutProfiles.Batch313.profile12554,MergedCutProfiles.Batch313.profile12555,MergedCutProfiles.Batch313.profile12556,MergedCutProfiles.Batch313.profile12557,MergedCutProfiles.Batch313.profile12558,MergedCutProfiles.Batch313.profile12559,MergedCutProfiles.Batch314.profile12560,MergedCutProfiles.Batch314.profile12561,MergedCutProfiles.Batch314.profile12562,MergedCutProfiles.Batch314.profile12563]⟩
theorem profilesValid1997 : retention1997.ProfilesValid := by
  change ∀ j : Fin 16, (retention1997.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch013.valid550
  · exact MergedCutProfiles.Batch313.valid12549
  · exact MergedCutProfiles.Batch313.valid12550
  · exact MergedCutProfiles.Batch313.valid12551
  · exact MergedCutProfiles.Batch313.valid12552
  · exact MergedCutProfiles.Batch313.valid12553
  · exact MergedCutProfiles.Batch313.valid12554
  · exact MergedCutProfiles.Batch313.valid12555
  · exact MergedCutProfiles.Batch313.valid12556
  · exact MergedCutProfiles.Batch313.valid12557
  · exact MergedCutProfiles.Batch313.valid12558
  · exact MergedCutProfiles.Batch313.valid12559
  · exact MergedCutProfiles.Batch314.valid12560
  · exact MergedCutProfiles.Batch314.valid12561
  · exact MergedCutProfiles.Batch314.valid12562
  · exact MergedCutProfiles.Batch314.valid12563
theorem numericValid1997 : retention1997.NumericValid := by decide +kernel
def certificate1997 : RatCutBinCertificate := ⟨⟨retention1997,(1845333152726590187/1000000000000000000),(5886872707676009/1000000000000000000),(7618205815286770169/1000000000000000000),(3077697513182770252021/500000000000000000),(2010723751316362133/1000000000000000000)⟩,(999701686392685649/1000000000000000000),(35931055419188661/100000000000000000),(27290612745524241/100000000000000000),(40772922382921203/200000000000000000)⟩
theorem valid1997 : certificate1997.Valid := by decide +kernel
theorem sound1997 : certificate1997.Sound := rat_cut_bin_certificate_sound certificate1997 profilesValid1997 numericValid1997 valid1997

def retention1998 : RatCutRetentionCertificate := ⟨(11/1000),(3/250),(32000000000000000000/402160494138211081563),(6088748871961534809/125000000000000000),1,(94404121242336620041407056087994329783/48709990975692278472000000000000000000),false,MergedCutProfiles.Batch314.profile12564,(fun _ => MergedCutProfiles.Batch314.profile12564)⟩
theorem profilesValid1998 : retention1998.ProfilesValid := by
  exact MergedCutProfiles.Batch314.valid12564
theorem numericValid1998 : retention1998.NumericValid := by decide +kernel
def certificate1998 : RatCutBinCertificate := ⟨⟨retention1998,(1845333152726590187/1000000000000000000),(5886872707676009/1000000000000000000),(7618205815286770169/1000000000000000000),(3077697513182770252021/500000000000000000),(1936659419373027963/1000000000000000000)⟩,(999701686392685649/1000000000000000000),(5551703394702363/25000000000000000),(110899596402700171/250000000000000000),(103249882654082787/125000000000000000)⟩
theorem valid1998 : certificate1998.Valid := by decide +kernel
theorem sound1998 : certificate1998.Sound := rat_cut_bin_certificate_sound certificate1998 profilesValid1998 numericValid1998 valid1998

def retention1999 : RatCutRetentionCertificate := ⟨(11/1000),(3/250),(1/2),64,1,(63842322836766415695342227016481542439/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch013.profile555,(fun _ => MergedCutProfiles.Batch013.profile555)⟩
theorem profilesValid1999 : retention1999.ProfilesValid := by
  exact MergedCutProfiles.Batch013.valid555
theorem numericValid1999 : retention1999.NumericValid := by decide +kernel
def certificate1999 : RatCutBinCertificate := ⟨⟨retention1999,(1845333152726590187/1000000000000000000),(5886872707676009/1000000000000000000),(7618205815286770169/1000000000000000000),(3077697513182770252021/500000000000000000),(996110336323459953/1000000000000000000)⟩,(999701686392685649/1000000000000000000),(85867194417072849/200000000000000000),(20765326030918263/100000000000000000),(101807118238571627/500000000000000000)⟩
theorem valid1999 : certificate1999.Valid := by decide +kernel
theorem sound1999 : certificate1999.Sound := rat_cut_bin_certificate_sound certificate1999 profilesValid1999 numericValid1999 valid1999

def retention2000 : RatCutRetentionCertificate := ⟨(11/1000),(3/250),(32000000000000000000/402160494138211081563),(4883574185300548147/1000000000000000000),(23/20),(14696895793272692376290729449151638017759/7813718696480877035200000000000000000000),false,MergedCutProfiles.Batch314.profile12564,(fun _ => MergedCutProfiles.Batch314.profile12564)⟩
theorem profilesValid2000 : retention2000.ProfilesValid := by
  exact MergedCutProfiles.Batch314.valid12564
theorem numericValid2000 : retention2000.NumericValid := by decide +kernel
def certificate2000 : RatCutBinCertificate := ⟨⟨retention2000,(2118906438726590187/1000000000000000000),(5886872707676009/1000000000000000000),(7618205815286770169/1000000000000000000),(3077697513182770252021/500000000000000000),(1879026290220733251/1000000000000000000)⟩,(499828730448789537/500000000000000000),(8120128405316631/62500000000000000),(603300906327607271/1000000000000000000),(763317585748160327/1000000000000000000)⟩
theorem valid2000 : certificate2000.Valid := by decide +kernel
theorem sound2000 : certificate2000.Sound := rat_cut_bin_certificate_sound certificate2000 profilesValid2000 numericValid2000 valid2000

def retention2001 : RatCutRetentionCertificate := ⟨(11/1000),(3/250),(1/2),64,1,(63842322836766415695342227016481542439/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch013.profile555,(fun _ => MergedCutProfiles.Batch013.profile555)⟩
theorem profilesValid2001 : retention2001.ProfilesValid := by
  exact MergedCutProfiles.Batch013.valid555
theorem numericValid2001 : retention2001.NumericValid := by decide +kernel
def certificate2001 : RatCutBinCertificate := ⟨⟨retention2001,(2118906438726590187/1000000000000000000),(5886872707676009/1000000000000000000),(7618205815286770169/1000000000000000000),(3077697513182770252021/500000000000000000),(995898936005062517/1000000000000000000)⟩,(499828730448789537/500000000000000000),(61283064784720469/250000000000000000),(410126140951606463/1000000000000000000),(50255878793205363/125000000000000000)⟩
theorem valid2001 : certificate2001.Valid := by decide +kernel
theorem sound2001 : certificate2001.Sound := rat_cut_bin_certificate_sound certificate2001 profilesValid2001 numericValid2001 valid2001

def retention2002 : RatCutRetentionCertificate := ⟨(3/250),(13/1000),(609349125297694621/682213167231499365169),(591428257662270171/1000000000000000000),4,(1787711556289430893/800000000000000000),true,MergedCutProfiles.Batch314.profile12565,![MergedCutProfiles.Batch314.profile12565,MergedCutProfiles.Batch013.profile556,MergedCutProfiles.Batch314.profile12566,MergedCutProfiles.Batch013.profile557,MergedCutProfiles.Batch314.profile12567,MergedCutProfiles.Batch013.profile558,MergedCutProfiles.Batch314.profile12568,MergedCutProfiles.Batch013.profile559,MergedCutProfiles.Batch314.profile12569,MergedCutProfiles.Batch014.profile560,MergedCutProfiles.Batch314.profile12570,MergedCutProfiles.Batch014.profile561,MergedCutProfiles.Batch314.profile12571,MergedCutProfiles.Batch014.profile562,MergedCutProfiles.Batch314.profile12572,MergedCutProfiles.Batch014.profile563]⟩
theorem profilesValid2002 : retention2002.ProfilesValid := by
  change ∀ j : Fin 16, (retention2002.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch314.valid12565
  · exact MergedCutProfiles.Batch013.valid556
  · exact MergedCutProfiles.Batch314.valid12566
  · exact MergedCutProfiles.Batch013.valid557
  · exact MergedCutProfiles.Batch314.valid12567
  · exact MergedCutProfiles.Batch013.valid558
  · exact MergedCutProfiles.Batch314.valid12568
  · exact MergedCutProfiles.Batch013.valid559
  · exact MergedCutProfiles.Batch314.valid12569
  · exact MergedCutProfiles.Batch014.valid560
  · exact MergedCutProfiles.Batch314.valid12570
  · exact MergedCutProfiles.Batch014.valid561
  · exact MergedCutProfiles.Batch314.valid12571
  · exact MergedCutProfiles.Batch014.valid562
  · exact MergedCutProfiles.Batch314.valid12572
  · exact MergedCutProfiles.Batch014.valid563
theorem numericValid2002 : retention2002.NumericValid := by decide +kernel
def certificate2002 : RatCutBinCertificate := ⟨⟨retention2002,(231550024312635889/125000000000000000),(21663071517499/3125000000000000),(7713429156654005149/1000000000000000000),(660788836219184268857/125000000000000000),(556995078559294741/250000000000000000)⟩,(15619556993347519/15625000000000000),(559032261630249853/1000000000000000000),(57931793228809699/500000000000000000),(52215004082197509/1000000000000000000)⟩
theorem valid2002 : certificate2002.Valid := by decide +kernel
theorem sound2002 : certificate2002.Sound := rat_cut_bin_certificate_sound certificate2002 profilesValid2002 numericValid2002 valid2002

def retention2003 : RatCutRetentionCertificate := ⟨(3/250),(13/1000),(1270020032000000000/682213167231499365169),(609349125297694621/1000000000000000000),4,(577348517853462642157/256000000000000000000),true,MergedCutProfiles.Batch314.profile12573,![MergedCutProfiles.Batch314.profile12573,MergedCutProfiles.Batch314.profile12574,MergedCutProfiles.Batch314.profile12575,MergedCutProfiles.Batch314.profile12576,MergedCutProfiles.Batch314.profile12577,MergedCutProfiles.Batch314.profile12578,MergedCutProfiles.Batch314.profile12579,MergedCutProfiles.Batch314.profile12580,MergedCutProfiles.Batch314.profile12581,MergedCutProfiles.Batch314.profile12582,MergedCutProfiles.Batch014.profile584,MergedCutProfiles.Batch314.profile12583,MergedCutProfiles.Batch314.profile12584,MergedCutProfiles.Batch314.profile12585,MergedCutProfiles.Batch314.profile12586,MergedCutProfiles.Batch314.profile12587]⟩
theorem profilesValid2003 : retention2003.ProfilesValid := by
  change ∀ j : Fin 16, (retention2003.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch314.valid12573
  · exact MergedCutProfiles.Batch314.valid12574
  · exact MergedCutProfiles.Batch314.valid12575
  · exact MergedCutProfiles.Batch314.valid12576
  · exact MergedCutProfiles.Batch314.valid12577
  · exact MergedCutProfiles.Batch314.valid12578
  · exact MergedCutProfiles.Batch314.valid12579
  · exact MergedCutProfiles.Batch314.valid12580
  · exact MergedCutProfiles.Batch314.valid12581
  · exact MergedCutProfiles.Batch314.valid12582
  · exact MergedCutProfiles.Batch014.valid584
  · exact MergedCutProfiles.Batch314.valid12583
  · exact MergedCutProfiles.Batch314.valid12584
  · exact MergedCutProfiles.Batch314.valid12585
  · exact MergedCutProfiles.Batch314.valid12586
  · exact MergedCutProfiles.Batch314.valid12587
theorem numericValid2003 : retention2003.NumericValid := by decide +kernel
def certificate2003 : RatCutBinCertificate := ⟨⟨retention2003,(231550024312635889/125000000000000000),(21663071517499/3125000000000000),(7713429156654005149/1000000000000000000),(660788836219184268857/125000000000000000),(1124304258424518847/500000000000000000)⟩,(15619556993347519/15625000000000000),(271567212412405467/500000000000000000),(25067432935964549/200000000000000000),(28615089260271729/500000000000000000)⟩
theorem valid2003 : certificate2003.Valid := by decide +kernel
theorem sound2003 : certificate2003.Sound := rat_cut_bin_certificate_sound certificate2003 profilesValid2003 numericValid2003 valid2003

def certificates : List RatCutBinCertificate := [certificate1992,certificate1993,certificate1994,certificate1995,certificate1996,certificate1997,certificate1998,certificate1999,certificate2000,certificate2001,certificate2002,certificate2003]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1992,List.forall_mem_cons.mpr ⟨sound1993,List.forall_mem_cons.mpr ⟨sound1994,List.forall_mem_cons.mpr ⟨sound1995,List.forall_mem_cons.mpr ⟨sound1996,List.forall_mem_cons.mpr ⟨sound1997,List.forall_mem_cons.mpr ⟨sound1998,List.forall_mem_cons.mpr ⟨sound1999,List.forall_mem_cons.mpr ⟨sound2000,List.forall_mem_cons.mpr ⟨sound2001,List.forall_mem_cons.mpr ⟨sound2002,List.forall_mem_cons.mpr ⟨sound2003,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch166
