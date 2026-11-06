import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch012
import Cycle12.MergedCutProfiles.Batch013
import Cycle12.MergedCutProfiles.Batch014
import Cycle12.MergedCutProfiles.Batch015

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch006

def retention72 : RatCutRetentionCertificate := ⟨(11/1000),(3/250),(203216362433694361/134053498046070360521),(37352286987861673/62500000000000000),4,(1070738323611298727533206580832914011/478109273444629414400000000000000000),true,MergedCutProfiles.Batch012.profile510,![MergedCutProfiles.Batch012.profile510,MergedCutProfiles.Batch012.profile511,MergedCutProfiles.Batch012.profile512,MergedCutProfiles.Batch012.profile513,MergedCutProfiles.Batch012.profile514,MergedCutProfiles.Batch012.profile515,MergedCutProfiles.Batch012.profile516,MergedCutProfiles.Batch012.profile517,MergedCutProfiles.Batch012.profile518,MergedCutProfiles.Batch012.profile519,MergedCutProfiles.Batch013.profile520,MergedCutProfiles.Batch013.profile521,MergedCutProfiles.Batch013.profile522,MergedCutProfiles.Batch013.profile523,MergedCutProfiles.Batch013.profile524,MergedCutProfiles.Batch013.profile525]⟩
theorem profilesValid72 : retention72.ProfilesValid := by
  change ∀ j : Fin 16, (retention72.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch012.valid510
  · exact MergedCutProfiles.Batch012.valid511
  · exact MergedCutProfiles.Batch012.valid512
  · exact MergedCutProfiles.Batch012.valid513
  · exact MergedCutProfiles.Batch012.valid514
  · exact MergedCutProfiles.Batch012.valid515
  · exact MergedCutProfiles.Batch012.valid516
  · exact MergedCutProfiles.Batch012.valid517
  · exact MergedCutProfiles.Batch012.valid518
  · exact MergedCutProfiles.Batch012.valid519
  · exact MergedCutProfiles.Batch013.valid520
  · exact MergedCutProfiles.Batch013.valid521
  · exact MergedCutProfiles.Batch013.valid522
  · exact MergedCutProfiles.Batch013.valid523
  · exact MergedCutProfiles.Batch013.valid524
  · exact MergedCutProfiles.Batch013.valid525
theorem numericValid72 : retention72.NumericValid := by decide +kernel
def certificate72 : RatCutBinCertificate := ⟨⟨retention72,(1864554888453180373/1000000000000000000),(5886872707676009/1000000000000000000),(7618201219976930221/1000000000000000000),(307769565671236112583/100000000000000000),(558440778093129771/250000000000000000)⟩,(999397156800223951/1000000000000000000),(107975190630998167/200000000000000000),(127335923318337793/1000000000000000000),(11520525895926531/200000000000000000)⟩
theorem valid72 : certificate72.Valid := by decide +kernel
theorem sound72 : certificate72.Sound := rat_cut_bin_certificate_sound certificate72 profilesValid72 numericValid72 valid72

def retention73 : RatCutRetentionCertificate := ⟨(11/1000),(3/250),(1250037047000000000/402160494138211081563),(609649087301083083/1000000000000000000),4,(574939972905275425611/256000000000000000000),true,MergedCutProfiles.Batch012.profile511,![MergedCutProfiles.Batch012.profile511,MergedCutProfiles.Batch013.profile526,MergedCutProfiles.Batch013.profile527,MergedCutProfiles.Batch013.profile528,MergedCutProfiles.Batch012.profile519,MergedCutProfiles.Batch013.profile521,MergedCutProfiles.Batch013.profile529,MergedCutProfiles.Batch013.profile530,MergedCutProfiles.Batch013.profile531,MergedCutProfiles.Batch013.profile532,MergedCutProfiles.Batch013.profile533,MergedCutProfiles.Batch013.profile534,MergedCutProfiles.Batch013.profile535,MergedCutProfiles.Batch013.profile536,MergedCutProfiles.Batch013.profile537,MergedCutProfiles.Batch013.profile538]⟩
theorem profilesValid73 : retention73.ProfilesValid := by
  change ∀ j : Fin 16, (retention73.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch012.valid511
  · exact MergedCutProfiles.Batch013.valid526
  · exact MergedCutProfiles.Batch013.valid527
  · exact MergedCutProfiles.Batch013.valid528
  · exact MergedCutProfiles.Batch012.valid519
  · exact MergedCutProfiles.Batch013.valid521
  · exact MergedCutProfiles.Batch013.valid529
  · exact MergedCutProfiles.Batch013.valid530
  · exact MergedCutProfiles.Batch013.valid531
  · exact MergedCutProfiles.Batch013.valid532
  · exact MergedCutProfiles.Batch013.valid533
  · exact MergedCutProfiles.Batch013.valid534
  · exact MergedCutProfiles.Batch013.valid535
  · exact MergedCutProfiles.Batch013.valid536
  · exact MergedCutProfiles.Batch013.valid537
  · exact MergedCutProfiles.Batch013.valid538
theorem numericValid73 : retention73.NumericValid := by decide +kernel
def certificate73 : RatCutBinCertificate := ⟨⟨retention73,(1864554888453180373/1000000000000000000),(5886872707676009/1000000000000000000),(7618201219976930221/1000000000000000000),(307769565671236112583/100000000000000000),(1120048007913802763/500000000000000000)⟩,(999397156800223951/1000000000000000000),(531464614558804677/1000000000000000000),(33146667372322457/250000000000000000),(12068288470285803/200000000000000000)⟩
theorem valid73 : certificate73.Valid := by decide +kernel
theorem sound73 : certificate73.Sound := rat_cut_bin_certificate_sound certificate73 profilesValid73 numericValid73 valid73

def retention74 : RatCutRetentionCertificate := ⟨(11/1000),(3/250),(577700735439001079/134053498046070360521),(1250037047/1000000000),(49/20),(9123163924589778559/4000000000000000000),true,MergedCutProfiles.Batch013.profile539,![MergedCutProfiles.Batch013.profile539,MergedCutProfiles.Batch013.profile540,MergedCutProfiles.Batch013.profile541,MergedCutProfiles.Batch013.profile542,MergedCutProfiles.Batch013.profile529,MergedCutProfiles.Batch013.profile543,MergedCutProfiles.Batch013.profile544,MergedCutProfiles.Batch013.profile545,MergedCutProfiles.Batch013.profile546,MergedCutProfiles.Batch013.profile536,MergedCutProfiles.Batch013.profile547,MergedCutProfiles.Batch013.profile548,MergedCutProfiles.Batch013.profile549,MergedCutProfiles.Batch013.profile550,MergedCutProfiles.Batch013.profile551,MergedCutProfiles.Batch013.profile552]⟩
theorem profilesValid74 : retention74.ProfilesValid := by
  change ∀ j : Fin 16, (retention74.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch013.valid539
  · exact MergedCutProfiles.Batch013.valid540
  · exact MergedCutProfiles.Batch013.valid541
  · exact MergedCutProfiles.Batch013.valid542
  · exact MergedCutProfiles.Batch013.valid529
  · exact MergedCutProfiles.Batch013.valid543
  · exact MergedCutProfiles.Batch013.valid544
  · exact MergedCutProfiles.Batch013.valid545
  · exact MergedCutProfiles.Batch013.valid546
  · exact MergedCutProfiles.Batch013.valid536
  · exact MergedCutProfiles.Batch013.valid547
  · exact MergedCutProfiles.Batch013.valid548
  · exact MergedCutProfiles.Batch013.valid549
  · exact MergedCutProfiles.Batch013.valid550
  · exact MergedCutProfiles.Batch013.valid551
  · exact MergedCutProfiles.Batch013.valid552
theorem numericValid74 : retention74.NumericValid := by decide +kernel
def certificate74 : RatCutBinCertificate := ⟨⟨retention74,(1864554888453180373/1000000000000000000),(5886872707676009/1000000000000000000),(7618201219976930221/1000000000000000000),(307769565671236112583/100000000000000000),(2277260989044734911/1000000000000000000)⟩,(999397156800223951/1000000000000000000),(350172900258371043/1000000000000000000),(70593750259627641/250000000000000000),(40243401469187843/200000000000000000)⟩
theorem valid74 : certificate74.Valid := by decide +kernel
theorem sound74 : certificate74.Sound := rat_cut_bin_certificate_sound certificate74 profilesValid74 numericValid74 valid74

def retention75 : RatCutRetentionCertificate := ⟨(11/1000),(3/250),(12379013754029014724/134053498046070360521),(1733102206317003237/1000000000000000000),2,(13260922263242784881158802282330817503/6932408825268012948000000000000000000),false,MergedCutProfiles.Batch013.profile553,(fun _ => MergedCutProfiles.Batch013.profile553)⟩
theorem profilesValid75 : retention75.ProfilesValid := by
  exact MergedCutProfiles.Batch013.valid553
theorem numericValid75 : retention75.NumericValid := by decide +kernel
def certificate75 : RatCutBinCertificate := ⟨⟨retention75,(1864554888453180373/1000000000000000000),(5886872707676009/1000000000000000000),(7618201219976930221/1000000000000000000),(307769565671236112583/100000000000000000),(47750161550952803/25000000000000000)⟩,(999397156800223951/1000000000000000000),(362892525504102033/1000000000000000000),(269257966818906533/1000000000000000000),(50365442884032049/250000000000000000)⟩
theorem valid75 : certificate75.Valid := by decide +kernel
theorem sound75 : certificate75.Sound := rat_cut_bin_certificate_sound certificate75 profilesValid75 numericValid75 valid75

def retention76 : RatCutRetentionCertificate := ⟨(11/1000),(3/250),(64000000000000000000/402160494138211081563),(9284260315521761043/250000000000000000),1,(254733662672047069022172308797860426887/148548165048348176688000000000000000000),false,MergedCutProfiles.Batch013.profile554,(fun _ => MergedCutProfiles.Batch013.profile554)⟩
theorem profilesValid76 : retention76.ProfilesValid := by
  exact MergedCutProfiles.Batch013.valid554
theorem numericValid76 : retention76.NumericValid := by decide +kernel
def certificate76 : RatCutBinCertificate := ⟨⟨retention76,(1864554888453180373/1000000000000000000),(5886872707676009/1000000000000000000),(7618201219976930221/1000000000000000000),(307769565671236112583/100000000000000000),(856690597858303273/500000000000000000)⟩,(999397156800223951/1000000000000000000),(254353061362524011/1000000000000000000),(15894140687837937/40000000000000000),(650394808735584973/1000000000000000000)⟩
theorem valid76 : certificate76.Valid := by decide +kernel
theorem sound76 : certificate76.Sound := rat_cut_bin_certificate_sound certificate76 profilesValid76 numericValid76 valid76

def retention77 : RatCutRetentionCertificate := ⟨(11/1000),(3/250),(1/2),64,1,(63842322836766415695342227016481542439/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch013.profile555,(fun _ => MergedCutProfiles.Batch013.profile555)⟩
theorem profilesValid77 : retention77.ProfilesValid := by
  exact MergedCutProfiles.Batch013.valid555
theorem numericValid77 : retention77.NumericValid := by decide +kernel
def certificate77 : RatCutBinCertificate := ⟨⟨retention77,(1864554888453180373/1000000000000000000),(5886872707676009/1000000000000000000),(7618201219976930221/1000000000000000000),(307769565671236112583/100000000000000000),(996095482078132239/1000000000000000000)⟩,(999397156800223951/1000000000000000000),(86440820549717337/200000000000000000),(205237817313206837/1000000000000000000),(100590505905810183/500000000000000000)⟩
theorem valid77 : certificate77.Valid := by decide +kernel
theorem sound77 : certificate77.Sound := rat_cut_bin_certificate_sound certificate77 profilesValid77 numericValid77 valid77

def retention78 : RatCutRetentionCertificate := ⟨(11/1000),(3/250),(64000000000000000000/402160494138211081563),(3412480648357843759/1000000000000000000),(27/20),(9356577494513020244145859561631598578471/5459969037372550014400000000000000000000),false,MergedCutProfiles.Batch013.profile554,(fun _ => MergedCutProfiles.Batch013.profile554)⟩
theorem profilesValid78 : retention78.ProfilesValid := by
  exact MergedCutProfiles.Batch013.valid554
theorem numericValid78 : retention78.NumericValid := by decide +kernel
def certificate78 : RatCutBinCertificate := ⟨⟨retention78,(2219995622453180373/1000000000000000000),(5886872707676009/1000000000000000000),(7618201219976930221/1000000000000000000),(307769565671236112583/100000000000000000),(342270541565904259/200000000000000000)⟩,(62455139761679033/62500000000000000),(224277454653225207/1000000000000000000),(88058809737187943/200000000000000000),(437365298226128053/1000000000000000000)⟩
theorem valid78 : certificate78.Valid := by decide +kernel
theorem sound78 : certificate78.Sound := rat_cut_bin_certificate_sound certificate78 profilesValid78 numericValid78 valid78

def retention79 : RatCutRetentionCertificate := ⟨(11/1000),(3/250),(1/2),64,1,(63842322836766415695342227016481542439/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch013.profile555,(fun _ => MergedCutProfiles.Batch013.profile555)⟩
theorem profilesValid79 : retention79.ProfilesValid := by
  exact MergedCutProfiles.Batch013.valid555
theorem numericValid79 : retention79.NumericValid := by decide +kernel
def certificate79 : RatCutBinCertificate := ⟨⟨retention79,(2219995622453180373/1000000000000000000),(5886872707676009/1000000000000000000),(7618201219976930221/1000000000000000000),(307769565671236112583/100000000000000000),(995820819548448707/1000000000000000000)⟩,(62455139761679033/62500000000000000),(385428605017467313/1000000000000000000),(247101950488880153/1000000000000000000),(121062016251699013/500000000000000000)⟩
theorem valid79 : certificate79.Valid := by decide +kernel
theorem sound79 : certificate79.Sound := rat_cut_bin_certificate_sound certificate79 profilesValid79 numericValid79 valid79

def retention80 : RatCutRetentionCertificate := ⟨(3/250),(13/1000),(205131696020416831/113702194538583227528),(150817343412717011/250000000000000000),4,(143780591455982945591/64000000000000000000),true,MergedCutProfiles.Batch013.profile556,![MergedCutProfiles.Batch013.profile556,MergedCutProfiles.Batch013.profile557,MergedCutProfiles.Batch013.profile558,MergedCutProfiles.Batch013.profile559,MergedCutProfiles.Batch014.profile560,MergedCutProfiles.Batch014.profile561,MergedCutProfiles.Batch014.profile562,MergedCutProfiles.Batch014.profile563,MergedCutProfiles.Batch014.profile564,MergedCutProfiles.Batch014.profile565,MergedCutProfiles.Batch014.profile566,MergedCutProfiles.Batch014.profile567,MergedCutProfiles.Batch014.profile568,MergedCutProfiles.Batch014.profile569,MergedCutProfiles.Batch014.profile570,MergedCutProfiles.Batch014.profile571]⟩
theorem profilesValid80 : retention80.ProfilesValid := by
  change ∀ j : Fin 16, (retention80.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch013.valid556
  · exact MergedCutProfiles.Batch013.valid557
  · exact MergedCutProfiles.Batch013.valid558
  · exact MergedCutProfiles.Batch013.valid559
  · exact MergedCutProfiles.Batch014.valid560
  · exact MergedCutProfiles.Batch014.valid561
  · exact MergedCutProfiles.Batch014.valid562
  · exact MergedCutProfiles.Batch014.valid563
  · exact MergedCutProfiles.Batch014.valid564
  · exact MergedCutProfiles.Batch014.valid565
  · exact MergedCutProfiles.Batch014.valid566
  · exact MergedCutProfiles.Batch014.valid567
  · exact MergedCutProfiles.Batch014.valid568
  · exact MergedCutProfiles.Batch014.valid569
  · exact MergedCutProfiles.Batch014.valid570
  · exact MergedCutProfiles.Batch014.valid571
theorem numericValid80 : retention80.NumericValid := by decide +kernel
def certificate80 : RatCutBinCertificate := ⟨⟨retention80,(1872784232002174223/1000000000000000000),(21663071517499/3125000000000000),(7713422769448688937/1000000000000000000),(660788289044395744131/250000000000000000),(2239839323324414543/1000000000000000000)⟩,(499647813225836113/500000000000000000),(106518684607810899/200000000000000000),(65937163588433329/500000000000000000),(7485767820413447/125000000000000000)⟩
theorem valid80 : certificate80.Valid := by decide +kernel
theorem sound80 : certificate80.Sound := rat_cut_bin_certificate_sound certificate80 profilesValid80 numericValid80 valid80

def retention81 : RatCutRetentionCertificate := ⟨(3/250),(13/1000),(154254620125000000/42638322951968710323),(615395088061250493/1000000000000000000),4,(144003652803544528573/64000000000000000000),true,MergedCutProfiles.Batch013.profile557,![MergedCutProfiles.Batch013.profile557,MergedCutProfiles.Batch013.profile559,MergedCutProfiles.Batch014.profile561,MergedCutProfiles.Batch014.profile563,MergedCutProfiles.Batch014.profile565,MergedCutProfiles.Batch014.profile567,MergedCutProfiles.Batch014.profile569,MergedCutProfiles.Batch014.profile572,MergedCutProfiles.Batch014.profile573,MergedCutProfiles.Batch014.profile574,MergedCutProfiles.Batch014.profile575,MergedCutProfiles.Batch014.profile576,MergedCutProfiles.Batch014.profile577,MergedCutProfiles.Batch014.profile578,MergedCutProfiles.Batch014.profile579,MergedCutProfiles.Batch014.profile580]⟩
theorem profilesValid81 : retention81.ProfilesValid := by
  change ∀ j : Fin 16, (retention81.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch013.valid557
  · exact MergedCutProfiles.Batch013.valid559
  · exact MergedCutProfiles.Batch014.valid561
  · exact MergedCutProfiles.Batch014.valid563
  · exact MergedCutProfiles.Batch014.valid565
  · exact MergedCutProfiles.Batch014.valid567
  · exact MergedCutProfiles.Batch014.valid569
  · exact MergedCutProfiles.Batch014.valid572
  · exact MergedCutProfiles.Batch014.valid573
  · exact MergedCutProfiles.Batch014.valid574
  · exact MergedCutProfiles.Batch014.valid575
  · exact MergedCutProfiles.Batch014.valid576
  · exact MergedCutProfiles.Batch014.valid577
  · exact MergedCutProfiles.Batch014.valid578
  · exact MergedCutProfiles.Batch014.valid579
  · exact MergedCutProfiles.Batch014.valid580
theorem numericValid81 : retention81.NumericValid := by decide +kernel
def certificate81 : RatCutBinCertificate := ⟨⟨retention81,(1872784232002174223/1000000000000000000),(21663071517499/3125000000000000),(7713422769448688937/1000000000000000000),(660788289044395744131/250000000000000000),(1121662328512121361/500000000000000000)⟩,(499647813225836113/500000000000000000),(525028172082503947/1000000000000000000),(27338878785427667/200000000000000000),(12477065950712869/200000000000000000)⟩
theorem valid81 : certificate81.Valid := by decide +kernel
theorem sound81 : certificate81.Sound := rat_cut_bin_certificate_sound certificate81 profilesValid81 numericValid81 valid81

def retention82 : RatCutRetentionCertificate := ⟨(3/250),(13/1000),(234248489472212799/56851097269291613764),(1234036961/1000000000),(49/20),(36455533800611313757/16000000000000000000),true,MergedCutProfiles.Batch014.profile581,![MergedCutProfiles.Batch014.profile581,MergedCutProfiles.Batch014.profile582,MergedCutProfiles.Batch014.profile583,MergedCutProfiles.Batch014.profile564,MergedCutProfiles.Batch014.profile584,MergedCutProfiles.Batch014.profile585,MergedCutProfiles.Batch014.profile571,MergedCutProfiles.Batch014.profile573,MergedCutProfiles.Batch014.profile586,MergedCutProfiles.Batch014.profile587,MergedCutProfiles.Batch014.profile588,MergedCutProfiles.Batch014.profile589,MergedCutProfiles.Batch014.profile590,MergedCutProfiles.Batch014.profile591,MergedCutProfiles.Batch014.profile592,MergedCutProfiles.Batch014.profile593]⟩
theorem profilesValid82 : retention82.ProfilesValid := by
  change ∀ j : Fin 16, (retention82.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch014.valid581
  · exact MergedCutProfiles.Batch014.valid582
  · exact MergedCutProfiles.Batch014.valid583
  · exact MergedCutProfiles.Batch014.valid564
  · exact MergedCutProfiles.Batch014.valid584
  · exact MergedCutProfiles.Batch014.valid585
  · exact MergedCutProfiles.Batch014.valid571
  · exact MergedCutProfiles.Batch014.valid573
  · exact MergedCutProfiles.Batch014.valid586
  · exact MergedCutProfiles.Batch014.valid587
  · exact MergedCutProfiles.Batch014.valid588
  · exact MergedCutProfiles.Batch014.valid589
  · exact MergedCutProfiles.Batch014.valid590
  · exact MergedCutProfiles.Batch014.valid591
  · exact MergedCutProfiles.Batch014.valid592
  · exact MergedCutProfiles.Batch014.valid593
theorem numericValid82 : retention82.NumericValid := by decide +kernel
def certificate82 : RatCutBinCertificate := ⟨⟨retention82,(1872784232002174223/1000000000000000000),(21663071517499/3125000000000000),(7713422769448688937/1000000000000000000),(660788289044395744131/250000000000000000),(227434725731053869/100000000000000000)⟩,(499647813225836113/500000000000000000),(70422241920469243/200000000000000000),(35043342816120709/125000000000000000),(39790469709387189/200000000000000000)⟩
theorem valid82 : certificate82.Valid := by decide +kernel
theorem sound82 : certificate82.Sound := rat_cut_bin_certificate_sound certificate82 profilesValid82 numericValid82 valid82

def retention83 : RatCutRetentionCertificate := ⟨(3/250),(13/1000),(3711526293106491221/113702194538583227528),(702745468416638397/500000000000000000),(9/4),(271071846430025662497/128000000000000000000),true,MergedCutProfiles.Batch014.profile573,![MergedCutProfiles.Batch014.profile573,MergedCutProfiles.Batch014.profile594,MergedCutProfiles.Batch014.profile595,MergedCutProfiles.Batch014.profile596,MergedCutProfiles.Batch014.profile597,MergedCutProfiles.Batch014.profile598,MergedCutProfiles.Batch014.profile599,MergedCutProfiles.Batch015.profile600,MergedCutProfiles.Batch015.profile601,MergedCutProfiles.Batch015.profile602,MergedCutProfiles.Batch015.profile603,MergedCutProfiles.Batch015.profile604,MergedCutProfiles.Batch015.profile605,MergedCutProfiles.Batch015.profile606,MergedCutProfiles.Batch015.profile607,MergedCutProfiles.Batch015.profile608]⟩
theorem profilesValid83 : retention83.ProfilesValid := by
  change ∀ j : Fin 16, (retention83.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch014.valid573
  · exact MergedCutProfiles.Batch014.valid594
  · exact MergedCutProfiles.Batch014.valid595
  · exact MergedCutProfiles.Batch014.valid596
  · exact MergedCutProfiles.Batch014.valid597
  · exact MergedCutProfiles.Batch014.valid598
  · exact MergedCutProfiles.Batch014.valid599
  · exact MergedCutProfiles.Batch015.valid600
  · exact MergedCutProfiles.Batch015.valid601
  · exact MergedCutProfiles.Batch015.valid602
  · exact MergedCutProfiles.Batch015.valid603
  · exact MergedCutProfiles.Batch015.valid604
  · exact MergedCutProfiles.Batch015.valid605
  · exact MergedCutProfiles.Batch015.valid606
  · exact MergedCutProfiles.Batch015.valid607
  · exact MergedCutProfiles.Batch015.valid608
theorem numericValid83 : retention83.NumericValid := by decide +kernel
def certificate83 : RatCutBinCertificate := ⟨⟨retention83,(1872784232002174223/1000000000000000000),(21663071517499/3125000000000000),(7713422769448688937/1000000000000000000),(660788289044395744131/250000000000000000),(422792363197235197/200000000000000000)⟩,(499647813225836113/500000000000000000),(357185524999986489/1000000000000000000),(55017451295574949/200000000000000000),(39819420328885647/200000000000000000)⟩
theorem valid83 : certificate83.Valid := by decide +kernel
theorem sound83 : certificate83.Sound := rat_cut_bin_certificate_sound certificate83 profilesValid83 numericValid83 valid83

def certificates : List RatCutBinCertificate := [certificate72,certificate73,certificate74,certificate75,certificate76,certificate77,certificate78,certificate79,certificate80,certificate81,certificate82,certificate83]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound72,List.forall_mem_cons.mpr ⟨sound73,List.forall_mem_cons.mpr ⟨sound74,List.forall_mem_cons.mpr ⟨sound75,List.forall_mem_cons.mpr ⟨sound76,List.forall_mem_cons.mpr ⟨sound77,List.forall_mem_cons.mpr ⟨sound78,List.forall_mem_cons.mpr ⟨sound79,List.forall_mem_cons.mpr ⟨sound80,List.forall_mem_cons.mpr ⟨sound81,List.forall_mem_cons.mpr ⟨sound82,List.forall_mem_cons.mpr ⟨sound83,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch006
