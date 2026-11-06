import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch337
import Cycle12.MergedCutProfiles.Batch338
import Cycle12.MergedCutProfiles.Batch339
import Cycle12.MergedCutProfiles.Batch340
import Cycle12.MergedCutProfiles.Batch465
import Cycle12.MergedCutProfiles.Batch466
import Cycle12.MergedCutProfiles.Batch467

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch251

def retention3012 : RatCutRetentionCertificate := ⟨(4/125),(33/1000),(15570765480000000/3202166334535091093),(288356665782585167/250000000000000000),(13/5),(734648524466407041803/320000000000000000000),true,MergedCutProfiles.Batch465.profile18621,![MergedCutProfiles.Batch465.profile18621,MergedCutProfiles.Batch465.profile18622,MergedCutProfiles.Batch465.profile18623,MergedCutProfiles.Batch465.profile18629,MergedCutProfiles.Batch338.profile13523,MergedCutProfiles.Batch465.profile18630,MergedCutProfiles.Batch465.profile18631,MergedCutProfiles.Batch465.profile18625,MergedCutProfiles.Batch465.profile18632,MergedCutProfiles.Batch465.profile18626,MergedCutProfiles.Batch465.profile18633,MergedCutProfiles.Batch465.profile18634,MergedCutProfiles.Batch465.profile18635,MergedCutProfiles.Batch465.profile18636,MergedCutProfiles.Batch465.profile18637,MergedCutProfiles.Batch465.profile18638]⟩
theorem profilesValid3012 : retention3012.ProfilesValid := by
  change ∀ j : Fin 16, (retention3012.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch465.valid18621
  · exact MergedCutProfiles.Batch465.valid18622
  · exact MergedCutProfiles.Batch465.valid18623
  · exact MergedCutProfiles.Batch465.valid18629
  · exact MergedCutProfiles.Batch338.valid13523
  · exact MergedCutProfiles.Batch465.valid18630
  · exact MergedCutProfiles.Batch465.valid18631
  · exact MergedCutProfiles.Batch465.valid18625
  · exact MergedCutProfiles.Batch465.valid18632
  · exact MergedCutProfiles.Batch465.valid18626
  · exact MergedCutProfiles.Batch465.valid18633
  · exact MergedCutProfiles.Batch465.valid18634
  · exact MergedCutProfiles.Batch465.valid18635
  · exact MergedCutProfiles.Batch465.valid18636
  · exact MergedCutProfiles.Batch465.valid18637
  · exact MergedCutProfiles.Batch465.valid18638
theorem numericValid3012 : retention3012.NumericValid := by decide +kernel
def certificate3012 : RatCutBinCertificate := ⟨⟨retention3012,(77333771313074839/40000000000000000),(481579510880593/10000000000000000),(10080644210854032517/1000000000000000000),(2433461079447895543817/1000000000000000000),(1135881302324781759/500000000000000000)⟩,(249810329147249703/250000000000000000),(97493845118591033/250000000000000000),(30349254369639287/125000000000000000),(3282714782729589/20000000000000000)⟩
theorem valid3012 : certificate3012.Valid := by decide +kernel
theorem sound3012 : certificate3012.Sound := rat_cut_bin_certificate_sound certificate3012 profilesValid3012 numericValid3012 valid3012

def retention3013 : RatCutRetentionCertificate := ⟨(4/125),(33/1000),(533917390409564207/80054158363377277325),(1167807411/1000000000),(51/20),(18195388108572702741/8000000000000000000),true,MergedCutProfiles.Batch465.profile18639,![MergedCutProfiles.Batch465.profile18639,MergedCutProfiles.Batch465.profile18614,MergedCutProfiles.Batch466.profile18640,MergedCutProfiles.Batch466.profile18641,MergedCutProfiles.Batch465.profile18624,MergedCutProfiles.Batch466.profile18642,MergedCutProfiles.Batch466.profile18643,MergedCutProfiles.Batch465.profile18633,MergedCutProfiles.Batch337.profile13483,MergedCutProfiles.Batch337.profile13484,MergedCutProfiles.Batch465.profile18637,MergedCutProfiles.Batch466.profile18644,MergedCutProfiles.Batch466.profile18645,MergedCutProfiles.Batch466.profile18646,MergedCutProfiles.Batch466.profile18647,MergedCutProfiles.Batch338.profile13529]⟩
theorem profilesValid3013 : retention3013.ProfilesValid := by
  change ∀ j : Fin 16, (retention3013.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch465.valid18639
  · exact MergedCutProfiles.Batch465.valid18614
  · exact MergedCutProfiles.Batch466.valid18640
  · exact MergedCutProfiles.Batch466.valid18641
  · exact MergedCutProfiles.Batch465.valid18624
  · exact MergedCutProfiles.Batch466.valid18642
  · exact MergedCutProfiles.Batch466.valid18643
  · exact MergedCutProfiles.Batch465.valid18633
  · exact MergedCutProfiles.Batch337.valid13483
  · exact MergedCutProfiles.Batch337.valid13484
  · exact MergedCutProfiles.Batch465.valid18637
  · exact MergedCutProfiles.Batch466.valid18644
  · exact MergedCutProfiles.Batch466.valid18645
  · exact MergedCutProfiles.Batch466.valid18646
  · exact MergedCutProfiles.Batch466.valid18647
  · exact MergedCutProfiles.Batch338.valid13529
theorem numericValid3013 : retention3013.NumericValid := by decide +kernel
def certificate3013 : RatCutBinCertificate := ⟨⟨retention3013,(77333771313074839/40000000000000000),(481579510880593/10000000000000000),(10080644210854032517/1000000000000000000),(2433461079447895543817/1000000000000000000),(1125435643259833181/500000000000000000)⟩,(249810329147249703/250000000000000000),(39129308918103967/100000000000000000),(30194434991599657/125000000000000000),(32865138897756041/200000000000000000)⟩
theorem valid3013 : certificate3013.Valid := by decide +kernel
theorem sound3013 : certificate3013.Sound := rat_cut_bin_certificate_sound certificate3013 profilesValid3013 numericValid3013 valid3013

def retention3014 : RatCutRetentionCertificate := ⟨(4/125),(33/1000),(7384426042796805348/80054158363377277325),(1601752171228692621/1000000000000000000),(21/10),(1233631618792104131498560360426740062519/640700868491477048400000000000000000000),false,MergedCutProfiles.Batch466.profile18648,(fun _ => MergedCutProfiles.Batch466.profile18648)⟩
theorem profilesValid3014 : retention3014.ProfilesValid := by
  exact MergedCutProfiles.Batch466.valid18648
theorem numericValid3014 : retention3014.NumericValid := by decide +kernel
def certificate3014 : RatCutBinCertificate := ⟨⟨retention3014,(77333771313074839/40000000000000000),(481579510880593/10000000000000000),(10080644210854032517/1000000000000000000),(2433461079447895543817/1000000000000000000),(238255612959805813/125000000000000000)⟩,(249810329147249703/250000000000000000),(201508383722558909/500000000000000000),(28841199035518657/125000000000000000),(10298553164976563/62500000000000000)⟩
theorem valid3014 : certificate3014.Valid := by decide +kernel
theorem sound3014 : certificate3014.Sound := rat_cut_bin_certificate_sound certificate3014 profilesValid3014 numericValid3014 valid3014

def retention3015 : RatCutRetentionCertificate := ⟨(4/125),(33/1000),(2560000000000000000/9606499003605273279),(5538319532097604011/250000000000000000),1,(6483840386765429438397396597525496651/4430655625678083208800000000000000000),false,MergedCutProfiles.Batch466.profile18649,(fun _ => MergedCutProfiles.Batch466.profile18649)⟩
theorem profilesValid3015 : retention3015.ProfilesValid := by
  exact MergedCutProfiles.Batch466.valid18649
theorem numericValid3015 : retention3015.NumericValid := by decide +kernel
def certificate3015 : RatCutBinCertificate := ⟨⟨retention3015,(77333771313074839/40000000000000000),(481579510880593/10000000000000000),(10080644210854032517/1000000000000000000),(2433461079447895543817/1000000000000000000),(58166726454227423/40000000000000000)⟩,(249810329147249703/250000000000000000),(334967438454252249/1000000000000000000),(74665614264948417/250000000000000000),(81447302279966793/200000000000000000)⟩
theorem valid3015 : certificate3015.Valid := by decide +kernel
theorem sound3015 : certificate3015.Sound := rat_cut_bin_certificate_sound certificate3015 profilesValid3015 numericValid3015 valid3015

def retention3016 : RatCutRetentionCertificate := ⟨(4/125),(33/1000),(1/2),64,1,(2553778241264668473974121578981079951/2560000000000000000000000000000000000),false,MergedCutProfiles.Batch338.profile13551,(fun _ => MergedCutProfiles.Batch338.profile13551)⟩
theorem profilesValid3016 : retention3016.ProfilesValid := by
  exact MergedCutProfiles.Batch338.valid13551
theorem numericValid3016 : retention3016.NumericValid := by decide +kernel
def certificate3016 : RatCutBinCertificate := ⟨⟨retention3016,(77333771313074839/40000000000000000),(481579510880593/10000000000000000),(10080644210854032517/1000000000000000000),(2433461079447895543817/1000000000000000000),(494166758272944733/500000000000000000)⟩,(249810329147249703/250000000000000000),(478356331705137899/1000000000000000000),(422259768169721/2500000000000000),(164268879814265711/1000000000000000000)⟩
theorem valid3016 : certificate3016.Valid := by decide +kernel
theorem sound3016 : certificate3016.Sound := rat_cut_bin_certificate_sound certificate3016 profilesValid3016 numericValid3016 valid3016

def retention3017 : RatCutRetentionCertificate := ⟨(4/125),(33/1000),(2560000000000000000/9606499003605273279),(9585934797911637177/1000000000000000000),1,(13713911528553167794631500692578653553/9585934797911637177000000000000000000),false,MergedCutProfiles.Batch466.profile18649,(fun _ => MergedCutProfiles.Batch466.profile18649)⟩
theorem profilesValid3017 : retention3017.ProfilesValid := by
  exact MergedCutProfiles.Batch466.valid18649
theorem numericValid3017 : retention3017.NumericValid := by decide +kernel
def certificate3017 : RatCutBinCertificate := ⟨⟨retention3017,(83337876353074839/40000000000000000),(481579510880593/10000000000000000),(10080644210854032517/1000000000000000000),(2433461079447895543817/1000000000000000000),(56827011739694421/40000000000000000)⟩,(999182411007490829/1000000000000000000),(46141085008616687/500000000000000000),(170938110178912871/250000000000000000),(845283473927406271/1000000000000000000)⟩
theorem valid3017 : certificate3017.Valid := by decide +kernel
theorem sound3017 : certificate3017.Sound := rat_cut_bin_certificate_sound certificate3017 profilesValid3017 numericValid3017 valid3017

def retention3018 : RatCutRetentionCertificate := ⟨(4/125),(33/1000),(1/2),64,1,(2553778241264668473974121578981079951/2560000000000000000000000000000000000),false,MergedCutProfiles.Batch338.profile13551,(fun _ => MergedCutProfiles.Batch338.profile13551)⟩
theorem profilesValid3018 : retention3018.ProfilesValid := by
  exact MergedCutProfiles.Batch338.valid13551
theorem numericValid3018 : retention3018.NumericValid := by decide +kernel
def certificate3018 : RatCutBinCertificate := ⟨⟨retention3018,(83337876353074839/40000000000000000),(481579510880593/10000000000000000),(10080644210854032517/1000000000000000000),(2433461079447895543817/1000000000000000000),(493808217836187121/500000000000000000)⟩,(999182411007490829/1000000000000000000),(132746878482322293/1000000000000000000),(597673883770569099/1000000000000000000),(580823063331716069/1000000000000000000)⟩
theorem valid3018 : certificate3018.Valid := by decide +kernel
theorem sound3018 : certificate3018.Sound := rat_cut_bin_certificate_sound certificate3018 profilesValid3018 numericValid3018 valid3018

def retention3019 : RatCutRetentionCertificate := ⟨(33/1000),(17/500),(667134486682535183/225076812372183446073),(130797860343600663/200000000000000000),4,(592382636539667476347/256000000000000000000),true,MergedCutProfiles.Batch466.profile18650,![MergedCutProfiles.Batch466.profile18650,MergedCutProfiles.Batch466.profile18651,MergedCutProfiles.Batch466.profile18652,MergedCutProfiles.Batch466.profile18653,MergedCutProfiles.Batch466.profile18654,MergedCutProfiles.Batch466.profile18655,MergedCutProfiles.Batch466.profile18656,MergedCutProfiles.Batch466.profile18657,MergedCutProfiles.Batch466.profile18658,MergedCutProfiles.Batch466.profile18659,MergedCutProfiles.Batch466.profile18660,MergedCutProfiles.Batch466.profile18661,MergedCutProfiles.Batch466.profile18662,MergedCutProfiles.Batch466.profile18663,MergedCutProfiles.Batch466.profile18664,MergedCutProfiles.Batch466.profile18665]⟩
theorem profilesValid3019 : retention3019.ProfilesValid := by
  change ∀ j : Fin 16, (retention3019.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch466.valid18650
  · exact MergedCutProfiles.Batch466.valid18651
  · exact MergedCutProfiles.Batch466.valid18652
  · exact MergedCutProfiles.Batch466.valid18653
  · exact MergedCutProfiles.Batch466.valid18654
  · exact MergedCutProfiles.Batch466.valid18655
  · exact MergedCutProfiles.Batch466.valid18656
  · exact MergedCutProfiles.Batch466.valid18657
  · exact MergedCutProfiles.Batch466.valid18658
  · exact MergedCutProfiles.Batch466.valid18659
  · exact MergedCutProfiles.Batch466.valid18660
  · exact MergedCutProfiles.Batch466.valid18661
  · exact MergedCutProfiles.Batch466.valid18662
  · exact MergedCutProfiles.Batch466.valid18663
  · exact MergedCutProfiles.Batch466.valid18664
  · exact MergedCutProfiles.Batch466.valid18665
theorem numericValid3019 : retention3019.NumericValid := by decide +kernel
def certificate3019 : RatCutBinCertificate := ⟨⟨retention3019,(388139244536164797/200000000000000000),(51337219122942991/1000000000000000000),(10227335373511528917/1000000000000000000),(1156931639542237074153/500000000000000000),(2275028202818972243/1000000000000000000)⟩,(499600816720827933/500000000000000000),(52743155388355697/100000000000000000),(1689392265389653/12500000000000000),(7885125134630833/125000000000000000)⟩
theorem valid3019 : certificate3019.Valid := by decide +kernel
theorem sound3019 : certificate3019.Sound := rat_cut_bin_certificate_sound certificate3019 profilesValid3019 numericValid3019 valid3019

def retention3020 : RatCutRetentionCertificate := ⟨(33/1000),(17/500),(1152713183000000000/225076812372183446073),(667134486682535183/1000000000000000000),4,(1475817056227342859/640000000000000000),true,MergedCutProfiles.Batch466.profile18666,![MergedCutProfiles.Batch466.profile18666,MergedCutProfiles.Batch339.profile13571,MergedCutProfiles.Batch466.profile18667,MergedCutProfiles.Batch466.profile18656,MergedCutProfiles.Batch466.profile18668,MergedCutProfiles.Batch339.profile13573,MergedCutProfiles.Batch466.profile18661,MergedCutProfiles.Batch339.profile13574,MergedCutProfiles.Batch466.profile18669,MergedCutProfiles.Batch339.profile13575,MergedCutProfiles.Batch339.profile13561,MergedCutProfiles.Batch339.profile13576,MergedCutProfiles.Batch466.profile18670,MergedCutProfiles.Batch339.profile13563,MergedCutProfiles.Batch466.profile18671,MergedCutProfiles.Batch466.profile18672]⟩
theorem profilesValid3020 : retention3020.ProfilesValid := by
  change ∀ j : Fin 16, (retention3020.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch466.valid18666
  · exact MergedCutProfiles.Batch339.valid13571
  · exact MergedCutProfiles.Batch466.valid18667
  · exact MergedCutProfiles.Batch466.valid18656
  · exact MergedCutProfiles.Batch466.valid18668
  · exact MergedCutProfiles.Batch339.valid13573
  · exact MergedCutProfiles.Batch466.valid18661
  · exact MergedCutProfiles.Batch339.valid13574
  · exact MergedCutProfiles.Batch466.valid18669
  · exact MergedCutProfiles.Batch339.valid13575
  · exact MergedCutProfiles.Batch339.valid13561
  · exact MergedCutProfiles.Batch339.valid13576
  · exact MergedCutProfiles.Batch466.valid18670
  · exact MergedCutProfiles.Batch339.valid13563
  · exact MergedCutProfiles.Batch466.valid18671
  · exact MergedCutProfiles.Batch466.valid18672
theorem numericValid3020 : retention3020.NumericValid := by decide +kernel
def certificate3020 : RatCutBinCertificate := ⟨⟨retention3020,(388139244536164797/200000000000000000),(51337219122942991/1000000000000000000),(10227335373511528917/1000000000000000000),(1156931639542237074153/500000000000000000),(566749421425743569/250000000000000000)⟩,(499600816720827933/500000000000000000),(261456256792329631/500000000000000000),(17257723313180227/125000000000000000),(16119709263538863/250000000000000000)⟩
theorem valid3020 : certificate3020.Valid := by decide +kernel
theorem sound3020 : certificate3020.Sound := rat_cut_bin_certificate_sound certificate3020 profilesValid3020 numericValid3020 valid3020

def retention3021 : RatCutRetentionCertificate := ⟨(33/1000),(17/500),(1236341837945444408/225076812372183446073),(1152713183/1000000000),(13/5),(36660696899175316253/16000000000000000000),true,MergedCutProfiles.Batch466.profile18673,![MergedCutProfiles.Batch466.profile18673,MergedCutProfiles.Batch466.profile18674,MergedCutProfiles.Batch338.profile13556,MergedCutProfiles.Batch466.profile18675,MergedCutProfiles.Batch466.profile18676,MergedCutProfiles.Batch466.profile18660,MergedCutProfiles.Batch466.profile18662,MergedCutProfiles.Batch466.profile18664,MergedCutProfiles.Batch339.profile13598,MergedCutProfiles.Batch340.profile13618,MergedCutProfiles.Batch466.profile18677,MergedCutProfiles.Batch466.profile18678,MergedCutProfiles.Batch339.profile13577,MergedCutProfiles.Batch466.profile18671,MergedCutProfiles.Batch466.profile18672,MergedCutProfiles.Batch466.profile18679]⟩
theorem profilesValid3021 : retention3021.ProfilesValid := by
  change ∀ j : Fin 16, (retention3021.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch466.valid18673
  · exact MergedCutProfiles.Batch466.valid18674
  · exact MergedCutProfiles.Batch338.valid13556
  · exact MergedCutProfiles.Batch466.valid18675
  · exact MergedCutProfiles.Batch466.valid18676
  · exact MergedCutProfiles.Batch466.valid18660
  · exact MergedCutProfiles.Batch466.valid18662
  · exact MergedCutProfiles.Batch466.valid18664
  · exact MergedCutProfiles.Batch339.valid13598
  · exact MergedCutProfiles.Batch340.valid13618
  · exact MergedCutProfiles.Batch466.valid18677
  · exact MergedCutProfiles.Batch466.valid18678
  · exact MergedCutProfiles.Batch339.valid13577
  · exact MergedCutProfiles.Batch466.valid18671
  · exact MergedCutProfiles.Batch466.valid18672
  · exact MergedCutProfiles.Batch466.valid18679
theorem numericValid3021 : retention3021.NumericValid := by decide +kernel
def certificate3021 : RatCutBinCertificate := ⟨⟨retention3021,(388139244536164797/200000000000000000),(51337219122942991/1000000000000000000),(10227335373511528917/1000000000000000000),(1156931639542237074153/500000000000000000),(226596537725707639/100000000000000000)⟩,(499600816720827933/500000000000000000),(389225119614887543/1000000000000000000),(7609412979868379/31250000000000000),(164257889134649029/1000000000000000000)⟩
theorem valid3021 : certificate3021.Valid := by decide +kernel
theorem sound3021 : certificate3021.Sound := rat_cut_bin_certificate_sound certificate3021 profilesValid3021 numericValid3021 valid3021

def retention3022 : RatCutRetentionCertificate := ⟨(33/1000),(17/500),(4462680385337352707/225076812372183446073),(154542729743180551/125000000000000000),(49/20),(21952189382982352207/10000000000000000000),true,MergedCutProfiles.Batch339.profile13572,![MergedCutProfiles.Batch339.profile13572,MergedCutProfiles.Batch467.profile18680,MergedCutProfiles.Batch467.profile18681,MergedCutProfiles.Batch467.profile18682,MergedCutProfiles.Batch467.profile18683,MergedCutProfiles.Batch467.profile18684,MergedCutProfiles.Batch467.profile18685,MergedCutProfiles.Batch339.profile13592,MergedCutProfiles.Batch467.profile18686,MergedCutProfiles.Batch340.profile13615,MergedCutProfiles.Batch340.profile13620,MergedCutProfiles.Batch467.profile18687,MergedCutProfiles.Batch467.profile18688,MergedCutProfiles.Batch467.profile18689,MergedCutProfiles.Batch467.profile18690,MergedCutProfiles.Batch467.profile18691]⟩
theorem profilesValid3022 : retention3022.ProfilesValid := by
  change ∀ j : Fin 16, (retention3022.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch339.valid13572
  · exact MergedCutProfiles.Batch467.valid18680
  · exact MergedCutProfiles.Batch467.valid18681
  · exact MergedCutProfiles.Batch467.valid18682
  · exact MergedCutProfiles.Batch467.valid18683
  · exact MergedCutProfiles.Batch467.valid18684
  · exact MergedCutProfiles.Batch467.valid18685
  · exact MergedCutProfiles.Batch339.valid13592
  · exact MergedCutProfiles.Batch467.valid18686
  · exact MergedCutProfiles.Batch340.valid13615
  · exact MergedCutProfiles.Batch340.valid13620
  · exact MergedCutProfiles.Batch467.valid18687
  · exact MergedCutProfiles.Batch467.valid18688
  · exact MergedCutProfiles.Batch467.valid18689
  · exact MergedCutProfiles.Batch467.valid18690
  · exact MergedCutProfiles.Batch467.valid18691
theorem numericValid3022 : retention3022.NumericValid := by decide +kernel
def certificate3022 : RatCutBinCertificate := ⟨⟨retention3022,(388139244536164797/200000000000000000),(51337219122942991/1000000000000000000),(10227335373511528917/1000000000000000000),(1156931639542237074153/500000000000000000),(434270400463038927/200000000000000000)⟩,(499600816720827933/500000000000000000),(393196574269792799/1000000000000000000),(239774162111949661/1000000000000000000),(82125578186498613/500000000000000000)⟩
theorem valid3022 : certificate3022.Valid := by decide +kernel
theorem sound3022 : certificate3022.Sound := rat_cut_bin_certificate_sound certificate3022 profilesValid3022 numericValid3022 valid3022

def retention3023 : RatCutRetentionCertificate := ⟨(33/1000),(17/500),(64000000000000000000/225076812372183446073),(4462680385337352707/1000000000000000000),(5/4),(412113261227433636730220464035985118231/285611544661590573248000000000000000000),false,MergedCutProfiles.Batch467.profile18692,(fun _ => MergedCutProfiles.Batch467.profile18692)⟩
theorem profilesValid3023 : retention3023.ProfilesValid := by
  exact MergedCutProfiles.Batch467.valid18692
theorem numericValid3023 : retention3023.NumericValid := by decide +kernel
def certificate3023 : RatCutBinCertificate := ⟨⟨retention3023,(388139244536164797/200000000000000000),(51337219122942991/1000000000000000000),(10227335373511528917/1000000000000000000),(1156931639542237074153/500000000000000000),(1430738310123366641/1000000000000000000)⟩,(499600816720827933/500000000000000000),(80060560299623061/200000000000000000),(233205035733604803/1000000000000000000),(2212882573038319/10000000000000000)⟩
theorem valid3023 : certificate3023.Valid := by decide +kernel
theorem sound3023 : certificate3023.Sound := rat_cut_bin_certificate_sound certificate3023 profilesValid3023 numericValid3023 valid3023

def certificates : List RatCutBinCertificate := [certificate3012,certificate3013,certificate3014,certificate3015,certificate3016,certificate3017,certificate3018,certificate3019,certificate3020,certificate3021,certificate3022,certificate3023]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3012,List.forall_mem_cons.mpr ⟨sound3013,List.forall_mem_cons.mpr ⟨sound3014,List.forall_mem_cons.mpr ⟨sound3015,List.forall_mem_cons.mpr ⟨sound3016,List.forall_mem_cons.mpr ⟨sound3017,List.forall_mem_cons.mpr ⟨sound3018,List.forall_mem_cons.mpr ⟨sound3019,List.forall_mem_cons.mpr ⟨sound3020,List.forall_mem_cons.mpr ⟨sound3021,List.forall_mem_cons.mpr ⟨sound3022,List.forall_mem_cons.mpr ⟨sound3023,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch251
