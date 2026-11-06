import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch255
import Cycle12.MergedCutProfiles.Batch419
import Cycle12.MergedCutProfiles.Batch420
import Cycle12.MergedCutProfiles.Batch421
import Cycle12.MergedCutProfiles.Batch544
import Cycle12.MergedCutProfiles.Batch545
import Cycle12.MergedCutProfiles.Batch546

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch295

def retention3540 : RatCutRetentionCertificate := ⟨(253/4000),(127/2000),(27157159285441985506/54547126863153105821),(25079180970385413099/1000000000000000000),1,(1560892853344090751670635114005887827/1567448810649088318687500000000000000),false,MergedCutProfiles.Batch544.profile21779,(fun _ => MergedCutProfiles.Batch544.profile21779)⟩
theorem profilesValid3540 : retention3540.ProfilesValid := by
  exact MergedCutProfiles.Batch544.valid21779
theorem numericValid3540 : retention3540.NumericValid := by decide +kernel
def certificate3540 : RatCutBinCertificate := ⟨⟨retention3540,(2311929792266006051/1000000000000000000),(2610492019033761/12500000000000000),(16855991791084864887/1000000000000000000),(920885892078861988323/1000000000000000000),(483586619995024311/500000000000000000)⟩,(499003878467440373/500000000000000000),(123747681330908027/1000000000000000000),(76973580236854869/125000000000000000),(286143806945479847/500000000000000000)⟩
theorem valid3540 : certificate3540.Valid := by decide +kernel
theorem sound3540 : certificate3540.Sound := rat_cut_bin_certificate_sound certificate3540 profilesValid3540 numericValid3540 valid3540

def retention3541 : RatCutRetentionCertificate := ⟨(253/4000),(127/2000),(1/2),(13578579642720992753/500000000000000000),1,(107802183958954023881714806659850319343/108628637141767942024000000000000000000),false,MergedCutProfiles.Batch255.profile10215,(fun _ => MergedCutProfiles.Batch255.profile10215)⟩
theorem profilesValid3541 : retention3541.ProfilesValid := by
  exact MergedCutProfiles.Batch255.valid10215
theorem numericValid3541 : retention3541.NumericValid := by decide +kernel
def certificate3541 : RatCutBinCertificate := ⟨⟨retention3541,(2311929792266006051/1000000000000000000),(2610492019033761/12500000000000000),(16855991791084864887/1000000000000000000),(920885892078861988323/1000000000000000000),(963747765358312853/1000000000000000000)⟩,(499003878467440373/500000000000000000),(12418752104662197/100000000000000000),(614890377379567247/1000000000000000000),(571123073655011521/1000000000000000000)⟩
theorem valid3541 : certificate3541.Valid := by decide +kernel
theorem sound3541 : certificate3541.Sound := rat_cut_bin_certificate_sound certificate3541 profilesValid3541 numericValid3541 valid3541

def retention3542 : RatCutRetentionCertificate := ⟨(127/2000),(8/125),(462345361303523587/26764961125307303143),(915535368917868489/1000000000000000000),(57/20),(566634662719018093269/256000000000000000000),true,MergedCutProfiles.Batch544.profile21780,![MergedCutProfiles.Batch544.profile21780,MergedCutProfiles.Batch544.profile21781,MergedCutProfiles.Batch544.profile21782,MergedCutProfiles.Batch544.profile21783,MergedCutProfiles.Batch544.profile21784,MergedCutProfiles.Batch544.profile21785,MergedCutProfiles.Batch544.profile21786,MergedCutProfiles.Batch419.profile16798,MergedCutProfiles.Batch544.profile21787,MergedCutProfiles.Batch544.profile21788,MergedCutProfiles.Batch544.profile21789,MergedCutProfiles.Batch544.profile21790,MergedCutProfiles.Batch544.profile21791,MergedCutProfiles.Batch544.profile21792,MergedCutProfiles.Batch544.profile21793,MergedCutProfiles.Batch420.profile16801]⟩
theorem profilesValid3542 : retention3542.ProfilesValid := by
  change ∀ j : Fin 16, (retention3542.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch544.valid21780
  · exact MergedCutProfiles.Batch544.valid21781
  · exact MergedCutProfiles.Batch544.valid21782
  · exact MergedCutProfiles.Batch544.valid21783
  · exact MergedCutProfiles.Batch544.valid21784
  · exact MergedCutProfiles.Batch544.valid21785
  · exact MergedCutProfiles.Batch544.valid21786
  · exact MergedCutProfiles.Batch419.valid16798
  · exact MergedCutProfiles.Batch544.valid21787
  · exact MergedCutProfiles.Batch544.valid21788
  · exact MergedCutProfiles.Batch544.valid21789
  · exact MergedCutProfiles.Batch544.valid21790
  · exact MergedCutProfiles.Batch544.valid21791
  · exact MergedCutProfiles.Batch544.valid21792
  · exact MergedCutProfiles.Batch544.valid21793
  · exact MergedCutProfiles.Batch420.valid16801
theorem numericValid3542 : retention3542.NumericValid := by decide +kernel
def certificate3542 : RatCutBinCertificate := ⟨⟨retention3542,(566877307631922261/250000000000000000),(106411689904918233/500000000000000000),(1693583516892780107/100000000000000000),(909423140879630589347/1000000000000000000),(2132199904257223517/1000000000000000000)⟩,(998026322101139937/1000000000000000000),(60607743347265497/200000000000000000),(335143755147671203/1000000000000000000),(194400888955787449/1000000000000000000)⟩
theorem valid3542 : certificate3542.Valid := by decide +kernel
theorem sound3542 : certificate3542.Sound := rat_cut_bin_certificate_sound certificate3542 profilesValid3542 numericValid3542 valid3542

def retention3543 : RatCutRetentionCertificate := ⟨(127/2000),(8/125),(1084272594488086981/53529922250614606286),(462345361303523587/500000000000000000),(57/20),(22060776638344093581/10000000000000000000),true,MergedCutProfiles.Batch544.profile21794,![MergedCutProfiles.Batch544.profile21794,MergedCutProfiles.Batch544.profile21795,MergedCutProfiles.Batch544.profile21796,MergedCutProfiles.Batch544.profile21797,MergedCutProfiles.Batch420.profile16813,MergedCutProfiles.Batch544.profile21786,MergedCutProfiles.Batch544.profile21798,MergedCutProfiles.Batch544.profile21799,MergedCutProfiles.Batch545.profile21800,MergedCutProfiles.Batch545.profile21801,MergedCutProfiles.Batch545.profile21802,MergedCutProfiles.Batch545.profile21803,MergedCutProfiles.Batch545.profile21804,MergedCutProfiles.Batch545.profile21805,MergedCutProfiles.Batch545.profile21806,MergedCutProfiles.Batch545.profile21807]⟩
theorem profilesValid3543 : retention3543.ProfilesValid := by
  change ∀ j : Fin 16, (retention3543.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch544.valid21794
  · exact MergedCutProfiles.Batch544.valid21795
  · exact MergedCutProfiles.Batch544.valid21796
  · exact MergedCutProfiles.Batch544.valid21797
  · exact MergedCutProfiles.Batch420.valid16813
  · exact MergedCutProfiles.Batch544.valid21786
  · exact MergedCutProfiles.Batch544.valid21798
  · exact MergedCutProfiles.Batch544.valid21799
  · exact MergedCutProfiles.Batch545.valid21800
  · exact MergedCutProfiles.Batch545.valid21801
  · exact MergedCutProfiles.Batch545.valid21802
  · exact MergedCutProfiles.Batch545.valid21803
  · exact MergedCutProfiles.Batch545.valid21804
  · exact MergedCutProfiles.Batch545.valid21805
  · exact MergedCutProfiles.Batch545.valid21806
  · exact MergedCutProfiles.Batch545.valid21807
theorem numericValid3543 : retention3543.NumericValid := by decide +kernel
def certificate3543 : RatCutBinCertificate := ⟨⟨retention3543,(566877307631922261/250000000000000000),(106411689904918233/500000000000000000),(1693583516892780107/100000000000000000),(909423140879630589347/1000000000000000000),(424972197791861487/200000000000000000)⟩,(998026322101139937/1000000000000000000),(75682854692548253/250000000000000000),(167755308386500859/500000000000000000),(6078789219756027/31250000000000000)⟩
theorem valid3543 : certificate3543.Valid := by decide +kernel
theorem sound3543 : certificate3543.Sound := rat_cut_bin_certificate_sound certificate3543 profilesValid3543 numericValid3543 valid3543

def retention3544 : RatCutRetentionCertificate := ⟨(127/2000),(8/125),(79586996000000000/3823565875043900449),(1084272594488086981/1000000000000000000),(49/20),(557737278823027870833/256000000000000000000),true,MergedCutProfiles.Batch545.profile21808,![MergedCutProfiles.Batch545.profile21808,MergedCutProfiles.Batch545.profile21809,MergedCutProfiles.Batch545.profile21810,MergedCutProfiles.Batch545.profile21811,MergedCutProfiles.Batch545.profile21812,MergedCutProfiles.Batch545.profile21813,MergedCutProfiles.Batch545.profile21814,MergedCutProfiles.Batch545.profile21815,MergedCutProfiles.Batch545.profile21816,MergedCutProfiles.Batch544.profile21790,MergedCutProfiles.Batch545.profile21817,MergedCutProfiles.Batch545.profile21818,MergedCutProfiles.Batch421.profile16843,MergedCutProfiles.Batch545.profile21819,MergedCutProfiles.Batch545.profile21820,MergedCutProfiles.Batch545.profile21821]⟩
theorem profilesValid3544 : retention3544.ProfilesValid := by
  change ∀ j : Fin 16, (retention3544.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch545.valid21808
  · exact MergedCutProfiles.Batch545.valid21809
  · exact MergedCutProfiles.Batch545.valid21810
  · exact MergedCutProfiles.Batch545.valid21811
  · exact MergedCutProfiles.Batch545.valid21812
  · exact MergedCutProfiles.Batch545.valid21813
  · exact MergedCutProfiles.Batch545.valid21814
  · exact MergedCutProfiles.Batch545.valid21815
  · exact MergedCutProfiles.Batch545.valid21816
  · exact MergedCutProfiles.Batch544.valid21790
  · exact MergedCutProfiles.Batch545.valid21817
  · exact MergedCutProfiles.Batch545.valid21818
  · exact MergedCutProfiles.Batch421.valid16843
  · exact MergedCutProfiles.Batch545.valid21819
  · exact MergedCutProfiles.Batch545.valid21820
  · exact MergedCutProfiles.Batch545.valid21821
theorem numericValid3544 : retention3544.NumericValid := by decide +kernel
def certificate3544 : RatCutBinCertificate := ⟨⟨retention3544,(566877307631922261/250000000000000000),(106411689904918233/500000000000000000),(1693583516892780107/100000000000000000),(909423140879630589347/1000000000000000000),(210884345132709251/100000000000000000)⟩,(998026322101139937/1000000000000000000),(284952269907267591/1000000000000000000),(11164836595360367/31250000000000000),(231719557388688493/1000000000000000000)⟩
theorem valid3544 : certificate3544.Valid := by decide +kernel
theorem sound3544 : certificate3544.Sound := rat_cut_bin_certificate_sound certificate3544 profilesValid3544 numericValid3544 valid3544

def retention3545 : RatCutRetentionCertificate := ⟨(127/2000),(8/125),(190892686655247649/7647131750087800898),(139277243/125000000),(49/20),(2174922978691961291/1000000000000000000),true,MergedCutProfiles.Batch545.profile21822,![MergedCutProfiles.Batch545.profile21822,MergedCutProfiles.Batch420.profile16812,MergedCutProfiles.Batch545.profile21823,MergedCutProfiles.Batch545.profile21824,MergedCutProfiles.Batch545.profile21813,MergedCutProfiles.Batch545.profile21825,MergedCutProfiles.Batch545.profile21826,MergedCutProfiles.Batch545.profile21827,MergedCutProfiles.Batch544.profile21791,MergedCutProfiles.Batch545.profile21818,MergedCutProfiles.Batch545.profile21828,MergedCutProfiles.Batch545.profile21829,MergedCutProfiles.Batch545.profile21807,MergedCutProfiles.Batch420.profile16830,MergedCutProfiles.Batch545.profile21830,MergedCutProfiles.Batch419.profile16788]⟩
theorem profilesValid3545 : retention3545.ProfilesValid := by
  change ∀ j : Fin 16, (retention3545.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch545.valid21822
  · exact MergedCutProfiles.Batch420.valid16812
  · exact MergedCutProfiles.Batch545.valid21823
  · exact MergedCutProfiles.Batch545.valid21824
  · exact MergedCutProfiles.Batch545.valid21813
  · exact MergedCutProfiles.Batch545.valid21825
  · exact MergedCutProfiles.Batch545.valid21826
  · exact MergedCutProfiles.Batch545.valid21827
  · exact MergedCutProfiles.Batch544.valid21791
  · exact MergedCutProfiles.Batch545.valid21818
  · exact MergedCutProfiles.Batch545.valid21828
  · exact MergedCutProfiles.Batch545.valid21829
  · exact MergedCutProfiles.Batch545.valid21807
  · exact MergedCutProfiles.Batch420.valid16830
  · exact MergedCutProfiles.Batch545.valid21830
  · exact MergedCutProfiles.Batch419.valid16788
theorem numericValid3545 : retention3545.NumericValid := by decide +kernel
def certificate3545 : RatCutBinCertificate := ⟨⟨retention3545,(566877307631922261/250000000000000000),(106411689904918233/500000000000000000),(1693583516892780107/100000000000000000),(909423140879630589347/1000000000000000000),(2105105349902526503/1000000000000000000)⟩,(998026322101139937/1000000000000000000),(282325889102137189/1000000000000000000),(360581703633633277/1000000000000000000),(235097094510419677/1000000000000000000)⟩
theorem valid3545 : certificate3545.Valid := by decide +kernel
theorem sound3545 : certificate3545.Sound := rat_cut_bin_certificate_sound certificate3545 profilesValid3545 numericValid3545 valid3545

def retention3546 : RatCutRetentionCertificate := ⟨(127/2000),(8/125),(4543769642175806001/53529922250614606286),(1336248806586733543/1000000000000000000),(43/20),(2511198095121849909271/1280000000000000000000),true,MergedCutProfiles.Batch545.profile21831,![MergedCutProfiles.Batch545.profile21831,MergedCutProfiles.Batch545.profile21832,MergedCutProfiles.Batch545.profile21833,MergedCutProfiles.Batch545.profile21834,MergedCutProfiles.Batch545.profile21835,MergedCutProfiles.Batch545.profile21836,MergedCutProfiles.Batch545.profile21837,MergedCutProfiles.Batch545.profile21838,MergedCutProfiles.Batch545.profile21839,MergedCutProfiles.Batch546.profile21840,MergedCutProfiles.Batch546.profile21841,MergedCutProfiles.Batch546.profile21842,MergedCutProfiles.Batch546.profile21843,MergedCutProfiles.Batch546.profile21844,MergedCutProfiles.Batch546.profile21845,MergedCutProfiles.Batch546.profile21846]⟩
theorem profilesValid3546 : retention3546.ProfilesValid := by
  change ∀ j : Fin 16, (retention3546.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch545.valid21831
  · exact MergedCutProfiles.Batch545.valid21832
  · exact MergedCutProfiles.Batch545.valid21833
  · exact MergedCutProfiles.Batch545.valid21834
  · exact MergedCutProfiles.Batch545.valid21835
  · exact MergedCutProfiles.Batch545.valid21836
  · exact MergedCutProfiles.Batch545.valid21837
  · exact MergedCutProfiles.Batch545.valid21838
  · exact MergedCutProfiles.Batch545.valid21839
  · exact MergedCutProfiles.Batch546.valid21840
  · exact MergedCutProfiles.Batch546.valid21841
  · exact MergedCutProfiles.Batch546.valid21842
  · exact MergedCutProfiles.Batch546.valid21843
  · exact MergedCutProfiles.Batch546.valid21844
  · exact MergedCutProfiles.Batch546.valid21845
  · exact MergedCutProfiles.Batch546.valid21846
theorem numericValid3546 : retention3546.NumericValid := by decide +kernel
def certificate3546 : RatCutBinCertificate := ⟨⟨retention3546,(566877307631922261/250000000000000000),(106411689904918233/500000000000000000),(1693583516892780107/100000000000000000),(909423140879630589347/1000000000000000000),(1900605242025127107/1000000000000000000)⟩,(998026322101139937/1000000000000000000),(291830096389751047/1000000000000000000),(348728165650881367/1000000000000000000),(2939882303365581/12500000000000000)⟩
theorem valid3546 : certificate3546.Valid := by decide +kernel
theorem sound3546 : certificate3546.Sound := rat_cut_bin_certificate_sound certificate3546 profilesValid3546 numericValid3546 valid3546

def retention3547 : RatCutRetentionCertificate := ⟨(127/2000),(8/125),(10516660942435415002/26764961125307303143),(4543769642175806001/1000000000000000000),(11/10),(1523094047783019722013/1280000000000000000000),true,MergedCutProfiles.Batch546.profile21847,![MergedCutProfiles.Batch546.profile21847,MergedCutProfiles.Batch420.profile16835,MergedCutProfiles.Batch546.profile21848,MergedCutProfiles.Batch546.profile21849,MergedCutProfiles.Batch546.profile21850,MergedCutProfiles.Batch546.profile21851,MergedCutProfiles.Batch421.profile16864,MergedCutProfiles.Batch546.profile21852,MergedCutProfiles.Batch546.profile21853,MergedCutProfiles.Batch546.profile21854,MergedCutProfiles.Batch546.profile21855,MergedCutProfiles.Batch546.profile21856,MergedCutProfiles.Batch546.profile21857,MergedCutProfiles.Batch546.profile21858,MergedCutProfiles.Batch546.profile21859,MergedCutProfiles.Batch546.profile21860]⟩
theorem profilesValid3547 : retention3547.ProfilesValid := by
  change ∀ j : Fin 16, (retention3547.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch546.valid21847
  · exact MergedCutProfiles.Batch420.valid16835
  · exact MergedCutProfiles.Batch546.valid21848
  · exact MergedCutProfiles.Batch546.valid21849
  · exact MergedCutProfiles.Batch546.valid21850
  · exact MergedCutProfiles.Batch546.valid21851
  · exact MergedCutProfiles.Batch421.valid16864
  · exact MergedCutProfiles.Batch546.valid21852
  · exact MergedCutProfiles.Batch546.valid21853
  · exact MergedCutProfiles.Batch546.valid21854
  · exact MergedCutProfiles.Batch546.valid21855
  · exact MergedCutProfiles.Batch546.valid21856
  · exact MergedCutProfiles.Batch546.valid21857
  · exact MergedCutProfiles.Batch546.valid21858
  · exact MergedCutProfiles.Batch546.valid21859
  · exact MergedCutProfiles.Batch546.valid21860
theorem numericValid3547 : retention3547.NumericValid := by decide +kernel
def certificate3547 : RatCutBinCertificate := ⟨⟨retention3547,(566877307631922261/250000000000000000),(106411689904918233/500000000000000000),(1693583516892780107/100000000000000000),(909423140879630589347/1000000000000000000),(579285876903894341/500000000000000000)⟩,(998026322101139937/1000000000000000000),(89359153316536937/250000000000000000),(274828883246040857/1000000000000000000),(238557101104171063/1000000000000000000)⟩
theorem valid3547 : certificate3547.Valid := by decide +kernel
theorem sound3547 : certificate3547.Sound := rat_cut_bin_certificate_sound certificate3547 profilesValid3547 numericValid3547 valid3547

def retention3548 : RatCutRetentionCertificate := ⟨(127/2000),(8/125),(13221157213339152531/26764961125307303143),(5258330471217707501/250000000000000000),1,(84259511837534165639892967130599193839/84133287539483320016000000000000000000),false,MergedCutProfiles.Batch546.profile21861,(fun _ => MergedCutProfiles.Batch546.profile21861)⟩
theorem profilesValid3548 : retention3548.ProfilesValid := by
  exact MergedCutProfiles.Batch546.valid21861
theorem numericValid3548 : retention3548.NumericValid := by decide +kernel
def certificate3548 : RatCutBinCertificate := ⟨⟨retention3548,(566877307631922261/250000000000000000),(106411689904918233/500000000000000000),(1693583516892780107/100000000000000000),(909423140879630589347/1000000000000000000),(486502711996133729/500000000000000000)⟩,(998026322101139937/1000000000000000000),(37843162328802363/100000000000000000),(253836288894809877/1000000000000000000),(29447939930252967/125000000000000000)⟩
theorem valid3548 : certificate3548.Valid := by decide +kernel
theorem sound3548 : certificate3548.Sound := rat_cut_bin_certificate_sound certificate3548 profilesValid3548 numericValid3548 valid3548

def retention3549 : RatCutRetentionCertificate := ⟨(127/2000),(8/125),(26706737570945088113/53529922250614606286),(13221157213339152531/500000000000000000),1,(273865731187349631286219793556756393/275440775277899011062500000000000000),false,MergedCutProfiles.Batch546.profile21862,(fun _ => MergedCutProfiles.Batch546.profile21862)⟩
theorem profilesValid3549 : retention3549.ProfilesValid := by
  exact MergedCutProfiles.Batch546.valid21862
theorem numericValid3549 : retention3549.NumericValid := by decide +kernel
def certificate3549 : RatCutBinCertificate := ⟨⟨retention3549,(566877307631922261/250000000000000000),(106411689904918233/500000000000000000),(1693583516892780107/100000000000000000),(909423140879630589347/1000000000000000000),(482893465758185459/500000000000000000)⟩,(998026322101139937/1000000000000000000),(15143248327704923/40000000000000000),(63422743764549241/250000000000000000),(47179972246655127/200000000000000000)⟩
theorem valid3549 : certificate3549.Valid := by decide +kernel
theorem sound3549 : certificate3549.Sound := rat_cut_bin_certificate_sound certificate3549 profilesValid3549 numericValid3549 valid3549

def retention3550 : RatCutRetentionCertificate := ⟨(127/2000),(8/125),(1/2),(26706737570945088113/1000000000000000000),1,(26499432102042579838909434898995722193/26706737570945088113000000000000000000),false,MergedCutProfiles.Batch421.profile16877,(fun _ => MergedCutProfiles.Batch421.profile16877)⟩
theorem profilesValid3550 : retention3550.ProfilesValid := by
  exact MergedCutProfiles.Batch421.valid16877
theorem numericValid3550 : retention3550.NumericValid := by decide +kernel
def certificate3550 : RatCutBinCertificate := ⟨⟨retention3550,(566877307631922261/250000000000000000),(106411689904918233/500000000000000000),(1693583516892780107/100000000000000000),(909423140879630589347/1000000000000000000),(12046786383905637/12500000000000000)⟩,(998026322101139937/1000000000000000000),(379280790017778121/1000000000000000000),(253012151842112213/1000000000000000000),(117435053501455837/500000000000000000)⟩
theorem valid3550 : certificate3550.Valid := by decide +kernel
theorem sound3550 : certificate3550.Sound := rat_cut_bin_certificate_sound certificate3550 profilesValid3550 numericValid3550 valid3550

def retention3551 : RatCutRetentionCertificate := ⟨(127/2000),(8/125),(12341941775547813027/26764961125307303143),(4428758446641500551/500000000000000000),1,(299175378630606542971164269262433909/285726351396225842000000000000000000),false,MergedCutProfiles.Batch546.profile21863,(fun _ => MergedCutProfiles.Batch546.profile21863)⟩
theorem profilesValid3551 : retention3551.ProfilesValid := by
  exact MergedCutProfiles.Batch546.valid21863
theorem numericValid3551 : retention3551.NumericValid := by decide +kernel
def certificate3551 : RatCutBinCertificate := ⟨⟨retention3551,(578746279881922261/250000000000000000),(106411689904918233/500000000000000000),(1693583516892780107/100000000000000000),(909423140879630589347/1000000000000000000),(1017977686842824581/1000000000000000000)⟩,(997984976315110531/1000000000000000000),(29325637092869191/250000000000000000),(157276873494089711/250000000000000000),(114633488401595649/200000000000000000)⟩
theorem valid3551 : certificate3551.Valid := by decide +kernel
theorem sound3551 : certificate3551.Sound := rat_cut_bin_certificate_sound certificate3551 profilesValid3551 numericValid3551 valid3551

def certificates : List RatCutBinCertificate := [certificate3540,certificate3541,certificate3542,certificate3543,certificate3544,certificate3545,certificate3546,certificate3547,certificate3548,certificate3549,certificate3550,certificate3551]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3540,List.forall_mem_cons.mpr ⟨sound3541,List.forall_mem_cons.mpr ⟨sound3542,List.forall_mem_cons.mpr ⟨sound3543,List.forall_mem_cons.mpr ⟨sound3544,List.forall_mem_cons.mpr ⟨sound3545,List.forall_mem_cons.mpr ⟨sound3546,List.forall_mem_cons.mpr ⟨sound3547,List.forall_mem_cons.mpr ⟨sound3548,List.forall_mem_cons.mpr ⟨sound3549,List.forall_mem_cons.mpr ⟨sound3550,List.forall_mem_cons.mpr ⟨sound3551,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch295
