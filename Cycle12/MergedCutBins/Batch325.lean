import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch040
import Cycle12.MergedCutProfiles.Batch041
import Cycle12.MergedCutProfiles.Batch042
import Cycle12.MergedCutProfiles.Batch043
import Cycle12.MergedCutProfiles.Batch044
import Cycle12.MergedCutProfiles.Batch330
import Cycle12.MergedCutProfiles.Batch331
import Cycle12.MergedCutProfiles.Batch332
import Cycle12.MergedCutProfiles.Batch333
import Cycle12.MergedCutProfiles.Batch462
import Cycle12.MergedCutProfiles.Batch463
import Cycle12.MergedCutProfiles.Batch593
import Cycle12.MergedCutProfiles.Batch594
import Cycle12.MergedCutProfiles.Batch595

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch325

def retention3900 : RatCutRetentionCertificate := ⟨(7/250),(29/1000),(1358367843764406437/634762562001393096337),(1195931403/1000000000),(53/20),(77949169684391533797834105994510319/33220316750000000000000000000000000),true,MergedCutProfiles.Batch593.profile23759,![MergedCutProfiles.Batch593.profile23759,MergedCutProfiles.Batch593.profile23748,MergedCutProfiles.Batch593.profile23751,MergedCutProfiles.Batch593.profile23755,MergedCutProfiles.Batch593.profile23757,MergedCutProfiles.Batch593.profile23758,MergedCutProfiles.Batch330.profile13233,MergedCutProfiles.Batch462.profile18509,MergedCutProfiles.Batch594.profile23760,MergedCutProfiles.Batch331.profile13253,MergedCutProfiles.Batch594.profile23761,MergedCutProfiles.Batch462.profile18501,MergedCutProfiles.Batch462.profile18502,MergedCutProfiles.Batch462.profile18503,MergedCutProfiles.Batch331.profile13254,MergedCutProfiles.Batch040.profile1626]⟩
theorem profilesValid3900 : retention3900.ProfilesValid := by
  change ∀ j : Fin 16, (retention3900.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch593.valid23759
  · exact MergedCutProfiles.Batch593.valid23748
  · exact MergedCutProfiles.Batch593.valid23751
  · exact MergedCutProfiles.Batch593.valid23755
  · exact MergedCutProfiles.Batch593.valid23757
  · exact MergedCutProfiles.Batch593.valid23758
  · exact MergedCutProfiles.Batch330.valid13233
  · exact MergedCutProfiles.Batch462.valid18509
  · exact MergedCutProfiles.Batch594.valid23760
  · exact MergedCutProfiles.Batch331.valid13253
  · exact MergedCutProfiles.Batch594.valid23761
  · exact MergedCutProfiles.Batch462.valid18501
  · exact MergedCutProfiles.Batch462.valid18502
  · exact MergedCutProfiles.Batch462.valid18503
  · exact MergedCutProfiles.Batch331.valid13254
  · exact MergedCutProfiles.Batch040.valid1626
theorem numericValid3900 : retention3900.NumericValid := by decide +kernel
def certificate3900 : RatCutBinCertificate := ⟨⟨retention3900,(916543144554320903/500000000000000000),(36585906920747501/1000000000000000000),(9525037074279240427/1000000000000000000),(12153077954679282224127/1000000000000000000),(2327772174178631017/1000000000000000000)⟩,(999854290072363393/1000000000000000000),(107670680491601173/250000000000000000),(12907293442428741/62500000000000000),(7100671797905873/50000000000000000)⟩
theorem valid3900 : certificate3900.Valid := by decide +kernel
theorem sound3900 : certificate3900.Sound := rat_cut_bin_certificate_sound certificate3900 profilesValid3900 numericValid3900 valid3900

def retention3901 : RatCutRetentionCertificate := ⟨(7/250),(29/1000),(32000000000000000000/634762562001393096337),(1358367843764406437/500000000000000000),(31/20),(1309799596144019172413/640000000000000000000),true,MergedCutProfiles.Batch041.profile1657,![MergedCutProfiles.Batch041.profile1657,MergedCutProfiles.Batch594.profile23762,MergedCutProfiles.Batch041.profile1676,MergedCutProfiles.Batch594.profile23763,MergedCutProfiles.Batch594.profile23764,MergedCutProfiles.Batch594.profile23765,MergedCutProfiles.Batch594.profile23766,MergedCutProfiles.Batch594.profile23767,MergedCutProfiles.Batch594.profile23768,MergedCutProfiles.Batch594.profile23769,MergedCutProfiles.Batch594.profile23770,MergedCutProfiles.Batch594.profile23771,MergedCutProfiles.Batch594.profile23772,MergedCutProfiles.Batch594.profile23773,MergedCutProfiles.Batch331.profile13276,MergedCutProfiles.Batch594.profile23774]⟩
theorem profilesValid3901 : retention3901.ProfilesValid := by
  change ∀ j : Fin 16, (retention3901.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch041.valid1657
  · exact MergedCutProfiles.Batch594.valid23762
  · exact MergedCutProfiles.Batch041.valid1676
  · exact MergedCutProfiles.Batch594.valid23763
  · exact MergedCutProfiles.Batch594.valid23764
  · exact MergedCutProfiles.Batch594.valid23765
  · exact MergedCutProfiles.Batch594.valid23766
  · exact MergedCutProfiles.Batch594.valid23767
  · exact MergedCutProfiles.Batch594.valid23768
  · exact MergedCutProfiles.Batch594.valid23769
  · exact MergedCutProfiles.Batch594.valid23770
  · exact MergedCutProfiles.Batch594.valid23771
  · exact MergedCutProfiles.Batch594.valid23772
  · exact MergedCutProfiles.Batch594.valid23773
  · exact MergedCutProfiles.Batch331.valid13276
  · exact MergedCutProfiles.Batch594.valid23774
theorem numericValid3901 : retention3901.NumericValid := by decide +kernel
def certificate3901 : RatCutBinCertificate := ⟨⟨retention3901,(916543144554320903/500000000000000000),(36585906920747501/1000000000000000000),(9525037074279240427/1000000000000000000),(12153077954679282224127/1000000000000000000),(1017824209424477489/500000000000000000)⟩,(999854290072363393/1000000000000000000),(353550873547028711/1000000000000000000),(139423584108864083/500000000000000000),(55821582480462751/200000000000000000)⟩
theorem valid3901 : certificate3901.Valid := by decide +kernel
theorem sound3901 : certificate3901.Sound := rat_cut_bin_certificate_sound certificate3901 profilesValid3901 numericValid3901 valid3901

def retention3902 : RatCutRetentionCertificate := ⟨(7/250),(29/1000),(1/2),64,1,(255375334696131669987701620024329127359/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch042.profile1701,(fun _ => MergedCutProfiles.Batch042.profile1701)⟩
theorem profilesValid3902 : retention3902.ProfilesValid := by
  exact MergedCutProfiles.Batch042.valid1701
theorem numericValid3902 : retention3902.NumericValid := by decide +kernel
def certificate3902 : RatCutBinCertificate := ⟨⟨retention3902,(916543144554320903/500000000000000000),(36585906920747501/1000000000000000000),(9525037074279240427/1000000000000000000),(12153077954679282224127/1000000000000000000),(990518970293962203/1000000000000000000)⟩,(999854290072363393/1000000000000000000),(511587750474407789/1000000000000000000),(72763805133237589/500000000000000000),(141930034596135027/1000000000000000000)⟩
theorem valid3902 : certificate3902.Valid := by decide +kernel
theorem sound3902 : certificate3902.Sound := rat_cut_bin_certificate_sound certificate3902 profilesValid3902 numericValid3902 valid3902

def retention3903 : RatCutRetentionCertificate := ⟨(7/250),(29/1000),(32000000000000000000/634762562001393096337),(5264505017135815123/250000000000000000),1,(170252684193842898888967604019813695367/84232080274173041968000000000000000000),false,MergedCutProfiles.Batch594.profile23775,(fun _ => MergedCutProfiles.Batch594.profile23775)⟩
theorem profilesValid3903 : retention3903.ProfilesValid := by
  exact MergedCutProfiles.Batch594.valid23775
theorem numericValid3903 : retention3903.NumericValid := by decide +kernel
def certificate3903 : RatCutBinCertificate := ⟨⟨retention3903,(901411817054320903/500000000000000000),(36585906920747501/1000000000000000000),(9525037074279240427/1000000000000000000),(12153077954679282224127/1000000000000000000),(201430859165950583/100000000000000000)⟩,(124982086953529753/125000000000000000),(1594402172645149/50000000000000000),(838784138370526483/1000000000000000000),(1541837036406469173/1000000000000000000)⟩
theorem valid3903 : certificate3903.Valid := by decide +kernel
theorem sound3903 : certificate3903.Sound := rat_cut_bin_certificate_sound certificate3903 profilesValid3903 numericValid3903 valid3903

def retention3904 : RatCutRetentionCertificate := ⟨(7/250),(29/1000),(1/2),64,1,(255375334696131669987701620024329127359/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch042.profile1701,(fun _ => MergedCutProfiles.Batch042.profile1701)⟩
theorem profilesValid3904 : retention3904.ProfilesValid := by
  exact MergedCutProfiles.Batch042.valid1701
theorem numericValid3904 : retention3904.NumericValid := by decide +kernel
def certificate3904 : RatCutBinCertificate := ⟨⟨retention3904,(901411817054320903/500000000000000000),(36585906920747501/1000000000000000000),(9525037074279240427/1000000000000000000),(12153077954679282224127/1000000000000000000),(495317604959137747/500000000000000000)⟩,(124982086953529753/125000000000000000),(64839568849660723/1000000000000000000),(749707155417172577/1000000000000000000),(182814991234648031/250000000000000000)⟩
theorem valid3904 : certificate3904.Valid := by decide +kernel
theorem sound3904 : certificate3904.Sound := rat_cut_bin_certificate_sound certificate3904 profilesValid3904 numericValid3904 valid3904

def retention3905 : RatCutRetentionCertificate := ⟨(29/1000),(3/100),(587517687254646157/1180330131266070829961),(69875365035608587/125000000000000000),4,(38940423973802452640741484819642347/17888093449115798272000000000000000),true,MergedCutProfiles.Batch594.profile23776,![MergedCutProfiles.Batch594.profile23776,MergedCutProfiles.Batch594.profile23777,MergedCutProfiles.Batch594.profile23778,MergedCutProfiles.Batch594.profile23779,MergedCutProfiles.Batch594.profile23780,MergedCutProfiles.Batch594.profile23781,MergedCutProfiles.Batch594.profile23782,MergedCutProfiles.Batch463.profile18528,MergedCutProfiles.Batch462.profile18518,MergedCutProfiles.Batch594.profile23783,MergedCutProfiles.Batch594.profile23784,MergedCutProfiles.Batch332.profile13285,MergedCutProfiles.Batch462.profile18519,MergedCutProfiles.Batch594.profile23785,MergedCutProfiles.Batch594.profile23786,MergedCutProfiles.Batch332.profile13295]⟩
theorem profilesValid3905 : retention3905.ProfilesValid := by
  change ∀ j : Fin 16, (retention3905.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch594.valid23776
  · exact MergedCutProfiles.Batch594.valid23777
  · exact MergedCutProfiles.Batch594.valid23778
  · exact MergedCutProfiles.Batch594.valid23779
  · exact MergedCutProfiles.Batch594.valid23780
  · exact MergedCutProfiles.Batch594.valid23781
  · exact MergedCutProfiles.Batch594.valid23782
  · exact MergedCutProfiles.Batch463.valid18528
  · exact MergedCutProfiles.Batch462.valid18518
  · exact MergedCutProfiles.Batch594.valid23783
  · exact MergedCutProfiles.Batch594.valid23784
  · exact MergedCutProfiles.Batch332.valid13285
  · exact MergedCutProfiles.Batch462.valid18519
  · exact MergedCutProfiles.Batch594.valid23785
  · exact MergedCutProfiles.Batch594.valid23786
  · exact MergedCutProfiles.Batch332.valid13295
theorem numericValid3905 : retention3905.NumericValid := by decide +kernel
def certificate3905 : RatCutBinCertificate := ⟨⟨retention3905,(28683414056223401/15625000000000000),(39310593322721927/1000000000000000000),(4829725624378704307/500000000000000000),(11459013770357306654367/1000000000000000000),(42940147582205503/20000000000000000)⟩,(999845659779460397/1000000000000000000),(184586739898751233/250000000000000000),(37681817912694249/1000000000000000000),(8153712424325713/500000000000000000)⟩
theorem valid3905 : certificate3905.Valid := by decide +kernel
theorem sound3905 : certificate3905.Sound := rat_cut_bin_certificate_sound certificate3905 profilesValid3905 numericValid3905 valid3905

def retention3906 : RatCutRetentionCertificate := ⟨(29/1000),(3/100),(1201763439000000000/1180330131266070829961),(587517687254646157/1000000000000000000),4,(41023350517850073614562546295303053/18359927726707692406250000000000000),true,MergedCutProfiles.Batch594.profile23777,![MergedCutProfiles.Batch594.profile23777,MergedCutProfiles.Batch594.profile23787,MergedCutProfiles.Batch594.profile23788,MergedCutProfiles.Batch463.profile18528,MergedCutProfiles.Batch594.profile23783,MergedCutProfiles.Batch594.profile23789,MergedCutProfiles.Batch594.profile23790,MergedCutProfiles.Batch594.profile23791,MergedCutProfiles.Batch594.profile23792,MergedCutProfiles.Batch594.profile23793,MergedCutProfiles.Batch594.profile23794,MergedCutProfiles.Batch042.profile1704,MergedCutProfiles.Batch463.profile18522,MergedCutProfiles.Batch594.profile23795,MergedCutProfiles.Batch332.profile13296,MergedCutProfiles.Batch594.profile23796]⟩
theorem profilesValid3906 : retention3906.ProfilesValid := by
  change ∀ j : Fin 16, (retention3906.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch594.valid23777
  · exact MergedCutProfiles.Batch594.valid23787
  · exact MergedCutProfiles.Batch594.valid23788
  · exact MergedCutProfiles.Batch463.valid18528
  · exact MergedCutProfiles.Batch594.valid23783
  · exact MergedCutProfiles.Batch594.valid23789
  · exact MergedCutProfiles.Batch594.valid23790
  · exact MergedCutProfiles.Batch594.valid23791
  · exact MergedCutProfiles.Batch594.valid23792
  · exact MergedCutProfiles.Batch594.valid23793
  · exact MergedCutProfiles.Batch594.valid23794
  · exact MergedCutProfiles.Batch042.valid1704
  · exact MergedCutProfiles.Batch463.valid18522
  · exact MergedCutProfiles.Batch594.valid23795
  · exact MergedCutProfiles.Batch332.valid13296
  · exact MergedCutProfiles.Batch594.valid23796
theorem numericValid3906 : retention3906.NumericValid := by decide +kernel
def certificate3906 : RatCutBinCertificate := ⟨⟨retention3906,(28683414056223401/15625000000000000),(39310593322721927/1000000000000000000),(4829725624378704307/500000000000000000),(11459013770357306654367/1000000000000000000),(17636102212834657/8000000000000000)⟩,(999845659779460397/1000000000000000000),(695209072279929257/1000000000000000000),(406662309640763/7812500000000000),(5808437803455409/250000000000000000)⟩
theorem valid3906 : certificate3906.Valid := by decide +kernel
theorem sound3906 : certificate3906.Sound := rat_cut_bin_certificate_sound certificate3906 profilesValid3906 numericValid3906 valid3906

def retention3907 : RatCutRetentionCertificate := ⟨(29/1000),(3/100),(534193290751133778/168618590180867261423),(1201763439/1000000000),(53/20),(9340120891316540231/4000000000000000000),true,MergedCutProfiles.Batch594.profile23788,![MergedCutProfiles.Batch594.profile23788,MergedCutProfiles.Batch594.profile23789,MergedCutProfiles.Batch594.profile23792,MergedCutProfiles.Batch594.profile23797,MergedCutProfiles.Batch463.profile18529,MergedCutProfiles.Batch332.profile13307,MergedCutProfiles.Batch463.profile18524,MergedCutProfiles.Batch594.profile23798,MergedCutProfiles.Batch332.profile13308,MergedCutProfiles.Batch463.profile18531,MergedCutProfiles.Batch043.profile1736,MergedCutProfiles.Batch594.profile23799,MergedCutProfiles.Batch595.profile23800,MergedCutProfiles.Batch043.profile1722,MergedCutProfiles.Batch332.profile13290,MergedCutProfiles.Batch595.profile23801]⟩
theorem profilesValid3907 : retention3907.ProfilesValid := by
  change ∀ j : Fin 16, (retention3907.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch594.valid23788
  · exact MergedCutProfiles.Batch594.valid23789
  · exact MergedCutProfiles.Batch594.valid23792
  · exact MergedCutProfiles.Batch594.valid23797
  · exact MergedCutProfiles.Batch463.valid18529
  · exact MergedCutProfiles.Batch332.valid13307
  · exact MergedCutProfiles.Batch463.valid18524
  · exact MergedCutProfiles.Batch594.valid23798
  · exact MergedCutProfiles.Batch332.valid13308
  · exact MergedCutProfiles.Batch463.valid18531
  · exact MergedCutProfiles.Batch043.valid1736
  · exact MergedCutProfiles.Batch594.valid23799
  · exact MergedCutProfiles.Batch595.valid23800
  · exact MergedCutProfiles.Batch043.valid1722
  · exact MergedCutProfiles.Batch332.valid13290
  · exact MergedCutProfiles.Batch595.valid23801
theorem numericValid3907 : retention3907.NumericValid := by decide +kernel
def certificate3907 : RatCutBinCertificate := ⟨⟨retention3907,(28683414056223401/15625000000000000),(39310593322721927/1000000000000000000),(4829725624378704307/500000000000000000),(11459013770357306654367/1000000000000000000),(72351016961301177/31250000000000000)⟩,(999845659779460397/1000000000000000000),(217074086483520411/500000000000000000),(50902853786342647/250000000000000000),(69784656440696799/500000000000000000)⟩
theorem valid3907 : certificate3907.Valid := by decide +kernel
theorem sound3907 : certificate3907.Sound := rat_cut_bin_certificate_sound certificate3907 profilesValid3907 numericValid3907 valid3907

def retention3908 : RatCutRetentionCertificate := ⟨(29/1000),(3/100),(64000000000000000000/1180330131266070829961),(1869676517628968223/500000000000000000),(27/20),(1296527515052994186759/640000000000000000000),true,MergedCutProfiles.Batch332.profile13299,![MergedCutProfiles.Batch332.profile13299,MergedCutProfiles.Batch595.profile23802,MergedCutProfiles.Batch043.profile1729,MergedCutProfiles.Batch595.profile23803,MergedCutProfiles.Batch595.profile23804,MergedCutProfiles.Batch333.profile13333,MergedCutProfiles.Batch595.profile23805,MergedCutProfiles.Batch595.profile23806,MergedCutProfiles.Batch595.profile23807,MergedCutProfiles.Batch595.profile23808,MergedCutProfiles.Batch595.profile23809,MergedCutProfiles.Batch595.profile23810,MergedCutProfiles.Batch595.profile23811,MergedCutProfiles.Batch595.profile23812,MergedCutProfiles.Batch595.profile23813,MergedCutProfiles.Batch595.profile23814]⟩
theorem profilesValid3908 : retention3908.ProfilesValid := by
  change ∀ j : Fin 16, (retention3908.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch332.valid13299
  · exact MergedCutProfiles.Batch595.valid23802
  · exact MergedCutProfiles.Batch043.valid1729
  · exact MergedCutProfiles.Batch595.valid23803
  · exact MergedCutProfiles.Batch595.valid23804
  · exact MergedCutProfiles.Batch333.valid13333
  · exact MergedCutProfiles.Batch595.valid23805
  · exact MergedCutProfiles.Batch595.valid23806
  · exact MergedCutProfiles.Batch595.valid23807
  · exact MergedCutProfiles.Batch595.valid23808
  · exact MergedCutProfiles.Batch595.valid23809
  · exact MergedCutProfiles.Batch595.valid23810
  · exact MergedCutProfiles.Batch595.valid23811
  · exact MergedCutProfiles.Batch595.valid23812
  · exact MergedCutProfiles.Batch595.valid23813
  · exact MergedCutProfiles.Batch595.valid23814
theorem numericValid3908 : retention3908.NumericValid := by decide +kernel
def certificate3908 : RatCutBinCertificate := ⟨⟨retention3908,(28683414056223401/15625000000000000),(39310593322721927/1000000000000000000),(4829725624378704307/500000000000000000),(11459013770357306654367/1000000000000000000),(1007869317840139423/500000000000000000)⟩,(999845659779460397/1000000000000000000),(328810865179102023/1000000000000000000),(76362828512684543/250000000000000000),(87978754006654879/250000000000000000)⟩
theorem valid3908 : certificate3908.Valid := by decide +kernel
theorem sound3908 : certificate3908.Sound := rat_cut_bin_certificate_sound certificate3908 profilesValid3908 numericValid3908 valid3908

def retention3909 : RatCutRetentionCertificate := ⟨(29/1000),(3/100),(1/2),64,1,(255375917609544558015305480512676517159/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch044.profile1794,(fun _ => MergedCutProfiles.Batch044.profile1794)⟩
theorem profilesValid3909 : retention3909.ProfilesValid := by
  exact MergedCutProfiles.Batch044.valid1794
theorem numericValid3909 : retention3909.NumericValid := by decide +kernel
def certificate3909 : RatCutBinCertificate := ⟨⟨retention3909,(28683414056223401/15625000000000000),(39310593322721927/1000000000000000000),(4829725624378704307/500000000000000000),(11459013770357306654367/1000000000000000000),(990091363142434237/1000000000000000000)⟩,(999845659779460397/1000000000000000000),(25762005407548751/50000000000000000),(35773169731808417/250000000000000000),(139494753097950621/1000000000000000000)⟩
theorem valid3909 : certificate3909.Valid := by decide +kernel
theorem sound3909 : certificate3909.Sound := rat_cut_bin_certificate_sound certificate3909 profilesValid3909 numericValid3909 valid3909

def retention3910 : RatCutRetentionCertificate := ⟨(29/1000),(3/100),(64000000000000000000/1180330131266070829961),(2133169366800988407/100000000000000000),1,(669448399346390538836797579483913441/333307713562654438593750000000000000),false,MergedCutProfiles.Batch595.profile23815,(fun _ => MergedCutProfiles.Batch595.profile23815)⟩
theorem profilesValid3910 : retention3910.ProfilesValid := by
  exact MergedCutProfiles.Batch595.valid23815
theorem numericValid3910 : retention3910.NumericValid := by decide +kernel
def certificate3910 : RatCutBinCertificate := ⟨⟨retention3910,(28201755571848401/15625000000000000),(39310593322721927/1000000000000000000),(4829725624378704307/500000000000000000),(11459013770357306654367/1000000000000000000),(2001154205770620953/1000000000000000000)⟩,(999848251510868367/1000000000000000000),(3186499966999403/100000000000000000),(25599692027483/30517578125000),(1534458769373502119/1000000000000000000)⟩
theorem valid3910 : certificate3910.Valid := by decide +kernel
theorem sound3910 : certificate3910.Sound := rat_cut_bin_certificate_sound certificate3910 profilesValid3910 numericValid3910 valid3910

def retention3911 : RatCutRetentionCertificate := ⟨(29/1000),(3/100),(1/2),64,1,(255375917609544558015305480512676517159/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch044.profile1794,(fun _ => MergedCutProfiles.Batch044.profile1794)⟩
theorem profilesValid3911 : retention3911.ProfilesValid := by
  exact MergedCutProfiles.Batch044.valid1794
theorem numericValid3911 : retention3911.NumericValid := by decide +kernel
def certificate3911 : RatCutBinCertificate := ⟨⟨retention3911,(28201755571848401/15625000000000000),(39310593322721927/1000000000000000000),(4829725624378704307/500000000000000000),(11459013770357306654367/1000000000000000000),(990216814786107241/1000000000000000000)⟩,(999848251510868367/1000000000000000000),(2012399492790059/31250000000000000),(375414271793646027/500000000000000000),(732042919997256969/1000000000000000000)⟩
theorem valid3911 : certificate3911.Valid := by decide +kernel
theorem sound3911 : certificate3911.Sound := rat_cut_bin_certificate_sound certificate3911 profilesValid3911 numericValid3911 valid3911

def certificates : List RatCutBinCertificate := [certificate3900,certificate3901,certificate3902,certificate3903,certificate3904,certificate3905,certificate3906,certificate3907,certificate3908,certificate3909,certificate3910,certificate3911]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3900,List.forall_mem_cons.mpr ⟨sound3901,List.forall_mem_cons.mpr ⟨sound3902,List.forall_mem_cons.mpr ⟨sound3903,List.forall_mem_cons.mpr ⟨sound3904,List.forall_mem_cons.mpr ⟨sound3905,List.forall_mem_cons.mpr ⟨sound3906,List.forall_mem_cons.mpr ⟨sound3907,List.forall_mem_cons.mpr ⟨sound3908,List.forall_mem_cons.mpr ⟨sound3909,List.forall_mem_cons.mpr ⟨sound3910,List.forall_mem_cons.mpr ⟨sound3911,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch325
