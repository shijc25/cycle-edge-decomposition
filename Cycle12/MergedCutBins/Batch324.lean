import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch038
import Cycle12.MergedCutProfiles.Batch039
import Cycle12.MergedCutProfiles.Batch040
import Cycle12.MergedCutProfiles.Batch329
import Cycle12.MergedCutProfiles.Batch330
import Cycle12.MergedCutProfiles.Batch461
import Cycle12.MergedCutProfiles.Batch462
import Cycle12.MergedCutProfiles.Batch592
import Cycle12.MergedCutProfiles.Batch593

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch324

def retention3888 : RatCutRetentionCertificate := ⟨(13/500),(27/1000),(1/2),64,1,(15960890419747252013481485060871619639/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch038.profile1543,(fun _ => MergedCutProfiles.Batch038.profile1543)⟩
theorem profilesValid3888 : retention3888.ProfilesValid := by
  exact MergedCutProfiles.Batch038.valid1543
theorem numericValid3888 : retention3888.NumericValid := by decide +kernel
def certificate3888 : RatCutBinCertificate := ⟨⟨retention3888,(365552146933234921/200000000000000000),(31463473579235007/1000000000000000000),(231617078966041587/25000000000000000),(13773261092007900957361/1000000000000000000),(39653938211987111/40000000000000000)⟩,(39994846106634309/40000000000000000),(100862693584877927/200000000000000000),(37613762719612811/250000000000000000),(146859170340486349/1000000000000000000)⟩
theorem valid3888 : certificate3888.Valid := by decide +kernel
theorem sound3888 : certificate3888.Sound := rat_cut_bin_certificate_sound certificate3888 profilesValid3888 numericValid3888 valid3888

def retention3889 : RatCutRetentionCertificate := ⟨(13/500),(27/1000),(16000000000000000000/369822667834612896403),(128305231017609091/6250000000000000),1,(6720751803082922718592227742737260727/3284613914050792729600000000000000000),false,MergedCutProfiles.Batch592.profile23706,(fun _ => MergedCutProfiles.Batch592.profile23706)⟩
theorem profilesValid3889 : retention3889.ProfilesValid := by
  exact MergedCutProfiles.Batch592.valid23706
theorem numericValid3889 : retention3889.NumericValid := by decide +kernel
def certificate3889 : RatCutBinCertificate := ⟨⟨retention3889,(359705048733234921/200000000000000000),(31463473579235007/1000000000000000000),(231617078966041587/25000000000000000),(13773261092007900957361/1000000000000000000),(1020011765433250317/500000000000000000)⟩,(999873213619078711/1000000000000000000),(3193519945959671/100000000000000000),(167729586363433277/200000000000000000),(1556012435117648467/1000000000000000000)⟩
theorem valid3889 : certificate3889.Valid := by decide +kernel
theorem sound3889 : certificate3889.Sound := rat_cut_bin_certificate_sound certificate3889 profilesValid3889 numericValid3889 valid3889

def retention3890 : RatCutRetentionCertificate := ⟨(13/500),(27/1000),(1/2),64,1,(15960890419747252013481485060871619639/16000000000000000000000000000000000000),false,MergedCutProfiles.Batch038.profile1543,(fun _ => MergedCutProfiles.Batch038.profile1543)⟩
theorem profilesValid3890 : retention3890.ProfilesValid := by
  exact MergedCutProfiles.Batch038.valid1543
theorem numericValid3890 : retention3890.NumericValid := by decide +kernel
def certificate3890 : RatCutBinCertificate := ⟨⟨retention3890,(359705048733234921/200000000000000000),(31463473579235007/1000000000000000000),(231617078966041587/25000000000000000),(13773261092007900957361/1000000000000000000),(991447740954215157/1000000000000000000)⟩,(999873213619078711/1000000000000000000),(32855265925458893/500000000000000000),(93438370433050867/125000000000000000),(29188599502672331/40000000000000000)⟩
theorem valid3890 : certificate3890.Valid := by decide +kernel
theorem sound3890 : certificate3890.Sound := rat_cut_bin_certificate_sound certificate3890 profilesValid3890 numericValid3890 valid3890

def retention3891 : RatCutRetentionCertificate := ⟨(27/1000),(7/250),(586322952147341080/1368672502240183129861),(557866170824488749/1000000000000000000),4,(7579229896193588314456274728295093/3486663567653054681250000000000000),true,MergedCutProfiles.Batch592.profile23707,![MergedCutProfiles.Batch592.profile23707,MergedCutProfiles.Batch592.profile23708,MergedCutProfiles.Batch592.profile23709,MergedCutProfiles.Batch461.profile18457,MergedCutProfiles.Batch592.profile23710,MergedCutProfiles.Batch592.profile23711,MergedCutProfiles.Batch592.profile23712,MergedCutProfiles.Batch592.profile23713,MergedCutProfiles.Batch461.profile18458,MergedCutProfiles.Batch592.profile23714,MergedCutProfiles.Batch592.profile23715,MergedCutProfiles.Batch329.profile13161,MergedCutProfiles.Batch592.profile23716,MergedCutProfiles.Batch592.profile23717,MergedCutProfiles.Batch592.profile23718,MergedCutProfiles.Batch329.profile13177]⟩
theorem profilesValid3891 : retention3891.ProfilesValid := by
  change ∀ j : Fin 16, (retention3891.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch592.valid23707
  · exact MergedCutProfiles.Batch592.valid23708
  · exact MergedCutProfiles.Batch592.valid23709
  · exact MergedCutProfiles.Batch461.valid18457
  · exact MergedCutProfiles.Batch592.valid23710
  · exact MergedCutProfiles.Batch592.valid23711
  · exact MergedCutProfiles.Batch592.valid23712
  · exact MergedCutProfiles.Batch592.valid23713
  · exact MergedCutProfiles.Batch461.valid18458
  · exact MergedCutProfiles.Batch592.valid23714
  · exact MergedCutProfiles.Batch592.valid23715
  · exact MergedCutProfiles.Batch329.valid13161
  · exact MergedCutProfiles.Batch592.valid23716
  · exact MergedCutProfiles.Batch592.valid23717
  · exact MergedCutProfiles.Batch592.valid23718
  · exact MergedCutProfiles.Batch329.valid13177
theorem numericValid3891 : retention3891.NumericValid := by decide +kernel
def certificate3891 : RatCutBinCertificate := ⟨⟨retention3891,(1830426513975396411/1000000000000000000),(1358828718451041/40000000000000000),(2348368674732809949/250000000000000000),(1615106879914194358303/125000000000000000),(536824716577718227/250000000000000000)⟩,(99986279214203883/100000000000000000),(36633830804153259/50000000000000000),(39423697475335739/1000000000000000000),(8528374068371647/500000000000000000)⟩
theorem valid3891 : certificate3891.Valid := by decide +kernel
theorem sound3891 : certificate3891.Sound := rat_cut_bin_certificate_sound certificate3891 profilesValid3891 numericValid3891 valid3891

def retention3892 : RatCutRetentionCertificate := ⟨(27/1000),(7/250),(1194963470000000000/1368672502240183129861),(14658073803683527/25000000000000000),4,(20451196548739409401646234956350651/9161296127302204375000000000000000),true,MergedCutProfiles.Batch592.profile23719,![MergedCutProfiles.Batch592.profile23719,MergedCutProfiles.Batch461.profile18457,MergedCutProfiles.Batch593.profile23720,MergedCutProfiles.Batch461.profile18470,MergedCutProfiles.Batch592.profile23714,MergedCutProfiles.Batch461.profile18459,MergedCutProfiles.Batch593.profile23721,MergedCutProfiles.Batch329.profile13177,MergedCutProfiles.Batch593.profile23722,MergedCutProfiles.Batch329.profile13189,MergedCutProfiles.Batch593.profile23723,MergedCutProfiles.Batch038.profile1546,MergedCutProfiles.Batch329.profile13198,MergedCutProfiles.Batch593.profile23724,MergedCutProfiles.Batch461.profile18463,MergedCutProfiles.Batch461.profile18471]⟩
theorem profilesValid3892 : retention3892.ProfilesValid := by
  change ∀ j : Fin 16, (retention3892.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch592.valid23719
  · exact MergedCutProfiles.Batch461.valid18457
  · exact MergedCutProfiles.Batch593.valid23720
  · exact MergedCutProfiles.Batch461.valid18470
  · exact MergedCutProfiles.Batch592.valid23714
  · exact MergedCutProfiles.Batch461.valid18459
  · exact MergedCutProfiles.Batch593.valid23721
  · exact MergedCutProfiles.Batch329.valid13177
  · exact MergedCutProfiles.Batch593.valid23722
  · exact MergedCutProfiles.Batch329.valid13189
  · exact MergedCutProfiles.Batch593.valid23723
  · exact MergedCutProfiles.Batch038.valid1546
  · exact MergedCutProfiles.Batch329.valid13198
  · exact MergedCutProfiles.Batch593.valid23724
  · exact MergedCutProfiles.Batch461.valid18463
  · exact MergedCutProfiles.Batch461.valid18471
theorem numericValid3892 : retention3892.NumericValid := by decide +kernel
def certificate3892 : RatCutBinCertificate := ⟨⟨retention3892,(1830426513975396411/1000000000000000000),(1358828718451041/40000000000000000),(2348368674732809949/250000000000000000),(1615106879914194358303/125000000000000000),(551467283875513019/250000000000000000)⟩,(99986279214203883/100000000000000000),(344737265689468271/500000000000000000),(5416124228530671/100000000000000000),(4835610164932331/200000000000000000)⟩
theorem valid3892 : certificate3892.Valid := by decide +kernel
theorem sound3892 : certificate3892.Sound := rat_cut_bin_certificate_sound certificate3892 profilesValid3892 numericValid3892 valid3892

def retention3893 : RatCutRetentionCertificate := ⟨(27/1000),(7/250),(2137546086600893451/1368672502240183129861),(119496347/100000000),(53/20),(703171352613537039846450432952900119/298740867500000000000000000000000000),true,MergedCutProfiles.Batch593.profile23725,![MergedCutProfiles.Batch593.profile23725,MergedCutProfiles.Batch592.profile23712,MergedCutProfiles.Batch592.profile23715,MergedCutProfiles.Batch593.profile23721,MergedCutProfiles.Batch593.profile23722,MergedCutProfiles.Batch461.profile18461,MergedCutProfiles.Batch461.profile18462,MergedCutProfiles.Batch039.profile1562,MergedCutProfiles.Batch461.profile18471,MergedCutProfiles.Batch593.profile23726,MergedCutProfiles.Batch461.profile18472,MergedCutProfiles.Batch593.profile23727,MergedCutProfiles.Batch329.profile13164,MergedCutProfiles.Batch461.profile18466,MergedCutProfiles.Batch593.profile23728,MergedCutProfiles.Batch329.profile13165]⟩
theorem profilesValid3893 : retention3893.ProfilesValid := by
  change ∀ j : Fin 16, (retention3893.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch593.valid23725
  · exact MergedCutProfiles.Batch592.valid23712
  · exact MergedCutProfiles.Batch592.valid23715
  · exact MergedCutProfiles.Batch593.valid23721
  · exact MergedCutProfiles.Batch593.valid23722
  · exact MergedCutProfiles.Batch461.valid18461
  · exact MergedCutProfiles.Batch461.valid18462
  · exact MergedCutProfiles.Batch039.valid1562
  · exact MergedCutProfiles.Batch461.valid18471
  · exact MergedCutProfiles.Batch593.valid23726
  · exact MergedCutProfiles.Batch461.valid18472
  · exact MergedCutProfiles.Batch593.valid23727
  · exact MergedCutProfiles.Batch329.valid13164
  · exact MergedCutProfiles.Batch461.valid18466
  · exact MergedCutProfiles.Batch593.valid23728
  · exact MergedCutProfiles.Batch329.valid13165
theorem numericValid3893 : retention3893.NumericValid := by decide +kernel
def certificate3893 : RatCutBinCertificate := ⟨⟨retention3893,(1830426513975396411/1000000000000000000),(1358828718451041/40000000000000000),(2348368674732809949/250000000000000000),(1615106879914194358303/125000000000000000),(1168120839508015227/500000000000000000)⟩,(99986279214203883/100000000000000000),(213552964686637941/500000000000000000),(209544558119933921/1000000000000000000),(144481708783366903/1000000000000000000)⟩
theorem valid3893 : certificate3893.Valid := by decide +kernel
theorem sound3893 : certificate3893.Sound := rat_cut_bin_certificate_sound certificate3893 profilesValid3893 numericValid3893 valid3893

def retention3894 : RatCutRetentionCertificate := ⟨(27/1000),(7/250),(64000000000000000000/1368672502240183129861),(2137546086600893451/1000000000000000000),(9/5),(2650674918234463936119/1280000000000000000000),true,MergedCutProfiles.Batch593.profile23729,![MergedCutProfiles.Batch593.profile23729,MergedCutProfiles.Batch038.profile1554,MergedCutProfiles.Batch039.profile1571,MergedCutProfiles.Batch593.profile23730,MergedCutProfiles.Batch593.profile23731,MergedCutProfiles.Batch593.profile23732,MergedCutProfiles.Batch040.profile1605,MergedCutProfiles.Batch593.profile23733,MergedCutProfiles.Batch593.profile23734,MergedCutProfiles.Batch593.profile23735,MergedCutProfiles.Batch593.profile23736,MergedCutProfiles.Batch593.profile23737,MergedCutProfiles.Batch593.profile23738,MergedCutProfiles.Batch040.profile1609,MergedCutProfiles.Batch593.profile23739,MergedCutProfiles.Batch593.profile23740]⟩
theorem profilesValid3894 : retention3894.ProfilesValid := by
  change ∀ j : Fin 16, (retention3894.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch593.valid23729
  · exact MergedCutProfiles.Batch038.valid1554
  · exact MergedCutProfiles.Batch039.valid1571
  · exact MergedCutProfiles.Batch593.valid23730
  · exact MergedCutProfiles.Batch593.valid23731
  · exact MergedCutProfiles.Batch593.valid23732
  · exact MergedCutProfiles.Batch040.valid1605
  · exact MergedCutProfiles.Batch593.valid23733
  · exact MergedCutProfiles.Batch593.valid23734
  · exact MergedCutProfiles.Batch593.valid23735
  · exact MergedCutProfiles.Batch593.valid23736
  · exact MergedCutProfiles.Batch593.valid23737
  · exact MergedCutProfiles.Batch593.valid23738
  · exact MergedCutProfiles.Batch040.valid1609
  · exact MergedCutProfiles.Batch593.valid23739
  · exact MergedCutProfiles.Batch593.valid23740
theorem numericValid3894 : retention3894.NumericValid := by decide +kernel
def certificate3894 : RatCutBinCertificate := ⟨⟨retention3894,(1830426513975396411/1000000000000000000),(1358828718451041/40000000000000000),(2348368674732809949/250000000000000000),(1615106879914194358303/125000000000000000),(1029462259494646039/500000000000000000)⟩,(99986279214203883/100000000000000000),(94178506296337497/250000000000000000),(7984658891018053/31250000000000000),(112626536644068823/500000000000000000)⟩
theorem valid3894 : certificate3894.Valid := by decide +kernel
theorem sound3894 : certificate3894.Sound := rat_cut_bin_certificate_sound certificate3894 profilesValid3894 numericValid3894 valid3894

def retention3895 : RatCutRetentionCertificate := ⟨(27/1000),(7/250),(1/2),64,1,(63843694446586541505180302875124093631/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch040.profile1621,(fun _ => MergedCutProfiles.Batch040.profile1621)⟩
theorem profilesValid3895 : retention3895.ProfilesValid := by
  exact MergedCutProfiles.Batch040.valid1621
theorem numericValid3895 : retention3895.NumericValid := by decide +kernel
def certificate3895 : RatCutBinCertificate := ⟨⟨retention3895,(1830426513975396411/1000000000000000000),(1358828718451041/40000000000000000),(2348368674732809949/250000000000000000),(1615106879914194358303/125000000000000000),(990938140600742961/1000000000000000000)⟩,(99986279214203883/100000000000000000),(507945738418166197/1000000000000000000),(73990804190846371/500000000000000000),(144384750976959833/1000000000000000000)⟩
theorem valid3895 : certificate3895.Valid := by decide +kernel
theorem sound3895 : certificate3895.Sound := rat_cut_bin_certificate_sound certificate3895 profilesValid3895 numericValid3895 valid3895

def retention3896 : RatCutRetentionCertificate := ⟨(27/1000),(7/250),(64000000000000000000/1368672502240183129861),(4158093384958469767/200000000000000000),1,(1321347951144223458997535018862853323/649702091399760901093750000000000000),false,MergedCutProfiles.Batch593.profile23741,(fun _ => MergedCutProfiles.Batch593.profile23741)⟩
theorem profilesValid3896 : retention3896.ProfilesValid := by
  exact MergedCutProfiles.Batch593.valid23741
theorem numericValid3896 : retention3896.NumericValid := by decide +kernel
def certificate3896 : RatCutBinCertificate := ⟨⟨retention3896,(1800678292975396411/1000000000000000000),(1358828718451041/40000000000000000),(2348368674732809949/250000000000000000),(1615106879914194358303/125000000000000000),(1013631559867458757/500000000000000000)⟩,(999865022063616093/1000000000000000000),(31911823671676201/1000000000000000000),(419357723827410781/500000000000000000),(19362723005928113/12500000000000000)⟩
theorem valid3896 : certificate3896.Valid := by decide +kernel
theorem sound3896 : certificate3896.Sound := rat_cut_bin_certificate_sound certificate3896 profilesValid3896 numericValid3896 valid3896

def retention3897 : RatCutRetentionCertificate := ⟨(27/1000),(7/250),(1/2),64,1,(63843694446586541505180302875124093631/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch040.profile1621,(fun _ => MergedCutProfiles.Batch040.profile1621)⟩
theorem profilesValid3897 : retention3897.ProfilesValid := by
  exact MergedCutProfiles.Batch040.valid1621
theorem numericValid3897 : retention3897.NumericValid := by decide +kernel
def certificate3897 : RatCutBinCertificate := ⟨⟨retention3897,(1800678292975396411/1000000000000000000),(1358828718451041/40000000000000000),(2348368674732809949/250000000000000000),(1615106879914194358303/125000000000000000),(495522861282906949/500000000000000000)⟩,(999865022063616093/1000000000000000000),(4079886385411993/62500000000000000),(187149555777529733/250000000000000000),(730482428261384777/1000000000000000000)⟩
theorem valid3897 : certificate3897.Valid := by decide +kernel
theorem sound3897 : certificate3897.Sound := rat_cut_bin_certificate_sound certificate3897 profilesValid3897 numericValid3897 valid3897

def retention3898 : RatCutRetentionCertificate := ⟨(7/250),(29/1000),(586888804839152685/1269525124002786192674),(558404560244987407/1000000000000000000),4,(4858693766897150671560063975832501543/2233618240979949628000000000000000000),true,MergedCutProfiles.Batch593.profile23742,![MergedCutProfiles.Batch593.profile23742,MergedCutProfiles.Batch593.profile23743,MergedCutProfiles.Batch593.profile23744,MergedCutProfiles.Batch462.profile18491,MergedCutProfiles.Batch593.profile23745,MergedCutProfiles.Batch593.profile23746,MergedCutProfiles.Batch593.profile23747,MergedCutProfiles.Batch462.profile18504,MergedCutProfiles.Batch593.profile23748,MergedCutProfiles.Batch593.profile23749,MergedCutProfiles.Batch593.profile23750,MergedCutProfiles.Batch462.profile18508,MergedCutProfiles.Batch462.profile18493,MergedCutProfiles.Batch593.profile23751,MergedCutProfiles.Batch593.profile23752,MergedCutProfiles.Batch462.profile18505]⟩
theorem profilesValid3898 : retention3898.ProfilesValid := by
  change ∀ j : Fin 16, (retention3898.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch593.valid23742
  · exact MergedCutProfiles.Batch593.valid23743
  · exact MergedCutProfiles.Batch593.valid23744
  · exact MergedCutProfiles.Batch462.valid18491
  · exact MergedCutProfiles.Batch593.valid23745
  · exact MergedCutProfiles.Batch593.valid23746
  · exact MergedCutProfiles.Batch593.valid23747
  · exact MergedCutProfiles.Batch462.valid18504
  · exact MergedCutProfiles.Batch593.valid23748
  · exact MergedCutProfiles.Batch593.valid23749
  · exact MergedCutProfiles.Batch593.valid23750
  · exact MergedCutProfiles.Batch462.valid18508
  · exact MergedCutProfiles.Batch462.valid18493
  · exact MergedCutProfiles.Batch593.valid23751
  · exact MergedCutProfiles.Batch593.valid23752
  · exact MergedCutProfiles.Batch462.valid18505
theorem numericValid3898 : retention3898.NumericValid := by decide +kernel
def certificate3898 : RatCutBinCertificate := ⟨⟨retention3898,(916543144554320903/500000000000000000),(36585906920747501/1000000000000000000),(9525037074279240427/1000000000000000000),(12153077954679282224127/1000000000000000000),(2147093263588706989/1000000000000000000)⟩,(999854290072363393/1000000000000000000),(18389451155623093/25000000000000000),(19263471239497759/500000000000000000),(8335211060257181/500000000000000000)⟩
theorem valid3898 : certificate3898.Valid := by decide +kernel
theorem sound3898 : certificate3898.Sound := rat_cut_bin_certificate_sound certificate3898 profilesValid3898 numericValid3898 valid3898

def retention3899 : RatCutRetentionCertificate := ⟨(7/250),(29/1000),(597965701500000000/634762562001393096337),(117377760967830537/200000000000000000),4,(69904158961947671164043748124356093/31300736258088143200000000000000000),true,MergedCutProfiles.Batch593.profile23743,![MergedCutProfiles.Batch593.profile23743,MergedCutProfiles.Batch462.profile18491,MergedCutProfiles.Batch593.profile23753,MergedCutProfiles.Batch462.profile18504,MergedCutProfiles.Batch593.profile23754,MergedCutProfiles.Batch462.profile18508,MergedCutProfiles.Batch593.profile23751,MergedCutProfiles.Batch462.profile18505,MergedCutProfiles.Batch593.profile23755,MergedCutProfiles.Batch593.profile23756,MergedCutProfiles.Batch593.profile23757,MergedCutProfiles.Batch040.profile1624,MergedCutProfiles.Batch462.profile18496,MergedCutProfiles.Batch593.profile23758,MergedCutProfiles.Batch462.profile18497,MergedCutProfiles.Batch330.profile13233]⟩
theorem profilesValid3899 : retention3899.ProfilesValid := by
  change ∀ j : Fin 16, (retention3899.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch593.valid23743
  · exact MergedCutProfiles.Batch462.valid18491
  · exact MergedCutProfiles.Batch593.valid23753
  · exact MergedCutProfiles.Batch462.valid18504
  · exact MergedCutProfiles.Batch593.valid23754
  · exact MergedCutProfiles.Batch462.valid18508
  · exact MergedCutProfiles.Batch593.valid23751
  · exact MergedCutProfiles.Batch462.valid18505
  · exact MergedCutProfiles.Batch593.valid23755
  · exact MergedCutProfiles.Batch593.valid23756
  · exact MergedCutProfiles.Batch593.valid23757
  · exact MergedCutProfiles.Batch040.valid1624
  · exact MergedCutProfiles.Batch462.valid18496
  · exact MergedCutProfiles.Batch593.valid23758
  · exact MergedCutProfiles.Batch462.valid18497
  · exact MergedCutProfiles.Batch330.valid13233
theorem numericValid3899 : retention3899.NumericValid := by decide +kernel
def certificate3899 : RatCutBinCertificate := ⟨⟨retention3899,(916543144554320903/500000000000000000),(36585906920747501/1000000000000000000),(9525037074279240427/1000000000000000000),(12153077954679282224127/1000000000000000000),(551285854939939387/250000000000000000)⟩,(999854290072363393/1000000000000000000),(692398370596888033/1000000000000000000),(5308027503368161/100000000000000000),(2369328936038689/100000000000000000)⟩
theorem valid3899 : certificate3899.Valid := by decide +kernel
theorem sound3899 : certificate3899.Sound := rat_cut_bin_certificate_sound certificate3899 profilesValid3899 numericValid3899 valid3899

def certificates : List RatCutBinCertificate := [certificate3888,certificate3889,certificate3890,certificate3891,certificate3892,certificate3893,certificate3894,certificate3895,certificate3896,certificate3897,certificate3898,certificate3899]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound3888,List.forall_mem_cons.mpr ⟨sound3889,List.forall_mem_cons.mpr ⟨sound3890,List.forall_mem_cons.mpr ⟨sound3891,List.forall_mem_cons.mpr ⟨sound3892,List.forall_mem_cons.mpr ⟨sound3893,List.forall_mem_cons.mpr ⟨sound3894,List.forall_mem_cons.mpr ⟨sound3895,List.forall_mem_cons.mpr ⟨sound3896,List.forall_mem_cons.mpr ⟨sound3897,List.forall_mem_cons.mpr ⟨sound3898,List.forall_mem_cons.mpr ⟨sound3899,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch324
