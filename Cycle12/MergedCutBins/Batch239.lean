import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch016
import Cycle12.MergedCutProfiles.Batch017
import Cycle12.MergedCutProfiles.Batch018
import Cycle12.MergedCutProfiles.Batch316
import Cycle12.MergedCutProfiles.Batch317
import Cycle12.MergedCutProfiles.Batch451
import Cycle12.MergedCutProfiles.Batch452

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch239

def retention2868 : RatCutRetentionCertificate := ⟨(13/1000),(7/500),(16000000000000000000/365960577732687798351),(8142021655799800351/1000000000000000000),1,(63654648418491590492585119590121225443/32568086623199201404000000000000000000),false,MergedCutProfiles.Batch451.profile18051,(fun _ => MergedCutProfiles.Batch451.profile18051)⟩
theorem profilesValid2868 : retention2868.ProfilesValid := by
  exact MergedCutProfiles.Batch451.valid18051
theorem numericValid2868 : retention2868.NumericValid := by decide +kernel
def certificate2868 : RatCutBinCertificate := ⟨⟨retention2868,(1981882583690379651/1000000000000000000),(1008381335301397/125000000000000000),(1562100323579834151/200000000000000000),(5743011293647465710453/500000000000000000),(390492588028006069/200000000000000000)⟩,(499914324294977847/500000000000000000),(18309638488280541/250000000000000000),(364396690605809139/500000000000000000),(573755850526709249/500000000000000000)⟩
theorem valid2868 : certificate2868.Valid := by decide +kernel
theorem sound2868 : certificate2868.Sound := rat_cut_bin_certificate_sound certificate2868 profilesValid2868 numericValid2868 valid2868

def retention2869 : RatCutRetentionCertificate := ⟨(13/1000),(7/500),(1/2),64,1,(255369632393373974456752157088663284991/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch016.profile655,(fun _ => MergedCutProfiles.Batch016.profile655)⟩
theorem profilesValid2869 : retention2869.ProfilesValid := by
  exact MergedCutProfiles.Batch016.valid655
theorem numericValid2869 : retention2869.NumericValid := by decide +kernel
def certificate2869 : RatCutBinCertificate := ⟨⟨retention2869,(1981882583690379651/1000000000000000000),(1008381335301397/125000000000000000),(1562100323579834151/200000000000000000),(5743011293647465710453/500000000000000000),(124436330707883399/125000000000000000)⟩,(499914324294977847/500000000000000000),(143643300924914249/1000000000000000000),(576458153157238111/1000000000000000000),(564971716772903859/1000000000000000000)⟩
theorem valid2869 : certificate2869.Valid := by decide +kernel
theorem sound2869 : certificate2869.Sound := rat_cut_bin_certificate_sound certificate2869 profilesValid2869 numericValid2869 valid2869

def retention2870 : RatCutRetentionCertificate := ⟨(7/500),(3/200),(206330098367569981/423095796872776905372),(9111200908907863/15625000000000000),4,(3558108674298548903/1600000000000000000),true,MergedCutProfiles.Batch451.profile18052,![MergedCutProfiles.Batch451.profile18052,MergedCutProfiles.Batch451.profile18053,MergedCutProfiles.Batch451.profile18054,MergedCutProfiles.Batch451.profile18055,MergedCutProfiles.Batch016.profile656,MergedCutProfiles.Batch451.profile18056,MergedCutProfiles.Batch451.profile18057,MergedCutProfiles.Batch316.profile12643,MergedCutProfiles.Batch451.profile18058,MergedCutProfiles.Batch016.profile672,MergedCutProfiles.Batch451.profile18059,MergedCutProfiles.Batch451.profile18060,MergedCutProfiles.Batch316.profile12644,MergedCutProfiles.Batch451.profile18061,MergedCutProfiles.Batch316.profile12645,MergedCutProfiles.Batch451.profile18062]⟩
theorem profilesValid2870 : retention2870.ProfilesValid := by
  change ∀ j : Fin 16, (retention2870.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch451.valid18052
  · exact MergedCutProfiles.Batch451.valid18053
  · exact MergedCutProfiles.Batch451.valid18054
  · exact MergedCutProfiles.Batch451.valid18055
  · exact MergedCutProfiles.Batch016.valid656
  · exact MergedCutProfiles.Batch451.valid18056
  · exact MergedCutProfiles.Batch451.valid18057
  · exact MergedCutProfiles.Batch316.valid12643
  · exact MergedCutProfiles.Batch451.valid18058
  · exact MergedCutProfiles.Batch016.valid672
  · exact MergedCutProfiles.Batch451.valid18059
  · exact MergedCutProfiles.Batch451.valid18060
  · exact MergedCutProfiles.Batch316.valid12644
  · exact MergedCutProfiles.Batch451.valid18061
  · exact MergedCutProfiles.Batch316.valid12645
  · exact MergedCutProfiles.Batch451.valid18062
theorem numericValid2870 : retention2870.NumericValid := by decide +kernel
def certificate2870 : RatCutBinCertificate := ⟨⟨retention2870,(366844958528310277/200000000000000000),(9292470143341151/1000000000000000000),(395473344547256561/50000000000000000),(10085909374252406242401/1000000000000000000),(2215198131461148371/1000000000000000000)⟩,(499909803339929247/500000000000000000),(118780230588512217/200000000000000000),(96651173985969921/1000000000000000000),(21622972807771897/500000000000000000)⟩
theorem valid2870 : certificate2870.Valid := by decide +kernel
theorem sound2870 : certificate2870.Sound := rat_cut_bin_certificate_sound certificate2870 profilesValid2870 numericValid2870 valid2870

def retention2871 : RatCutRetentionCertificate := ⟨(7/500),(3/200),(28410002750000000/28847440695871152639),(618990295102709943/1000000000000000000),4,(1128656772513252575727628123722247171/495192236082167954400000000000000000),true,MergedCutProfiles.Batch451.profile18063,![MergedCutProfiles.Batch451.profile18063,MergedCutProfiles.Batch451.profile18055,MergedCutProfiles.Batch451.profile18056,MergedCutProfiles.Batch316.profile12654,MergedCutProfiles.Batch016.profile672,MergedCutProfiles.Batch451.profile18060,MergedCutProfiles.Batch451.profile18061,MergedCutProfiles.Batch451.profile18062,MergedCutProfiles.Batch451.profile18064,MergedCutProfiles.Batch016.profile673,MergedCutProfiles.Batch316.profile12647,MergedCutProfiles.Batch451.profile18065,MergedCutProfiles.Batch016.profile660,MergedCutProfiles.Batch451.profile18066,MergedCutProfiles.Batch016.profile661,MergedCutProfiles.Batch316.profile12650]⟩
theorem profilesValid2871 : retention2871.ProfilesValid := by
  change ∀ j : Fin 16, (retention2871.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch451.valid18063
  · exact MergedCutProfiles.Batch451.valid18055
  · exact MergedCutProfiles.Batch451.valid18056
  · exact MergedCutProfiles.Batch316.valid12654
  · exact MergedCutProfiles.Batch016.valid672
  · exact MergedCutProfiles.Batch451.valid18060
  · exact MergedCutProfiles.Batch451.valid18061
  · exact MergedCutProfiles.Batch451.valid18062
  · exact MergedCutProfiles.Batch451.valid18064
  · exact MergedCutProfiles.Batch016.valid673
  · exact MergedCutProfiles.Batch316.valid12647
  · exact MergedCutProfiles.Batch451.valid18065
  · exact MergedCutProfiles.Batch016.valid660
  · exact MergedCutProfiles.Batch451.valid18066
  · exact MergedCutProfiles.Batch016.valid661
  · exact MergedCutProfiles.Batch316.valid12650
theorem numericValid2871 : retention2871.NumericValid := by decide +kernel
def certificate2871 : RatCutBinCertificate := ⟨⟨retention2871,(366844958528310277/200000000000000000),(9292470143341151/1000000000000000000),(395473344547256561/50000000000000000),(10085909374252406242401/1000000000000000000),(1135304875167607463/500000000000000000)⟩,(499909803339929247/500000000000000000),(69602686091937479/125000000000000000),(58576816949816209/500000000000000000),(54087879056412337/1000000000000000000)⟩
theorem valid2871 : certificate2871.Valid := by decide +kernel
theorem sound2871 : certificate2871.Sound := rat_cut_bin_certificate_sound certificate2871 profilesValid2871 numericValid2871 valid2871

def retention2872 : RatCutRetentionCertificate := ⟨(7/500),(3/200),(35550165371511910/35257983072731408781),(1250040121/1000000000),(5/2),(2336640047530635789/1000000000000000000),true,MergedCutProfiles.Batch451.profile18063,![MergedCutProfiles.Batch451.profile18063,MergedCutProfiles.Batch451.profile18055,MergedCutProfiles.Batch451.profile18067,MergedCutProfiles.Batch316.profile12654,MergedCutProfiles.Batch016.profile657,MergedCutProfiles.Batch451.profile18060,MergedCutProfiles.Batch316.profile12645,MergedCutProfiles.Batch451.profile18062,MergedCutProfiles.Batch451.profile18064,MergedCutProfiles.Batch016.profile659,MergedCutProfiles.Batch316.profile12647,MergedCutProfiles.Batch316.profile12648,MergedCutProfiles.Batch017.profile689,MergedCutProfiles.Batch451.profile18066,MergedCutProfiles.Batch016.profile661,MergedCutProfiles.Batch316.profile12656]⟩
theorem profilesValid2872 : retention2872.ProfilesValid := by
  change ∀ j : Fin 16, (retention2872.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch451.valid18063
  · exact MergedCutProfiles.Batch451.valid18055
  · exact MergedCutProfiles.Batch451.valid18067
  · exact MergedCutProfiles.Batch316.valid12654
  · exact MergedCutProfiles.Batch016.valid657
  · exact MergedCutProfiles.Batch451.valid18060
  · exact MergedCutProfiles.Batch316.valid12645
  · exact MergedCutProfiles.Batch451.valid18062
  · exact MergedCutProfiles.Batch451.valid18064
  · exact MergedCutProfiles.Batch016.valid659
  · exact MergedCutProfiles.Batch316.valid12647
  · exact MergedCutProfiles.Batch316.valid12648
  · exact MergedCutProfiles.Batch017.valid689
  · exact MergedCutProfiles.Batch451.valid18066
  · exact MergedCutProfiles.Batch016.valid661
  · exact MergedCutProfiles.Batch316.valid12656
theorem numericValid2872 : retention2872.NumericValid := by decide +kernel
def certificate2872 : RatCutBinCertificate := ⟨⟨retention2872,(366844958528310277/200000000000000000),(9292470143341151/1000000000000000000),(395473344547256561/50000000000000000),(10085909374252406242401/1000000000000000000),(58281316983393089/25000000000000000)⟩,(499909803339929247/500000000000000000),(361819743625608359/1000000000000000000),(54069370351108467/200000000000000000),(48530658412505063/250000000000000000)⟩
theorem valid2872 : certificate2872.Valid := by decide +kernel
theorem sound2872 : certificate2872.Sound := rat_cut_bin_certificate_sound certificate2872 profilesValid2872 numericValid2872 valid2872

def retention2873 : RatCutRetentionCertificate := ⟨(7/500),(3/200),(1045508612899584113/317321847654582679029),(31995148834360719/25000000000000000),(49/20),(73674047429330515721/32000000000000000000),true,MergedCutProfiles.Batch451.profile18057,![MergedCutProfiles.Batch451.profile18057,MergedCutProfiles.Batch017.profile688,MergedCutProfiles.Batch016.profile673,MergedCutProfiles.Batch017.profile689,MergedCutProfiles.Batch316.profile12656,MergedCutProfiles.Batch016.profile675,MergedCutProfiles.Batch451.profile18068,MergedCutProfiles.Batch451.profile18069,MergedCutProfiles.Batch016.profile667,MergedCutProfiles.Batch016.profile668,MergedCutProfiles.Batch451.profile18070,MergedCutProfiles.Batch017.profile691,MergedCutProfiles.Batch451.profile18071,MergedCutProfiles.Batch017.profile692,MergedCutProfiles.Batch316.profile12661,MergedCutProfiles.Batch017.profile682]⟩
theorem profilesValid2873 : retention2873.ProfilesValid := by
  change ∀ j : Fin 16, (retention2873.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch451.valid18057
  · exact MergedCutProfiles.Batch017.valid688
  · exact MergedCutProfiles.Batch016.valid673
  · exact MergedCutProfiles.Batch017.valid689
  · exact MergedCutProfiles.Batch316.valid12656
  · exact MergedCutProfiles.Batch016.valid675
  · exact MergedCutProfiles.Batch451.valid18068
  · exact MergedCutProfiles.Batch451.valid18069
  · exact MergedCutProfiles.Batch016.valid667
  · exact MergedCutProfiles.Batch016.valid668
  · exact MergedCutProfiles.Batch451.valid18070
  · exact MergedCutProfiles.Batch017.valid691
  · exact MergedCutProfiles.Batch451.valid18071
  · exact MergedCutProfiles.Batch017.valid692
  · exact MergedCutProfiles.Batch316.valid12661
  · exact MergedCutProfiles.Batch017.valid682
theorem numericValid2873 : retention2873.NumericValid := by decide +kernel
def certificate2873 : RatCutBinCertificate := ⟨⟨retention2873,(366844958528310277/200000000000000000),(9292470143341151/1000000000000000000),(395473344547256561/50000000000000000),(10085909374252406242401/1000000000000000000),(1148517180670369699/500000000000000000)⟩,(499909803339929247/500000000000000000),(363030080629665547/1000000000000000000),(10764743049354301/40000000000000000),(97098452630096917/500000000000000000)⟩
theorem valid2873 : certificate2873.Valid := by decide +kernel
theorem sound2873 : certificate2873.Sound := rat_cut_bin_certificate_sound certificate2873 profilesValid2873 numericValid2873 valid2873

def retention2874 : RatCutRetentionCertificate := ⟨(7/500),(3/200),(16000000000000000000/317321847654582679029),(1045508612899584113/250000000000000000),(5/4),(75078735066755227200837779301398257/37339593317842289750000000000000000),true,MergedCutProfiles.Batch451.profile18072,![MergedCutProfiles.Batch451.profile18072,MergedCutProfiles.Batch451.profile18073,MergedCutProfiles.Batch451.profile18074,MergedCutProfiles.Batch451.profile18075,MergedCutProfiles.Batch451.profile18076,MergedCutProfiles.Batch451.profile18077,MergedCutProfiles.Batch451.profile18078,MergedCutProfiles.Batch451.profile18079,MergedCutProfiles.Batch452.profile18080,MergedCutProfiles.Batch452.profile18081,MergedCutProfiles.Batch452.profile18082,MergedCutProfiles.Batch452.profile18083,MergedCutProfiles.Batch452.profile18084,MergedCutProfiles.Batch452.profile18085,MergedCutProfiles.Batch452.profile18086,MergedCutProfiles.Batch452.profile18087]⟩
theorem profilesValid2874 : retention2874.ProfilesValid := by
  change ∀ j : Fin 16, (retention2874.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch451.valid18072
  · exact MergedCutProfiles.Batch451.valid18073
  · exact MergedCutProfiles.Batch451.valid18074
  · exact MergedCutProfiles.Batch451.valid18075
  · exact MergedCutProfiles.Batch451.valid18076
  · exact MergedCutProfiles.Batch451.valid18077
  · exact MergedCutProfiles.Batch451.valid18078
  · exact MergedCutProfiles.Batch451.valid18079
  · exact MergedCutProfiles.Batch452.valid18080
  · exact MergedCutProfiles.Batch452.valid18081
  · exact MergedCutProfiles.Batch452.valid18082
  · exact MergedCutProfiles.Batch452.valid18083
  · exact MergedCutProfiles.Batch452.valid18084
  · exact MergedCutProfiles.Batch452.valid18085
  · exact MergedCutProfiles.Batch452.valid18086
  · exact MergedCutProfiles.Batch452.valid18087
theorem numericValid2874 : retention2874.NumericValid := by decide +kernel
def certificate2874 : RatCutBinCertificate := ⟨⟨retention2874,(366844958528310277/200000000000000000),(9292470143341151/1000000000000000000),(395473344547256561/50000000000000000),(10085909374252406242401/1000000000000000000),(2008006712117243119/1000000000000000000)⟩,(499909803339929247/500000000000000000),(55188056548646467/200000000000000000),(184361803490906747/500000000000000000),(452999060288335217/1000000000000000000)⟩
theorem valid2874 : certificate2874.Valid := by decide +kernel
theorem sound2874 : certificate2874.Sound := rat_cut_bin_certificate_sound certificate2874 profilesValid2874 numericValid2874 valid2874

def retention2875 : RatCutRetentionCertificate := ⟨(7/500),(3/200),(1/2),64,1,(255369839288059878534814821034680834799/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch017.profile702,(fun _ => MergedCutProfiles.Batch017.profile702)⟩
theorem profilesValid2875 : retention2875.ProfilesValid := by
  exact MergedCutProfiles.Batch017.valid702
theorem numericValid2875 : retention2875.NumericValid := by decide +kernel
def certificate2875 : RatCutBinCertificate := ⟨⟨retention2875,(366844958528310277/200000000000000000),(9292470143341151/1000000000000000000),(395473344547256561/50000000000000000),(10085909374252406242401/1000000000000000000),(497691744022655583/500000000000000000)⟩,(499909803339929247/500000000000000000),(2755011839632603/6250000000000000),(198110571747032721/1000000000000000000),(12133791964514931/62500000000000000)⟩
theorem valid2875 : certificate2875.Valid := by decide +kernel
theorem sound2875 : certificate2875.Sound := rat_cut_bin_certificate_sound certificate2875 profilesValid2875 numericValid2875 valid2875

def retention2876 : RatCutRetentionCertificate := ⟨(7/500),(3/200),(16000000000000000000/317321847654582679029),(8134844503729419927/1000000000000000000),1,(218215544502388191743382261889318657/112983951440686387875000000000000000),false,MergedCutProfiles.Batch452.profile18088,(fun _ => MergedCutProfiles.Batch452.profile18088)⟩
theorem profilesValid2876 : retention2876.ProfilesValid := by
  exact MergedCutProfiles.Batch452.valid18088
theorem numericValid2876 : retention2876.NumericValid := by decide +kernel
def certificate2876 : RatCutBinCertificate := ⟨⟨retention2876,(397892401528310277/200000000000000000),(9292470143341151/1000000000000000000),(395473344547256561/50000000000000000),(10085909374252406242401/1000000000000000000),(1929047985757130961/1000000000000000000)⟩,(124975542412872843/125000000000000000),(74410376580739619/1000000000000000000),(362964187731538253/500000000000000000),(1131698575006424487/1000000000000000000)⟩
theorem valid2876 : certificate2876.Valid := by decide +kernel
theorem sound2876 : certificate2876.Sound := rat_cut_bin_certificate_sound certificate2876 profilesValid2876 numericValid2876 valid2876

def retention2877 : RatCutRetentionCertificate := ⟨(7/500),(3/200),(1/2),64,1,(255369839288059878534814821034680834799/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch017.profile702,(fun _ => MergedCutProfiles.Batch017.profile702)⟩
theorem profilesValid2877 : retention2877.ProfilesValid := by
  exact MergedCutProfiles.Batch017.valid702
theorem numericValid2877 : retention2877.NumericValid := by decide +kernel
def certificate2877 : RatCutBinCertificate := ⟨⟨retention2877,(397892401528310277/200000000000000000),(9292470143341151/1000000000000000000),(395473344547256561/50000000000000000),(10085909374252406242401/1000000000000000000),(995201106953617001/1000000000000000000)⟩,(124975542412872843/125000000000000000),(5769333898829569/40000000000000000),(143832744168565047/250000000000000000),(563691698192387419/1000000000000000000)⟩
theorem valid2877 : certificate2877.Valid := by decide +kernel
theorem sound2877 : certificate2877.Sound := rat_cut_bin_certificate_sound certificate2877 profilesValid2877 numericValid2877 valid2877

def retention2878 : RatCutRetentionCertificate := ⟨(3/200),(2/125),(303848123445640672/555204668868246689109),(291992074339249059/500000000000000000),4,(284832588186098393803/128000000000000000000),true,MergedCutProfiles.Batch452.profile18089,![MergedCutProfiles.Batch452.profile18089,MergedCutProfiles.Batch452.profile18090,MergedCutProfiles.Batch452.profile18091,MergedCutProfiles.Batch452.profile18092,MergedCutProfiles.Batch452.profile18093,MergedCutProfiles.Batch317.profile12686,MergedCutProfiles.Batch452.profile18094,MergedCutProfiles.Batch316.profile12668,MergedCutProfiles.Batch452.profile18095,MergedCutProfiles.Batch017.profile719,MergedCutProfiles.Batch452.profile18096,MergedCutProfiles.Batch018.profile734,MergedCutProfiles.Batch316.profile12669,MergedCutProfiles.Batch452.profile18097,MergedCutProfiles.Batch316.profile12677,MergedCutProfiles.Batch017.profile705]⟩
theorem profilesValid2878 : retention2878.ProfilesValid := by
  change ∀ j : Fin 16, (retention2878.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch452.valid18089
  · exact MergedCutProfiles.Batch452.valid18090
  · exact MergedCutProfiles.Batch452.valid18091
  · exact MergedCutProfiles.Batch452.valid18092
  · exact MergedCutProfiles.Batch452.valid18093
  · exact MergedCutProfiles.Batch317.valid12686
  · exact MergedCutProfiles.Batch452.valid18094
  · exact MergedCutProfiles.Batch316.valid12668
  · exact MergedCutProfiles.Batch452.valid18095
  · exact MergedCutProfiles.Batch017.valid719
  · exact MergedCutProfiles.Batch452.valid18096
  · exact MergedCutProfiles.Batch018.valid734
  · exact MergedCutProfiles.Batch316.valid12669
  · exact MergedCutProfiles.Batch452.valid18097
  · exact MergedCutProfiles.Batch316.valid12677
  · exact MergedCutProfiles.Batch017.valid705
theorem numericValid2878 : retention2878.NumericValid := by decide +kernel
def certificate2878 : RatCutBinCertificate := ⟨⟨retention2878,(92034014439784127/50000000000000000),(1060946273715283/100000000000000000),(8010376178086522153/1000000000000000000),(446812623498984896617/50000000000000000),(443100584781688383/200000000000000000)⟩,(6248724591683959/6250000000000000),(595384533673735303/1000000000000000000),(47940060403539949/500000000000000000),(8583347259093297/200000000000000000)⟩
theorem valid2878 : certificate2878.Valid := by decide +kernel
theorem sound2878 : certificate2878.Sound := rat_cut_bin_certificate_sound certificate2878 profilesValid2878 numericValid2878 valid2878

def retention2879 : RatCutRetentionCertificate := ⟨(3/200),(2/125),(208599566500000000/185068222956082229703),(9495253857676271/15625000000000000),4,(18087660236015064133/8000000000000000000),true,MergedCutProfiles.Batch452.profile18098,![MergedCutProfiles.Batch452.profile18098,MergedCutProfiles.Batch452.profile18099,MergedCutProfiles.Batch317.profile12686,MergedCutProfiles.Batch452.profile18100,MergedCutProfiles.Batch017.profile704,MergedCutProfiles.Batch452.profile18101,MergedCutProfiles.Batch452.profile18102,MergedCutProfiles.Batch452.profile18103,MergedCutProfiles.Batch452.profile18104,MergedCutProfiles.Batch017.profile706,MergedCutProfiles.Batch316.profile12671,MergedCutProfiles.Batch452.profile18105,MergedCutProfiles.Batch017.profile707,MergedCutProfiles.Batch452.profile18106,MergedCutProfiles.Batch316.profile12674,MergedCutProfiles.Batch452.profile18107]⟩
theorem profilesValid2879 : retention2879.ProfilesValid := by
  change ∀ j : Fin 16, (retention2879.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch452.valid18098
  · exact MergedCutProfiles.Batch452.valid18099
  · exact MergedCutProfiles.Batch317.valid12686
  · exact MergedCutProfiles.Batch452.valid18100
  · exact MergedCutProfiles.Batch017.valid704
  · exact MergedCutProfiles.Batch452.valid18101
  · exact MergedCutProfiles.Batch452.valid18102
  · exact MergedCutProfiles.Batch452.valid18103
  · exact MergedCutProfiles.Batch452.valid18104
  · exact MergedCutProfiles.Batch017.valid706
  · exact MergedCutProfiles.Batch316.valid12671
  · exact MergedCutProfiles.Batch452.valid18105
  · exact MergedCutProfiles.Batch017.valid707
  · exact MergedCutProfiles.Batch452.valid18106
  · exact MergedCutProfiles.Batch316.valid12674
  · exact MergedCutProfiles.Batch452.valid18107
theorem numericValid2879 : retention2879.NumericValid := by decide +kernel
def certificate2879 : RatCutBinCertificate := ⟨⟨retention2879,(92034014439784127/50000000000000000),(1060946273715283/100000000000000000),(8010376178086522153/1000000000000000000),(446812623498984896617/50000000000000000),(281400732299977941/125000000000000000)⟩,(6248724591683959/6250000000000000),(4457822891171837/7812500000000000),(109254511304736677/1000000000000000000),(24958259716034601/500000000000000000)⟩
theorem valid2879 : certificate2879.Valid := by decide +kernel
theorem sound2879 : certificate2879.Sound := rat_cut_bin_certificate_sound certificate2879 profilesValid2879 numericValid2879 valid2879

def certificates : List RatCutBinCertificate := [certificate2868,certificate2869,certificate2870,certificate2871,certificate2872,certificate2873,certificate2874,certificate2875,certificate2876,certificate2877,certificate2878,certificate2879]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound2868,List.forall_mem_cons.mpr ⟨sound2869,List.forall_mem_cons.mpr ⟨sound2870,List.forall_mem_cons.mpr ⟨sound2871,List.forall_mem_cons.mpr ⟨sound2872,List.forall_mem_cons.mpr ⟨sound2873,List.forall_mem_cons.mpr ⟨sound2874,List.forall_mem_cons.mpr ⟨sound2875,List.forall_mem_cons.mpr ⟨sound2876,List.forall_mem_cons.mpr ⟨sound2877,List.forall_mem_cons.mpr ⟨sound2878,List.forall_mem_cons.mpr ⟨sound2879,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch239
