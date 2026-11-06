import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch168
import Cycle12.MergedCutProfiles.Batch169
import Cycle12.MergedCutProfiles.Batch170

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch084

def retention1008 : RatCutRetentionCertificate := ⟨(207/4000),(13/250),(1/2),(4339717943620629497/500000000000000000),(21/20),(3444981397206934517755629391373693876151/3471774354896503597600000000000000000000),false,MergedCutProfiles.Batch168.profile6736,(fun _ => MergedCutProfiles.Batch168.profile6736)⟩
theorem profilesValid1008 : retention1008.ProfilesValid := by
  exact MergedCutProfiles.Batch168.valid6736
theorem numericValid1008 : retention1008.NumericValid := by decide +kernel
def certificate1008 : RatCutBinCertificate := ⟨⟨retention1008,(639241692768221649/250000000000000000),(65444215677591123/500000000000000000),(13717782655446071423/1000000000000000000),(14970718593046750777/62500000000000000),(966663892653707827/1000000000000000000)⟩,(990693895977825093/1000000000000000000),(417851899041907859/1000000000000000000),(217517965823287299/1000000000000000000),(45025630691983999/250000000000000000)⟩
theorem valid1008 : certificate1008.Valid := by decide +kernel
theorem sound1008 : certificate1008.Sound := rat_cut_bin_certificate_sound certificate1008 profilesValid1008 numericValid1008 valid1008

def retention1009 : RatCutRetentionCertificate := ⟨(13/250),(209/4000),(851834001336929278/17244595680082648633),(421700000661846177/500000000000000000),(29/10),(1318270140163907239477/640000000000000000000),true,MergedCutProfiles.Batch168.profile6740,![MergedCutProfiles.Batch168.profile6740,MergedCutProfiles.Batch168.profile6741,MergedCutProfiles.Batch168.profile6742,MergedCutProfiles.Batch168.profile6743,MergedCutProfiles.Batch168.profile6744,MergedCutProfiles.Batch168.profile6745,MergedCutProfiles.Batch168.profile6746,MergedCutProfiles.Batch168.profile6747,MergedCutProfiles.Batch168.profile6748,MergedCutProfiles.Batch168.profile6749,MergedCutProfiles.Batch168.profile6750,MergedCutProfiles.Batch168.profile6751,MergedCutProfiles.Batch168.profile6752,MergedCutProfiles.Batch168.profile6753,MergedCutProfiles.Batch168.profile6754,MergedCutProfiles.Batch168.profile6755]⟩
theorem profilesValid1009 : retention1009.ProfilesValid := by
  change ∀ j : Fin 16, (retention1009.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch168.valid6740
  · exact MergedCutProfiles.Batch168.valid6741
  · exact MergedCutProfiles.Batch168.valid6742
  · exact MergedCutProfiles.Batch168.valid6743
  · exact MergedCutProfiles.Batch168.valid6744
  · exact MergedCutProfiles.Batch168.valid6745
  · exact MergedCutProfiles.Batch168.valid6746
  · exact MergedCutProfiles.Batch168.valid6747
  · exact MergedCutProfiles.Batch168.valid6748
  · exact MergedCutProfiles.Batch168.valid6749
  · exact MergedCutProfiles.Batch168.valid6750
  · exact MergedCutProfiles.Batch168.valid6751
  · exact MergedCutProfiles.Batch168.valid6752
  · exact MergedCutProfiles.Batch168.valid6753
  · exact MergedCutProfiles.Batch168.valid6754
  · exact MergedCutProfiles.Batch168.valid6755
theorem numericValid1009 : retention1009.NumericValid := by decide +kernel
def certificate1009 : RatCutBinCertificate := ⟨⟨retention1009,(274860218768783229/125000000000000000),(132328855686888103/1000000000000000000),(3444023630450536769/250000000000000000),(475816539608415039/2000000000000000),(249816253760730949/125000000000000000)⟩,(991957161331499799/1000000000000000000),(9182116950035333/25000000000000000),(132416409914887827/500000000000000000),(141028455979570131/1000000000000000000)⟩
theorem valid1009 : certificate1009.Valid := by decide +kernel
theorem sound1009 : certificate1009.Sound := rat_cut_bin_certificate_sound certificate1009 profilesValid1009 numericValid1009 valid1009

def retention1010 : RatCutRetentionCertificate := ⟨(13/250),(209/4000),(913281346960091902/17244595680082648633),(425917000668464639/500000000000000000),(57/20),(1308239324816502060431/640000000000000000000),true,MergedCutProfiles.Batch168.profile6756,![MergedCutProfiles.Batch168.profile6756,MergedCutProfiles.Batch168.profile6757,MergedCutProfiles.Batch168.profile6758,MergedCutProfiles.Batch168.profile6759,MergedCutProfiles.Batch169.profile6760,MergedCutProfiles.Batch169.profile6761,MergedCutProfiles.Batch169.profile6762,MergedCutProfiles.Batch169.profile6763,MergedCutProfiles.Batch169.profile6764,MergedCutProfiles.Batch169.profile6765,MergedCutProfiles.Batch169.profile6766,MergedCutProfiles.Batch169.profile6767,MergedCutProfiles.Batch169.profile6768,MergedCutProfiles.Batch168.profile6754,MergedCutProfiles.Batch169.profile6769,MergedCutProfiles.Batch169.profile6770]⟩
theorem profilesValid1010 : retention1010.ProfilesValid := by
  change ∀ j : Fin 16, (retention1010.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch168.valid6756
  · exact MergedCutProfiles.Batch168.valid6757
  · exact MergedCutProfiles.Batch168.valid6758
  · exact MergedCutProfiles.Batch168.valid6759
  · exact MergedCutProfiles.Batch169.valid6760
  · exact MergedCutProfiles.Batch169.valid6761
  · exact MergedCutProfiles.Batch169.valid6762
  · exact MergedCutProfiles.Batch169.valid6763
  · exact MergedCutProfiles.Batch169.valid6764
  · exact MergedCutProfiles.Batch169.valid6765
  · exact MergedCutProfiles.Batch169.valid6766
  · exact MergedCutProfiles.Batch169.valid6767
  · exact MergedCutProfiles.Batch169.valid6768
  · exact MergedCutProfiles.Batch168.valid6754
  · exact MergedCutProfiles.Batch169.valid6769
  · exact MergedCutProfiles.Batch169.valid6770
theorem numericValid1010 : retention1010.NumericValid := by decide +kernel
def certificate1010 : RatCutBinCertificate := ⟨⟨retention1010,(274860218768783229/125000000000000000),(132328855686888103/1000000000000000000),(3444023630450536769/250000000000000000),(475816539608415039/2000000000000000),(1983913107544393449/1000000000000000000)⟩,(991957161331499799/1000000000000000000),(368489138391497489/1000000000000000000),(65907126226059707/250000000000000000),(70628283232784393/500000000000000000)⟩
theorem valid1010 : certificate1010.Valid := by decide +kernel
theorem sound1010 : certificate1010.Sound := rat_cut_bin_certificate_sound certificate1010 profilesValid1010 numericValid1010 valid1010

def retention1011 : RatCutRetentionCertificate := ⟨(13/250),(209/4000),(1387082480720116595/17244595680082648633),(456640673480045951/500000000000000000),(53/20),(312833315026067857421/160000000000000000000),true,MergedCutProfiles.Batch169.profile6771,![MergedCutProfiles.Batch169.profile6771,MergedCutProfiles.Batch169.profile6772,MergedCutProfiles.Batch169.profile6773,MergedCutProfiles.Batch169.profile6774,MergedCutProfiles.Batch169.profile6775,MergedCutProfiles.Batch169.profile6776,MergedCutProfiles.Batch169.profile6777,MergedCutProfiles.Batch168.profile6752,MergedCutProfiles.Batch169.profile6778,MergedCutProfiles.Batch169.profile6779,MergedCutProfiles.Batch169.profile6780,MergedCutProfiles.Batch169.profile6781,MergedCutProfiles.Batch169.profile6782,MergedCutProfiles.Batch169.profile6783,MergedCutProfiles.Batch169.profile6784,MergedCutProfiles.Batch169.profile6785]⟩
theorem profilesValid1011 : retention1011.ProfilesValid := by
  change ∀ j : Fin 16, (retention1011.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch169.valid6771
  · exact MergedCutProfiles.Batch169.valid6772
  · exact MergedCutProfiles.Batch169.valid6773
  · exact MergedCutProfiles.Batch169.valid6774
  · exact MergedCutProfiles.Batch169.valid6775
  · exact MergedCutProfiles.Batch169.valid6776
  · exact MergedCutProfiles.Batch169.valid6777
  · exact MergedCutProfiles.Batch168.valid6752
  · exact MergedCutProfiles.Batch169.valid6778
  · exact MergedCutProfiles.Batch169.valid6779
  · exact MergedCutProfiles.Batch169.valid6780
  · exact MergedCutProfiles.Batch169.valid6781
  · exact MergedCutProfiles.Batch169.valid6782
  · exact MergedCutProfiles.Batch169.valid6783
  · exact MergedCutProfiles.Batch169.valid6784
  · exact MergedCutProfiles.Batch169.valid6785
theorem numericValid1011 : retention1011.NumericValid := by decide +kernel
def certificate1011 : RatCutBinCertificate := ⟨⟨retention1011,(274860218768783229/125000000000000000),(132328855686888103/1000000000000000000),(3444023630450536769/250000000000000000),(475816539608415039/2000000000000000),(1899222663453624621/1000000000000000000)⟩,(991957161331499799/1000000000000000000),(37436735176297811/100000000000000000),(64451800438375757/250000000000000000),(141190964810826671/1000000000000000000)⟩
theorem valid1011 : certificate1011.Valid := by decide +kernel
theorem sound1011 : certificate1011.Sound := rat_cut_bin_certificate_sound certificate1011 profilesValid1011 numericValid1011 valid1011

def retention1012 : RatCutRetentionCertificate := ⟨(13/250),(209/4000),(3827211053915730570/17244595680082648633),(277416496144023319/200000000000000000),(39/20),(405499288426690373799/256000000000000000000),true,MergedCutProfiles.Batch169.profile6786,![MergedCutProfiles.Batch169.profile6786,MergedCutProfiles.Batch168.profile6748,MergedCutProfiles.Batch169.profile6787,MergedCutProfiles.Batch169.profile6788,MergedCutProfiles.Batch169.profile6789,MergedCutProfiles.Batch169.profile6790,MergedCutProfiles.Batch169.profile6791,MergedCutProfiles.Batch169.profile6792,MergedCutProfiles.Batch169.profile6793,MergedCutProfiles.Batch169.profile6794,MergedCutProfiles.Batch169.profile6795,MergedCutProfiles.Batch169.profile6796,MergedCutProfiles.Batch169.profile6797,MergedCutProfiles.Batch169.profile6798,MergedCutProfiles.Batch169.profile6799,MergedCutProfiles.Batch170.profile6800]⟩
theorem profilesValid1012 : retention1012.ProfilesValid := by
  change ∀ j : Fin 16, (retention1012.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch169.valid6786
  · exact MergedCutProfiles.Batch168.valid6748
  · exact MergedCutProfiles.Batch169.valid6787
  · exact MergedCutProfiles.Batch169.valid6788
  · exact MergedCutProfiles.Batch169.valid6789
  · exact MergedCutProfiles.Batch169.valid6790
  · exact MergedCutProfiles.Batch169.valid6791
  · exact MergedCutProfiles.Batch169.valid6792
  · exact MergedCutProfiles.Batch169.valid6793
  · exact MergedCutProfiles.Batch169.valid6794
  · exact MergedCutProfiles.Batch169.valid6795
  · exact MergedCutProfiles.Batch169.valid6796
  · exact MergedCutProfiles.Batch169.valid6797
  · exact MergedCutProfiles.Batch169.valid6798
  · exact MergedCutProfiles.Batch169.valid6799
  · exact MergedCutProfiles.Batch170.valid6800
theorem numericValid1012 : retention1012.NumericValid := by decide +kernel
def certificate1012 : RatCutBinCertificate := ⟨⟨retention1012,(274860218768783229/125000000000000000),(132328855686888103/1000000000000000000),(3444023630450536769/250000000000000000),(475816539608415039/2000000000000000),(192848209162221833/125000000000000000)⟩,(991957161331499799/1000000000000000000),(2495872873511619/6250000000000000),(234087944937044359/1000000000000000000),(14194348220980793/100000000000000000)⟩
theorem valid1012 : certificate1012.Valid := by decide +kernel
theorem sound1012 : certificate1012.Sound := rat_cut_bin_certificate_sound certificate1012 profilesValid1012 numericValid1012 valid1012

def retention1013 : RatCutRetentionCertificate := ⟨(13/250),(209/4000),(7454430254960422277/17244595680082648633),(382721105391573057/100000000000000000),(11/10),(141526135289310171021/128000000000000000000),true,MergedCutProfiles.Batch170.profile6801,![MergedCutProfiles.Batch170.profile6801,MergedCutProfiles.Batch170.profile6802,MergedCutProfiles.Batch170.profile6803,MergedCutProfiles.Batch170.profile6804,MergedCutProfiles.Batch170.profile6805,MergedCutProfiles.Batch170.profile6806,MergedCutProfiles.Batch170.profile6807,MergedCutProfiles.Batch170.profile6808,MergedCutProfiles.Batch170.profile6809,MergedCutProfiles.Batch170.profile6810,MergedCutProfiles.Batch170.profile6811,MergedCutProfiles.Batch170.profile6812,MergedCutProfiles.Batch170.profile6813,MergedCutProfiles.Batch170.profile6814,MergedCutProfiles.Batch170.profile6815,MergedCutProfiles.Batch170.profile6816]⟩
theorem profilesValid1013 : retention1013.ProfilesValid := by
  change ∀ j : Fin 16, (retention1013.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch170.valid6801
  · exact MergedCutProfiles.Batch170.valid6802
  · exact MergedCutProfiles.Batch170.valid6803
  · exact MergedCutProfiles.Batch170.valid6804
  · exact MergedCutProfiles.Batch170.valid6805
  · exact MergedCutProfiles.Batch170.valid6806
  · exact MergedCutProfiles.Batch170.valid6807
  · exact MergedCutProfiles.Batch170.valid6808
  · exact MergedCutProfiles.Batch170.valid6809
  · exact MergedCutProfiles.Batch170.valid6810
  · exact MergedCutProfiles.Batch170.valid6811
  · exact MergedCutProfiles.Batch170.valid6812
  · exact MergedCutProfiles.Batch170.valid6813
  · exact MergedCutProfiles.Batch170.valid6814
  · exact MergedCutProfiles.Batch170.valid6815
  · exact MergedCutProfiles.Batch170.valid6816
theorem numericValid1013 : retention1013.NumericValid := by decide +kernel
def certificate1013 : RatCutBinCertificate := ⟨⟨retention1013,(274860218768783229/125000000000000000),(132328855686888103/1000000000000000000),(3444023630450536769/250000000000000000),(475816539608415039/2000000000000000),(216487182961172031/200000000000000000)⟩,(991957161331499799/1000000000000000000),(230707813607519781/500000000000000000),(5678108317778113/31250000000000000),(7181274751199859/50000000000000000)⟩
theorem valid1013 : certificate1013.Valid := by decide +kernel
theorem sound1013 : certificate1013.Sound := rat_cut_bin_certificate_sound certificate1013 profilesValid1013 numericValid1013 valid1013

def retention1014 : RatCutRetentionCertificate := ⟨(13/250),(209/4000),(8483836982629069009/17244595680082648633),(7454430254960422277/1000000000000000000),(21/20),(11971382212090125700783001885619133523351/11927088407936675643200000000000000000000),false,MergedCutProfiles.Batch170.profile6817,(fun _ => MergedCutProfiles.Batch170.profile6817)⟩
theorem profilesValid1014 : retention1014.ProfilesValid := by
  exact MergedCutProfiles.Batch170.valid6817
theorem numericValid1014 : retention1014.NumericValid := by decide +kernel
def certificate1014 : RatCutBinCertificate := ⟨⟨retention1014,(274860218768783229/125000000000000000),(132328855686888103/1000000000000000000),(3444023630450536769/250000000000000000),(475816539608415039/2000000000000000),(98153427979166153/100000000000000000)⟩,(991957161331499799/1000000000000000000),(237989512091816357/500000000000000000),(42665710069369731/250000000000000000),(8830671076853211/62500000000000000)⟩
theorem valid1014 : certificate1014.Valid := by decide +kernel
theorem sound1014 : certificate1014.Sound := rat_cut_bin_certificate_sound certificate1014 profilesValid1014 numericValid1014 valid1014

def retention1015 : RatCutRetentionCertificate := ⟨(13/250),(209/4000),(8568675352455359700/17244595680082648633),(8483836982629069009/1000000000000000000),(21/20),(1041823519051520920599912799242041874563/1044164551708193108800000000000000000000),false,MergedCutProfiles.Batch170.profile6818,(fun _ => MergedCutProfiles.Batch170.profile6818)⟩
theorem profilesValid1015 : retention1015.ProfilesValid := by
  exact MergedCutProfiles.Batch170.valid6818
theorem numericValid1015 : retention1015.NumericValid := by decide +kernel
def certificate1015 : RatCutBinCertificate := ⟨⟨retention1015,(274860218768783229/125000000000000000),(132328855686888103/1000000000000000000),(3444023630450536769/250000000000000000),(475816539608415039/2000000000000000),(975578741204416711/1000000000000000000)⟩,(991957161331499799/1000000000000000000),(18986029215589637/40000000000000000),(171650790711316711/1000000000000000000),(35797478882087541/250000000000000000)⟩
theorem valid1015 : certificate1015.Valid := by decide +kernel
theorem sound1015 : certificate1015.Sound := rat_cut_bin_certificate_sound certificate1015 profilesValid1015 numericValid1015 valid1015

def retention1016 : RatCutRetentionCertificate := ⟨(13/250),(209/4000),(1/2),(85686753524553597/10000000000000000),(21/20),(2833316955151176957041273524070626113/2856225117485119900000000000000000000),false,MergedCutProfiles.Batch170.profile6819,(fun _ => MergedCutProfiles.Batch170.profile6819)⟩
theorem profilesValid1016 : retention1016.ProfilesValid := by
  exact MergedCutProfiles.Batch170.valid6819
theorem numericValid1016 : retention1016.NumericValid := by decide +kernel
def certificate1016 : RatCutBinCertificate := ⟨⟨retention1016,(274860218768783229/125000000000000000),(132328855686888103/1000000000000000000),(3444023630450536769/250000000000000000),(475816539608415039/2000000000000000),(242450084232581339/250000000000000000)⟩,(991957161331499799/1000000000000000000),(477173487915485751/1000000000000000000),(84888797344359943/500000000000000000),(140998974106993177/1000000000000000000)⟩
theorem valid1016 : certificate1016.Valid := by decide +kernel
theorem sound1016 : certificate1016.Sound := rat_cut_bin_certificate_sound certificate1016 profilesValid1016 numericValid1016 valid1016

def retention1017 : RatCutRetentionCertificate := ⟨(13/250),(209/4000),(1/2),64,1,(255397059441885515491868088928498541871/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch170.profile6819,(fun _ => MergedCutProfiles.Batch170.profile6819)⟩
theorem profilesValid1017 : retention1017.ProfilesValid := by
  exact MergedCutProfiles.Batch170.valid6819
theorem numericValid1017 : retention1017.NumericValid := by decide +kernel
def certificate1017 : RatCutBinCertificate := ⟨⟨retention1017,(274860218768783229/125000000000000000),(132328855686888103/1000000000000000000),(3444023630450536769/250000000000000000),(475816539608415039/2000000000000000),(488261404728249591/500000000000000000)⟩,(991957161331499799/1000000000000000000),(223810847517238019/500000000000000000),(96288312990968141/500000000000000000),(183725886378945329/1000000000000000000)⟩
theorem valid1017 : certificate1017.Valid := by decide +kernel
theorem sound1017 : certificate1017.Sound := rat_cut_bin_certificate_sound certificate1017 profilesValid1017 numericValid1017 valid1017

def retention1018 : RatCutRetentionCertificate := ⟨(13/250),(209/4000),(7867971289119443454/17244595680082648633),(923375543519927311/250000000000000000),(6/5),(399407046654901005577080762780562943039/369350217407970924400000000000000000000),false,MergedCutProfiles.Batch170.profile6820,(fun _ => MergedCutProfiles.Batch170.profile6820)⟩
theorem profilesValid1018 : retention1018.ProfilesValid := by
  exact MergedCutProfiles.Batch170.valid6820
theorem numericValid1018 : retention1018.NumericValid := by decide +kernel
def certificate1018 : RatCutBinCertificate := ⟨⟨retention1018,(319993243018783229/125000000000000000),(132328855686888103/1000000000000000000),(3444023630450536769/250000000000000000),(475816539608415039/2000000000000000),(1051865835163981551/1000000000000000000)⟩,(990634636477481583/1000000000000000000),(76569153786237271/200000000000000000),(49914586517215407/200000000000000000),(90384587837314251/500000000000000000)⟩
theorem valid1018 : certificate1018.Valid := by decide +kernel
theorem sound1018 : certificate1018.Sound := rat_cut_bin_certificate_sound certificate1018 profilesValid1018 numericValid1018 valid1018

def retention1019 : RatCutRetentionCertificate := ⟨(13/250),(209/4000),(8519885470112199088/17244595680082648633),(3933985644559721727/500000000000000000),(21/20),(3151127772150910499270722308500821612031/3147188515647777381600000000000000000000),false,MergedCutProfiles.Batch170.profile6821,(fun _ => MergedCutProfiles.Batch170.profile6821)⟩
theorem profilesValid1019 : retention1019.ProfilesValid := by
  exact MergedCutProfiles.Batch170.valid6821
theorem numericValid1019 : retention1019.NumericValid := by decide +kernel
def certificate1019 : RatCutBinCertificate := ⟨⟨retention1019,(319993243018783229/125000000000000000),(132328855686888103/1000000000000000000),(3444023630450536769/250000000000000000),(475816539608415039/2000000000000000),(975430394258016127/1000000000000000000)⟩,(990634636477481583/1000000000000000000),(25802865256093183/62500000000000000),(221916368135916541/1000000000000000000),(183486052022635831/1000000000000000000)⟩
theorem valid1019 : certificate1019.Valid := by decide +kernel
theorem sound1019 : certificate1019.Sound := rat_cut_bin_certificate_sound certificate1019 profilesValid1019 numericValid1019 valid1019

def certificates : List RatCutBinCertificate := [certificate1008,certificate1009,certificate1010,certificate1011,certificate1012,certificate1013,certificate1014,certificate1015,certificate1016,certificate1017,certificate1018,certificate1019]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1008,List.forall_mem_cons.mpr ⟨sound1009,List.forall_mem_cons.mpr ⟨sound1010,List.forall_mem_cons.mpr ⟨sound1011,List.forall_mem_cons.mpr ⟨sound1012,List.forall_mem_cons.mpr ⟨sound1013,List.forall_mem_cons.mpr ⟨sound1014,List.forall_mem_cons.mpr ⟨sound1015,List.forall_mem_cons.mpr ⟨sound1016,List.forall_mem_cons.mpr ⟨sound1017,List.forall_mem_cons.mpr ⟨sound1018,List.forall_mem_cons.mpr ⟨sound1019,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch084
