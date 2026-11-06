import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch020
import Cycle12.MergedCutProfiles.Batch021
import Cycle12.MergedCutProfiles.Batch022

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch010

def retention120 : RatCutRetentionCertificate := ⟨(2/125),(17/1000),(64000000000000000000/195805185359399352263),(3489881170794847273/1000000000000000000),(13/10),(1883378773839960256509127473562277060919/1395952468317938909200000000000000000000),false,MergedCutProfiles.Batch020.profile829,(fun _ => MergedCutProfiles.Batch020.profile829)⟩
theorem profilesValid120 : retention120.ProfilesValid := by
  exact MergedCutProfiles.Batch020.valid829
theorem numericValid120 : retention120.NumericValid := by decide +kernel
def certificate120 : RatCutBinCertificate := ⟨⟨retention120,(2268386293046795801/1000000000000000000),(12019078477736559/1000000000000000000),(4056627898521048907/500000000000000000),(199508041444546027759/125000000000000000),(1344802585614903179/1000000000000000000)⟩,(99859381993131509/100000000000000000),(290103915129266911/1000000000000000000),(175428939011994287/500000000000000000),(147554528477407881/500000000000000000)⟩
theorem valid120 : certificate120.Valid := by decide +kernel
theorem sound120 : certificate120.Sound := rat_cut_bin_certificate_sound certificate120 profilesValid120 numericValid120 valid120

def retention121 : RatCutRetentionCertificate := ⟨(2/125),(17/1000),(1/2),64,1,(408592521868712119380352324506759031/409600000000000000000000000000000000),false,MergedCutProfiles.Batch020.profile830,(fun _ => MergedCutProfiles.Batch020.profile830)⟩
theorem profilesValid121 : retention121.ProfilesValid := by
  exact MergedCutProfiles.Batch020.valid830
theorem numericValid121 : retention121.NumericValid := by decide +kernel
def certificate121 : RatCutBinCertificate := ⟨⟨retention121,(2268386293046795801/1000000000000000000),(12019078477736559/1000000000000000000),(4056627898521048907/500000000000000000),(199508041444546027759/125000000000000000),(994179920409954563/1000000000000000000)⟩,(99859381993131509/100000000000000000),(98104097445956181/250000000000000000),(240503157365454701/1000000000000000000),(117556300630055461/500000000000000000)⟩
theorem valid121 : certificate121.Valid := by decide +kernel
theorem sound121 : certificate121.Sound := rat_cut_bin_certificate_sound certificate121 profilesValid121 numericValid121 valid121

def retention122 : RatCutRetentionCertificate := ⟨(17/1000),(9/500),(642964773521171531/173833819108730224839),(159149696416131567/250000000000000000),4,(145762533321448337407/64000000000000000000),true,MergedCutProfiles.Batch020.profile831,![MergedCutProfiles.Batch020.profile831,MergedCutProfiles.Batch020.profile832,MergedCutProfiles.Batch020.profile833,MergedCutProfiles.Batch020.profile834,MergedCutProfiles.Batch020.profile835,MergedCutProfiles.Batch020.profile836,MergedCutProfiles.Batch020.profile837,MergedCutProfiles.Batch020.profile838,MergedCutProfiles.Batch020.profile839,MergedCutProfiles.Batch021.profile840,MergedCutProfiles.Batch021.profile841,MergedCutProfiles.Batch021.profile842,MergedCutProfiles.Batch021.profile843,MergedCutProfiles.Batch021.profile844,MergedCutProfiles.Batch021.profile845,MergedCutProfiles.Batch021.profile846]⟩
theorem profilesValid122 : retention122.ProfilesValid := by
  change ∀ j : Fin 16, (retention122.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch020.valid831
  · exact MergedCutProfiles.Batch020.valid832
  · exact MergedCutProfiles.Batch020.valid833
  · exact MergedCutProfiles.Batch020.valid834
  · exact MergedCutProfiles.Batch020.valid835
  · exact MergedCutProfiles.Batch020.valid836
  · exact MergedCutProfiles.Batch020.valid837
  · exact MergedCutProfiles.Batch020.valid838
  · exact MergedCutProfiles.Batch020.valid839
  · exact MergedCutProfiles.Batch021.valid840
  · exact MergedCutProfiles.Batch021.valid841
  · exact MergedCutProfiles.Batch021.valid842
  · exact MergedCutProfiles.Batch021.valid843
  · exact MergedCutProfiles.Batch021.valid844
  · exact MergedCutProfiles.Batch021.valid845
  · exact MergedCutProfiles.Batch021.valid846
theorem numericValid122 : retention122.NumericValid := by decide +kernel
def certificate122 : RatCutBinCertificate := ⟨⟨retention122,(955411694774741523/500000000000000000),(13522397103991873/1000000000000000000),(256818799957362497/31250000000000000),(179417096775373226307/125000000000000000),(1132481552484799721/500000000000000000)⟩,(499342353869091447/500000000000000000),(99290706976384759/200000000000000000),(15589718178198637/100000000000000000),(72105208648347643/1000000000000000000)⟩
theorem valid122 : certificate122.Valid := by decide +kernel
theorem sound122 : certificate122.Sound := rat_cut_bin_certificate_sound certificate122 profilesValid122 numericValid122 valid122

def retention123 : RatCutRetentionCertificate := ⟨(17/1000),(9/500),(117493369650840365/19314868789858913871),(642964773521171531/1000000000000000000),4,(36263268026616572327/16000000000000000000),true,MergedCutProfiles.Batch021.profile847,![MergedCutProfiles.Batch021.profile847,MergedCutProfiles.Batch021.profile848,MergedCutProfiles.Batch020.profile835,MergedCutProfiles.Batch021.profile849,MergedCutProfiles.Batch021.profile850,MergedCutProfiles.Batch021.profile851,MergedCutProfiles.Batch021.profile852,MergedCutProfiles.Batch021.profile843,MergedCutProfiles.Batch021.profile853,MergedCutProfiles.Batch021.profile854,MergedCutProfiles.Batch021.profile855,MergedCutProfiles.Batch021.profile856,MergedCutProfiles.Batch021.profile857,MergedCutProfiles.Batch021.profile858,MergedCutProfiles.Batch021.profile859,MergedCutProfiles.Batch021.profile860]⟩
theorem profilesValid123 : retention123.ProfilesValid := by
  change ∀ j : Fin 16, (retention123.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch021.valid847
  · exact MergedCutProfiles.Batch021.valid848
  · exact MergedCutProfiles.Batch020.valid835
  · exact MergedCutProfiles.Batch021.valid849
  · exact MergedCutProfiles.Batch021.valid850
  · exact MergedCutProfiles.Batch021.valid851
  · exact MergedCutProfiles.Batch021.valid852
  · exact MergedCutProfiles.Batch021.valid843
  · exact MergedCutProfiles.Batch021.valid853
  · exact MergedCutProfiles.Batch021.valid854
  · exact MergedCutProfiles.Batch021.valid855
  · exact MergedCutProfiles.Batch021.valid856
  · exact MergedCutProfiles.Batch021.valid857
  · exact MergedCutProfiles.Batch021.valid858
  · exact MergedCutProfiles.Batch021.valid859
  · exact MergedCutProfiles.Batch021.valid860
theorem numericValid123 : retention123.NumericValid := by decide +kernel
def certificate123 : RatCutBinCertificate := ⟨⟨retention123,(955411694774741523/500000000000000000),(13522397103991873/1000000000000000000),(256818799957362497/31250000000000000),(179417096775373226307/125000000000000000),(18031022191569571/8000000000000000)⟩,(499342353869091447/500000000000000000),(99177258054107229/200000000000000000),(78147363285653249/500000000000000000),(18032223981352919/250000000000000000)⟩
theorem valid123 : certificate123.Valid := by decide +kernel
theorem sound123 : certificate123.Sound := rat_cut_bin_certificate_sound certificate123 profilesValid123 numericValid123 valid123

def retention124 : RatCutRetentionCertificate := ⟨(17/1000),(9/500),(1208543893000000000/173833819108730224839),(211488065371512657/200000000000000000),(27/10),(576808174155665131381/256000000000000000000),true,MergedCutProfiles.Batch021.profile861,![MergedCutProfiles.Batch021.profile861,MergedCutProfiles.Batch021.profile862,MergedCutProfiles.Batch021.profile863,MergedCutProfiles.Batch021.profile864,MergedCutProfiles.Batch021.profile865,MergedCutProfiles.Batch021.profile866,MergedCutProfiles.Batch021.profile843,MergedCutProfiles.Batch021.profile845,MergedCutProfiles.Batch021.profile867,MergedCutProfiles.Batch021.profile868,MergedCutProfiles.Batch021.profile869,MergedCutProfiles.Batch021.profile870,MergedCutProfiles.Batch021.profile871,MergedCutProfiles.Batch021.profile860,MergedCutProfiles.Batch021.profile872,MergedCutProfiles.Batch021.profile873]⟩
theorem profilesValid124 : retention124.ProfilesValid := by
  change ∀ j : Fin 16, (retention124.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch021.valid861
  · exact MergedCutProfiles.Batch021.valid862
  · exact MergedCutProfiles.Batch021.valid863
  · exact MergedCutProfiles.Batch021.valid864
  · exact MergedCutProfiles.Batch021.valid865
  · exact MergedCutProfiles.Batch021.valid866
  · exact MergedCutProfiles.Batch021.valid843
  · exact MergedCutProfiles.Batch021.valid845
  · exact MergedCutProfiles.Batch021.valid867
  · exact MergedCutProfiles.Batch021.valid868
  · exact MergedCutProfiles.Batch021.valid869
  · exact MergedCutProfiles.Batch021.valid870
  · exact MergedCutProfiles.Batch021.valid871
  · exact MergedCutProfiles.Batch021.valid860
  · exact MergedCutProfiles.Batch021.valid872
  · exact MergedCutProfiles.Batch021.valid873
theorem numericValid124 : retention124.NumericValid := by decide +kernel
def certificate124 : RatCutBinCertificate := ⟨⟨retention124,(955411694774741523/500000000000000000),(13522397103991873/1000000000000000000),(256818799957362497/31250000000000000),(179417096775373226307/125000000000000000),(2244667810921206817/1000000000000000000)⟩,(499342353869091447/500000000000000000),(379497056940232407/1000000000000000000),(790008009994123/3125000000000000),(81263683503910729/500000000000000000)⟩
theorem valid124 : certificate124.Valid := by decide +kernel
theorem sound124 : certificate124.Sound := rat_cut_bin_certificate_sound certificate124 profilesValid124 numericValid124 valid124

def retention125 : RatCutRetentionCertificate := ⟨(17/1000),(9/500),(634009356676788043/57944606369576741613),(1208543893/1000000000),(49/20),(17784574417599230249/8000000000000000000),true,MergedCutProfiles.Batch020.profile833,![MergedCutProfiles.Batch020.profile833,MergedCutProfiles.Batch021.profile874,MergedCutProfiles.Batch021.profile875,MergedCutProfiles.Batch021.profile842,MergedCutProfiles.Batch021.profile853,MergedCutProfiles.Batch021.profile876,MergedCutProfiles.Batch021.profile869,MergedCutProfiles.Batch021.profile877,MergedCutProfiles.Batch021.profile878,MergedCutProfiles.Batch021.profile879,MergedCutProfiles.Batch022.profile880,MergedCutProfiles.Batch022.profile881,MergedCutProfiles.Batch022.profile882,MergedCutProfiles.Batch022.profile883,MergedCutProfiles.Batch022.profile884,MergedCutProfiles.Batch022.profile885]⟩
theorem profilesValid125 : retention125.ProfilesValid := by
  change ∀ j : Fin 16, (retention125.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch020.valid833
  · exact MergedCutProfiles.Batch021.valid874
  · exact MergedCutProfiles.Batch021.valid875
  · exact MergedCutProfiles.Batch021.valid842
  · exact MergedCutProfiles.Batch021.valid853
  · exact MergedCutProfiles.Batch021.valid876
  · exact MergedCutProfiles.Batch021.valid869
  · exact MergedCutProfiles.Batch021.valid877
  · exact MergedCutProfiles.Batch021.valid878
  · exact MergedCutProfiles.Batch021.valid879
  · exact MergedCutProfiles.Batch022.valid880
  · exact MergedCutProfiles.Batch022.valid881
  · exact MergedCutProfiles.Batch022.valid882
  · exact MergedCutProfiles.Batch022.valid883
  · exact MergedCutProfiles.Batch022.valid884
  · exact MergedCutProfiles.Batch022.valid885
theorem numericValid125 : retention125.NumericValid := by decide +kernel
def certificate125 : RatCutBinCertificate := ⟨⟨retention125,(955411694774741523/500000000000000000),(13522397103991873/1000000000000000000),(256818799957362497/31250000000000000),(179417096775373226307/125000000000000000),(2163446009087753/976562500000000)⟩,(499342353869091447/500000000000000000),(361243398610071609/1000000000000000000),(54186631867032799/200000000000000000),(23424028250846671/125000000000000000)⟩
theorem valid125 : certificate125.Valid := by decide +kernel
theorem sound125 : certificate125.Sound := rat_cut_bin_certificate_sound certificate125 profilesValid125 numericValid125 valid125

def retention126 : RatCutRetentionCertificate := ⟨(17/1000),(9/500),(25787951989525619557/173833819108730224839),(1902028070030364129/1000000000000000000),(37/20),(5360792352188060539258724891063890946591/3043244912048582606400000000000000000000),false,MergedCutProfiles.Batch022.profile886,(fun _ => MergedCutProfiles.Batch022.profile886)⟩
theorem profilesValid126 : retention126.ProfilesValid := by
  exact MergedCutProfiles.Batch022.valid886
theorem numericValid126 : retention126.NumericValid := by decide +kernel
def certificate126 : RatCutBinCertificate := ⟨⟨retention126,(955411694774741523/500000000000000000),(13522397103991873/1000000000000000000),(256818799957362497/31250000000000000),(179417096775373226307/125000000000000000),(1755721646453480197/1000000000000000000)⟩,(499342353869091447/500000000000000000),(190444986174674939/500000000000000000),(6286390215078619/25000000000000000),(187672558122022103/1000000000000000000)⟩
theorem valid126 : certificate126.Valid := by decide +kernel
theorem sound126 : certificate126.Sound := rat_cut_bin_certificate_sound certificate126 profilesValid126 numericValid126 valid126

def retention127 : RatCutRetentionCertificate := ⟨(17/1000),(9/500),(64000000000000000000/173833819108730224839),(25787951989525619557/1000000000000000000),1,(4042110974607518681642282539141697481/3223493998690702444625000000000000000),false,MergedCutProfiles.Batch022.profile887,(fun _ => MergedCutProfiles.Batch022.profile887)⟩
theorem profilesValid127 : retention127.ProfilesValid := by
  exact MergedCutProfiles.Batch022.valid887
theorem numericValid127 : retention127.NumericValid := by decide +kernel
def certificate127 : RatCutBinCertificate := ⟨⟨retention127,(955411694774741523/500000000000000000),(13522397103991873/1000000000000000000),(256818799957362497/31250000000000000),(179417096775373226307/125000000000000000),(312702300636891963/250000000000000000)⟩,(499342353869091447/500000000000000000),(91219135355185189/250000000000000000),(267252509261770053/1000000000000000000),(39798800115728639/125000000000000000)⟩
theorem valid127 : certificate127.Valid := by decide +kernel
theorem sound127 : certificate127.Sound := rat_cut_bin_certificate_sound certificate127 profilesValid127 numericValid127 valid127

def retention128 : RatCutRetentionCertificate := ⟨(17/1000),(9/500),(1/2),64,1,(63842651577774958124598119296594031199/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch022.profile888,(fun _ => MergedCutProfiles.Batch022.profile888)⟩
theorem profilesValid128 : retention128.ProfilesValid := by
  exact MergedCutProfiles.Batch022.valid888
theorem numericValid128 : retention128.NumericValid := by decide +kernel
def certificate128 : RatCutBinCertificate := ⟨⟨retention128,(955411694774741523/500000000000000000),(13522397103991873/1000000000000000000),(256818799957362497/31250000000000000),(179417096775373226307/125000000000000000),(24859933063196479/25000000000000000)⟩,(499342353869091447/500000000000000000),(448809713166170419/1000000000000000000),(191623275485596473/1000000000000000000),(37477095876465223/200000000000000000)⟩
theorem valid128 : certificate128.Valid := by decide +kernel
theorem sound128 : certificate128.Sound := rat_cut_bin_certificate_sound certificate128 profilesValid128 numericValid128 valid128

def retention129 : RatCutRetentionCertificate := ⟨(17/1000),(9/500),(64000000000000000000/173833819108730224839),(706094556336518541/200000000000000000),(13/10),(23846099148223574438374555207493141733/18829188168973827760000000000000000000),false,MergedCutProfiles.Batch022.profile887,(fun _ => MergedCutProfiles.Batch022.profile887)⟩
theorem profilesValid129 : retention129.ProfilesValid := by
  exact MergedCutProfiles.Batch022.valid887
theorem numericValid129 : retention129.NumericValid := by decide +kernel
def certificate129 : RatCutBinCertificate := ⟨⟨retention129,(1138399246774741523/500000000000000000),(13522397103991873/1000000000000000000),(256818799957362497/31250000000000000),(179417096775373226307/125000000000000000),(630786554554263029/500000000000000000)⟩,(998432788381115373/1000000000000000000),(307446759372958273/1000000000000000000),(164957647091358733/500000000000000000),(131917440918503409/500000000000000000)⟩
theorem valid129 : certificate129.Valid := by decide +kernel
theorem sound129 : certificate129.Sound := rat_cut_bin_certificate_sound certificate129 profilesValid129 numericValid129 valid129

def retention130 : RatCutRetentionCertificate := ⟨(17/1000),(9/500),(1/2),64,1,(63842651577774958124598119296594031199/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch022.profile888,(fun _ => MergedCutProfiles.Batch022.profile888)⟩
theorem profilesValid130 : retention130.ProfilesValid := by
  exact MergedCutProfiles.Batch022.valid888
theorem numericValid130 : retention130.NumericValid := by decide +kernel
def certificate130 : RatCutBinCertificate := ⟨⟨retention130,(1138399246774741523/500000000000000000),(13522397103991873/1000000000000000000),(256818799957362497/31250000000000000),(179417096775373226307/125000000000000000),(397518055805221/400000000000000)⟩,(998432788381115373/1000000000000000000),(390288248237492619/1000000000000000000),(242499558624688769/1000000000000000000),(236935429549155737/1000000000000000000)⟩
theorem valid130 : certificate130.Valid := by decide +kernel
theorem sound130 : certificate130.Sound := rat_cut_bin_certificate_sound certificate130 profilesValid130 numericValid130 valid130

def retention131 : RatCutRetentionCertificate := ⟨(9/500),(19/1000),(650180900073611281/155280714373951182740),(643743465419417109/1000000000000000000),4,(584121143462486321229/256000000000000000000),true,MergedCutProfiles.Batch022.profile889,![MergedCutProfiles.Batch022.profile889,MergedCutProfiles.Batch022.profile890,MergedCutProfiles.Batch022.profile891,MergedCutProfiles.Batch022.profile892,MergedCutProfiles.Batch022.profile893,MergedCutProfiles.Batch022.profile894,MergedCutProfiles.Batch022.profile895,MergedCutProfiles.Batch022.profile896,MergedCutProfiles.Batch022.profile897,MergedCutProfiles.Batch022.profile898,MergedCutProfiles.Batch022.profile899,MergedCutProfiles.Batch022.profile900,MergedCutProfiles.Batch022.profile901,MergedCutProfiles.Batch022.profile902,MergedCutProfiles.Batch022.profile903,MergedCutProfiles.Batch022.profile904]⟩
theorem profilesValid131 : retention131.ProfilesValid := by
  change ∀ j : Fin 16, (retention131.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch022.valid889
  · exact MergedCutProfiles.Batch022.valid890
  · exact MergedCutProfiles.Batch022.valid891
  · exact MergedCutProfiles.Batch022.valid892
  · exact MergedCutProfiles.Batch022.valid893
  · exact MergedCutProfiles.Batch022.valid894
  · exact MergedCutProfiles.Batch022.valid895
  · exact MergedCutProfiles.Batch022.valid896
  · exact MergedCutProfiles.Batch022.valid897
  · exact MergedCutProfiles.Batch022.valid898
  · exact MergedCutProfiles.Batch022.valid899
  · exact MergedCutProfiles.Batch022.valid900
  · exact MergedCutProfiles.Batch022.valid901
  · exact MergedCutProfiles.Batch022.valid902
  · exact MergedCutProfiles.Batch022.valid903
  · exact MergedCutProfiles.Batch022.valid904
theorem numericValid131 : retention131.NumericValid := by decide +kernel
def certificate131 : RatCutBinCertificate := ⟨⟨retention131,(958950628382366181/500000000000000000),(15120529320228081/1000000000000000000),(4162624447707471869/500000000000000000),(649440413585474310029/500000000000000000),(2267789788999021319/1000000000000000000)⟩,(499271678933108497/500000000000000000),(489989727309601957/1000000000000000000),(160465810891582111/1000000000000000000),(74432327164241043/1000000000000000000)⟩
theorem valid131 : certificate131.Valid := by decide +kernel
theorem sound131 : certificate131.Sound := rat_cut_bin_certificate_sound certificate131 profilesValid131 numericValid131 valid131

def certificates : List RatCutBinCertificate := [certificate120,certificate121,certificate122,certificate123,certificate124,certificate125,certificate126,certificate127,certificate128,certificate129,certificate130,certificate131]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound120,List.forall_mem_cons.mpr ⟨sound121,List.forall_mem_cons.mpr ⟨sound122,List.forall_mem_cons.mpr ⟨sound123,List.forall_mem_cons.mpr ⟨sound124,List.forall_mem_cons.mpr ⟨sound125,List.forall_mem_cons.mpr ⟨sound126,List.forall_mem_cons.mpr ⟨sound127,List.forall_mem_cons.mpr ⟨sound128,List.forall_mem_cons.mpr ⟨sound129,List.forall_mem_cons.mpr ⟨sound130,List.forall_mem_cons.mpr ⟨sound131,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch010
