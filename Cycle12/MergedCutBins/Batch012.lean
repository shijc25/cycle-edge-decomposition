import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch024
import Cycle12.MergedCutProfiles.Batch025
import Cycle12.MergedCutProfiles.Batch026

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch012

def retention144 : RatCutRetentionCertificate := ⟨(19/1000),(1/50),(1502082892129141934/139475608349223280593),(1177044509/1000000000),(5/2),(8908805898678406473/4000000000000000000),true,MergedCutProfiles.Batch024.profile990,![MergedCutProfiles.Batch024.profile990,MergedCutProfiles.Batch024.profile991,MergedCutProfiles.Batch024.profile992,MergedCutProfiles.Batch024.profile993,MergedCutProfiles.Batch024.profile994,MergedCutProfiles.Batch024.profile995,MergedCutProfiles.Batch024.profile964,MergedCutProfiles.Batch024.profile996,MergedCutProfiles.Batch024.profile997,MergedCutProfiles.Batch024.profile998,MergedCutProfiles.Batch024.profile999,MergedCutProfiles.Batch025.profile1000,MergedCutProfiles.Batch025.profile1001,MergedCutProfiles.Batch025.profile1002,MergedCutProfiles.Batch025.profile1003,MergedCutProfiles.Batch025.profile1004]⟩
theorem profilesValid144 : retention144.ProfilesValid := by
  change ∀ j : Fin 16, (retention144.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch024.valid990
  · exact MergedCutProfiles.Batch024.valid991
  · exact MergedCutProfiles.Batch024.valid992
  · exact MergedCutProfiles.Batch024.valid993
  · exact MergedCutProfiles.Batch024.valid994
  · exact MergedCutProfiles.Batch024.valid995
  · exact MergedCutProfiles.Batch024.valid964
  · exact MergedCutProfiles.Batch024.valid996
  · exact MergedCutProfiles.Batch024.valid997
  · exact MergedCutProfiles.Batch024.valid998
  · exact MergedCutProfiles.Batch024.valid999
  · exact MergedCutProfiles.Batch025.valid1000
  · exact MergedCutProfiles.Batch025.valid1001
  · exact MergedCutProfiles.Batch025.valid1002
  · exact MergedCutProfiles.Batch025.valid1003
  · exact MergedCutProfiles.Batch025.valid1004
theorem numericValid144 : retention144.NumericValid := by decide +kernel
def certificate144 : RatCutBinCertificate := ⟨⟨retention144,(120338172838091963/62500000000000000),(16814618099358171/1000000000000000000),(4217227099650750953/500000000000000000),(1182011536263273450937/1000000000000000000),(2217605357822559409/1000000000000000000)⟩,(199679132671688709/200000000000000000),(90882823111930987/250000000000000000),(134305558410278107/500000000000000000),(1427699073032613/7812500000000000)⟩
theorem valid144 : certificate144.Valid := by decide +kernel
theorem sound144 : certificate144.Sound := rat_cut_bin_certificate_sound certificate144 profilesValid144 numericValid144 valid144

def retention145 : RatCutRetentionCertificate := ⟨(19/1000),(1/50),(10880460647272425188/139475608349223280593),(751041446064570967/500000000000000000),(43/20),(1176084501698380306121034235922452687879/600833156851656773600000000000000000000),false,MergedCutProfiles.Batch025.profile1005,(fun _ => MergedCutProfiles.Batch025.profile1005)⟩
theorem profilesValid145 : retention145.ProfilesValid := by
  exact MergedCutProfiles.Batch025.valid1005
theorem numericValid145 : retention145.NumericValid := by decide +kernel
def certificate145 : RatCutBinCertificate := ⟨⟨retention145,(120338172838091963/62500000000000000),(16814618099358171/1000000000000000000),(4217227099650750953/500000000000000000),(1182011536263273450937/1000000000000000000),(1949170112233121481/1000000000000000000)⟩,(199679132671688709/200000000000000000),(93378569044160503/250000000000000000),(12932313179303617/50000000000000000),(91378560117945669/500000000000000000)⟩
theorem valid145 : certificate145.Valid := by decide +kernel
theorem sound145 : certificate145.Sound := rat_cut_bin_certificate_sound certificate145 profilesValid145 numericValid145 valid145

def retention146 : RatCutRetentionCertificate := ⟨(19/1000),(1/50),(62691558762781485274/139475608349223280593),(2720115161818106297/250000000000000000),(21/20),(170352086519946246139919549977684616873/155435152103891788400000000000000000000),false,MergedCutProfiles.Batch025.profile1006,(fun _ => MergedCutProfiles.Batch025.profile1006)⟩
theorem profilesValid146 : retention146.ProfilesValid := by
  exact MergedCutProfiles.Batch025.valid1006
theorem numericValid146 : retention146.NumericValid := by decide +kernel
def certificate146 : RatCutBinCertificate := ⟨⟨retention146,(120338172838091963/62500000000000000),(16814618099358171/1000000000000000000),(4217227099650750953/500000000000000000),(1182011536263273450937/1000000000000000000),(545969252902999413/500000000000000000)⟩,(199679132671688709/200000000000000000),(110854722267360089/250000000000000000),(48993654651242073/250000000000000000),(93242886550271361/500000000000000000)⟩
theorem valid146 : certificate146.Valid := by decide +kernel
theorem sound146 : certificate146.Sound := rat_cut_bin_certificate_sound certificate146 profilesValid146 numericValid146 valid146

def retention147 : RatCutRetentionCertificate := ⟨(19/1000),(1/50),(64000000000000000000/139475608349223280593),(31345779381390742637/500000000000000000),1,(16918863152092333030976405332980387369/15672889690695371318500000000000000000),false,MergedCutProfiles.Batch025.profile1007,(fun _ => MergedCutProfiles.Batch025.profile1007)⟩
theorem profilesValid147 : retention147.ProfilesValid := by
  exact MergedCutProfiles.Batch025.valid1007
theorem numericValid147 : retention147.NumericValid := by decide +kernel
def certificate147 : RatCutBinCertificate := ⟨⟨retention147,(120338172838091963/62500000000000000),(16814618099358171/1000000000000000000),(4217227099650750953/500000000000000000),(1182011536263273450937/1000000000000000000),(215132042777742011/200000000000000000)⟩,(199679132671688709/200000000000000000),(210060556072117543/500000000000000000),(215543990013814953/1000000000000000000),(227572317757494029/1000000000000000000)⟩
theorem valid147 : certificate147.Valid := by decide +kernel
theorem sound147 : certificate147.Sound := rat_cut_bin_certificate_sound certificate147 profilesValid147 numericValid147 valid147

def retention148 : RatCutRetentionCertificate := ⟨(19/1000),(1/50),(1/2),64,1,(3990175631981414592578765135707307871/4000000000000000000000000000000000000),false,MergedCutProfiles.Batch025.profile1008,(fun _ => MergedCutProfiles.Batch025.profile1008)⟩
theorem profilesValid148 : retention148.ProfilesValid := by
  exact MergedCutProfiles.Batch025.valid1008
theorem numericValid148 : retention148.NumericValid := by decide +kernel
def certificate148 : RatCutBinCertificate := ⟨⟨retention148,(120338172838091963/62500000000000000),(16814618099358171/1000000000000000000),(4217227099650750953/500000000000000000),(1182011536263273450937/1000000000000000000),(99370547895942267/100000000000000000)⟩,(199679132671688709/200000000000000000),(454630663546113491/1000000000000000000),(11687338805594581/62500000000000000),(182683324208660877/1000000000000000000)⟩
theorem valid148 : certificate148.Valid := by decide +kernel
theorem sound148 : certificate148.Sound := rat_cut_bin_certificate_sound certificate148 profilesValid148 numericValid148 valid148

def retention149 : RatCutRetentionCertificate := ⟨(19/1000),(1/50),(18743156066280581741/46491869449741093531),(3501875410708896779/1000000000000000000),(13/10),(1675239372842907620227948293779478401791/1400750164283558711600000000000000000000),false,MergedCutProfiles.Batch025.profile1009,(fun _ => MergedCutProfiles.Batch025.profile1009)⟩
theorem profilesValid149 : retention149.ProfilesValid := by
  exact MergedCutProfiles.Batch025.valid1009
theorem numericValid149 : retention149.NumericValid := by decide +kernel
def certificate149 : RatCutBinCertificate := ⟨⟨retention149,(143446950650591963/62500000000000000),(16814618099358171/1000000000000000000),(4217227099650750953/500000000000000000),(1182011536263273450937/1000000000000000000),(595005256516366733/500000000000000000)⟩,(99808757036817497/100000000000000000),(336147082464936729/1000000000000000000),(297374615682954579/1000000000000000000),(4523457493499581/20000000000000000)⟩
theorem valid149 : certificate149.Valid := by decide +kernel
theorem sound149 : certificate149.Sound := rat_cut_bin_certificate_sound certificate149 profilesValid149 numericValid149 valid149

def retention150 : RatCutRetentionCertificate := ⟨(19/1000),(1/50),(64000000000000000000/139475608349223280593),(56229468198841745223/1000000000000000000),1,(7583667968744449030232037531254850901/7028683524855218152875000000000000000),false,MergedCutProfiles.Batch025.profile1007,(fun _ => MergedCutProfiles.Batch025.profile1007)⟩
theorem profilesValid150 : retention150.ProfilesValid := by
  exact MergedCutProfiles.Batch025.valid1007
theorem numericValid150 : retention150.NumericValid := by decide +kernel
def certificate150 : RatCutBinCertificate := ⟨⟨retention150,(143446950650591963/62500000000000000),(16814618099358171/1000000000000000000),(4217227099650750953/500000000000000000),(1182011536263273450937/1000000000000000000),(1074384411750098663/1000000000000000000)⟩,(99808757036817497/100000000000000000),(372323497701305127/1000000000000000000),(259820736744344817/1000000000000000000),(136692845151451017/500000000000000000)⟩
theorem valid150 : certificate150.Valid := by decide +kernel
theorem sound150 : certificate150.Sound := rat_cut_bin_certificate_sound certificate150 profilesValid150 numericValid150 valid150

def retention151 : RatCutRetentionCertificate := ⟨(19/1000),(1/50),(1/2),64,1,(3990175631981414592578765135707307871/4000000000000000000000000000000000000),false,MergedCutProfiles.Batch025.profile1008,(fun _ => MergedCutProfiles.Batch025.profile1008)⟩
theorem profilesValid151 : retention151.ProfilesValid := by
  exact MergedCutProfiles.Batch025.valid1008
theorem numericValid151 : retention151.NumericValid := by decide +kernel
def certificate151 : RatCutBinCertificate := ⟨⟨retention151,(143446950650591963/62500000000000000),(16814618099358171/1000000000000000000),(4217227099650750953/500000000000000000),(1182011536263273450937/1000000000000000000),(496484188912387531/500000000000000000)⟩,(99808757036817497/100000000000000000),(201425629955531931/500000000000000000),(230880029541106449/1000000000000000000),(225319239571505363/1000000000000000000)⟩
theorem valid151 : certificate151.Valid := by decide +kernel
theorem sound151 : certificate151.Sound := rat_cut_bin_certificate_sound certificate151 profilesValid151 numericValid151 valid151

def retention152 : RatCutRetentionCertificate := ⟨(1/50),(21/1000),(672013381012651627/125904482924188692167),(164693015638822573/250000000000000000),4,(9147385704953036887/4000000000000000000),true,MergedCutProfiles.Batch025.profile1010,![MergedCutProfiles.Batch025.profile1010,MergedCutProfiles.Batch025.profile1011,MergedCutProfiles.Batch025.profile1012,MergedCutProfiles.Batch025.profile1013,MergedCutProfiles.Batch025.profile1014,MergedCutProfiles.Batch025.profile1015,MergedCutProfiles.Batch025.profile1016,MergedCutProfiles.Batch025.profile1017,MergedCutProfiles.Batch025.profile1018,MergedCutProfiles.Batch025.profile1019,MergedCutProfiles.Batch025.profile1020,MergedCutProfiles.Batch025.profile1021,MergedCutProfiles.Batch025.profile1022,MergedCutProfiles.Batch025.profile1023,MergedCutProfiles.Batch025.profile1024,MergedCutProfiles.Batch025.profile1025]⟩
theorem profilesValid152 : retention152.ProfilesValid := by
  change ∀ j : Fin 16, (retention152.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch025.valid1010
  · exact MergedCutProfiles.Batch025.valid1011
  · exact MergedCutProfiles.Batch025.valid1012
  · exact MergedCutProfiles.Batch025.valid1013
  · exact MergedCutProfiles.Batch025.valid1014
  · exact MergedCutProfiles.Batch025.valid1015
  · exact MergedCutProfiles.Batch025.valid1016
  · exact MergedCutProfiles.Batch025.valid1017
  · exact MergedCutProfiles.Batch025.valid1018
  · exact MergedCutProfiles.Batch025.valid1019
  · exact MergedCutProfiles.Batch025.valid1020
  · exact MergedCutProfiles.Batch025.valid1021
  · exact MergedCutProfiles.Batch025.valid1022
  · exact MergedCutProfiles.Batch025.valid1023
  · exact MergedCutProfiles.Batch025.valid1024
  · exact MergedCutProfiles.Batch025.valid1025
theorem numericValid152 : retention152.NumericValid := by decide +kernel
def certificate152 : RatCutBinCertificate := ⟨⟨retention152,(967578226972775499/500000000000000000),(1860584005120499/100000000000000000),(8545876015757703223/1000000000000000000),(135140731992612482481/125000000000000000),(567498411032408929/250000000000000000)⟩,(249560024619351623/250000000000000000),(95055207961789367/200000000000000000),(2139815492576101/12500000000000000),(39884328646750873/500000000000000000)⟩
theorem valid152 : certificate152.Valid := by decide +kernel
theorem sound152 : certificate152.Sound := rat_cut_bin_certificate_sound certificate152 profilesValid152 numericValid152 valid152

def retention153 : RatCutRetentionCertificate := ⟨(1/50),(21/1000),(1160097462000000000/125904482924188692167),(672013381012651627/1000000000000000000),(79/20),(2893758029525310424411/1280000000000000000000),true,MergedCutProfiles.Batch025.profile1026,![MergedCutProfiles.Batch025.profile1026,MergedCutProfiles.Batch025.profile1027,MergedCutProfiles.Batch025.profile1028,MergedCutProfiles.Batch025.profile1016,MergedCutProfiles.Batch025.profile1029,MergedCutProfiles.Batch025.profile1030,MergedCutProfiles.Batch025.profile1031,MergedCutProfiles.Batch025.profile1023,MergedCutProfiles.Batch025.profile1032,MergedCutProfiles.Batch025.profile1033,MergedCutProfiles.Batch025.profile1034,MergedCutProfiles.Batch025.profile1035,MergedCutProfiles.Batch025.profile1036,MergedCutProfiles.Batch025.profile1037,MergedCutProfiles.Batch025.profile1038,MergedCutProfiles.Batch025.profile1039]⟩
theorem profilesValid153 : retention153.ProfilesValid := by
  change ∀ j : Fin 16, (retention153.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch025.valid1026
  · exact MergedCutProfiles.Batch025.valid1027
  · exact MergedCutProfiles.Batch025.valid1028
  · exact MergedCutProfiles.Batch025.valid1016
  · exact MergedCutProfiles.Batch025.valid1029
  · exact MergedCutProfiles.Batch025.valid1030
  · exact MergedCutProfiles.Batch025.valid1031
  · exact MergedCutProfiles.Batch025.valid1023
  · exact MergedCutProfiles.Batch025.valid1032
  · exact MergedCutProfiles.Batch025.valid1033
  · exact MergedCutProfiles.Batch025.valid1034
  · exact MergedCutProfiles.Batch025.valid1035
  · exact MergedCutProfiles.Batch025.valid1036
  · exact MergedCutProfiles.Batch025.valid1037
  · exact MergedCutProfiles.Batch025.valid1038
  · exact MergedCutProfiles.Batch025.valid1039
theorem numericValid153 : retention153.NumericValid := by decide +kernel
def certificate153 : RatCutBinCertificate := ⟨⟨retention153,(967578226972775499/500000000000000000),(1860584005120499/100000000000000000),(8545876015757703223/1000000000000000000),(135140731992612482481/125000000000000000),(17952850712218249/8000000000000000)⟩,(249560024619351623/250000000000000000),(475205258128545117/1000000000000000000),(85618948006516761/500000000000000000),(79969655604219127/1000000000000000000)⟩
theorem valid153 : certificate153.Valid := by decide +kernel
theorem sound153 : certificate153.Sound := rat_cut_bin_certificate_sound certificate153 profilesValid153 numericValid153 valid153

def retention154 : RatCutRetentionCertificate := ⟨(1/50),(21/1000),(1335219639690811114/125904482924188692167),(580048731/500000000),(5/2),(17786006637442133647/8000000000000000000),true,MergedCutProfiles.Batch025.profile1011,![MergedCutProfiles.Batch025.profile1011,MergedCutProfiles.Batch025.profile1013,MergedCutProfiles.Batch025.profile1015,MergedCutProfiles.Batch025.profile1017,MergedCutProfiles.Batch026.profile1040,MergedCutProfiles.Batch025.profile1021,MergedCutProfiles.Batch025.profile1023,MergedCutProfiles.Batch025.profile1025,MergedCutProfiles.Batch026.profile1041,MergedCutProfiles.Batch026.profile1042,MergedCutProfiles.Batch026.profile1043,MergedCutProfiles.Batch026.profile1044,MergedCutProfiles.Batch025.profile1038,MergedCutProfiles.Batch026.profile1045,MergedCutProfiles.Batch026.profile1046,MergedCutProfiles.Batch026.profile1047]⟩
theorem profilesValid154 : retention154.ProfilesValid := by
  change ∀ j : Fin 16, (retention154.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch025.valid1011
  · exact MergedCutProfiles.Batch025.valid1013
  · exact MergedCutProfiles.Batch025.valid1015
  · exact MergedCutProfiles.Batch025.valid1017
  · exact MergedCutProfiles.Batch026.valid1040
  · exact MergedCutProfiles.Batch025.valid1021
  · exact MergedCutProfiles.Batch025.valid1023
  · exact MergedCutProfiles.Batch025.valid1025
  · exact MergedCutProfiles.Batch026.valid1041
  · exact MergedCutProfiles.Batch026.valid1042
  · exact MergedCutProfiles.Batch026.valid1043
  · exact MergedCutProfiles.Batch026.valid1044
  · exact MergedCutProfiles.Batch025.valid1038
  · exact MergedCutProfiles.Batch026.valid1045
  · exact MergedCutProfiles.Batch026.valid1046
  · exact MergedCutProfiles.Batch026.valid1047
theorem numericValid154 : retention154.NumericValid := by decide +kernel
def certificate154 : RatCutBinCertificate := ⟨⟨retention154,(967578226972775499/500000000000000000),(1860584005120499/100000000000000000),(8545876015757703223/1000000000000000000),(135140731992612482481/125000000000000000),(553179461787884277/250000000000000000)⟩,(249560024619351623/250000000000000000),(91013744468195247/250000000000000000),(268081641019763849/1000000000000000000),(7257223256272531/40000000000000000)⟩
theorem valid154 : certificate154.Valid := by decide +kernel
theorem sound154 : certificate154.Sound := rat_cut_bin_certificate_sound certificate154 profilesValid154 numericValid154 valid154

def retention155 : RatCutRetentionCertificate := ⟨(1/50),(21/1000),(6119598091029033036/125904482924188692167),(667609819845405557/500000000000000000),(9/4),(262752905709345150537/128000000000000000000),true,MergedCutProfiles.Batch025.profile1018,![MergedCutProfiles.Batch025.profile1018,MergedCutProfiles.Batch026.profile1048,MergedCutProfiles.Batch026.profile1049,MergedCutProfiles.Batch026.profile1050,MergedCutProfiles.Batch026.profile1051,MergedCutProfiles.Batch026.profile1052,MergedCutProfiles.Batch026.profile1053,MergedCutProfiles.Batch026.profile1054,MergedCutProfiles.Batch026.profile1055,MergedCutProfiles.Batch026.profile1056,MergedCutProfiles.Batch026.profile1057,MergedCutProfiles.Batch026.profile1058,MergedCutProfiles.Batch026.profile1059,MergedCutProfiles.Batch026.profile1060,MergedCutProfiles.Batch026.profile1061,MergedCutProfiles.Batch026.profile1062]⟩
theorem profilesValid155 : retention155.ProfilesValid := by
  change ∀ j : Fin 16, (retention155.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch025.valid1018
  · exact MergedCutProfiles.Batch026.valid1048
  · exact MergedCutProfiles.Batch026.valid1049
  · exact MergedCutProfiles.Batch026.valid1050
  · exact MergedCutProfiles.Batch026.valid1051
  · exact MergedCutProfiles.Batch026.valid1052
  · exact MergedCutProfiles.Batch026.valid1053
  · exact MergedCutProfiles.Batch026.valid1054
  · exact MergedCutProfiles.Batch026.valid1055
  · exact MergedCutProfiles.Batch026.valid1056
  · exact MergedCutProfiles.Batch026.valid1057
  · exact MergedCutProfiles.Batch026.valid1058
  · exact MergedCutProfiles.Batch026.valid1059
  · exact MergedCutProfiles.Batch026.valid1060
  · exact MergedCutProfiles.Batch026.valid1061
  · exact MergedCutProfiles.Batch026.valid1062
theorem numericValid155 : retention155.NumericValid := by decide +kernel
def certificate155 : RatCutBinCertificate := ⟨⟨retention155,(967578226972775499/500000000000000000),(1860584005120499/100000000000000000),(8545876015757703223/1000000000000000000),(135140731992612482481/125000000000000000),(25540967419071129/12500000000000000)⟩,(249560024619351623/250000000000000000),(371190222591946067/1000000000000000000),(130471013725549209/500000000000000000),(18159951775226847/100000000000000000)⟩
theorem valid155 : certificate155.Valid := by decide +kernel
theorem sound155 : certificate155.Sound := rat_cut_bin_certificate_sound certificate155 profilesValid155 numericValid155 valid155

def certificates : List RatCutBinCertificate := [certificate144,certificate145,certificate146,certificate147,certificate148,certificate149,certificate150,certificate151,certificate152,certificate153,certificate154,certificate155]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound144,List.forall_mem_cons.mpr ⟨sound145,List.forall_mem_cons.mpr ⟨sound146,List.forall_mem_cons.mpr ⟨sound147,List.forall_mem_cons.mpr ⟨sound148,List.forall_mem_cons.mpr ⟨sound149,List.forall_mem_cons.mpr ⟨sound150,List.forall_mem_cons.mpr ⟨sound151,List.forall_mem_cons.mpr ⟨sound152,List.forall_mem_cons.mpr ⟨sound153,List.forall_mem_cons.mpr ⟨sound154,List.forall_mem_cons.mpr ⟨sound155,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch012
