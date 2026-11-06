import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch151
import Cycle12.MergedCutProfiles.Batch152
import Cycle12.MergedCutProfiles.Batch153

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch075

def retention900 : RatCutRetentionCertificate := ⟨(199/4000),(1/20),(128614658567378569/1734323001295199709),(182630245761339553/200000000000000000),(27/10),(126502659876850304193/64000000000000000000),true,MergedCutProfiles.Batch152.profile6097,![MergedCutProfiles.Batch152.profile6097,MergedCutProfiles.Batch152.profile6098,MergedCutProfiles.Batch151.profile6069,MergedCutProfiles.Batch152.profile6099,MergedCutProfiles.Batch152.profile6100,MergedCutProfiles.Batch152.profile6101,MergedCutProfiles.Batch152.profile6102,MergedCutProfiles.Batch152.profile6103,MergedCutProfiles.Batch151.profile6079,MergedCutProfiles.Batch152.profile6104,MergedCutProfiles.Batch152.profile6105,MergedCutProfiles.Batch152.profile6106,MergedCutProfiles.Batch152.profile6107,MergedCutProfiles.Batch152.profile6108,MergedCutProfiles.Batch152.profile6109,MergedCutProfiles.Batch152.profile6110]⟩
theorem profilesValid900 : retention900.ProfilesValid := by
  change ∀ j : Fin 16, (retention900.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch152.valid6097
  · exact MergedCutProfiles.Batch152.valid6098
  · exact MergedCutProfiles.Batch151.valid6069
  · exact MergedCutProfiles.Batch152.valid6099
  · exact MergedCutProfiles.Batch152.valid6100
  · exact MergedCutProfiles.Batch152.valid6101
  · exact MergedCutProfiles.Batch152.valid6102
  · exact MergedCutProfiles.Batch152.valid6103
  · exact MergedCutProfiles.Batch151.valid6079
  · exact MergedCutProfiles.Batch152.valid6104
  · exact MergedCutProfiles.Batch152.valid6105
  · exact MergedCutProfiles.Batch152.valid6106
  · exact MergedCutProfiles.Batch152.valid6107
  · exact MergedCutProfiles.Batch152.valid6108
  · exact MergedCutProfiles.Batch152.valid6109
  · exact MergedCutProfiles.Batch152.valid6110
theorem numericValid900 : retention900.NumericValid := by decide +kernel
def certificate900 : RatCutBinCertificate := ⟨⟨retention900,(216391810996116503/100000000000000000),(59865971199444307/500000000000000000),(1326455612614145873/100000000000000000),(6335438781896511673/25000000000000000),(961928084269051153/500000000000000000)⟩,(992464092671492243/1000000000000000000),(15093035037326977/40000000000000000),(127456149063149203/500000000000000000),(8728367684205601/62500000000000000)⟩
theorem valid900 : certificate900.Valid := by decide +kernel
theorem sound900 : certificate900.Sound := rat_cut_bin_certificate_sound certificate900 profilesValid900 numericValid900 valid900

def retention901 : RatCutRetentionCertificate := ⟨(199/4000),(1/20),(384274516887688969/1734323001295199709),(1414761244241164259/1000000000000000000),(39/20),(3587667189583194662542684293070007853719/2263617990785862814400000000000000000000),false,MergedCutProfiles.Batch152.profile6111,(fun _ => MergedCutProfiles.Batch152.profile6111)⟩
theorem profilesValid901 : retention901.ProfilesValid := by
  exact MergedCutProfiles.Batch152.valid6111
theorem numericValid901 : retention901.NumericValid := by decide +kernel
def certificate901 : RatCutBinCertificate := ⟨⟨retention901,(216391810996116503/100000000000000000),(59865971199444307/500000000000000000),(1326455612614145873/100000000000000000),(6335438781896511673/25000000000000000),(77341557824213313/50000000000000000)⟩,(992464092671492243/1000000000000000000),(404334320206877517/1000000000000000000),(57383607518951029/250000000000000000),(28034858816742189/200000000000000000)⟩
theorem valid901 : certificate901.Valid := by decide +kernel
theorem sound901 : certificate901.Sound := rat_cut_bin_certificate_sound certificate901 profilesValid901 numericValid901 valid901

def retention902 : RatCutRetentionCertificate := ⟨(199/4000),(1/20),(8398641844434180508/19077553014247196799),(4227019685764578659/1000000000000000000),(11/10),(1401437106956454169367/1280000000000000000000),true,MergedCutProfiles.Batch152.profile6112,![MergedCutProfiles.Batch152.profile6112,MergedCutProfiles.Batch152.profile6113,MergedCutProfiles.Batch152.profile6114,MergedCutProfiles.Batch152.profile6115,MergedCutProfiles.Batch152.profile6116,MergedCutProfiles.Batch152.profile6117,MergedCutProfiles.Batch152.profile6118,MergedCutProfiles.Batch152.profile6119,MergedCutProfiles.Batch153.profile6120,MergedCutProfiles.Batch153.profile6121,MergedCutProfiles.Batch153.profile6122,MergedCutProfiles.Batch153.profile6123,MergedCutProfiles.Batch153.profile6124,MergedCutProfiles.Batch153.profile6125,MergedCutProfiles.Batch153.profile6126,MergedCutProfiles.Batch153.profile6127]⟩
theorem profilesValid902 : retention902.ProfilesValid := by
  change ∀ j : Fin 16, (retention902.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch152.valid6112
  · exact MergedCutProfiles.Batch152.valid6113
  · exact MergedCutProfiles.Batch152.valid6114
  · exact MergedCutProfiles.Batch152.valid6115
  · exact MergedCutProfiles.Batch152.valid6116
  · exact MergedCutProfiles.Batch152.valid6117
  · exact MergedCutProfiles.Batch152.valid6118
  · exact MergedCutProfiles.Batch152.valid6119
  · exact MergedCutProfiles.Batch153.valid6120
  · exact MergedCutProfiles.Batch153.valid6121
  · exact MergedCutProfiles.Batch153.valid6122
  · exact MergedCutProfiles.Batch153.valid6123
  · exact MergedCutProfiles.Batch153.valid6124
  · exact MergedCutProfiles.Batch153.valid6125
  · exact MergedCutProfiles.Batch153.valid6126
  · exact MergedCutProfiles.Batch153.valid6127
theorem numericValid902 : retention902.NumericValid := by decide +kernel
def certificate902 : RatCutBinCertificate := ⟨⟨retention902,(216391810996116503/100000000000000000),(59865971199444307/500000000000000000),(1326455612614145873/100000000000000000),(6335438781896511673/25000000000000000),(536692395999485627/500000000000000000)⟩,(992464092671492243/1000000000000000000),(234648430129472783/500000000000000000),(87835325520038093/500000000000000000),(70253392114352141/500000000000000000)⟩
theorem valid902 : certificate902.Valid := by decide +kernel
theorem sound902 : certificate902.Sound := rat_cut_bin_certificate_sound certificate902 profilesValid902 numericValid902 valid902

def retention903 : RatCutRetentionCertificate := ⟨(199/4000),(1/20),(9370098860814026942/19077553014247196799),(2099660461108545127/250000000000000000),(21/20),(847078672711894937465389772743267724351/839864184443418050800000000000000000000),false,MergedCutProfiles.Batch153.profile6128,(fun _ => MergedCutProfiles.Batch153.profile6128)⟩
theorem profilesValid903 : retention903.ProfilesValid := by
  exact MergedCutProfiles.Batch153.valid6128
theorem numericValid903 : retention903.NumericValid := by decide +kernel
def certificate903 : RatCutBinCertificate := ⟨⟨retention903,(216391810996116503/100000000000000000),(59865971199444307/500000000000000000),(1326455612614145873/100000000000000000),(6335438781896511673/25000000000000000),(494039913828955067/500000000000000000)⟩,(992464092671492243/1000000000000000000),(29939765343946427/62500000000000000),(8420151236385953/50000000000000000),(3551205151036249/25000000000000000)⟩
theorem valid903 : certificate903.Valid := by decide +kernel
theorem sound903 : certificate903.Sound := rat_cut_bin_certificate_sound certificate903 profilesValid903 numericValid903 valid903

def retention904 : RatCutRetentionCertificate := ⟨(199/4000),(1/20),(9463799849422167212/19077553014247196799),(4685049430407013471/500000000000000000),(21/20),(3754118614407694695767620671936730232999/3748039544325610776800000000000000000000),false,MergedCutProfiles.Batch153.profile6129,(fun _ => MergedCutProfiles.Batch153.profile6129)⟩
theorem profilesValid904 : retention904.ProfilesValid := by
  exact MergedCutProfiles.Batch153.valid6129
theorem numericValid904 : retention904.NumericValid := by decide +kernel
def certificate904 : RatCutBinCertificate := ⟨⟨retention904,(216391810996116503/100000000000000000),(59865971199444307/500000000000000000),(1326455612614145873/100000000000000000),(6335438781896511673/25000000000000000),(7664936011443349/7812500000000000)⟩,(992464092671492243/1000000000000000000),(239591133349977309/500000000000000000),(84147789485774123/500000000000000000),(14247359797427787/100000000000000000)⟩
theorem valid904 : certificate904.Valid := by decide +kernel
theorem sound904 : certificate904.Sound := rat_cut_bin_certificate_sound certificate904 profilesValid904 numericValid904 valid904

def retention905 : RatCutRetentionCertificate := ⟨(199/4000),(1/20),(1/2),(2365949962355541803/250000000000000000),(21/20),(940869961189572792803088987821166020511/946379984942216721200000000000000000000),false,MergedCutProfiles.Batch153.profile6130,(fun _ => MergedCutProfiles.Batch153.profile6130)⟩
theorem profilesValid905 : retention905.ProfilesValid := by
  exact MergedCutProfiles.Batch153.valid6130
theorem numericValid905 : retention905.NumericValid := by decide +kernel
def certificate905 : RatCutBinCertificate := ⟨⟨retention905,(216391810996116503/100000000000000000),(59865971199444307/500000000000000000),(1326455612614145873/100000000000000000),(6335438781896511673/25000000000000000),(15213557424232569/15625000000000000)⟩,(992464092671492243/1000000000000000000),(48256498090489283/100000000000000000),(165818926694440759/1000000000000000000),(6976152584382141/50000000000000000)⟩
theorem valid905 : certificate905.Valid := by decide +kernel
theorem sound905 : certificate905.Sound := rat_cut_bin_certificate_sound certificate905 profilesValid905 numericValid905 valid905

def retention906 : RatCutRetentionCertificate := ⟨(199/4000),(1/20),(1/2),64,1,(63848575886467267409213260666983225151/64000000000000000000000000000000000000),false,MergedCutProfiles.Batch153.profile6130,(fun _ => MergedCutProfiles.Batch153.profile6130)⟩
theorem profilesValid906 : retention906.ProfilesValid := by
  exact MergedCutProfiles.Batch153.valid6130
theorem numericValid906 : retention906.NumericValid := by decide +kernel
def certificate906 : RatCutBinCertificate := ⟨⟨retention906,(216391810996116503/100000000000000000),(59865971199444307/500000000000000000),(1326455612614145873/100000000000000000),(6335438781896511673/25000000000000000),(978101340764899799/1000000000000000000)⟩,(992464092671492243/1000000000000000000),(114138434972243047/250000000000000000),(92742796973455011/500000000000000000),(177334023466530093/1000000000000000000)⟩
theorem valid906 : certificate906.Valid := by decide +kernel
theorem sound906 : certificate906.Sound := rat_cut_bin_certificate_sound certificate906 profilesValid906 numericValid906 valid906

def retention907 : RatCutRetentionCertificate := ⟨(199/4000),(1/20),(2867539847729650175/6359184338082398933),(93234216871258459/25000000000000000),(6/5),(16290999785198891982667548948233489231/14917474699401353440000000000000000000),false,MergedCutProfiles.Batch153.profile6131,(fun _ => MergedCutProfiles.Batch153.profile6131)⟩
theorem profilesValid907 : retention907.ProfilesValid := by
  exact MergedCutProfiles.Batch153.valid6131
theorem numericValid907 : retention907.NumericValid := by decide +kernel
def certificate907 : RatCutBinCertificate := ⟨⟨retention907,(253799116496116503/100000000000000000),(59865971199444307/500000000000000000),(1326455612614145873/100000000000000000),(6335438781896511673/25000000000000000),(1064581122991467681/1000000000000000000)⟩,(991159826423693097/1000000000000000000),(188922959816127917/500000000000000000),(254405837841272941/1000000000000000000),(46634318266026587/250000000000000000)⟩
theorem valid907 : certificate907.Valid := by decide +kernel
theorem sound907 : certificate907.Sound := rat_cut_bin_certificate_sound certificate907 profilesValid907 numericValid907 valid907

def retention908 : RatCutRetentionCertificate := ⟨(199/4000),(1/20),(285107827299770290/578107667098399903),(344104781727558021/40000000000000000),(21/20),(7379718979270755584589629004220637373/7340902010187904448000000000000000000),false,MergedCutProfiles.Batch153.profile6132,(fun _ => MergedCutProfiles.Batch153.profile6132)⟩
theorem profilesValid908 : retention908.ProfilesValid := by
  exact MergedCutProfiles.Batch153.valid6132
theorem numericValid908 : retention908.NumericValid := by decide +kernel
def certificate908 : RatCutBinCertificate := ⟨⟨retention908,(253799116496116503/100000000000000000),(59865971199444307/500000000000000000),(1326455612614145873/100000000000000000),(6335438781896511673/25000000000000000),(122653998311649667/125000000000000000)⟩,(991159826423693097/1000000000000000000),(204970709769375957/500000000000000000),(112248006513325097/500000000000000000),(188358428366678733/1000000000000000000)⟩
theorem valid908 : certificate908.Valid := by decide +kernel
theorem sound908 : certificate908.Sound := rat_cut_bin_certificate_sound certificate908 profilesValid908 numericValid908 valid908

def retention909 : RatCutRetentionCertificate := ⟨(199/4000),(1/20),(3167547961300447922/6359184338082398933),(940855830089241957/100000000000000000),(21/20),(150197319148652705456919719252294170511/150536932814278713120000000000000000000),false,MergedCutProfiles.Batch153.profile6133,(fun _ => MergedCutProfiles.Batch153.profile6133)⟩
theorem profilesValid909 : retention909.ProfilesValid := by
  exact MergedCutProfiles.Batch153.valid6133
theorem numericValid909 : retention909.NumericValid := by decide +kernel
def certificate909 : RatCutBinCertificate := ⟨⟨retention909,(253799116496116503/100000000000000000),(59865971199444307/500000000000000000),(1326455612614145873/100000000000000000),(6335438781896511673/25000000000000000),(194737662619486027/200000000000000000)⟩,(991159826423693097/1000000000000000000),(206558725225040609/500000000000000000),(5541904501336513/25000000000000000),(186187039187634783/1000000000000000000)⟩
theorem valid909 : certificate909.Valid := by decide +kernel
theorem sound909 : certificate909.Sound := rat_cut_bin_certificate_sound certificate909 profilesValid909 numericValid909 valid909

def retention910 : RatCutRetentionCertificate := ⟨(199/4000),(1/20),(1/2),(4751321941950671883/500000000000000000),(21/20),(3779246438974117008055342885277156445551/3801057553560537506400000000000000000000),false,MergedCutProfiles.Batch153.profile6130,(fun _ => MergedCutProfiles.Batch153.profile6130)⟩
theorem profilesValid910 : retention910.ProfilesValid := by
  exact MergedCutProfiles.Batch153.valid6130
theorem numericValid910 : retention910.NumericValid := by decide +kernel
def certificate910 : RatCutBinCertificate := ⟨⟨retention910,(253799116496116503/100000000000000000),(59865971199444307/500000000000000000),(1326455612614145873/100000000000000000),(6335438781896511673/25000000000000000),(242551542505853669/250000000000000000)⟩,(991159826423693097/1000000000000000000),(207300080059346063/500000000000000000),(22036812801140153/100000000000000000),(184640123321207203/1000000000000000000)⟩
theorem valid910 : certificate910.Valid := by decide +kernel
theorem sound910 : certificate910.Sound := rat_cut_bin_certificate_sound certificate910 profilesValid910 numericValid910 valid910

def retention911 : RatCutRetentionCertificate := ⟨(1/20),(201/4000),(849830963168499954/18861153311560677731),(416542967928879499/500000000000000000),(59/20),(1328059063068887949147/640000000000000000000),true,MergedCutProfiles.Batch153.profile6134,![MergedCutProfiles.Batch153.profile6134,MergedCutProfiles.Batch153.profile6135,MergedCutProfiles.Batch153.profile6136,MergedCutProfiles.Batch153.profile6137,MergedCutProfiles.Batch153.profile6138,MergedCutProfiles.Batch153.profile6139,MergedCutProfiles.Batch153.profile6140,MergedCutProfiles.Batch153.profile6141,MergedCutProfiles.Batch153.profile6142,MergedCutProfiles.Batch153.profile6143,MergedCutProfiles.Batch153.profile6144,MergedCutProfiles.Batch153.profile6145,MergedCutProfiles.Batch153.profile6146,MergedCutProfiles.Batch153.profile6147,MergedCutProfiles.Batch153.profile6148,MergedCutProfiles.Batch153.profile6149]⟩
theorem profilesValid911 : retention911.ProfilesValid := by
  change ∀ j : Fin 16, (retention911.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch153.valid6134
  · exact MergedCutProfiles.Batch153.valid6135
  · exact MergedCutProfiles.Batch153.valid6136
  · exact MergedCutProfiles.Batch153.valid6137
  · exact MergedCutProfiles.Batch153.valid6138
  · exact MergedCutProfiles.Batch153.valid6139
  · exact MergedCutProfiles.Batch153.valid6140
  · exact MergedCutProfiles.Batch153.valid6141
  · exact MergedCutProfiles.Batch153.valid6142
  · exact MergedCutProfiles.Batch153.valid6143
  · exact MergedCutProfiles.Batch153.valid6144
  · exact MergedCutProfiles.Batch153.valid6145
  · exact MergedCutProfiles.Batch153.valid6146
  · exact MergedCutProfiles.Batch153.valid6147
  · exact MergedCutProfiles.Batch153.valid6148
  · exact MergedCutProfiles.Batch153.valid6149
theorem numericValid911 : retention911.NumericValid := by decide +kernel
def certificate911 : RatCutBinCertificate := ⟨⟨retention911,(1081120266088097079/500000000000000000),(121091336014959573/1000000000000000000),(13319948354367943353/1000000000000000000),(251589832803632728293/1000000000000000000),(1008546570266987857/500000000000000000)⟩,(992426697239596233/1000000000000000000),(380733168882295009/1000000000000000000),(125803491786164853/500000000000000000),(133382495604080971/1000000000000000000)⟩
theorem valid911 : certificate911.Valid := by decide +kernel
theorem sound911 : certificate911.Sound := rat_cut_bin_certificate_sound certificate911 profilesValid911 numericValid911 valid911

def certificates : List RatCutBinCertificate := [certificate900,certificate901,certificate902,certificate903,certificate904,certificate905,certificate906,certificate907,certificate908,certificate909,certificate910,certificate911]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound900,List.forall_mem_cons.mpr ⟨sound901,List.forall_mem_cons.mpr ⟨sound902,List.forall_mem_cons.mpr ⟨sound903,List.forall_mem_cons.mpr ⟨sound904,List.forall_mem_cons.mpr ⟨sound905,List.forall_mem_cons.mpr ⟨sound906,List.forall_mem_cons.mpr ⟨sound907,List.forall_mem_cons.mpr ⟨sound908,List.forall_mem_cons.mpr ⟨sound909,List.forall_mem_cons.mpr ⟨sound910,List.forall_mem_cons.mpr ⟨sound911,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch075
