import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch197
import Cycle12.MergedCutProfiles.Batch198

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch099

def retention1188 : RatCutRetentionCertificate := ⟨(7/125),(9/160),(1/2),64,1,(255402368671851885228092572350193125711/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch197.profile7884,(fun _ => MergedCutProfiles.Batch197.profile7884)⟩
theorem profilesValid1188 : retention1188.ProfilesValid := by
  exact MergedCutProfiles.Batch197.valid7884
theorem numericValid1188 : retention1188.NumericValid := by decide +kernel
def certificate1188 : RatCutBinCertificate := ⟨⟨retention1188,(564868087819829857/250000000000000000),(78413240231001367/500000000000000000),(1476294129818532509/100000000000000000),(53717100140915108179/250000000000000000),(486831445798746221/500000000000000000)⟩,(991101507837600943/1000000000000000000),(430155193821038919/1000000000000000000),(41392278117702837/200000000000000000),(196708192454349577/1000000000000000000)⟩
theorem valid1188 : certificate1188.Valid := by decide +kernel
theorem sound1188 : certificate1188.Sound := rat_cut_bin_certificate_sound certificate1188 profilesValid1188 numericValid1188 valid1188

def retention1189 : RatCutRetentionCertificate := ⟨(7/125),(9/160),(3342451975141480614/7266453255346924291),(901799532402232753/250000000000000000),(6/5),(387119684374314537092179467057916740791/360719812960893101200000000000000000000),false,MergedCutProfiles.Batch197.profile7885,(fun _ => MergedCutProfiles.Batch197.profile7885)⟩
theorem profilesValid1189 : retention1189.ProfilesValid := by
  exact MergedCutProfiles.Batch197.valid7885
theorem numericValid1189 : retention1189.NumericValid := by decide +kernel
def certificate1189 : RatCutBinCertificate := ⟨⟨retention1189,(650353821069829857/250000000000000000),(78413240231001367/500000000000000000),(1476294129818532509/100000000000000000),(53717100140915108179/250000000000000000),(260004824912015937/250000000000000000)⟩,(494876148779352963/500000000000000000),(38793547732209913/100000000000000000),(61180046126118627/250000000000000000),(174719554170781149/1000000000000000000)⟩
theorem valid1189 : certificate1189.Valid := by decide +kernel
theorem sound1189 : certificate1189.Sound := rat_cut_bin_certificate_sound certificate1189 profilesValid1189 numericValid1189 valid1189

def retention1190 : RatCutRetentionCertificate := ⟨(7/125),(9/160),(7167121850538164711/14532906510693848582),(1671225987570740307/250000000000000000),(21/20),(18530972108248409569655923037654607731/18569177639674892300000000000000000000),false,MergedCutProfiles.Batch197.profile7886,(fun _ => MergedCutProfiles.Batch197.profile7886)⟩
theorem profilesValid1190 : retention1190.ProfilesValid := by
  exact MergedCutProfiles.Batch197.valid7886
theorem numericValid1190 : retention1190.NumericValid := by decide +kernel
def certificate1190 : RatCutBinCertificate := ⟨⟨retention1190,(650353821069829857/250000000000000000),(78413240231001367/500000000000000000),(1476294129818532509/100000000000000000),(53717100140915108179/250000000000000000),(242230745376309053/250000000000000000)⟩,(494876148779352963/500000000000000000),(104100220330821643/250000000000000000),(43757330259845911/200000000000000000),(176485328751378623/1000000000000000000)⟩
theorem valid1190 : certificate1190.Valid := by decide +kernel
theorem sound1190 : certificate1190.Sound := rat_cut_bin_certificate_sound certificate1190 profilesValid1190 numericValid1190 valid1190

def retention1191 : RatCutRetentionCertificate := ⟨(7/125),(9/160),(7238793069043546359/14532906510693848582),(7167121850538164711/1000000000000000000),(21/20),(11361827386770016782530791735528758596759/11467394960861063537600000000000000000000),false,MergedCutProfiles.Batch197.profile7887,(fun _ => MergedCutProfiles.Batch197.profile7887)⟩
theorem profilesValid1191 : retention1191.ProfilesValid := by
  exact MergedCutProfiles.Batch197.valid7887
theorem numericValid1191 : retention1191.NumericValid := by decide +kernel
def certificate1191 : RatCutBinCertificate := ⟨⟨retention1191,(650353821069829857/250000000000000000),(78413240231001367/500000000000000000),(1476294129818532509/100000000000000000),(53717100140915108179/250000000000000000),(961774765025174137/1000000000000000000)⟩,(494876148779352963/500000000000000000),(419495705340747229/1000000000000000000),(108043400961843931/500000000000000000),(87266247008197561/500000000000000000)⟩
theorem valid1191 : certificate1191.Valid := by decide +kernel
theorem sound1191 : certificate1191.Sound := rat_cut_bin_certificate_sound certificate1191 profilesValid1191 numericValid1191 valid1191

def retention1192 : RatCutRetentionCertificate := ⟨(7/125),(9/160),(1/2),(7238793069043546359/1000000000000000000),(21/20),(3812252828313947780875386127755169759533/3860689636823224724800000000000000000000),false,MergedCutProfiles.Batch197.profile7884,(fun _ => MergedCutProfiles.Batch197.profile7884)⟩
theorem profilesValid1192 : retention1192.ProfilesValid := by
  exact MergedCutProfiles.Batch197.valid7884
theorem numericValid1192 : retention1192.NumericValid := by decide +kernel
def certificate1192 : RatCutBinCertificate := ⟨⟨retention1192,(650353821069829857/250000000000000000),(78413240231001367/500000000000000000),(1476294129818532509/100000000000000000),(53717100140915108179/250000000000000000),(119804316026170501/125000000000000000)⟩,(494876148779352963/500000000000000000),(420957688353474537/1000000000000000000),(10740967596059707/50000000000000000),(173157766688372173/1000000000000000000)⟩
theorem valid1192 : certificate1192.Valid := by decide +kernel
theorem sound1192 : certificate1192.Sound := rat_cut_bin_certificate_sound certificate1192 profilesValid1192 numericValid1192 valid1192

def retention1193 : RatCutRetentionCertificate := ⟨(9/160),(113/2000),(23595453759404944/306023323711238729),(864752541266041591/1000000000000000000),(11/4),(100834954132490387519/51200000000000000000),true,MergedCutProfiles.Batch197.profile7888,![MergedCutProfiles.Batch197.profile7888,MergedCutProfiles.Batch197.profile7889,MergedCutProfiles.Batch197.profile7890,MergedCutProfiles.Batch197.profile7891,MergedCutProfiles.Batch197.profile7892,MergedCutProfiles.Batch197.profile7893,MergedCutProfiles.Batch197.profile7894,MergedCutProfiles.Batch197.profile7895,MergedCutProfiles.Batch197.profile7896,MergedCutProfiles.Batch197.profile7897,MergedCutProfiles.Batch197.profile7898,MergedCutProfiles.Batch197.profile7899,MergedCutProfiles.Batch197.profile7900,MergedCutProfiles.Batch197.profile7901,MergedCutProfiles.Batch197.profile7902,MergedCutProfiles.Batch197.profile7903]⟩
theorem profilesValid1193 : retention1193.ProfilesValid := by
  change ∀ j : Fin 16, (retention1193.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch197.valid7888
  · exact MergedCutProfiles.Batch197.valid7889
  · exact MergedCutProfiles.Batch197.valid7890
  · exact MergedCutProfiles.Batch197.valid7891
  · exact MergedCutProfiles.Batch197.valid7892
  · exact MergedCutProfiles.Batch197.valid7893
  · exact MergedCutProfiles.Batch197.valid7894
  · exact MergedCutProfiles.Batch197.valid7895
  · exact MergedCutProfiles.Batch197.valid7896
  · exact MergedCutProfiles.Batch197.valid7897
  · exact MergedCutProfiles.Batch197.valid7898
  · exact MergedCutProfiles.Batch197.valid7899
  · exact MergedCutProfiles.Batch197.valid7900
  · exact MergedCutProfiles.Batch197.valid7901
  · exact MergedCutProfiles.Batch197.valid7902
  · exact MergedCutProfiles.Batch197.valid7903
theorem numericValid1193 : retention1193.NumericValid := by decide +kernel
def certificate1193 : RatCutBinCertificate := ⟨⟨retention1193,(452197733855523329/200000000000000000),(39612838789917267/250000000000000000),(1853520589949574469/125000000000000000),(106796751771871583253/500000000000000000),(951485219920289189/500000000000000000)⟩,(991059230897117743/1000000000000000000),(360594524704936277/1000000000000000000),(3394929358193561/12500000000000000),(7201036759054727/50000000000000000)⟩
theorem valid1193 : certificate1193.Valid := by decide +kernel
theorem sound1193 : certificate1193.Sound := rat_cut_bin_certificate_sound certificate1193 profilesValid1193 numericValid1193 valid1193

def retention1194 : RatCutRetentionCertificate := ⟨(9/160),(113/2000),(2433967194097613416/14383096214428220263),(69311645418252023/62500000000000000),(11/5),(68335493609889641099/40000000000000000000),true,MergedCutProfiles.Batch197.profile7904,![MergedCutProfiles.Batch197.profile7904,MergedCutProfiles.Batch197.profile7905,MergedCutProfiles.Batch197.profile7906,MergedCutProfiles.Batch197.profile7907,MergedCutProfiles.Batch197.profile7908,MergedCutProfiles.Batch197.profile7909,MergedCutProfiles.Batch197.profile7910,MergedCutProfiles.Batch197.profile7911,MergedCutProfiles.Batch197.profile7912,MergedCutProfiles.Batch197.profile7913,MergedCutProfiles.Batch197.profile7914,MergedCutProfiles.Batch197.profile7915,MergedCutProfiles.Batch197.profile7916,MergedCutProfiles.Batch197.profile7917,MergedCutProfiles.Batch197.profile7918,MergedCutProfiles.Batch197.profile7919]⟩
theorem profilesValid1194 : retention1194.ProfilesValid := by
  change ∀ j : Fin 16, (retention1194.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch197.valid7904
  · exact MergedCutProfiles.Batch197.valid7905
  · exact MergedCutProfiles.Batch197.valid7906
  · exact MergedCutProfiles.Batch197.valid7907
  · exact MergedCutProfiles.Batch197.valid7908
  · exact MergedCutProfiles.Batch197.valid7909
  · exact MergedCutProfiles.Batch197.valid7910
  · exact MergedCutProfiles.Batch197.valid7911
  · exact MergedCutProfiles.Batch197.valid7912
  · exact MergedCutProfiles.Batch197.valid7913
  · exact MergedCutProfiles.Batch197.valid7914
  · exact MergedCutProfiles.Batch197.valid7915
  · exact MergedCutProfiles.Batch197.valid7916
  · exact MergedCutProfiles.Batch197.valid7917
  · exact MergedCutProfiles.Batch197.valid7918
  · exact MergedCutProfiles.Batch197.valid7919
theorem numericValid1194 : retention1194.NumericValid := by decide +kernel
def certificate1194 : RatCutBinCertificate := ⟨⟨retention1194,(452197733855523329/200000000000000000),(39612838789917267/250000000000000000),(1853520589949574469/125000000000000000),(106796751771871583253/500000000000000000),(413804488281513083/250000000000000000)⟩,(991059230897117743/1000000000000000000),(378558026222154119/1000000000000000000),(253713491250909247/1000000000000000000),(144344216556159099/1000000000000000000)⟩
theorem valid1194 : certificate1194.Valid := by decide +kernel
theorem sound1194 : certificate1194.Sound := rat_cut_bin_certificate_sound certificate1194 profilesValid1194 numericValid1194 valid1194

def retention1195 : RatCutRetentionCertificate := ⟨(9/160),(113/2000),(5503859900865673366/14383096214428220263),(304245899262201677/125000000000000000),(13/10),(195002965311033991783/160000000000000000000),true,MergedCutProfiles.Batch198.profile7920,![MergedCutProfiles.Batch198.profile7920,MergedCutProfiles.Batch198.profile7921,MergedCutProfiles.Batch198.profile7922,MergedCutProfiles.Batch198.profile7923,MergedCutProfiles.Batch198.profile7924,MergedCutProfiles.Batch198.profile7925,MergedCutProfiles.Batch198.profile7926,MergedCutProfiles.Batch198.profile7927,MergedCutProfiles.Batch198.profile7928,MergedCutProfiles.Batch198.profile7929,MergedCutProfiles.Batch198.profile7930,MergedCutProfiles.Batch198.profile7931,MergedCutProfiles.Batch198.profile7932,MergedCutProfiles.Batch198.profile7933,MergedCutProfiles.Batch198.profile7934,MergedCutProfiles.Batch198.profile7935]⟩
theorem profilesValid1195 : retention1195.ProfilesValid := by
  change ∀ j : Fin 16, (retention1195.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch198.valid7920
  · exact MergedCutProfiles.Batch198.valid7921
  · exact MergedCutProfiles.Batch198.valid7922
  · exact MergedCutProfiles.Batch198.valid7923
  · exact MergedCutProfiles.Batch198.valid7924
  · exact MergedCutProfiles.Batch198.valid7925
  · exact MergedCutProfiles.Batch198.valid7926
  · exact MergedCutProfiles.Batch198.valid7927
  · exact MergedCutProfiles.Batch198.valid7928
  · exact MergedCutProfiles.Batch198.valid7929
  · exact MergedCutProfiles.Batch198.valid7930
  · exact MergedCutProfiles.Batch198.valid7931
  · exact MergedCutProfiles.Batch198.valid7932
  · exact MergedCutProfiles.Batch198.valid7933
  · exact MergedCutProfiles.Batch198.valid7934
  · exact MergedCutProfiles.Batch198.valid7935
theorem numericValid1195 : retention1195.NumericValid := by decide +kernel
def certificate1195 : RatCutBinCertificate := ⟨⟨retention1195,(452197733855523329/200000000000000000),(39612838789917267/250000000000000000),(1853520589949574469/125000000000000000),(106796751771871583253/500000000000000000),(74209527834282221/62500000000000000)⟩,(991059230897117743/1000000000000000000),(430968551717376109/1000000000000000000),(103138008148706853/500000000000000000),(144699288605961211/1000000000000000000)⟩
theorem valid1195 : certificate1195.Valid := by decide +kernel
theorem sound1195 : certificate1195.Sound := rat_cut_bin_certificate_sound certificate1195 profilesValid1195 numericValid1195 valid1195

def retention1196 : RatCutRetentionCertificate := ⟨(9/160),(113/2000),(6919249125539181579/14383096214428220263),(2751929950432836683/500000000000000000),(11/10),(70775354625722810759530244043155774047/68798248760820917075000000000000000000),false,MergedCutProfiles.Batch198.profile7936,(fun _ => MergedCutProfiles.Batch198.profile7936)⟩
theorem profilesValid1196 : retention1196.ProfilesValid := by
  exact MergedCutProfiles.Batch198.valid7936
theorem numericValid1196 : retention1196.NumericValid := by decide +kernel
def certificate1196 : RatCutBinCertificate := ⟨⟨retention1196,(452197733855523329/200000000000000000),(39612838789917267/250000000000000000),(1853520589949574469/125000000000000000),(106796751771871583253/500000000000000000),(501078933094465343/500000000000000000)⟩,(991059230897117743/1000000000000000000),(114273003395080647/250000000000000000),(185063882222368317/1000000000000000000),(145125720081203451/1000000000000000000)⟩
theorem valid1196 : certificate1196.Valid := by decide +kernel
theorem sound1196 : certificate1196.Sound := rat_cut_bin_certificate_sound certificate1196 profilesValid1196 numericValid1196 valid1196

def retention1197 : RatCutRetentionCertificate := ⟨(9/160),(113/2000),(7128909293292144321/14383096214428220263),(6919249125539181579/1000000000000000000),(21/20),(11008443078967230071055285674211207902999/11070798600862690526400000000000000000000),false,MergedCutProfiles.Batch198.profile7937,(fun _ => MergedCutProfiles.Batch198.profile7937)⟩
theorem profilesValid1197 : retention1197.ProfilesValid := by
  exact MergedCutProfiles.Batch198.valid7937
theorem numericValid1197 : retention1197.NumericValid := by decide +kernel
def certificate1197 : RatCutBinCertificate := ⟨⟨retention1197,(452197733855523329/200000000000000000),(39612838789917267/250000000000000000),(1853520589949574469/125000000000000000),(106796751771871583253/500000000000000000),(968996392690386499/1000000000000000000)⟩,(991059230897117743/1000000000000000000),(231879036746127881/500000000000000000),(89946818568470701/500000000000000000),(72944984518923683/500000000000000000)⟩
theorem valid1197 : certificate1197.Valid := by decide +kernel
theorem sound1197 : certificate1197.Sound := rat_cut_bin_certificate_sound certificate1197 profilesValid1197 numericValid1197 valid1197

def retention1198 : RatCutRetentionCertificate := ⟨(9/160),(113/2000),(1/2),(7128909293292144321/1000000000000000000),(21/20),(11257857387913786926098396792946499352759/11406254869267430913600000000000000000000),false,MergedCutProfiles.Batch198.profile7938,(fun _ => MergedCutProfiles.Batch198.profile7938)⟩
theorem profilesValid1198 : retention1198.ProfilesValid := by
  exact MergedCutProfiles.Batch198.valid7938
theorem numericValid1198 : retention1198.NumericValid := by decide +kernel
def certificate1198 : RatCutBinCertificate := ⟨⟨retention1198,(452197733855523329/200000000000000000),(39612838789917267/250000000000000000),(1853520589949574469/125000000000000000),(106796751771871583253/500000000000000000),(961618716423311953/1000000000000000000)⟩,(991059230897117743/1000000000000000000),(466281608100299321/1000000000000000000),(88980720255940423/500000000000000000),(143823104282158023/1000000000000000000)⟩
theorem valid1198 : certificate1198.Valid := by decide +kernel
theorem sound1198 : certificate1198.Sound := rat_cut_bin_certificate_sound certificate1198 profilesValid1198 numericValid1198 valid1198

def retention1199 : RatCutRetentionCertificate := ⟨(9/160),(113/2000),(1/2),64,1,(10216108735834957980041681676251254959/10240000000000000000000000000000000000),false,MergedCutProfiles.Batch198.profile7938,(fun _ => MergedCutProfiles.Batch198.profile7938)⟩
theorem profilesValid1199 : retention1199.ProfilesValid := by
  exact MergedCutProfiles.Batch198.valid7938
theorem numericValid1199 : retention1199.NumericValid := by decide +kernel
def certificate1199 : RatCutBinCertificate := ⟨⟨retention1199,(452197733855523329/200000000000000000),(39612838789917267/250000000000000000),(1853520589949574469/125000000000000000),(106796751771871583253/500000000000000000),(486753015851116773/500000000000000000)⟩,(991059230897117743/1000000000000000000),(107655243965759169/250000000000000000),(206568712392444801/1000000000000000000),(98147658427672957/500000000000000000)⟩
theorem valid1199 : certificate1199.Valid := by decide +kernel
theorem sound1199 : certificate1199.Sound := rat_cut_bin_certificate_sound certificate1199 profilesValid1199 numericValid1199 valid1199

def certificates : List RatCutBinCertificate := [certificate1188,certificate1189,certificate1190,certificate1191,certificate1192,certificate1193,certificate1194,certificate1195,certificate1196,certificate1197,certificate1198,certificate1199]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1188,List.forall_mem_cons.mpr ⟨sound1189,List.forall_mem_cons.mpr ⟨sound1190,List.forall_mem_cons.mpr ⟨sound1191,List.forall_mem_cons.mpr ⟨sound1192,List.forall_mem_cons.mpr ⟨sound1193,List.forall_mem_cons.mpr ⟨sound1194,List.forall_mem_cons.mpr ⟨sound1195,List.forall_mem_cons.mpr ⟨sound1196,List.forall_mem_cons.mpr ⟨sound1197,List.forall_mem_cons.mpr ⟨sound1198,List.forall_mem_cons.mpr ⟨sound1199,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch099
