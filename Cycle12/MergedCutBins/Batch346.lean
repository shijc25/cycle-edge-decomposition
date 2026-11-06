import Cycle12.RationalCutBin
import Cycle12.MergedCutProfiles.Batch517
import Cycle12.MergedCutProfiles.Batch518
import Cycle12.MergedCutProfiles.Batch519
import Cycle12.MergedCutProfiles.Batch623
import Cycle12.MergedCutProfiles.Batch624

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MergedCutBins.Batch346

def retention4152 : RatCutRetentionCertificate := ⟨(29/500),(117/2000),(732961384455623737/265120006639563607947),(45356521315323251/62500000000000000),(77/20),(2698737650303578263256148444805481219/1133913032883081275000000000000000000),true,MergedCutProfiles.Batch623.profile24925,![MergedCutProfiles.Batch623.profile24925,MergedCutProfiles.Batch623.profile24926,MergedCutProfiles.Batch623.profile24927,MergedCutProfiles.Batch623.profile24928,MergedCutProfiles.Batch623.profile24929,MergedCutProfiles.Batch517.profile20705,MergedCutProfiles.Batch623.profile24930,MergedCutProfiles.Batch623.profile24931,MergedCutProfiles.Batch623.profile24932,MergedCutProfiles.Batch623.profile24933,MergedCutProfiles.Batch623.profile24934,MergedCutProfiles.Batch517.profile20706,MergedCutProfiles.Batch623.profile24935,MergedCutProfiles.Batch623.profile24936,MergedCutProfiles.Batch623.profile24937,MergedCutProfiles.Batch623.profile24938]⟩
theorem profilesValid4152 : retention4152.ProfilesValid := by
  change ∀ j : Fin 16, (retention4152.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch623.valid24925
  · exact MergedCutProfiles.Batch623.valid24926
  · exact MergedCutProfiles.Batch623.valid24927
  · exact MergedCutProfiles.Batch623.valid24928
  · exact MergedCutProfiles.Batch623.valid24929
  · exact MergedCutProfiles.Batch517.valid20705
  · exact MergedCutProfiles.Batch623.valid24930
  · exact MergedCutProfiles.Batch623.valid24931
  · exact MergedCutProfiles.Batch623.valid24932
  · exact MergedCutProfiles.Batch623.valid24933
  · exact MergedCutProfiles.Batch623.valid24934
  · exact MergedCutProfiles.Batch517.valid20706
  · exact MergedCutProfiles.Batch623.valid24935
  · exact MergedCutProfiles.Batch623.valid24936
  · exact MergedCutProfiles.Batch623.valid24937
  · exact MergedCutProfiles.Batch623.valid24938
theorem numericValid4152 : retention4152.NumericValid := by decide +kernel
def certificate4152 : RatCutBinCertificate := ⟨⟨retention4152,(127622259736967313/62500000000000000),(42966716513336319/250000000000000000),(7651397377082467531/500000000000000000),(4069359556869383403307/1000000000000000000),(91669077048178583/40000000000000000)⟩,(999582699060267599/1000000000000000000),(2014442155294741/4000000000000000),(150936735087440509/1000000000000000000),(37014354807025617/500000000000000000)⟩
theorem valid4152 : certificate4152.Valid := by decide +kernel
theorem sound4152 : certificate4152.Sound := rat_cut_bin_certificate_sound certificate4152 profilesValid4152 numericValid4152 valid4152

def retention4153 : RatCutRetentionCertificate := ⟨(29/500),(117/2000),(1102744244000000000/265120006639563607947),(732961384455623737/1000000000000000000),(19/5),(3023350083426454626789/1280000000000000000000),true,MergedCutProfiles.Batch623.profile24939,![MergedCutProfiles.Batch623.profile24939,MergedCutProfiles.Batch623.profile24927,MergedCutProfiles.Batch623.profile24940,MergedCutProfiles.Batch623.profile24941,MergedCutProfiles.Batch518.profile20720,MergedCutProfiles.Batch623.profile24932,MergedCutProfiles.Batch623.profile24942,MergedCutProfiles.Batch517.profile20706,MergedCutProfiles.Batch623.profile24943,MergedCutProfiles.Batch623.profile24937,MergedCutProfiles.Batch623.profile24944,MergedCutProfiles.Batch517.profile20707,MergedCutProfiles.Batch623.profile24945,MergedCutProfiles.Batch623.profile24946,MergedCutProfiles.Batch518.profile20722,MergedCutProfiles.Batch623.profile24947]⟩
theorem profilesValid4153 : retention4153.ProfilesValid := by
  change ∀ j : Fin 16, (retention4153.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch623.valid24939
  · exact MergedCutProfiles.Batch623.valid24927
  · exact MergedCutProfiles.Batch623.valid24940
  · exact MergedCutProfiles.Batch623.valid24941
  · exact MergedCutProfiles.Batch518.valid20720
  · exact MergedCutProfiles.Batch623.valid24932
  · exact MergedCutProfiles.Batch623.valid24942
  · exact MergedCutProfiles.Batch517.valid20706
  · exact MergedCutProfiles.Batch623.valid24943
  · exact MergedCutProfiles.Batch623.valid24937
  · exact MergedCutProfiles.Batch623.valid24944
  · exact MergedCutProfiles.Batch517.valid20707
  · exact MergedCutProfiles.Batch623.valid24945
  · exact MergedCutProfiles.Batch623.valid24946
  · exact MergedCutProfiles.Batch518.valid20722
  · exact MergedCutProfiles.Batch623.valid24947
theorem numericValid4153 : retention4153.NumericValid := by decide +kernel
def certificate4153 : RatCutBinCertificate := ⟨⟨retention4153,(127622259736967313/62500000000000000),(42966716513336319/250000000000000000),(7651397377082467531/500000000000000000),(4069359556869383403307/1000000000000000000),(227484413739254721/100000000000000000)⟩,(999582699060267599/1000000000000000000),(252203055705367141/500000000000000000),(4699738742560839/31250000000000000),(74066381887228941/1000000000000000000)⟩
theorem valid4153 : certificate4153.Valid := by decide +kernel
theorem sound4153 : certificate4153.Sound := rat_cut_bin_certificate_sound certificate4153 profilesValid4153 numericValid4153 valid4153

def retention4154 : RatCutRetentionCertificate := ⟨(29/500),(117/2000),(1515449193374217668/265120006639563607947),(275686061/250000000),(27/10),(9309331360310014281/4000000000000000000),true,MergedCutProfiles.Batch623.profile24926,![MergedCutProfiles.Batch623.profile24926,MergedCutProfiles.Batch623.profile24948,MergedCutProfiles.Batch623.profile24949,MergedCutProfiles.Batch623.profile24950,MergedCutProfiles.Batch623.profile24951,MergedCutProfiles.Batch623.profile24952,MergedCutProfiles.Batch623.profile24953,MergedCutProfiles.Batch623.profile24944,MergedCutProfiles.Batch623.profile24954,MergedCutProfiles.Batch623.profile24955,MergedCutProfiles.Batch517.profile20693,MergedCutProfiles.Batch623.profile24956,MergedCutProfiles.Batch623.profile24957,MergedCutProfiles.Batch517.profile20694,MergedCutProfiles.Batch623.profile24958,MergedCutProfiles.Batch623.profile24959]⟩
theorem profilesValid4154 : retention4154.ProfilesValid := by
  change ∀ j : Fin 16, (retention4154.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch623.valid24926
  · exact MergedCutProfiles.Batch623.valid24948
  · exact MergedCutProfiles.Batch623.valid24949
  · exact MergedCutProfiles.Batch623.valid24950
  · exact MergedCutProfiles.Batch623.valid24951
  · exact MergedCutProfiles.Batch623.valid24952
  · exact MergedCutProfiles.Batch623.valid24953
  · exact MergedCutProfiles.Batch623.valid24944
  · exact MergedCutProfiles.Batch623.valid24954
  · exact MergedCutProfiles.Batch623.valid24955
  · exact MergedCutProfiles.Batch517.valid20693
  · exact MergedCutProfiles.Batch623.valid24956
  · exact MergedCutProfiles.Batch623.valid24957
  · exact MergedCutProfiles.Batch517.valid20694
  · exact MergedCutProfiles.Batch623.valid24958
  · exact MergedCutProfiles.Batch623.valid24959
theorem numericValid4154 : retention4154.NumericValid := by decide +kernel
def certificate4154 : RatCutBinCertificate := ⟨⟨retention4154,(127622259736967313/62500000000000000),(42966716513336319/250000000000000000),(7651397377082467531/500000000000000000),(4069359556869383403307/1000000000000000000),(113270593569659077/50000000000000000)⟩,(999582699060267599/1000000000000000000),(203721087237424293/500000000000000000),(56683061806365337/250000000000000000),(18542639232906043/125000000000000000)⟩
theorem valid4154 : certificate4154.Valid := by decide +kernel
theorem sound4154 : certificate4154.Sound := rat_cut_bin_certificate_sound certificate4154 profilesValid4154 numericValid4154 valid4154

def retention4155 : RatCutRetentionCertificate := ⟨(29/500),(117/2000),(24092579041089098102/265120006639563607947),(378862298343554417/250000000000000000),(43/20),(295563011224094767218209610324666338039/151544919337421766800000000000000000000),false,MergedCutProfiles.Batch624.profile24960,(fun _ => MergedCutProfiles.Batch624.profile24960)⟩
theorem profilesValid4155 : retention4155.ProfilesValid := by
  exact MergedCutProfiles.Batch624.valid24960
theorem numericValid4155 : retention4155.NumericValid := by decide +kernel
def certificate4155 : RatCutBinCertificate := ⟨⟨retention4155,(127622259736967313/62500000000000000),(42966716513336319/250000000000000000),(7651397377082467531/500000000000000000),(4069359556869383403307/1000000000000000000),(1901025319094119789/1000000000000000000)⟩,(999582699060267599/1000000000000000000),(421815521408521807/1000000000000000000),(214078027196541621/1000000000000000000),(7440574202509161/50000000000000000)⟩
theorem valid4155 : certificate4155.Valid := by decide +kernel
theorem sound4155 : certificate4155.Sound := rat_cut_bin_certificate_sound certificate4155 profilesValid4155 numericValid4155 valid4155

def retention4156 : RatCutRetentionCertificate := ⟨(29/500),(117/2000),(64000000000000000000/265120006639563607947),(12046289520544549051/500000000000000000),1,(147198037394602854518560127251606346647/96370316164356392408000000000000000000),false,MergedCutProfiles.Batch624.profile24961,(fun _ => MergedCutProfiles.Batch624.profile24961)⟩
theorem profilesValid4156 : retention4156.ProfilesValid := by
  exact MergedCutProfiles.Batch624.valid24961
theorem numericValid4156 : retention4156.NumericValid := by decide +kernel
def certificate4156 : RatCutBinCertificate := ⟨⟨retention4156,(127622259736967313/62500000000000000),(42966716513336319/250000000000000000),(7651397377082467531/500000000000000000),(4069359556869383403307/1000000000000000000),(300897503467974561/200000000000000000)⟩,(999582699060267599/1000000000000000000),(331376061649630051/1000000000000000000),(75652204229168769/250000000000000000),(214164315028587561/500000000000000000)⟩
theorem valid4156 : certificate4156.Valid := by decide +kernel
theorem sound4156 : certificate4156.Sound := rat_cut_bin_certificate_sound certificate4156 profilesValid4156 numericValid4156 valid4156

def retention4157 : RatCutRetentionCertificate := ⟨(29/500),(117/2000),(1/2),64,1,(255405207982785659836014480125285671879/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch518.profile20753,(fun _ => MergedCutProfiles.Batch518.profile20753)⟩
theorem profilesValid4157 : retention4157.ProfilesValid := by
  exact MergedCutProfiles.Batch518.valid20753
theorem numericValid4157 : retention4157.NumericValid := by decide +kernel
def certificate4157 : RatCutBinCertificate := ⟨⟨retention4157,(127622259736967313/62500000000000000),(42966716513336319/250000000000000000),(7651397377082467531/500000000000000000),(4069359556869383403307/1000000000000000000),(974743211751896587/1000000000000000000)⟩,(999582699060267599/1000000000000000000),(498444369435770157/1000000000000000000),(154507059585516221/1000000000000000000),(9267674491534287/62500000000000000)⟩
theorem valid4157 : certificate4157.Valid := by decide +kernel
theorem sound4157 : certificate4157.Sound := rat_cut_bin_certificate_sound certificate4157 profilesValid4157 numericValid4157 valid4157

def retention4158 : RatCutRetentionCertificate := ⟨(29/500),(117/2000),(64000000000000000000/265120006639563607947),(24831132594638999937/1000000000000000000),1,(151784245201596494904004886883668811587/99324530378555999748000000000000000000),false,MergedCutProfiles.Batch624.profile24961,(fun _ => MergedCutProfiles.Batch624.profile24961)⟩
theorem profilesValid4158 : retention4158.ProfilesValid := by
  exact MergedCutProfiles.Batch624.valid24961
theorem numericValid4158 : retention4158.NumericValid := by decide +kernel
def certificate4158 : RatCutBinCertificate := ⟨⟨retention4158,(119044180236967313/62500000000000000),(42966716513336319/250000000000000000),(7651397377082467531/500000000000000000),(4069359556869383403307/1000000000000000000),(1506772794563503901/1000000000000000000)⟩,(999610749988761803/1000000000000000000),(34756195438421141/1000000000000000000),(83054822891464969/100000000000000000),(47175236023297853/40000000000000000)⟩
theorem valid4158 : certificate4158.Valid := by decide +kernel
theorem sound4158 : certificate4158.Sound := rat_cut_bin_certificate_sound certificate4158 profilesValid4158 numericValid4158 valid4158

def retention4159 : RatCutRetentionCertificate := ⟨(29/500),(117/2000),(1/2),64,1,(255405207982785659836014480125285671879/256000000000000000000000000000000000000),false,MergedCutProfiles.Batch518.profile20753,(fun _ => MergedCutProfiles.Batch518.profile20753)⟩
theorem profilesValid4159 : retention4159.ProfilesValid := by
  exact MergedCutProfiles.Batch518.valid20753
theorem numericValid4159 : retention4159.NumericValid := by decide +kernel
def certificate4159 : RatCutBinCertificate := ⟨⟨retention4159,(119044180236967313/62500000000000000),(42966716513336319/250000000000000000),(7651397377082467531/500000000000000000),(4069359556869383403307/1000000000000000000),(122035583738730057/125000000000000000)⟩,(999610749988761803/1000000000000000000),(26820911637371839/500000000000000000),(155733940426577149/200000000000000000),(748486270118443913/1000000000000000000)⟩
theorem valid4159 : certificate4159.Valid := by decide +kernel
theorem sound4159 : certificate4159.Sound := rat_cut_bin_certificate_sound certificate4159 profilesValid4159 numericValid4159 valid4159

def retention4160 : RatCutRetentionCertificate := ⟨(117/2000),(59/1000),(740205492375189891/259856146211192519276),(732876725123950387/1000000000000000000),(19/5),(190130705435628230167/80000000000000000000),true,MergedCutProfiles.Batch624.profile24962,![MergedCutProfiles.Batch624.profile24962,MergedCutProfiles.Batch624.profile24963,MergedCutProfiles.Batch624.profile24964,MergedCutProfiles.Batch624.profile24965,MergedCutProfiles.Batch624.profile24966,MergedCutProfiles.Batch519.profile20786,MergedCutProfiles.Batch624.profile24967,MergedCutProfiles.Batch624.profile24968,MergedCutProfiles.Batch624.profile24969,MergedCutProfiles.Batch624.profile24970,MergedCutProfiles.Batch624.profile24971,MergedCutProfiles.Batch519.profile20787,MergedCutProfiles.Batch624.profile24972,MergedCutProfiles.Batch518.profile20758,MergedCutProfiles.Batch624.profile24973,MergedCutProfiles.Batch624.profile24974]⟩
theorem profilesValid4160 : retention4160.ProfilesValid := by
  change ∀ j : Fin 16, (retention4160.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch624.valid24962
  · exact MergedCutProfiles.Batch624.valid24963
  · exact MergedCutProfiles.Batch624.valid24964
  · exact MergedCutProfiles.Batch624.valid24965
  · exact MergedCutProfiles.Batch624.valid24966
  · exact MergedCutProfiles.Batch519.valid20786
  · exact MergedCutProfiles.Batch624.valid24967
  · exact MergedCutProfiles.Batch624.valid24968
  · exact MergedCutProfiles.Batch624.valid24969
  · exact MergedCutProfiles.Batch624.valid24970
  · exact MergedCutProfiles.Batch624.valid24971
  · exact MergedCutProfiles.Batch519.valid20787
  · exact MergedCutProfiles.Batch624.valid24972
  · exact MergedCutProfiles.Batch518.valid20758
  · exact MergedCutProfiles.Batch624.valid24973
  · exact MergedCutProfiles.Batch624.valid24974
theorem numericValid4160 : retention4160.NumericValid := by decide +kernel
def certificate4160 : RatCutBinCertificate := ⟨⟨retention4160,(2048786597038828997/1000000000000000000),(175338961017292427/1000000000000000000),(15441190913345225551/1000000000000000000),(4024676736448661465887/1000000000000000000),(2288227205223531789/1000000000000000000)⟩,(999578396734357809/1000000000000000000),(495846637564448597/1000000000000000000),(78161270412378417/500000000000000000),(9669711423049571/125000000000000000)⟩
theorem valid4160 : certificate4160.Valid := by decide +kernel
theorem sound4160 : certificate4160.Sound := rat_cut_bin_certificate_sound certificate4160 profilesValid4160 numericValid4160 valid4160

def retention4161 : RatCutRetentionCertificate := ⟨(117/2000),(59/1000),(1102065113000232601/259856146211192519276),(740205492375189891/1000000000000000000),(19/5),(3028790797614270545047/1280000000000000000000),true,MergedCutProfiles.Batch624.profile24975,![MergedCutProfiles.Batch624.profile24975,MergedCutProfiles.Batch624.profile24964,MergedCutProfiles.Batch624.profile24976,MergedCutProfiles.Batch519.profile20786,MergedCutProfiles.Batch624.profile24977,MergedCutProfiles.Batch624.profile24969,MergedCutProfiles.Batch624.profile24978,MergedCutProfiles.Batch519.profile20787,MergedCutProfiles.Batch624.profile24979,MergedCutProfiles.Batch624.profile24973,MergedCutProfiles.Batch624.profile24980,MergedCutProfiles.Batch519.profile20788,MergedCutProfiles.Batch624.profile24981,MergedCutProfiles.Batch624.profile24982,MergedCutProfiles.Batch519.profile20775,MergedCutProfiles.Batch519.profile20789]⟩
theorem profilesValid4161 : retention4161.ProfilesValid := by
  change ∀ j : Fin 16, (retention4161.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch624.valid24975
  · exact MergedCutProfiles.Batch624.valid24964
  · exact MergedCutProfiles.Batch624.valid24976
  · exact MergedCutProfiles.Batch519.valid20786
  · exact MergedCutProfiles.Batch624.valid24977
  · exact MergedCutProfiles.Batch624.valid24969
  · exact MergedCutProfiles.Batch624.valid24978
  · exact MergedCutProfiles.Batch519.valid20787
  · exact MergedCutProfiles.Batch624.valid24979
  · exact MergedCutProfiles.Batch624.valid24973
  · exact MergedCutProfiles.Batch624.valid24980
  · exact MergedCutProfiles.Batch519.valid20788
  · exact MergedCutProfiles.Batch624.valid24981
  · exact MergedCutProfiles.Batch624.valid24982
  · exact MergedCutProfiles.Batch519.valid20775
  · exact MergedCutProfiles.Batch519.valid20789
theorem numericValid4161 : retention4161.NumericValid := by decide +kernel
def certificate4161 : RatCutBinCertificate := ⟨⟨retention4161,(2048786597038828997/1000000000000000000),(175338961017292427/1000000000000000000),(15441190913345225551/1000000000000000000),(4024676736448661465887/1000000000000000000),(1138918105803520029/500000000000000000)⟩,(999578396734357809/1000000000000000000),(495238370671828613/1000000000000000000),(156749605078823659/1000000000000000000),(77414978188849247/1000000000000000000)⟩
theorem valid4161 : certificate4161.Valid := by decide +kernel
theorem sound4161 : certificate4161.Sound := rat_cut_bin_certificate_sound certificate4161 profilesValid4161 numericValid4161 valid4161

def retention4162 : RatCutRetentionCertificate := ⟨(117/2000),(59/1000),(278155119750000000/64964036552798129819),(1102065113000232601/1000000000000000000),(27/10),(2996425259071798647693/1280000000000000000000),true,MergedCutProfiles.Batch624.profile24975,![MergedCutProfiles.Batch624.profile24975,MergedCutProfiles.Batch624.profile24964,MergedCutProfiles.Batch624.profile24983,MergedCutProfiles.Batch624.profile24984,MergedCutProfiles.Batch624.profile24977,MergedCutProfiles.Batch624.profile24985,MergedCutProfiles.Batch624.profile24978,MergedCutProfiles.Batch519.profile20787,MergedCutProfiles.Batch624.profile24979,MergedCutProfiles.Batch624.profile24973,MergedCutProfiles.Batch624.profile24986,MergedCutProfiles.Batch624.profile24987,MergedCutProfiles.Batch624.profile24981,MergedCutProfiles.Batch624.profile24988,MergedCutProfiles.Batch519.profile20775,MergedCutProfiles.Batch624.profile24989]⟩
theorem profilesValid4162 : retention4162.ProfilesValid := by
  change ∀ j : Fin 16, (retention4162.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch624.valid24975
  · exact MergedCutProfiles.Batch624.valid24964
  · exact MergedCutProfiles.Batch624.valid24983
  · exact MergedCutProfiles.Batch624.valid24984
  · exact MergedCutProfiles.Batch624.valid24977
  · exact MergedCutProfiles.Batch624.valid24985
  · exact MergedCutProfiles.Batch624.valid24978
  · exact MergedCutProfiles.Batch519.valid20787
  · exact MergedCutProfiles.Batch624.valid24979
  · exact MergedCutProfiles.Batch624.valid24973
  · exact MergedCutProfiles.Batch624.valid24986
  · exact MergedCutProfiles.Batch624.valid24987
  · exact MergedCutProfiles.Batch624.valid24981
  · exact MergedCutProfiles.Batch624.valid24988
  · exact MergedCutProfiles.Batch519.valid20775
  · exact MergedCutProfiles.Batch624.valid24989
theorem numericValid4162 : retention4162.NumericValid := by decide +kernel
def certificate4162 : RatCutBinCertificate := ⟨⟨retention4162,(2048786597038828997/1000000000000000000),(175338961017292427/1000000000000000000),(15441190913345225551/1000000000000000000),(4024676736448661465887/1000000000000000000),(91125682871125419/40000000000000000)⟩,(999578396734357809/1000000000000000000),(400942041134661371/1000000000000000000),(232620325795330653/1000000000000000000),(76419103889395463/500000000000000000)⟩
theorem valid4162 : certificate4162.Valid := by decide +kernel
theorem sound4162 : certificate4162.Sound := rat_cut_bin_certificate_sound certificate4162 profilesValid4162 numericValid4162 valid4162

def retention4163 : RatCutRetentionCertificate := ⟨(117/2000),(59/1000),(924461215405648845/129928073105596259638),(1112620479/1000000000),(27/10),(2320005483440571241/1000000000000000000),true,MergedCutProfiles.Batch624.profile24990,![MergedCutProfiles.Batch624.profile24990,MergedCutProfiles.Batch624.profile24966,MergedCutProfiles.Batch624.profile24977,MergedCutProfiles.Batch624.profile24970,MergedCutProfiles.Batch624.profile24991,MergedCutProfiles.Batch624.profile24973,MergedCutProfiles.Batch624.profile24992,MergedCutProfiles.Batch624.profile24993,MergedCutProfiles.Batch519.profile20775,MergedCutProfiles.Batch624.profile24994,MergedCutProfiles.Batch624.profile24995,MergedCutProfiles.Batch519.profile20790,MergedCutProfiles.Batch624.profile24996,MergedCutProfiles.Batch624.profile24997,MergedCutProfiles.Batch519.profile20763,MergedCutProfiles.Batch624.profile24998]⟩
theorem profilesValid4163 : retention4163.ProfilesValid := by
  change ∀ j : Fin 16, (retention4163.fine j).Valid
  intro j
  fin_cases j
  · exact MergedCutProfiles.Batch624.valid24990
  · exact MergedCutProfiles.Batch624.valid24966
  · exact MergedCutProfiles.Batch624.valid24977
  · exact MergedCutProfiles.Batch624.valid24970
  · exact MergedCutProfiles.Batch624.valid24991
  · exact MergedCutProfiles.Batch624.valid24973
  · exact MergedCutProfiles.Batch624.valid24992
  · exact MergedCutProfiles.Batch624.valid24993
  · exact MergedCutProfiles.Batch519.valid20775
  · exact MergedCutProfiles.Batch624.valid24994
  · exact MergedCutProfiles.Batch624.valid24995
  · exact MergedCutProfiles.Batch519.valid20790
  · exact MergedCutProfiles.Batch624.valid24996
  · exact MergedCutProfiles.Batch624.valid24997
  · exact MergedCutProfiles.Batch519.valid20763
  · exact MergedCutProfiles.Batch624.valid24998
theorem numericValid4163 : retention4163.NumericValid := by decide +kernel
def certificate4163 : RatCutBinCertificate := ⟨⟨retention4163,(2048786597038828997/1000000000000000000),(175338961017292427/1000000000000000000),(15441190913345225551/1000000000000000000),(4024676736448661465887/1000000000000000000),(1128595165146885233/500000000000000000)⟩,(999578396734357809/1000000000000000000),(1573508070165029/3906250000000000),(115455104599491739/500000000000000000),(9433717591158981/62500000000000000)⟩
theorem valid4163 : certificate4163.Valid := by decide +kernel
theorem sound4163 : certificate4163.Sound := rat_cut_bin_certificate_sound certificate4163 profilesValid4163 numericValid4163 valid4163

def certificates : List RatCutBinCertificate := [certificate4152,certificate4153,certificate4154,certificate4155,certificate4156,certificate4157,certificate4158,certificate4159,certificate4160,certificate4161,certificate4162,certificate4163]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound4152,List.forall_mem_cons.mpr ⟨sound4153,List.forall_mem_cons.mpr ⟨sound4154,List.forall_mem_cons.mpr ⟨sound4155,List.forall_mem_cons.mpr ⟨sound4156,List.forall_mem_cons.mpr ⟨sound4157,List.forall_mem_cons.mpr ⟨sound4158,List.forall_mem_cons.mpr ⟨sound4159,List.forall_mem_cons.mpr ⟨sound4160,List.forall_mem_cons.mpr ⟨sound4161,List.forall_mem_cons.mpr ⟨sound4162,List.forall_mem_cons.mpr ⟨sound4163,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.MergedCutBins.Batch346
