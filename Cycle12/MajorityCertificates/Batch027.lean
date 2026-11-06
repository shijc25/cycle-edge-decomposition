import Cycle12.RationalMajorityCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Batch027

def certificate1080 : RatMajorityCertificate := ⟨0,(500231065899539629/500000000000000000),(1346942437/1133430000),(43912166589663816287/100000000000000000000),(1372255205926994259/3125000000000000000),(356165411479192317/500000000000000000),false⟩
theorem valid1080 : certificate1080.Valid := by decide +kernel
theorem bound1080 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1080.a certificate1080.b certificate1080.c x ≤ (certificate1080.bound:ℝ) :=
  rat_majority_certificate_sound certificate1080 valid1080 x hx0 hx1

def certificate1081 : RatMajorityCertificate := ⟨(38652104723968483/200000000000000000),(80711229634576540579007848394487193/100000000000000000000000000000000000),(1346942437/1133430000),(19868337179866698397/50000000000000000000),(7947334871946679359/20000000000000000000),(356165411479192317/500000000000000000),false⟩
theorem valid1081 : certificate1081.Valid := by decide +kernel
theorem bound1081 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1081.a certificate1081.b certificate1081.c x ≤ (certificate1081.bound:ℝ) :=
  rat_majority_certificate_sound certificate1081 valid1081 x hx0 hx1

def certificate1082 : RatMajorityCertificate := ⟨0,(500231065899539629/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(543289364098608161/1000000000000000000),false⟩
theorem valid1082 : certificate1082.Valid := by decide +kernel
theorem bound1082 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1082.a certificate1082.b certificate1082.c x ≤ (certificate1082.bound:ℝ) :=
  rat_majority_certificate_sound certificate1082 valid1082 x hx0 hx1

def certificate1083 : RatMajorityCertificate := ⟨(154940609775269569/1000000000000000000),(422724959520531903202759253526750099/500000000000000000000000000000000000),1,(7180076986711716913/20000000000000000000),(17950192466779292283/50000000000000000000),(543289364098608161/1000000000000000000),false⟩
theorem valid1083 : certificate1083.Valid := by decide +kernel
theorem bound1083 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1083.a certificate1083.b certificate1083.c x ≤ (certificate1083.bound:ℝ) :=
  rat_majority_certificate_sound certificate1083 valid1083 x hx0 hx1

def certificate1084 : RatMajorityCertificate := ⟨0,(31265305523187043/31250000000000000),(673002823/565825000),(4393576900518494133/10000000000000000000),(43935769005184941331/100000000000000000000),(356613024201688691/500000000000000000),false⟩
theorem valid1084 : certificate1084.Valid := by decide +kernel
theorem bound1084 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1084.a certificate1084.b certificate1084.c x ≤ (certificate1084.bound:ℝ) :=
  rat_majority_certificate_sound certificate1084 valid1084 x hx0 hx1

def certificate1085 : RatMajorityCertificate := ⟨(192661657948553167/1000000000000000000),(25241679924821770803448087428984819/31250000000000000000000000000000000),(673002823/565825000),(2486041987894596271/6250000000000000000),(39776671806313540337/100000000000000000000),(356613024201688691/500000000000000000),false⟩
theorem valid1085 : certificate1085.Valid := by decide +kernel
theorem bound1085 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1085.a certificate1085.b certificate1085.c x ≤ (certificate1085.bound:ℝ) :=
  rat_majority_certificate_sound certificate1085 valid1085 x hx0 hx1

def certificate1086 : RatMajorityCertificate := ⟨0,(31265305523187043/31250000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(67901027898955943/125000000000000000),false⟩
theorem valid1086 : certificate1086.Valid := by decide +kernel
theorem bound1086 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1086.a certificate1086.b certificate1086.c x ≤ (certificate1086.bound:ℝ) :=
  rat_majority_certificate_sound certificate1086 valid1086 x hx0 hx1

def certificate1087 : RatMajorityCertificate := ⟨(7706589576263253/50000000000000000),(1322316398515672972643040673369121/1562500000000000000000000000000000),1,(35920347601420156151/100000000000000000000),(4490043450177519519/12500000000000000000),(67901027898955943/125000000000000000),false⟩
theorem valid1087 : certificate1087.Valid := by decide +kernel
theorem bound1087 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1087.a certificate1087.b certificate1087.c x ≤ (certificate1087.bound:ℝ) :=
  rat_majority_certificate_sound certificate1087 valid1087 x hx0 hx1

def certificate1088 : RatMajorityCertificate := ⟨0,(500258969357328593/500000000000000000),(1344075391/1129910000),(43938562189490126613/100000000000000000000),(21969281094745063307/50000000000000000000),(89153922177171361/125000000000000000),false⟩
theorem valid1088 : certificate1088.Valid := by decide +kernel
theorem bound1088 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1088.a certificate1088.b certificate1088.c x ≤ (certificate1088.bound:ℝ) :=
  rat_majority_certificate_sound certificate1088 valid1088 x hx0 hx1

def certificate1089 : RatMajorityCertificate := ⟨(191407219232125113/1000000000000000000),(404505791136713439953353695971743991/500000000000000000000000000000000000),(1344075391/1129910000),(19905894932790793851/50000000000000000000),(39811789865581587703/100000000000000000000),(89153922177171361/125000000000000000),false⟩
theorem valid1089 : certificate1089.Valid := by decide +kernel
theorem bound1089 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1089.a certificate1089.b certificate1089.c x ≤ (certificate1089.bound:ℝ) :=
  rat_majority_certificate_sound certificate1089 valid1089 x hx0 hx1

def certificate1090 : RatMajorityCertificate := ⟨0,(500258969357328593/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(135799665890183447/250000000000000000),false⟩
theorem valid1090 : certificate1090.Valid := by decide +kernel
theorem bound1090 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1090.a certificate1090.b certificate1090.c x ≤ (certificate1090.bound:ℝ) :=
  rat_majority_certificate_sound certificate1090 valid1090 x hx0 hx1

def certificate1091 : RatMajorityCertificate := ⟨(30788084781383861/200000000000000000),(84649778310244574886804083355962427/100000000000000000000000000000000000),1,(1437005415480507479/4000000000000000000),(280665120211036617/781250000000000000),(135799665890183447/250000000000000000),false⟩
theorem valid1091 : certificate1091.Valid := by decide +kernel
theorem bound1091 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1091.a certificate1091.b certificate1091.c x ≤ (certificate1091.bound:ℝ) :=
  rat_majority_certificate_sound certificate1091 valid1091 x hx0 hx1

def certificate1092 : RatMajorityCertificate := ⟨0,(1000546589763049639/1000000000000000000),(268643897/225642000),(5495245652001745121/12500000000000000000),(43961965216013960969/100000000000000000000),(714120238045222989/1000000000000000000),false⟩
theorem valid1092 : certificate1092.Valid := by decide +kernel
theorem bound1092 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1092.a certificate1092.b certificate1092.c x ≤ (certificate1092.bound:ℝ) :=
  rat_majority_certificate_sound certificate1092 valid1092 x hx0 hx1

def certificate1093 : RatMajorityCertificate := ⟨(1490585497320541/7812500000000000),(6325369996429498641873776722665301/7812500000000000000000000000000000),(268643897/225642000),(1992592907399093233/5000000000000000000),(39851858147981864661/100000000000000000000),(714120238045222989/1000000000000000000),false⟩
theorem valid1093 : certificate1093.Valid := by decide +kernel
theorem bound1093 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1093.a certificate1093.b certificate1093.c x ≤ (certificate1093.bound:ℝ) :=
  rat_majority_certificate_sound certificate1093 valid1093 x hx0 hx1

def certificate1094 : RatMajorityCertificate := ⟨0,(1000546589763049639/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(271559178935745003/500000000000000000),false⟩
theorem valid1094 : certificate1094.Valid := by decide +kernel
theorem bound1094 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1094.a certificate1094.b certificate1094.c x ≤ (certificate1094.bound:ℝ) :=
  rat_majority_certificate_sound certificate1094 valid1094 x hx0 hx1

def certificate1095 : RatMajorityCertificate := ⟨(153132579008469983/1000000000000000000),(847330310054504236268910014529513863/1000000000000000000000000000000000000),1,(8986259763821816509/25000000000000000000),(35945039055287266037/100000000000000000000),(271559178935745003/500000000000000000),false⟩
theorem valid1095 : certificate1095.Valid := by decide +kernel
theorem bound1095 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1095.a certificate1095.b certificate1095.c x ≤ (certificate1095.bound:ℝ) :=
  rat_majority_certificate_sound certificate1095 valid1095 x hx0 hx1

def certificate1096 : RatMajorityCertificate := ⟨0,(500287850845951069/500000000000000000),(335347169/281637500),(43964888391166091227/100000000000000000000),(10991222097791522807/25000000000000000000),(714141746397430143/1000000000000000000),false⟩
theorem valid1096 : certificate1096.Valid := by decide +kernel
theorem bound1096 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1096.a certificate1096.b certificate1096.c x ≤ (certificate1096.bound:ℝ) :=
  rat_majority_certificate_sound certificate1096 valid1096 x hx0 hx1

def certificate1097 : RatMajorityCertificate := ⟨(189635972975471061/1000000000000000000),(405415277482971795095636295168485791/500000000000000000000000000000000000),(335347169/281637500),(39884555845981432537/100000000000000000000),(19942277922990716269/50000000000000000000),(714141746397430143/1000000000000000000),false⟩
theorem valid1097 : certificate1097.Valid := by decide +kernel
theorem bound1097 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1097.a certificate1097.b certificate1097.c x ≤ (certificate1097.bound:ℝ) :=
  rat_majority_certificate_sound certificate1097 valid1097 x hx0 hx1

def certificate1098 : RatMajorityCertificate := ⟨0,(500287850845951069/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(271554534474063121/500000000000000000),false⟩
theorem valid1098 : certificate1098.Valid := by decide +kernel
theorem bound1098 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1098.a certificate1098.b certificate1098.c x ≤ (certificate1098.bound:ℝ) :=
  rat_majority_certificate_sound certificate1098 valid1098 x hx0 hx1

def certificate1099 : RatMajorityCertificate := ⟨(4779350536539371/31250000000000000),(13242944330571245852796445541962401/15625000000000000000000000000000000),1,(1123433410959569191/3125000000000000000),(35949869150706214113/100000000000000000000),(271554534474063121/500000000000000000),false⟩
theorem valid1099 : certificate1099.Valid := by decide +kernel
theorem bound1099 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1099.a certificate1099.b certificate1099.c x ≤ (certificate1099.bound:ℝ) :=
  rat_majority_certificate_sound certificate1099 valid1099 x hx0 hx1

def certificate1100 : RatMajorityCertificate := ⟨0,(1000605248765683253/1000000000000000000),(2679152971/2249850000),(2198367804403888393/5000000000000000000),(43967356088077767861/100000000000000000000),(714136237924556893/1000000000000000000),false⟩
theorem valid1100 : certificate1100.Valid := by decide +kernel
theorem bound1100 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1100.a certificate1100.b certificate1100.c x ≤ (certificate1100.bound:ℝ) :=
  rat_majority_certificate_sound certificate1100 valid1100 x hx0 hx1

def certificate1101 : RatMajorityCertificate := ⟨(188375975015340831/1000000000000000000),(812115259423980007655926019616196757/1000000000000000000000000000000000000),(2679152971/2249850000),(19959639296110918327/50000000000000000000),(7983855718444367331/20000000000000000000),(714136237924556893/1000000000000000000),false⟩
theorem valid1101 : certificate1101.Valid := by decide +kernel
theorem bound1101 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1101.a certificate1101.b certificate1101.c x ≤ (certificate1101.bound:ℝ) :=
  rat_majority_certificate_sound certificate1101 valid1101 x hx0 hx1

def certificate1102 : RatMajorityCertificate := ⟨0,(1000605248765683253/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(27150398110855889/50000000000000000),false⟩
theorem valid1102 : certificate1102.Valid := by decide +kernel
theorem bound1102 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1102.a certificate1102.b certificate1102.c x ≤ (certificate1102.bound:ℝ) :=
  rat_majority_certificate_sound certificate1102 valid1102 x hx0 hx1

def certificate1103 : RatMajorityCertificate := ⟨(151944131397098933/1000000000000000000),(848569153370603411862609470217730951/1000000000000000000000000000000000000),1,(1798715823051870513/5000000000000000000),(35974316461037410261/100000000000000000000),(27150398110855889/50000000000000000),false⟩
theorem valid1103 : certificate1103.Valid := by decide +kernel
theorem bound1103 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1103.a certificate1103.b certificate1103.c x ≤ (certificate1103.bound:ℝ) :=
  rat_majority_certificate_sound certificate1103 valid1103 x hx0 hx1

def certificate1104 : RatMajorityCertificate := ⟨0,(1000635197090143403/1000000000000000000),(668913687/561672500),(5496252712727680769/12500000000000000000),(43970021701821446153/100000000000000000000),(714148615317772683/1000000000000000000),false⟩
theorem valid1104 : certificate1104.Valid := by decide +kernel
theorem bound1104 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1104.a certificate1104.b certificate1104.c x ≤ (certificate1104.bound:ℝ) :=
  rat_majority_certificate_sound certificate1104 valid1104 x hx0 hx1

def certificate1105 : RatMajorityCertificate := ⟨(23401525366137269/125000000000000000),(101663009689313168948248572607213593/125000000000000000000000000000000000),(668913687/561672500),(9987922050755936589/25000000000000000000),(39951688203023746357/100000000000000000000),(714148615317772683/1000000000000000000),false⟩
theorem valid1105 : certificate1105.Valid := by decide +kernel
theorem bound1105 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1105.a certificate1105.b certificate1105.c x ≤ (certificate1105.bound:ℝ) :=
  rat_majority_certificate_sound certificate1105 valid1105 x hx0 hx1

def certificate1106 : RatMajorityCertificate := ⟨0,(1000635197090143403/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(67863568005820287/125000000000000000),false⟩
theorem valid1106 : certificate1106.Valid := by decide +kernel
theorem bound1106 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1106.a certificate1106.b certificate1106.c x ≤ (certificate1106.bound:ℝ) :=
  rat_majority_certificate_sound certificate1106 valid1106 x hx0 hx1

def certificate1107 : RatMajorityCertificate := ⟨(75479729664014737/500000000000000000),(424789924376409571641667475964669989/500000000000000000000000000000000000),1,(35998464920829319753/100000000000000000000),(17999232460414659877/50000000000000000000),(67863568005820287/125000000000000000),false⟩
theorem valid1107 : certificate1107.Valid := by decide +kernel
theorem bound1107 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1107.a certificate1107.b certificate1107.c x ≤ (certificate1107.bound:ℝ) :=
  rat_majority_certificate_sound certificate1107 valid1107 x hx0 hx1

def certificate1108 : RatMajorityCertificate := ⟨0,(12508319078719077/12500000000000000),(2672223999/2243590000),(43972654309019984059/100000000000000000000),(2198632715450999203/5000000000000000000),(142832342628043919/200000000000000000),false⟩
theorem valid1108 : certificate1108.Valid := by decide +kernel
theorem bound1108 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1108.a certificate1108.b certificate1108.c x ≤ (certificate1108.bound:ℝ) :=
  rat_majority_certificate_sound certificate1108 valid1108 x hx0 hx1

def certificate1109 : RatMajorityCertificate := ⟨(186061956470394847/1000000000000000000),(10180996758776638719604146818603781/12500000000000000000000000000000000),(2672223999/2243590000),(624744579473156029/1562500000000000000),(39983653086281985857/100000000000000000000),(142832342628043919/200000000000000000),false⟩
theorem valid1109 : certificate1109.Valid := by decide +kernel
theorem bound1109 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1109.a certificate1109.b certificate1109.c x ≤ (certificate1109.bound:ℝ) :=
  rat_majority_certificate_sound certificate1109 valid1109 x hx0 hx1

def certificate1110 : RatMajorityCertificate := ⟨0,(12508319078719077/12500000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(542897763879778503/1000000000000000000),false⟩
theorem valid1110 : certificate1110.Valid := by decide +kernel
theorem bound1110 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1110.a certificate1110.b certificate1110.c x ≤ (certificate1110.bound:ℝ) :=
  rat_majority_certificate_sound certificate1110 valid1110 x hx0 hx1

def certificate1111 : RatMajorityCertificate := ⟨(37686710870677039/250000000000000000),(2655682365081910005306996124826997/3125000000000000000000000000000000),1,(36003747773788025547/100000000000000000000),(9000936943447006387/25000000000000000000),(542897763879778503/1000000000000000000),false⟩
theorem valid1111 : certificate1111.Valid := by decide +kernel
theorem bound1111 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1111.a certificate1111.b certificate1111.c x ≤ (certificate1111.bound:ℝ) :=
  rat_majority_certificate_sound certificate1111 valid1111 x hx0 hx1

def certificate1112 : RatMajorityCertificate := ⟨0,(62543512622288661/62500000000000000),(1334412831/1120285000),(21987329614932272909/50000000000000000000),(43974659229864545819/100000000000000000000),(357068456338098407/500000000000000000),false⟩
theorem valid1112 : certificate1112.Valid := by decide +kernel
theorem bound1112 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1112.a certificate1112.b certificate1112.c x ≤ (certificate1112.bound:ℝ) :=
  rat_majority_certificate_sound certificate1112 valid1112 x hx0 hx1

def certificate1113 : RatMajorityCertificate := ⟨(184767789135185571/1000000000000000000),(50987486070319812521069671035889569/62500000000000000000000000000000000),(1334412831/1120285000),(40018529733450480063/100000000000000000000),(625289527085163751/1562500000000000000),(357068456338098407/500000000000000000),false⟩
theorem valid1113 : certificate1113.Valid := by decide +kernel
theorem bound1113 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1113.a certificate1113.b certificate1113.c x ≤ (certificate1113.bound:ℝ) :=
  rat_majority_certificate_sound certificate1113 valid1113 x hx0 hx1

def certificate1114 : RatMajorityCertificate := ⟨0,(62543512622288661/62500000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(135700386939407563/250000000000000000),false⟩
theorem valid1114 : certificate1114.Valid := by decide +kernel
theorem bound1114 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1114.a certificate1114.b certificate1114.c x ≤ (certificate1114.bound:ℝ) :=
  rat_majority_certificate_sound certificate1114 valid1114 x hx0 hx1

def certificate1115 : RatMajorityCertificate := ⟨(1497839687978449/10000000000000000),(531754970791641575402345174933211/625000000000000000000000000000000),1,(36027312574365162563/100000000000000000000),(9006828143591290641/25000000000000000000),(135700386939407563/250000000000000000),false⟩
theorem valid1115 : certificate1115.Valid := by decide +kernel
theorem bound1115 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1115.a certificate1115.b certificate1115.c x ≤ (certificate1115.bound:ℝ) :=
  rat_majority_certificate_sound certificate1115 valid1115 x hx0 hx1

def certificate1116 : RatMajorityCertificate := ⟨0,(500363597414956843/500000000000000000),(2665998839/2237630000),(21990740713864559953/50000000000000000000),(43981481427729119907/100000000000000000000),(714435441265451647/1000000000000000000),false⟩
theorem valid1116 : certificate1116.Valid := by decide +kernel
theorem bound1116 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1116.a certificate1116.b certificate1116.c x ≤ (certificate1116.bound:ℝ) :=
  rat_majority_certificate_sound certificate1116 valid1116 x hx0 hx1

def certificate1117 : RatMajorityCertificate := ⟨(184858132885527197/1000000000000000000),(407867317032942318242699544942240929/500000000000000000000000000000000000),(2665998839/2237630000),(8004689757541232193/20000000000000000000),(20011724393853080483/50000000000000000000),(714435441265451647/1000000000000000000),false⟩
theorem valid1117 : certificate1117.Valid := by decide +kernel
theorem bound1117 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1117.a certificate1117.b certificate1117.c x ≤ (certificate1117.bound:ℝ) :=
  rat_majority_certificate_sound certificate1117 valid1117 x hx0 hx1

def certificate1118 : RatMajorityCertificate := ⟨0,(500363597414956843/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(271352490828728283/500000000000000000),false⟩
theorem valid1118 : certificate1118.Valid := by decide +kernel
theorem bound1118 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1118.a certificate1118.b certificate1118.c x ≤ (certificate1118.bound:ℝ) :=
  rat_majority_certificate_sound certificate1118 valid1118 x hx0 hx1

def certificate1119 : RatMajorityCertificate := ⟨(37203535320485789/250000000000000000),(106475604584226532013549190770195873/125000000000000000000000000000000000),1,(90127511317264031/250000000000000000),(36051004526905612401/100000000000000000000),(271352490828728283/500000000000000000),false⟩
theorem valid1119 : certificate1119.Valid := by decide +kernel
theorem bound1119 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1119.a certificate1119.b certificate1119.c x ≤ (certificate1119.bound:ℝ) :=
  rat_majority_certificate_sound certificate1119 valid1119 x hx0 hx1

end Cycle12.MajorityCertificates.Batch027
