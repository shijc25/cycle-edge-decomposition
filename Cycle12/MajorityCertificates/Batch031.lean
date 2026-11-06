import Cycle12.RationalMajorityCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Batch031

def certificate1240 : RatMajorityCertificate := ⟨0,(250355309764807189/250000000000000000),(2528641673/2191270000),(336865324782609399/781250000000000000),(43118761572174003073/100000000000000000000),(338506157266019787/500000000000000000),false⟩
theorem valid1240 : certificate1240.Valid := by decide +kernel
theorem bound1240 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1240.a certificate1240.b certificate1240.c x ≤ (certificate1240.bound:ℝ) :=
  rat_majority_certificate_sound certificate1240 valid1240 x hx0 hx1

def certificate1241 : RatMajorityCertificate := ⟨(70206913842783073/500000000000000000),(107600981219662508414651333002088203/125000000000000000000000000000000000),(2528641673/2191270000),(20107080237948378809/50000000000000000000),(40214160475896757619/100000000000000000000),(338506157266019787/500000000000000000),false⟩
theorem valid1241 : certificate1241.Valid := by decide +kernel
theorem bound1241 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1241.a certificate1241.b certificate1241.c x ≤ (certificate1241.bound:ℝ) :=
  rat_majority_certificate_sound certificate1241 valid1241 x hx0 hx1

def certificate1242 : RatMajorityCertificate := ⟨0,(250355309764807189/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(540638710442496913/1000000000000000000),false⟩
theorem valid1242 : certificate1242.Valid := by decide +kernel
theorem bound1242 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1242.a certificate1242.b certificate1242.c x ≤ (certificate1242.bound:ℝ) :=
  rat_majority_certificate_sound certificate1242 valid1242 x hx0 hx1

def certificate1243 : RatMajorityCertificate := ⟨(12726823761016103/100000000000000000),(21849303071469423973898039480835533/25000000000000000000000000000000000),1,(7313281739666477151/20000000000000000000),(9141602174583096439/25000000000000000000),(540638710442496913/1000000000000000000),false⟩
theorem valid1243 : certificate1243.Valid := by decide +kernel
theorem bound1243 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1243.a certificate1243.b certificate1243.c x ≤ (certificate1243.bound:ℝ) :=
  rat_majority_certificate_sound certificate1243 valid1243 x hx0 hx1

def certificate1244 : RatMajorityCertificate := ⟨0,(250359063763244259/250000000000000000),(360596011/312940000),(43079431864397762587/100000000000000000000),(10769857966099440647/25000000000000000000),(675399130069886999/1000000000000000000),false⟩
theorem valid1244 : certificate1244.Valid := by decide +kernel
theorem bound1244 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1244.a certificate1244.b certificate1244.c x ≤ (certificate1244.bound:ℝ) :=
  rat_majority_certificate_sound certificate1244 valid1244 x hx0 hx1

def certificate1245 : RatMajorityCertificate := ⟨(139127030847751323/1000000000000000000),(215527350576041234550447550660595343/250000000000000000000000000000000000),(360596011/312940000),(2010194195806467393/5000000000000000000),(40203883916129347861/100000000000000000000),(675399130069886999/1000000000000000000),false⟩
theorem valid1245 : certificate1245.Valid := by decide +kernel
theorem bound1245 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1245.a certificate1245.b certificate1245.c x ≤ (certificate1245.bound:ℝ) :=
  rat_majority_certificate_sound certificate1245 valid1245 x hx0 hx1

def certificate1246 : RatMajorityCertificate := ⟨0,(250359063763244259/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(527878518766241/976562500000000),false⟩
theorem valid1246 : certificate1246.Valid := by decide +kernel
theorem bound1246 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1246.a certificate1246.b certificate1246.c x ≤ (certificate1246.bound:ℝ) :=
  rat_majority_certificate_sound certificate1246 valid1246 x hx0 hx1

def certificate1247 : RatMajorityCertificate := ⟨(6317714241011013/50000000000000000),(10936256165658980438184982971975633/12500000000000000000000000000000000),1,(1463511247333307021/4000000000000000000),(18293890591666337763/50000000000000000000),(527878518766241/976562500000000),false⟩
theorem valid1247 : certificate1247.Valid := by decide +kernel
theorem bound1247 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1247.a certificate1247.b certificate1247.c x ≤ (certificate1247.bound:ℝ) :=
  rat_majority_certificate_sound certificate1247 valid1247 x hx0 hx1

def certificate1248 : RatMajorityCertificate := ⟨0,(500725591330549761/500000000000000000),(3149677/2737375),(43040310862961848443/100000000000000000000),(10760077715740462111/25000000000000000000),(84225431495097947/125000000000000000),false⟩
theorem valid1248 : certificate1248.Valid := by decide +kernel
theorem bound1248 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1248.a certificate1248.b certificate1248.c x ≤ (certificate1248.bound:ℝ) :=
  rat_majority_certificate_sound certificate1248 valid1248 x hx0 hx1

def certificate1249 : RatMajorityCertificate := ⟨(27583286205381401/200000000000000000),(86333460970080554141083589985604839/100000000000000000000000000000000000),(3149677/2737375),(40192001862413450699/100000000000000000000),(401920018624134507/1000000000000000000),(84225431495097947/125000000000000000),false⟩
theorem valid1249 : certificate1249.Valid := by decide +kernel
theorem bound1249 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1249.a certificate1249.b certificate1249.c x ≤ (certificate1249.bound:ℝ) :=
  rat_majority_certificate_sound certificate1249 valid1249 x hx0 hx1

def certificate1250 : RatMajorityCertificate := ⟨0,(500725591330549761/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(21618200723668247/40000000000000000),false⟩
theorem valid1250 : certificate1250.Valid := by decide +kernel
theorem bound1250 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1250.a certificate1250.b certificate1250.c x ≤ (certificate1250.bound:ℝ) :=
  rat_majority_certificate_sound certificate1250 valid1250 x hx0 hx1

def certificate1251 : RatMajorityCertificate := ⟨(125424652084568221/1000000000000000000),(437922258248075867789894211760254819/500000000000000000000000000000000000),1,(9152370763574514821/25000000000000000000),(7321896610859611857/20000000000000000000),(21618200723668247/40000000000000000),false⟩
theorem valid1251 : certificate1251.Valid := by decide +kernel
theorem bound1251 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1251.a certificate1251.b certificate1251.c x ≤ (certificate1251.bound:ℝ) :=
  rat_majority_certificate_sound certificate1251 valid1251 x hx0 hx1

def certificate1252 : RatMajorityCertificate := ⟨0,(500726880851974343/500000000000000000),(503570583/438008000),(21509148429272392201/50000000000000000000),(43018296858544784403/100000000000000000000),(336431988516153173/500000000000000000),false⟩
theorem valid1252 : certificate1252.Valid := by decide +kernel
theorem bound1252 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1252.a certificate1252.b certificate1252.c x ≤ (certificate1252.bound:ℝ) :=
  rat_majority_certificate_sound certificate1252 valid1252 x hx0 hx1

def certificate1253 : RatMajorityCertificate := ⟨(34194951693725593/250000000000000000),(108059388710510432487781560681539601/125000000000000000000000000000000000),(503570583/438008000),(8039170617004877451/20000000000000000000),(5024481635628048407/12500000000000000000),(336431988516153173/500000000000000000),false⟩
theorem valid1253 : certificate1253.Valid := by decide +kernel
theorem bound1253 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1253.a certificate1253.b certificate1253.c x ≤ (certificate1253.bound:ℝ) :=
  rat_majority_certificate_sound certificate1253 valid1253 x hx0 hx1

def certificate1254 : RatMajorityCertificate := ⟨0,(500726880851974343/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(540419139393352273/1000000000000000000),false⟩
theorem valid1254 : certificate1254.Valid := by decide +kernel
theorem bound1254 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1254.a certificate1254.b certificate1254.c x ≤ (certificate1254.bound:ℝ) :=
  rat_majority_certificate_sound certificate1254 valid1254 x hx0 hx1

def certificate1255 : RatMajorityCertificate := ⟨(31269402143744239/250000000000000000),(109524290011450493090136390417940023/125000000000000000000000000000000000),1,(18308783817297442523/50000000000000000000),(36617567634594885047/100000000000000000000),(540419139393352273/1000000000000000000),false⟩
theorem valid1255 : certificate1255.Valid := by decide +kernel
theorem bound1255 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1255.a certificate1255.b certificate1255.c x ≤ (certificate1255.bound:ℝ) :=
  rat_majority_certificate_sound certificate1255 valid1255 x hx0 hx1

def certificate1256 : RatMajorityCertificate := ⟨0,(1001461128321935677/1000000000000000000),(2515669263/2189710000),(8599780091742938011/20000000000000000000),(5374862557339336257/12500000000000000000),(33603937210470561/50000000000000000),false⟩
theorem valid1256 : certificate1256.Valid := by decide +kernel
theorem bound1256 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1256.a certificate1256.b certificate1256.c x ≤ (certificate1256.bound:ℝ) :=
  rat_majority_certificate_sound certificate1256 valid1256 x hx0 hx1

def certificate1257 : RatMajorityCertificate := ⟨(532133280599949/3906250000000000),(3379046736900283108054602452519527/3906250000000000000000000000000000),(2515669263/2189710000),(10047211628543683589/25000000000000000000),(40188846514174734357/100000000000000000000),(33603937210470561/50000000000000000),false⟩
theorem valid1257 : certificate1257.Valid := by decide +kernel
theorem bound1257 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1257.a certificate1257.b certificate1257.c x ≤ (certificate1257.bound:ℝ) :=
  rat_majority_certificate_sound certificate1257 valid1257 x hx0 hx1

def certificate1258 : RatMajorityCertificate := ⟨0,(1001461128321935677/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(108069597169435423/200000000000000000),false⟩
theorem valid1258 : certificate1258.Valid := by decide +kernel
theorem bound1258 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1258.a certificate1258.b certificate1258.c x ≤ (certificate1258.bound:ℝ) :=
  rat_majority_certificate_sound certificate1258 valid1258 x hx0 hx1

def certificate1259 : RatMajorityCertificate := ⟨(62189353820145433/500000000000000000),(438450343714632912319490519788686859/500000000000000000000000000000000000),1,(9158459777432069247/25000000000000000000),(36633839109728276989/100000000000000000000),(108069597169435423/200000000000000000),false⟩
theorem valid1259 : certificate1259.Valid := by decide +kernel
theorem bound1259 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1259.a certificate1259.b certificate1259.c x ≤ (certificate1259.bound:ℝ) :=
  rat_majority_certificate_sound certificate1259 valid1259 x hx0 hx1

def certificate1260 : RatMajorityCertificate := ⟨0,(500734236370344571/500000000000000000),(62836261/54734500),(42979104379813601071/100000000000000000000),(2686194023738350067/6250000000000000000),(671265471129192551/1000000000000000000),false⟩
theorem valid1260 : certificate1260.Valid := by decide +kernel
theorem bound1260 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1260.a certificate1260.b certificate1260.c x ≤ (certificate1260.bound:ℝ) :=
  rat_majority_certificate_sound certificate1260 valid1260 x hx0 hx1

def certificate1261 : RatMajorityCertificate := ⟨(67758450281149631/500000000000000000),(216438142326002865618535894520496699/250000000000000000000000000000000000),(62836261/54734500),(40185024703402529403/100000000000000000000),(10046256175850632351/25000000000000000000),(671265471129192551/1000000000000000000),false⟩
theorem valid1261 : certificate1261.Valid := by decide +kernel
theorem bound1261 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1261.a certificate1261.b certificate1261.c x ≤ (certificate1261.bound:ℝ) :=
  rat_majority_certificate_sound certificate1261 valid1261 x hx0 hx1

def certificate1262 : RatMajorityCertificate := ⟨0,(500734236370344571/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(135081833990635961/250000000000000000),false⟩
theorem valid1262 : certificate1262.Valid := by decide +kernel
theorem bound1262 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1262.a certificate1262.b certificate1262.c x ≤ (certificate1262.bound:ℝ) :=
  rat_majority_certificate_sound certificate1262 valid1262 x hx0 hx1

def certificate1263 : RatMajorityCertificate := ⟨(124153103291150063/1000000000000000000),(438566527000842030865663473821642027/500000000000000000000000000000000000),1,(36639099669032840557/100000000000000000000),(18319549834516420279/50000000000000000000),(135081833990635961/250000000000000000),false⟩
theorem valid1263 : certificate1263.Valid := by decide +kernel
theorem bound1263 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1263.a certificate1263.b certificate1263.c x ≤ (certificate1263.bound:ℝ) :=
  rat_majority_certificate_sound certificate1263 valid1263 x hx0 hx1

def certificate1264 : RatMajorityCertificate := ⟨0,(500737893913241227/500000000000000000),(2511264683/2189060000),(21479759582583610881/50000000000000000000),(42959519165167221763/100000000000000000000),(670468530351266337/1000000000000000000),false⟩
theorem valid1264 : certificate1264.Valid := by decide +kernel
theorem bound1264 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1264.a certificate1264.b certificate1264.c x ≤ (certificate1264.bound:ℝ) :=
  rat_majority_certificate_sound certificate1264 valid1264 x hx0 hx1

def certificate1265 : RatMajorityCertificate := ⟨(67447493775743281/500000000000000000),(216595430973628476489318410222554213/250000000000000000000000000000000000),(2511264683/2189060000),(40179383975693511643/100000000000000000000),(10044845993923377911/25000000000000000000),(670468530351266337/1000000000000000000),false⟩
theorem valid1265 : certificate1265.Valid := by decide +kernel
theorem bound1265 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1265.a certificate1265.b certificate1265.c x ≤ (certificate1265.bound:ℝ) :=
  rat_majority_certificate_sound certificate1265 valid1265 x hx0 hx1

def certificate1266 : RatMajorityCertificate := ⟨0,(500737893913241227/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(270156264814551641/500000000000000000),false⟩
theorem valid1266 : certificate1266.Valid := by decide +kernel
theorem bound1266 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1266.a certificate1266.b certificate1266.c x ≤ (certificate1266.bound:ℝ) :=
  rat_majority_certificate_sound certificate1266 valid1266 x hx0 hx1

def certificate1267 : RatMajorityCertificate := ⟨(61991188883379553/500000000000000000),(219327609593979204012451868111568469/250000000000000000000000000000000000),1,(36643083557531815401/100000000000000000000),(18321541778765907701/50000000000000000000),(270156264814551641/500000000000000000),false⟩
theorem valid1267 : certificate1267.Valid := by decide +kernel
theorem bound1267 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1267.a certificate1267.b certificate1267.c x ≤ (certificate1267.bound:ℝ) :=
  rat_majority_certificate_sound certificate1267 valid1267 x hx0 hx1

def certificate1268 : RatMajorityCertificate := ⟨0,(40059323195068479/40000000000000000),(627275531/547185000),(5367520365155285073/12500000000000000000),(8588032584248456117/20000000000000000000),(26787511164796519/40000000000000000),false⟩
theorem valid1268 : certificate1268.Valid := by decide +kernel
theorem bound1268 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1268.a certificate1268.b certificate1268.c x ≤ (certificate1268.bound:ℝ) :=
  rat_majority_certificate_sound certificate1268 valid1268 x hx0 hx1

def certificate1269 : RatMajorityCertificate := ⟨(134351108587654899/1000000000000000000),(34677308714539871184268943675171379/40000000000000000000000000000000000),(627275531/547185000),(20086081547085454869/50000000000000000000),(40172163094170909739/100000000000000000000),(26787511164796519/40000000000000000),false⟩
theorem valid1269 : certificate1269.Valid := by decide +kernel
theorem bound1269 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1269.a certificate1269.b certificate1269.c x ≤ (certificate1269.bound:ℝ) :=
  rat_majority_certificate_sound certificate1269 valid1269 x hx0 hx1

def certificate1270 : RatMajorityCertificate := ⟨0,(40059323195068479/40000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(540238805450822753/1000000000000000000),false⟩
theorem valid1270 : certificate1270.Valid := by decide +kernel
theorem bound1270 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1270.a certificate1270.b certificate1270.c x ≤ (certificate1270.bound:ℝ) :=
  rat_majority_certificate_sound certificate1270 valid1270 x hx0 hx1

def certificate1271 : RatMajorityCertificate := ⟨(61628788000495123/500000000000000000),(17560854060902047269948236109472083/20000000000000000000000000000000000),1,(36659923307316708023/100000000000000000000),(4582490413414588503/12500000000000000000),(540238805450822753/1000000000000000000),false⟩
theorem valid1271 : certificate1271.Valid := by decide +kernel
theorem bound1271 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1271.a certificate1271.b certificate1271.c x ≤ (certificate1271.bound:ℝ) :=
  rat_majority_certificate_sound certificate1271 valid1271 x hx0 hx1

def certificate1272 : RatMajorityCertificate := ⟨0,(500745170845787897/500000000000000000),(2506938113/2188430000),(858412931337833611/2000000000000000000),(42920646566891680551/100000000000000000000),(66889814388740311/100000000000000000),false⟩
theorem valid1272 : certificate1272.Valid := by decide +kernel
theorem bound1272 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1272.a certificate1272.b certificate1272.c x ≤ (certificate1272.bound:ℝ) :=
  rat_majority_certificate_sound certificate1272 valid1272 x hx0 hx1

def certificate1273 : RatMajorityCertificate := ⟨(16720888208735149/125000000000000000),(54220242332947084579981471297308347/62500000000000000000000000000000000),(2506938113/2188430000),(40165697220377134209/100000000000000000000),(4016569722037713421/10000000000000000000),(66889814388740311/100000000000000000),false⟩
theorem valid1273 : certificate1273.Valid := by decide +kernel
theorem bound1273 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1273.a certificate1273.b certificate1273.c x ≤ (certificate1273.bound:ℝ) :=
  rat_majority_certificate_sound certificate1273 valid1273 x hx0 hx1

def certificate1274 : RatMajorityCertificate := ⟨0,(500745170845787897/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(2110226287156371/3906250000000000),false⟩
theorem valid1274 : certificate1274.Valid := by decide +kernel
theorem bound1274 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1274.a certificate1274.b certificate1274.c x ≤ (certificate1274.bound:ℝ) :=
  rat_majority_certificate_sound certificate1274 valid1274 x hx0 hx1

def certificate1275 : RatMajorityCertificate := ⟨(123029502224255999/1000000000000000000),(439138741735430584702014866216155897/500000000000000000000000000000000000),1,(36665230140295997579/100000000000000000000),(1833261507014799879/5000000000000000000),(2110226287156371/3906250000000000),false⟩
theorem valid1275 : certificate1275.Valid := by decide +kernel
theorem bound1275 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1275.a certificate1275.b certificate1275.c x ≤ (certificate1275.bound:ℝ) :=
  rat_majority_certificate_sound certificate1275 valid1275 x hx0 hx1

def certificate1276 : RatMajorityCertificate := ⟨0,(500754954232798727/500000000000000000),(1250987321/1093665000),(5360077093577296397/12500000000000000000),(42880616748618371177/100000000000000000000),(333601928615426543/500000000000000000),false⟩
theorem valid1276 : certificate1276.Valid := by decide +kernel
theorem bound1276 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1276.a certificate1276.b certificate1276.c x ≤ (certificate1276.bound:ℝ) :=
  rat_majority_certificate_sound certificate1276 valid1276 x hx0 hx1

def certificate1277 : RatMajorityCertificate := ⟨(32912081855026759/250000000000000000),(108707850515179631619415885953864207/125000000000000000000000000000000000),(1250987321/1093665000),(40173628327234779103/100000000000000000000),(1255425885226086847/3125000000000000000),(333601928615426543/500000000000000000),false⟩
theorem valid1277 : certificate1277.Valid := by decide +kernel
theorem bound1277 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1277.a certificate1277.b certificate1277.c x ≤ (certificate1277.bound:ℝ) :=
  rat_majority_certificate_sound certificate1277 valid1277 x hx0 hx1

def certificate1278 : RatMajorityCertificate := ⟨0,(500754954232798727/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(270098482465613537/500000000000000000),false⟩
theorem valid1278 : certificate1278.Valid := by decide +kernel
theorem bound1278 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1278.a certificate1278.b certificate1278.c x ≤ (certificate1278.bound:ℝ) :=
  rat_majority_certificate_sound certificate1278 valid1278 x hx0 hx1

def certificate1279 : RatMajorityCertificate := ⟨(122746904662947999/1000000000000000000),(439288833606086493107638295765602727/500000000000000000000000000000000000),1,(36671828881929128699/100000000000000000000),(366718288819291287/1000000000000000000),(270098482465613537/500000000000000000),false⟩
theorem valid1279 : certificate1279.Valid := by decide +kernel
theorem bound1279 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1279.a certificate1279.b certificate1279.c x ≤ (certificate1279.bound:ℝ) :=
  rat_majority_certificate_sound certificate1279 valid1279 x hx0 hx1

end Cycle12.MajorityCertificates.Batch031
