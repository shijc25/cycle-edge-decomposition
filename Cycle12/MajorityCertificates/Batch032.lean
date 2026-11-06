import Cycle12.RationalMajorityCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Batch032

def certificate1280 : RatMajorityCertificate := ⟨0,(1001524323377492271/1000000000000000000),(178431137/156195000),(42845398529299769593/100000000000000000000),(21422699264649884797/50000000000000000000),(332954377810346047/500000000000000000),false⟩
theorem valid1280 : certificate1280.Valid := by decide +kernel
theorem bound1280 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1280.a certificate1280.b certificate1280.c x ≤ (certificate1280.bound:ℝ) :=
  rat_majority_certificate_sound certificate1280 valid1280 x hx0 hx1

def certificate1281 : RatMajorityCertificate := ⟨(66018296289630141/500000000000000000),(434643232166739500020657101323859789/500000000000000000000000000000000000),(178431137/156195000),(40128697089234698879/100000000000000000000),(62701089201929217/156250000000000000),(332954377810346047/500000000000000000),false⟩
theorem valid1281 : certificate1281.Valid := by decide +kernel
theorem bound1281 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1281.a certificate1281.b certificate1281.c x ≤ (certificate1281.bound:ℝ) :=
  rat_majority_certificate_sound certificate1281 valid1281 x hx0 hx1

def certificate1282 : RatMajorityCertificate := ⟨0,(1001524323377492271/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(33756807810488003/62500000000000000),false⟩
theorem valid1282 : certificate1282.Valid := by decide +kernel
theorem bound1282 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1282.a certificate1282.b certificate1282.c x ≤ (certificate1282.bound:ℝ) :=
  rat_majority_certificate_sound certificate1282 valid1282 x hx0 hx1

def certificate1283 : RatMajorityCertificate := ⟨(30463350979200769/250000000000000000),(219871293867117950952787040945243601/250000000000000000000000000000000000),1,(18346275911429660523/50000000000000000000),(36692551822859321047/100000000000000000000),(33756807810488003/62500000000000000),false⟩
theorem valid1283 : certificate1283.Valid := by decide +kernel
theorem bound1283 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1283.a certificate1283.b certificate1283.c x ≤ (certificate1283.bound:ℝ) :=
  rat_majority_certificate_sound certificate1283 valid1283 x hx0 hx1

def certificate1284 : RatMajorityCertificate := ⟨0,(1001538629846823003/1000000000000000000),(1246864667/1093070000),(21402997063921727419/50000000000000000000),(42805994127843454839/100000000000000000000),(664309187908522527/1000000000000000000),false⟩
theorem valid1284 : certificate1284.Valid := by decide +kernel
theorem bound1284 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1284.a certificate1284.b certificate1284.c x ≤ (certificate1284.bound:ℝ) :=
  rat_majority_certificate_sound certificate1284 valid1284 x hx0 hx1

def certificate1285 : RatMajorityCertificate := ⟨(65355195394021841/500000000000000000),(435313562075111469243586667356791477/500000000000000000000000000000000000),(1246864667/1093070000),(20059472143392824333/50000000000000000000),(40118944286785648667/100000000000000000000),(664309187908522527/1000000000000000000),false⟩
theorem valid1285 : certificate1285.Valid := by decide +kernel
theorem bound1285 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1285.a certificate1285.b certificate1285.c x ≤ (certificate1285.bound:ℝ) :=
  rat_majority_certificate_sound certificate1285 valid1285 x hx0 hx1

def certificate1286 : RatMajorityCertificate := ⟨0,(1001538629846823003/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(540015549326937759/1000000000000000000),false⟩
theorem valid1286 : certificate1286.Valid := by decide +kernel
theorem bound1286 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1286.a certificate1286.b certificate1286.c x ≤ (certificate1286.bound:ℝ) :=
  rat_majority_certificate_sound certificate1286 valid1286 x hx0 hx1

def certificate1287 : RatMajorityCertificate := ⟨(120907731985031791/1000000000000000000),(880444865616647365834961688694911627/1000000000000000000000000000000000000),1,(91786114965236958745753/250000000000000000000000),(367144459860947834983013/1000000000000000000000000),(540015549326937759/1000000000000000000),false⟩
theorem valid1287 : certificate1287.Valid := by decide +kernel
theorem bound1287 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1287.a certificate1287.b certificate1287.c x ≤ (certificate1287.bound:ℝ) :=
  rat_majority_certificate_sound certificate1287 valid1287 x hx0 hx1

def certificate1288 : RatMajorityCertificate := ⟨0,(500776408781975263/500000000000000000),(1244753077/1092785000),(21383582756395012493/50000000000000000000),(42767165512790024987/100000000000000000000),(662750328479416491/1000000000000000000),false⟩
theorem valid1288 : certificate1288.Valid := by decide +kernel
theorem bound1288 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1288.a certificate1288.b certificate1288.c x ≤ (certificate1288.bound:ℝ) :=
  rat_majority_certificate_sound certificate1288 valid1288 x hx0 hx1

def certificate1289 : RatMajorityCertificate := ⟨(129570669445581597/1000000000000000000),(435890474253540501066641690497964989/500000000000000000000000000000000000),(1244753077/1092785000),(40105450942340706991/100000000000000000000),(2506590683896294187/6250000000000000000),(662750328479416491/1000000000000000000),false⟩
theorem valid1289 : certificate1289.Valid := by decide +kernel
theorem bound1289 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1289.a certificate1289.b certificate1289.c x ≤ (certificate1289.bound:ℝ) :=
  rat_majority_certificate_sound certificate1289 valid1289 x hx0 hx1

def certificate1290 : RatMajorityCertificate := ⟨0,(500776408781975263/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(53997884207366611/100000000000000000),false⟩
theorem valid1290 : certificate1290.Valid := by decide +kernel
theorem bound1290 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1290.a certificate1290.b certificate1290.c x ≤ (certificate1290.bound:ℝ) :=
  rat_majority_certificate_sound certificate1290 valid1290 x hx0 hx1

def certificate1291 : RatMajorityCertificate := ⟨(120497743622936743/1000000000000000000),(440433981464149839668788323560211591/500000000000000000000000000000000000),1,(36723945909898991667/100000000000000000000),(9180986477474747917/25000000000000000000),(53997884207366611/100000000000000000),false⟩
theorem valid1291 : certificate1291.Valid := by decide +kernel
theorem bound1291 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1291.a certificate1291.b certificate1291.c x ≤ (certificate1291.bound:ℝ) :=
  rat_majority_certificate_sound certificate1291 valid1291 x hx0 hx1

def certificate1292 : RatMajorityCertificate := ⟨0,(100156688315736157/100000000000000000),(165683791/145668000),(5340965497283912131/12500000000000000000),(42727723978271297049/100000000000000000000),(661146613584402163/1000000000000000000),false⟩
theorem valid1292 : certificate1292.Valid := by decide +kernel
theorem bound1292 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1292.a certificate1292.b certificate1292.c x ≤ (certificate1292.bound:ℝ) :=
  rat_majority_certificate_sound certificate1292 valid1292 x hx0 hx1

def certificate1293 : RatMajorityCertificate := ⟨(128147785179964959/1000000000000000000),(87321830537114493529720518450677437/100000000000000000000000000000000000),(165683791/145668000),(2004889001925174647/5000000000000000000),(40097780038503492941/100000000000000000000),(661146613584402163/1000000000000000000),false⟩
theorem valid1293 : certificate1293.Valid := by decide +kernel
theorem bound1293 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1293.a certificate1293.b certificate1293.c x ≤ (certificate1293.bound:ℝ) :=
  rat_majority_certificate_sound certificate1293 valid1293 x hx0 hx1

def certificate1294 : RatMajorityCertificate := ⟨0,(100156688315736157/100000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(539889133830467151/1000000000000000000),false⟩
theorem valid1294 : certificate1294.Valid := by decide +kernel
theorem bound1294 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1294.a certificate1294.b certificate1294.c x ≤ (certificate1294.bound:ℝ) :=
  rat_majority_certificate_sound certificate1294 valid1294 x hx0 hx1

def certificate1295 : RatMajorityCertificate := ⟨(59792268733651001/500000000000000000),(44089748534621058943681088365056843/50000000000000000000000000000000000),1,(7349007563449955839/20000000000000000000),(9186259454312444799/25000000000000000000),(539889133830467151/1000000000000000000),false⟩
theorem valid1295 : certificate1295.Valid := by decide +kernel
theorem bound1295 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1295.a certificate1295.b certificate1295.c x ≤ (certificate1295.bound:ℝ) :=
  rat_majority_certificate_sound certificate1295 valid1295 x hx0 hx1

def certificate1296 : RatMajorityCertificate := ⟨0,(125197603816143359/125000000000000000),(165292411/145632000),(2666898235278012773/6250000000000000000),(42670371764448204369/100000000000000000000),(65889368507565313/100000000000000000),false⟩
theorem valid1296 : certificate1296.Valid := by decide +kernel
theorem bound1296 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1296.a certificate1296.b certificate1296.c x ≤ (certificate1296.bound:ℝ) :=
  rat_majority_certificate_sound certificate1296 valid1296 x hx0 hx1

def certificate1297 : RatMajorityCertificate := ⟨(15872142486989677/125000000000000000),(13662546270218409944997400214894957/15625000000000000000000000000000000),(165292411/145632000),(4006598727073209039/10000000000000000000),(40065987270732090391/100000000000000000000),(65889368507565313/100000000000000000),false⟩
theorem valid1297 : certificate1297.Valid := by decide +kernel
theorem bound1297 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1297.a certificate1297.b certificate1297.c x ≤ (certificate1297.bound:ℝ) :=
  rat_majority_certificate_sound certificate1297 valid1297 x hx0 hx1

def certificate1298 : RatMajorityCertificate := ⟨0,(125197603816143359/125000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(134943793017943021/250000000000000000),false⟩
theorem valid1298 : certificate1298.Valid := by decide +kernel
theorem bound1298 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1298.a certificate1298.b certificate1298.c x ≤ (certificate1298.bound:ℝ) :=
  rat_majority_certificate_sound certificate1298 valid1298 x hx0 hx1

def certificate1299 : RatMajorityCertificate := ⟨(118438586407984561/1000000000000000000),(110369376598492446155568452965319601/125000000000000000000000000000000000),1,(36771447360105458091/100000000000000000000),(9192861840026364523/25000000000000000000),(134943793017943021/250000000000000000),false⟩
theorem valid1299 : certificate1299.Valid := by decide +kernel
theorem bound1299 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1299.a certificate1299.b certificate1299.c x ≤ (certificate1299.bound:ℝ) :=
  rat_majority_certificate_sound certificate1299 valid1299 x hx0 hx1

def certificate1300 : RatMajorityCertificate := ⟨0,(125199332070059441/125000000000000000),(1237813681/1091975000),(42635852541460226431/100000000000000000000),(333092597980158019/781250000000000000),(328820741716693039/500000000000000000),false⟩
theorem valid1300 : certificate1300.Valid := by decide +kernel
theorem bound1300 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1300.a certificate1300.b certificate1300.c x ≤ (certificate1300.bound:ℝ) :=
  rat_majority_certificate_sound certificate1300 valid1300 x hx0 hx1

def certificate1301 : RatMajorityCertificate := ⟨(31850475770657919/250000000000000000),(27312174724914877062613553992636721/31250000000000000000000000000000000),(1237813681/1091975000),(8004208804097977273/20000000000000000000),(20010522010244943183/50000000000000000000),(328820741716693039/500000000000000000),false⟩
theorem valid1301 : certificate1301.Valid := by decide +kernel
theorem bound1301 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1301.a certificate1301.b certificate1301.c x ≤ (certificate1301.bound:ℝ) :=
  rat_majority_certificate_sound certificate1301 valid1301 x hx0 hx1

def certificate1302 : RatMajorityCertificate := ⟨0,(125199332070059441/125000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(539737391076274947/1000000000000000000),false⟩
theorem valid1302 : certificate1302.Valid := by decide +kernel
theorem bound1302 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1302.a certificate1302.b certificate1302.c x ≤ (certificate1302.bound:ℝ) :=
  rat_majority_certificate_sound certificate1302 valid1302 x hx0 hx1

def certificate1303 : RatMajorityCertificate := ⟨(118017153947944041/1000000000000000000),(110423663222967468459415485388258919/125000000000000000000000000000000000),1,(9195291694559563231/25000000000000000000),(1471246671129530117/4000000000000000000),(539737391076274947/1000000000000000000),false⟩
theorem valid1303 : certificate1303.Valid := by decide +kernel
theorem bound1303 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1303.a certificate1303.b certificate1303.c x ≤ (certificate1303.bound:ℝ) :=
  rat_majority_certificate_sound certificate1303 valid1303 x hx0 hx1

def certificate1304 : RatMajorityCertificate := ⟨0,(40064334031345821/40000000000000000),(123555083/109172000),(10648153915438557891/25000000000000000000),(8518523132350846313/20000000000000000000),(65578401154486843/100000000000000000),false⟩
theorem valid1304 : certificate1304.Valid := by decide +kernel
theorem bound1304 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1304.a certificate1304.b certificate1304.c x ≤ (certificate1304.bound:ℝ) :=
  rat_majority_certificate_sound certificate1304 valid1304 x hx0 hx1

def certificate1305 : RatMajorityCertificate := ⟨(124582892175534907/1000000000000000000),(35073003424634050819496444225926353/40000000000000000000000000000000000),(123555083/109172000),(10010314006023765977/25000000000000000000),(40041256024095063909/100000000000000000000),(65578401154486843/100000000000000000),false⟩
theorem valid1305 : certificate1305.Valid := by decide +kernel
theorem bound1305 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1305.a certificate1305.b certificate1305.c x ≤ (certificate1305.bound:ℝ) :=
  rat_majority_certificate_sound certificate1305 valid1305 x hx0 hx1

def certificate1306 : RatMajorityCertificate := ⟨0,(40064334031345821/40000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(21585811572310111/40000000000000000),false⟩
theorem valid1306 : certificate1306.Valid := by decide +kernel
theorem bound1306 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1306.a certificate1306.b certificate1306.c x ≤ (certificate1306.bound:ℝ) :=
  rat_majority_certificate_sound certificate1306 valid1306 x hx0 hx1

def certificate1307 : RatMajorityCertificate := ⟨(117076667100104083/1000000000000000000),(35373735333370575333727826332912857/40000000000000000000000000000000000),1,(7360557884126395111/20000000000000000000),(9200697355157993889/25000000000000000000),(21585811572310111/40000000000000000),false⟩
theorem valid1307 : certificate1307.Valid := by decide +kernel
theorem bound1307 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1307.a certificate1307.b certificate1307.c x ≤ (certificate1307.bound:ℝ) :=
  rat_majority_certificate_sound certificate1307 valid1307 x hx0 hx1

def certificate1308 : RatMajorityCertificate := ⟨0,(250405477485432323/250000000000000000),(273911797/242550000),(10633496696163732447/25000000000000000000),(42533986784654929789/100000000000000000000),(163360028236576653/250000000000000000),false⟩
theorem valid1308 : certificate1308.Valid := by decide +kernel
theorem bound1308 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1308.a certificate1308.b certificate1308.c x ≤ (certificate1308.bound:ℝ) :=
  rat_majority_certificate_sound certificate1308 valid1308 x hx0 hx1

def certificate1309 : RatMajorityCertificate := ⟨(122749344160771869/1000000000000000000),(219668369349830579172183513158278313/250000000000000000000000000000000000),(273911797/242550000),(40023128799093864813/100000000000000000000),(20011564399546932407/50000000000000000000),(163360028236576653/250000000000000000),false⟩
theorem valid1309 : certificate1309.Valid := by decide +kernel
theorem bound1309 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1309.a certificate1309.b certificate1309.c x ≤ (certificate1309.bound:ℝ) :=
  rat_majority_certificate_sound certificate1309 valid1309 x hx0 hx1

def certificate1310 : RatMajorityCertificate := ⟨0,(250405477485432323/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(539531295427428091/1000000000000000000),false⟩
theorem valid1310 : certificate1310.Valid := by decide +kernel
theorem bound1310 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1310.a certificate1310.b certificate1310.c x ≤ (certificate1310.bound:ℝ) :=
  rat_majority_certificate_sound certificate1310 valid1310 x hx0 hx1

def certificate1311 : RatMajorityCertificate := ⟨(7245283026784683/62500000000000000),(13836083787000403294106649110491391/15625000000000000000000000000000000),1,(36829220837462890199/100000000000000000000),(184146104187314451/500000000000000000),(539531295427428091/1000000000000000000),false⟩
theorem valid1311 : certificate1311.Valid := by decide +kernel
theorem bound1311 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1311.a certificate1311.b certificate1311.c x ≤ (certificate1311.bound:ℝ) :=
  rat_majority_certificate_sound certificate1311 valid1311 x hx0 hx1

def certificate1312 : RatMajorityCertificate := ⟨0,(500001193614664263/500000000000000000),(694811003/602792500),(43088088899421690519/100000000000000000000),(1077202222485542263/2500000000000000000),(681389053121324357/1000000000000000000),false⟩
theorem valid1312 : certificate1312.Valid := by decide +kernel
theorem bound1312 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1312.a certificate1312.b certificate1312.c x ≤ (certificate1312.bound:ℝ) :=
  rat_majority_certificate_sound certificate1312 valid1312 x hx0 hx1

def certificate1313 : RatMajorityCertificate := ⟨(205534660685740379/1000000000000000000),(397233617942609064680372168332624323/500000000000000000000000000000000000),(694811003/602792500),(38558740728471340971/100000000000000000000),(9639685182117835243/25000000000000000000),(681389053121324357/1000000000000000000),false⟩
theorem valid1313 : certificate1313.Valid := by decide +kernel
theorem bound1313 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1313.a certificate1313.b certificate1313.c x ≤ (certificate1313.bound:ℝ) :=
  rat_majority_certificate_sound certificate1313 valid1313 x hx0 hx1

def certificate1314 : RatMajorityCertificate := ⟨0,(500001193614664263/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(549566758183060013/1000000000000000000),false⟩
theorem valid1314 : certificate1314.Valid := by decide +kernel
theorem bound1314 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1314.a certificate1314.b certificate1314.c x ≤ (certificate1314.bound:ℝ) :=
  rat_majority_certificate_sound certificate1314 valid1314 x hx0 hx1

def certificate1315 : RatMajorityCertificate := ⟨(25905529158215633/125000000000000000),(49547353701505727636090208546976521/62500000000000000000000000000000000),1,(3454657639421466131/10000000000000000000),(34546576394214661311/100000000000000000000),(549566758183060013/1000000000000000000),false⟩
theorem valid1315 : certificate1315.Valid := by decide +kernel
theorem bound1315 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1315.a certificate1315.b certificate1315.c x ≤ (certificate1315.bound:ℝ) :=
  rat_majority_certificate_sound certificate1315 valid1315 x hx0 hx1

def certificate1316 : RatMajorityCertificate := ⟨0,(200000741511401477/200000000000000000),(2769602081/2407820000),(21515846233098799023/50000000000000000000),(43031692466197598047/100000000000000000000),(676496766482074299/1000000000000000000),false⟩
theorem valid1316 : certificate1316.Valid := by decide +kernel
theorem bound1316 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1316.a certificate1316.b certificate1316.c x ≤ (certificate1316.bound:ℝ) :=
  rat_majority_certificate_sound certificate1316 valid1316 x hx0 hx1

def certificate1317 : RatMajorityCertificate := ⟨(178967927355920517/1000000000000000000),(164207023333458740477450445911596391/200000000000000000000000000000000000),(2769602081/2407820000),(244911814429796343/625000000000000000),(39185890308767414881/100000000000000000000),(676496766482074299/1000000000000000000),false⟩
theorem valid1317 : certificate1317.Valid := by decide +kernel
theorem bound1317 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1317.a certificate1317.b certificate1317.c x ≤ (certificate1317.bound:ℝ) :=
  rat_majority_certificate_sound certificate1317 valid1317 x hx0 hx1

def certificate1318 : RatMajorityCertificate := ⟨0,(200000741511401477/200000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(549488971839446569/1000000000000000000),false⟩
theorem valid1318 : certificate1318.Valid := by decide +kernel
theorem bound1318 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1318.a certificate1318.b certificate1318.c x ≤ (certificate1318.bound:ℝ) :=
  rat_majority_certificate_sound certificate1318 valid1318 x hx0 hx1

def certificate1319 : RatMajorityCertificate := ⟨(51663043941052671/250000000000000000),(39667538280903717752200552115804933/50000000000000000000000000000000000),1,(432033307151358181/1250000000000000000),(34562664572108654481/100000000000000000000),(549488971839446569/1000000000000000000),false⟩
theorem valid1319 : certificate1319.Valid := by decide +kernel
theorem bound1319 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1319.a certificate1319.b certificate1319.c x ≤ (certificate1319.bound:ℝ) :=
  rat_majority_certificate_sound certificate1319 valid1319 x hx0 hx1

end Cycle12.MajorityCertificates.Batch032
