import Cycle12.RationalMajorityCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Batch033

def certificate1320 : RatMajorityCertificate := ⟨0,(1000004455145094413/1000000000000000000),(69422209/60162000),(21558906458052057437/50000000000000000000),(344942503328832919/800000000000000000),(340617102204368261/500000000000000000),false⟩
theorem valid1320 : certificate1320.Valid := by decide +kernel
theorem bound1320 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1320.a certificate1320.b certificate1320.c x ≤ (certificate1320.bound:ℝ) :=
  rat_majority_certificate_sound certificate1320 valid1320 x hx0 hx1

def certificate1321 : RatMajorityCertificate := ⟨(193397391451343349/1000000000000000000),(806606202080311267277016323715390863/1000000000000000000000000000000000000),(69422209/60162000),(19453543235329449821/50000000000000000000),(38907086470658899643/100000000000000000000),(340617102204368261/500000000000000000),false⟩
theorem valid1321 : certificate1321.Valid := by decide +kernel
theorem bound1321 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1321.a certificate1321.b certificate1321.c x ≤ (certificate1321.bound:ℝ) :=
  rat_majority_certificate_sound certificate1321 valid1321 x hx0 hx1

def certificate1322 : RatMajorityCertificate := ⟨0,(1000004455145094413/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(68688351960154883/125000000000000000),false⟩
theorem valid1322 : certificate1322.Valid := by decide +kernel
theorem bound1322 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1322.a certificate1322.b certificate1322.c x ≤ (certificate1322.bound:ℝ) :=
  rat_majority_certificate_sound certificate1322 valid1322 x hx0 hx1

def certificate1323 : RatMajorityCertificate := ⟨(51696195528123393/250000000000000000),(198304687944098303315797896301096691/250000000000000000000000000000000000),1,(34559067491162832609/100000000000000000000),(3455906749116283261/10000000000000000000),(68688351960154883/125000000000000000),false⟩
theorem valid1323 : certificate1323.Valid := by decide +kernel
theorem bound1323 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1323.a certificate1323.b certificate1323.c x ≤ (certificate1323.bound:ℝ) :=
  rat_majority_certificate_sound certificate1323 valid1323 x hx0 hx1

def certificate1324 : RatMajorityCertificate := ⟨0,(125000660700460127/125000000000000000),(1388963351/1202435000),(43146020545815556629/100000000000000000000),(4314602054581555663/10000000000000000000),(170640342519457387/250000000000000000),false⟩
theorem valid1324 : certificate1324.Valid := by decide +kernel
theorem bound1324 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1324.a certificate1324.b certificate1324.c x ≤ (certificate1324.bound:ℝ) :=
  rat_majority_certificate_sound certificate1324 valid1324 x hx0 hx1

def certificate1325 : RatMajorityCertificate := ⟨(12240122610978601/62500000000000000),(6282517880351791728041697549257673/7812500000000000000000000000000000),(1388963351/1202435000),(9718247850385200843/25000000000000000000),(38872991401540803373/100000000000000000000),(170640342519457387/250000000000000000),false⟩
theorem valid1325 : certificate1325.Valid := by decide +kernel
theorem bound1325 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1325.a certificate1325.b certificate1325.c x ≤ (certificate1325.bound:ℝ) :=
  rat_majority_certificate_sound certificate1325 valid1325 x hx0 hx1

def certificate1326 : RatMajorityCertificate := ⟨0,(125000660700460127/125000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(549454838526523649/1000000000000000000),false⟩
theorem valid1326 : certificate1326.Valid := by decide +kernel
theorem bound1326 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1326.a certificate1326.b certificate1326.c x ≤ (certificate1326.bound:ℝ) :=
  rat_majority_certificate_sound certificate1326 valid1326 x hx0 hx1

def certificate1327 : RatMajorityCertificate := ⟨(206388954398155987/1000000000000000000),(99201905039413492632919028780169651/125000000000000000000000000000000000),1,(6913963112449866073/20000000000000000000),(17284907781124665183/50000000000000000000),(549454838526523649/1000000000000000000),false⟩
theorem valid1327 : certificate1327.Valid := by decide +kernel
theorem bound1327 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1327.a certificate1327.b certificate1327.c x ≤ (certificate1327.bound:ℝ) :=
  rat_majority_certificate_sound certificate1327 valid1327 x hx0 hx1

def certificate1328 : RatMajorityCertificate := ⟨0,(500003588688533471/500000000000000000),(2780588529/2401450000),(21605196452509643253/50000000000000000000),(43210392905019286507/100000000000000000000),(5357294450111349/7812500000000000),false⟩
theorem valid1328 : certificate1328.Valid := by decide +kernel
theorem bound1328 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1328.a certificate1328.b certificate1328.c x ≤ (certificate1328.bound:ℝ) :=
  rat_majority_certificate_sound certificate1328 valid1328 x hx0 hx1

def certificate1329 : RatMajorityCertificate := ⟨(202685777543964683/1000000000000000000),(398659972540425359820037537712595307/500000000000000000000000000000000000),(2780588529/2401450000),(1211278804186580723/3125000000000000000),(38760921733970583137/100000000000000000000),(5357294450111349/7812500000000000),false⟩
theorem valid1329 : certificate1329.Valid := by decide +kernel
theorem bound1329 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1329.a certificate1329.b certificate1329.c x ≤ (certificate1329.bound:ℝ) :=
  rat_majority_certificate_sound certificate1329 valid1329 x hx0 hx1

def certificate1330 : RatMajorityCertificate := ⟨0,(500003588688533471/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(549536528834180869/1000000000000000000),false⟩
theorem valid1330 : certificate1330.Valid := by decide +kernel
theorem bound1330 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1330.a certificate1330.b certificate1330.c x ≤ (certificate1330.bound:ℝ) :=
  rat_majority_certificate_sound certificate1330 valid1330 x hx0 hx1

def certificate1331 : RatMajorityCertificate := ⟨(20700087323853907/100000000000000000),(39650240920760372637085452316378803/50000000000000000000000000000000000),1,(6910642101708168737/20000000000000000000),(17276605254270421843/50000000000000000000),(549536528834180869/1000000000000000000),false⟩
theorem valid1331 : certificate1331.Valid := by decide +kernel
theorem bound1331 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1331.a certificate1331.b certificate1331.c x ≤ (certificate1331.bound:ℝ) :=
  rat_majority_certificate_sound certificate1331 valid1331 x hx0 hx1

def certificate1332 : RatMajorityCertificate := ⟨0,(500004090583869843/500000000000000000),(1390506703/1200110000),(5403546605836095471/12500000000000000000),(43228372846688763769/100000000000000000000),(27436627541683403/40000000000000000),false⟩
theorem valid1332 : certificate1332.Valid := by decide +kernel
theorem bound1332 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1332.a certificate1332.b certificate1332.c x ≤ (certificate1332.bound:ℝ) :=
  rat_majority_certificate_sound certificate1332 valid1332 x hx0 hx1

def certificate1333 : RatMajorityCertificate := ⟨(39577314067131707/200000000000000000),(80211999188885580380580488773587999/100000000000000000000000000000000000),(1390506703/1200110000),(19452608413626340653/50000000000000000000),(38905216827252681307/100000000000000000000),(27436627541683403/40000000000000000),false⟩
theorem valid1333 : certificate1333.Valid := by decide +kernel
theorem bound1333 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1333.a certificate1333.b certificate1333.c x ≤ (certificate1333.bound:ℝ) :=
  rat_majority_certificate_sound certificate1333 valid1333 x hx0 hx1

def certificate1334 : RatMajorityCertificate := ⟨0,(500004090583869843/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(109902473688077397/200000000000000000),false⟩
theorem valid1334 : certificate1334.Valid := by decide +kernel
theorem bound1334 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1334.a certificate1334.b certificate1334.c x ≤ (certificate1334.bound:ℝ) :=
  rat_majority_certificate_sound certificate1334 valid1334 x hx0 hx1

def certificate1335 : RatMajorityCertificate := ⟨(206815099082693547/1000000000000000000),(396595695048014721851951044695996879/500000000000000000000000000000000000),1,(34558260818810985669/100000000000000000000),(3455826081881098567/10000000000000000000),(109902473688077397/200000000000000000),false⟩
theorem valid1335 : certificate1335.Valid := by decide +kernel
theorem bound1335 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1335.a certificate1335.b certificate1335.c x ≤ (certificate1335.bound:ℝ) :=
  rat_majority_certificate_sound certificate1335 valid1335 x hx0 hx1

def certificate1336 : RatMajorityCertificate := ⟨0,(1000009278712206949/1000000000000000000),(2780777237/2398710000),(43243088158570597509/100000000000000000000),(4324308815857059751/10000000000000000000),(343173790034140309/500000000000000000),false⟩
theorem valid1336 : certificate1336.Valid := by decide +kernel
theorem bound1336 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1336.a certificate1336.b certificate1336.c x ≤ (certificate1336.bound:ℝ) :=
  rat_majority_certificate_sound certificate1336 valid1336 x hx0 hx1

def certificate1337 : RatMajorityCertificate := ⟨(39325301899315393/200000000000000000),(160676188954967221667568424762734043/200000000000000000000000000000000000),(2780777237/2398710000),(7790653711123320081/20000000000000000000),(19476634277808300203/50000000000000000000),(343173790034140309/500000000000000000),false⟩
theorem valid1337 : certificate1337.Valid := by decide +kernel
theorem bound1337 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1337.a certificate1337.b certificate1337.c x ≤ (certificate1337.bound:ℝ) :=
  rat_majority_certificate_sound certificate1337 valid1337 x hx0 hx1

def certificate1338 : RatMajorityCertificate := ⟨0,(1000009278712206949/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(274753890792743221/500000000000000000),false⟩
theorem valid1338 : certificate1338.Valid := by decide +kernel
theorem bound1338 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1338.a certificate1338.b certificate1338.c x ≤ (certificate1338.bound:ℝ) :=
  rat_majority_certificate_sound certificate1338 valid1338 x hx0 hx1

def certificate1339 : RatMajorityCertificate := ⟨(206776978937186431/1000000000000000000),(793230381150941937492002371333290981/1000000000000000000000000000000000000),1,(17279650432572548343/50000000000000000000),(34559300865145096687/100000000000000000000),(274753890792743221/500000000000000000),false⟩
theorem valid1339 : certificate1339.Valid := by decide +kernel
theorem bound1339 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1339.a certificate1339.b certificate1339.c x ≤ (certificate1339.bound:ℝ) :=
  rat_majority_certificate_sound certificate1339 valid1339 x hx0 hx1

def certificate1340 : RatMajorityCertificate := ⟨0,(1000011714386519253/1000000000000000000),(557168173/479090000),(43329010545456619039/100000000000000000000),(270806315909103869/625000000000000000),(690944806042897451/1000000000000000000),false⟩
theorem valid1340 : certificate1340.Valid := by decide +kernel
theorem bound1340 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1340.a certificate1340.b certificate1340.c x ≤ (certificate1340.bound:ℝ) :=
  rat_majority_certificate_sound certificate1340 valid1340 x hx0 hx1

def certificate1341 : RatMajorityCertificate := ⟨(209004363452952831/1000000000000000000),(791004902575668723674961837117644757/1000000000000000000000000000000000000),(557168173/479090000),(19358512860021879881/50000000000000000000),(38717025720043759763/100000000000000000000),(690944806042897451/1000000000000000000),false⟩
theorem valid1341 : certificate1341.Valid := by decide +kernel
theorem bound1341 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1341.a certificate1341.b certificate1341.c x ≤ (certificate1341.bound:ℝ) :=
  rat_majority_certificate_sound certificate1341 valid1341 x hx0 hx1

def certificate1342 : RatMajorityCertificate := ⟨0,(1000011714386519253/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(549582372769416393/1000000000000000000),false⟩
theorem valid1342 : certificate1342.Valid := by decide +kernel
theorem bound1342 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1342.a certificate1342.b certificate1342.c x ≤ (certificate1342.bound:ℝ) :=
  rat_majority_certificate_sound certificate1342 valid1342 x hx0 hx1

def certificate1343 : RatMajorityCertificate := ⟨(207332996872705653/1000000000000000000),(792676288734950038052491232913562791/1000000000000000000000000000000000000),1,(17272102663828831889/50000000000000000000),(34544205327657663779/100000000000000000000),(549582372769416393/1000000000000000000),false⟩
theorem valid1343 : certificate1343.Valid := by decide +kernel
theorem bound1343 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1343.a certificate1343.b certificate1343.c x ≤ (certificate1343.bound:ℝ) :=
  rat_majority_certificate_sound certificate1343 valid1343 x hx0 hx1

def certificate1344 : RatMajorityCertificate := ⟨0,(1000012958107946833/1000000000000000000),(696292863/598577500),(43335379206051568137/100000000000000000000),(21667689603025784069/50000000000000000000),(69084582690088713/100000000000000000),false⟩
theorem valid1344 : certificate1344.Valid := by decide +kernel
theorem bound1344 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1344.a certificate1344.b certificate1344.c x ≤ (certificate1344.bound:ℝ) :=
  rat_majority_certificate_sound certificate1344 valid1344 x hx0 hx1

def certificate1345 : RatMajorityCertificate := ⟨(205781973580996613/1000000000000000000),(794228317981923045109330492642923371/1000000000000000000000000000000000000),(696292863/598577500),(19404564491625802469/50000000000000000000),(38809128983251604939/100000000000000000000),(69084582690088713/100000000000000000),false⟩
theorem valid1345 : certificate1345.Valid := by decide +kernel
theorem bound1345 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1345.a certificate1345.b certificate1345.c x ≤ (certificate1345.bound:ℝ) :=
  rat_majority_certificate_sound certificate1345 valid1345 x hx0 hx1

def certificate1346 : RatMajorityCertificate := ⟨0,(1000012958107946833/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(68687548660571411/125000000000000000),false⟩
theorem valid1346 : certificate1346.Valid := by decide +kernel
theorem bound1346 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1346.a certificate1346.b certificate1346.c x ≤ (certificate1346.bound:ℝ) :=
  rat_majority_certificate_sound certificate1346 valid1346 x hx0 hx1

def certificate1347 : RatMajorityCertificate := ⟨(41341909861764729/200000000000000000),(158660146046893920612892647713346743/200000000000000000000000000000000000),1,(34561148115911533221/100000000000000000000),(17280574057955766611/50000000000000000000),(68687548660571411/125000000000000000),false⟩
theorem valid1347 : certificate1347.Valid := by decide +kernel
theorem bound1347 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1347.a certificate1347.b certificate1347.c x ≤ (certificate1347.bound:ℝ) :=
  rat_majority_certificate_sound certificate1347 valid1347 x hx0 hx1

def certificate1348 : RatMajorityCertificate := ⟨0,(1000014311052684239/1000000000000000000),(1395083141/1196440000),(43399927175313751697/100000000000000000000),(21699963587656875849/50000000000000000000),(173527602768723659/250000000000000000),false⟩
theorem valid1348 : certificate1348.Valid := by decide +kernel
theorem bound1348 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1348.a certificate1348.b certificate1348.c x ≤ (certificate1348.bound:ℝ) :=
  rat_majority_certificate_sound certificate1348 valid1348 x hx0 hx1

def certificate1349 : RatMajorityCertificate := ⟨(213104549985774973/1000000000000000000),(786906711316467168530923381722249453/1000000000000000000000000000000000000),(1395083141/1196440000),(38681306276773308757/100000000000000000000),(19340653138386654379/50000000000000000000),(173527602768723659/250000000000000000),false⟩
theorem valid1349 : certificate1349.Valid := by decide +kernel
theorem bound1349 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1349.a certificate1349.b certificate1349.c x ≤ (certificate1349.bound:ℝ) :=
  rat_majority_certificate_sound certificate1349 valid1349 x hx0 hx1

def certificate1350 : RatMajorityCertificate := ⟨0,(1000014311052684239/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(54955829231321259/100000000000000000),false⟩
theorem valid1350 : certificate1350.Valid := by decide +kernel
theorem bound1350 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1350.a certificate1350.b certificate1350.c x ≤ (certificate1350.bound:ℝ) :=
  rat_majority_certificate_sound certificate1350 valid1350 x hx0 hx1

def certificate1351 : RatMajorityCertificate := ⟨(25892875308481783/125000000000000000),(99108543018801060761054234017281863/125000000000000000000000000000000000),1,(17274690354135554753/50000000000000000000),(34549380708271109507/100000000000000000000),(54955829231321259/100000000000000000),false⟩
theorem valid1351 : certificate1351.Valid := by decide +kernel
theorem bound1351 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1351.a certificate1351.b certificate1351.c x ≤ (certificate1351.bound:ℝ) :=
  rat_majority_certificate_sound certificate1351 valid1351 x hx0 hx1

def certificate1352 : RatMajorityCertificate := ⟨0,(250003931495918979/250000000000000000),(2785750949/2391470000),(216865333790609931/500000000000000000),(43373066758121986201/100000000000000000000),(345895214216595203/500000000000000000),false⟩
theorem valid1352 : certificate1352.Valid := by decide +kernel
theorem bound1352 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1352.a certificate1352.b certificate1352.c x ≤ (certificate1352.bound:ℝ) :=
  rat_majority_certificate_sound certificate1352 valid1352 x hx0 hx1

def certificate1353 : RatMajorityCertificate := ⟨(100491175837773257/500000000000000000),(99878776707868475643348749755055397/125000000000000000000000000000000000),(2785750949/2391470000),(19487289061914101479/50000000000000000000),(38974578123828202959/100000000000000000000),(345895214216595203/500000000000000000),false⟩
theorem valid1353 : certificate1353.Valid := by decide +kernel
theorem bound1353 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1353.a certificate1353.b certificate1353.c x ≤ (certificate1353.bound:ℝ) :=
  rat_majority_certificate_sound certificate1353 valid1353 x hx0 hx1

def certificate1354 : RatMajorityCertificate := ⟨0,(250003931495918979/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(109901209391064981/200000000000000000),false⟩
theorem valid1354 : certificate1354.Valid := by decide +kernel
theorem bound1354 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1354.a certificate1354.b certificate1354.c x ≤ (certificate1354.bound:ℝ) :=
  rat_majority_certificate_sound certificate1354 valid1354 x hx0 hx1

def certificate1355 : RatMajorityCertificate := ⟨(206743666913987679/1000000000000000000),(198317201955539312153733000411740259/250000000000000000000000000000000000),1,(17280117051438674557/50000000000000000000),(6912046820575469823/20000000000000000000),(109901209391064981/200000000000000000),false⟩
theorem valid1355 : certificate1355.Valid := by decide +kernel
theorem bound1355 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1355.a certificate1355.b certificate1355.c x ≤ (certificate1355.bound:ℝ) :=
  rat_majority_certificate_sound certificate1355 valid1355 x hx0 hx1

def certificate1356 : RatMajorityCertificate := ⟨0,(31250537569314281/31250000000000000),(92837703/79669000),(43382874753235848753/100000000000000000000),(21691437376617924377/50000000000000000000),(345951420466857503/500000000000000000),false⟩
theorem valid1356 : certificate1356.Valid := by decide +kernel
theorem bound1356 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1356.a certificate1356.b certificate1356.c x ≤ (certificate1356.bound:ℝ) :=
  rat_majority_certificate_sound certificate1356 valid1356 x hx0 hx1

def certificate1357 : RatMajorityCertificate := ⟨(99210348128710779/500000000000000000),(12524892073196115525905004396665101/15625000000000000000000000000000000),(92837703/79669000),(152545563519731009/390625000000000000),(7810332852210227661/20000000000000000000),(345951420466857503/500000000000000000),false⟩
theorem valid1357 : certificate1357.Valid := by decide +kernel
theorem bound1357 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1357.a certificate1357.b certificate1357.c x ≤ (certificate1357.bound:ℝ) :=
  rat_majority_certificate_sound certificate1357 valid1357 x hx0 hx1

def certificate1358 : RatMajorityCertificate := ⟨0,(31250537569314281/31250000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(274764002043578773/500000000000000000),false⟩
theorem valid1358 : certificate1358.Valid := by decide +kernel
theorem bound1358 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1358.a certificate1358.b certificate1358.c x ≤ (certificate1358.bound:ℝ) :=
  rat_majority_certificate_sound certificate1358 valid1358 x hx0 hx1

def certificate1359 : RatMajorityCertificate := ⟨(41381012715913441/200000000000000000),(4956928621327931221820065078849079/6250000000000000000000000000000000),1,(4319482214801087037/12500000000000000000),(34555857718408696297/100000000000000000000),(274764002043578773/500000000000000000),false⟩
theorem valid1359 : certificate1359.Valid := by decide +kernel
theorem bound1359 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1359.a certificate1359.b certificate1359.c x ≤ (certificate1359.bound:ℝ) :=
  rat_majority_certificate_sound certificate1359 valid1359 x hx0 hx1

end Cycle12.MajorityCertificates.Batch033
