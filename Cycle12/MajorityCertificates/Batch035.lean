import Cycle12.RationalMajorityCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Batch035

def certificate1400 : RatMajorityCertificate := ⟨0,(1000048740153977629/1000000000000000000),(116614913/98727500),(1093709839356554183/2500000000000000000),(43748393574262167321/100000000000000000000),(706192089653867151/1000000000000000000),false⟩
theorem valid1400 : certificate1400.Valid := by decide +kernel
theorem bound1400 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1400.a certificate1400.b certificate1400.c x ≤ (certificate1400.bound:ℝ) :=
  rat_majority_certificate_sound certificate1400 valid1400 x hx0 hx1

def certificate1401 : RatMajorityCertificate := ⟨(49728102824385037/250000000000000000),(200281658458720694355729608619662727/250000000000000000000000000000000000),(116614913/98727500),(39418763126407347517/100000000000000000000),(19709381563203673759/50000000000000000000),(706192089653867151/1000000000000000000),false⟩
theorem valid1401 : certificate1401.Valid := by decide +kernel
theorem bound1401 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1401.a certificate1401.b certificate1401.c x ≤ (certificate1401.bound:ℝ) :=
  rat_majority_certificate_sound certificate1401 valid1401 x hx0 hx1

def certificate1402 : RatMajorityCertificate := ⟨0,(1000048740153977629/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(549567899888167037/1000000000000000000),false⟩
theorem valid1402 : certificate1402.Valid := by decide +kernel
theorem bound1402 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1402.a certificate1402.b certificate1402.c x ≤ (certificate1402.bound:ℝ) :=
  rat_majority_certificate_sound certificate1402 valid1402 x hx0 hx1

def certificate1403 : RatMajorityCertificate := ⟨(5177697544855913/25000000000000000),(19823268597217941856164345369629723/25000000000000000000000000000000000),1,(34550488098430218939/100000000000000000000),(1727524404921510947/5000000000000000000),(549567899888167037/1000000000000000000),false⟩
theorem valid1403 : certificate1403.Valid := by decide +kernel
theorem bound1403 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1403.a certificate1403.b certificate1403.c x ≤ (certificate1403.bound:ℝ) :=
  rat_majority_certificate_sound certificate1403 valid1403 x hx0 hx1

def certificate1404 : RatMajorityCertificate := ⟨0,(1000050931989036567/1000000000000000000),(1400676597/1184330000),(43782494930581843403/100000000000000000000),(10945623732645460851/25000000000000000000),(44217280540842007/62500000000000000),false⟩
theorem valid1404 : certificate1404.Valid := by decide +kernel
theorem bound1404 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1404.a certificate1404.b certificate1404.c x ≤ (certificate1404.bound:ℝ) :=
  rat_majority_certificate_sound certificate1404 valid1404 x hx0 hx1

def certificate1405 : RatMajorityCertificate := ⟨(99166346589744923/500000000000000000),(400854068665496055208273210950400659/500000000000000000000000000000000000),(1400676597/1184330000),(9867322898444039851/25000000000000000000),(7893858318755231881/20000000000000000000),(44217280540842007/62500000000000000),false⟩
theorem valid1405 : certificate1405.Valid := by decide +kernel
theorem bound1405 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1405.a certificate1405.b certificate1405.c x ≤ (certificate1405.bound:ℝ) :=
  rat_majority_certificate_sound certificate1405 valid1405 x hx0 hx1

def certificate1406 : RatMajorityCertificate := ⟨0,(1000050931989036567/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(549517165000835517/1000000000000000000),false⟩
theorem valid1406 : certificate1406.Valid := by decide +kernel
theorem bound1406 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1406.a certificate1406.b certificate1406.c x ≤ (certificate1406.bound:ℝ) :=
  rat_majority_certificate_sound certificate1406 valid1406 x hx0 hx1

def certificate1407 : RatMajorityCertificate := ⟨(206717461015223321/1000000000000000000),(793322942442355151679585340859820993/1000000000000000000000000000000000000),1,(6912220474485426239/20000000000000000000),(8640275593106782799/25000000000000000000),(549517165000835517/1000000000000000000),false⟩
theorem valid1407 : certificate1407.Valid := by decide +kernel
theorem bound1407 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1407.a certificate1407.b certificate1407.c x ≤ (certificate1407.bound:ℝ) :=
  rat_majority_certificate_sound certificate1407 valid1407 x hx0 hx1

def certificate1408 : RatMajorityCertificate := ⟨0,(1000053379928365091/1000000000000000000),(1400989831/1183760000),(10950376084031937403/25000000000000000000),(43801504336127749613/100000000000000000000),(708212041135595529/1000000000000000000),false⟩
theorem valid1408 : certificate1408.Valid := by decide +kernel
theorem bound1408 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1408.a certificate1408.b certificate1408.c x ≤ (certificate1408.bound:ℝ) :=
  rat_majority_certificate_sound certificate1408 valid1408 x hx0 hx1

def certificate1409 : RatMajorityCertificate := ⟨(99092717186916717/500000000000000000),(400928683215120888663894055012873753/500000000000000000000000000000000000),(1400989831/1183760000),(19746445689741893959/50000000000000000000),(39492891379483787919/100000000000000000000),(708212041135595529/1000000000000000000),false⟩
theorem valid1409 : certificate1409.Valid := by decide +kernel
theorem bound1409 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1409.a certificate1409.b certificate1409.c x ≤ (certificate1409.bound:ℝ) :=
  rat_majority_certificate_sound certificate1409 valid1409 x hx0 hx1

def certificate1410 : RatMajorityCertificate := ⟨0,(1000053379928365091/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(549538402784489019/1000000000000000000),false⟩
theorem valid1410 : certificate1410.Valid := by decide +kernel
theorem bound1410 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1410.a certificate1410.b certificate1410.c x ≤ (certificate1410.bound:ℝ) :=
  rat_majority_certificate_sound certificate1410 valid1410 x hx0 hx1

def certificate1411 : RatMajorityCertificate := ⟨(206870411332335471/1000000000000000000),(793171925868291843023142440222557139/1000000000000000000000000000000000000),1,(34556960070090078079/100000000000000000000),(53995250109515747/156250000000000000),(549538402784489019/1000000000000000000),false⟩
theorem valid1411 : certificate1411.Valid := by decide +kernel
theorem bound1411 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1411.a certificate1411.b certificate1411.c x ≤ (certificate1411.bound:ℝ) :=
  rat_majority_certificate_sound certificate1411 valid1411 x hx0 hx1

def certificate1412 : RatMajorityCertificate := ⟨0,(250014667532055947/250000000000000000),(2803302577/2364910000),(8768793299408184993/20000000000000000000),(21921983248520462483/50000000000000000000),(354980076301320479/500000000000000000),false⟩
theorem valid1412 : certificate1412.Valid := by decide +kernel
theorem bound1412 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1412.a certificate1412.b certificate1412.c x ≤ (certificate1412.bound:ℝ) :=
  rat_majority_certificate_sound certificate1412 valid1412 x hx0 hx1

def certificate1413 : RatMajorityCertificate := ⟨(39775623077647967/200000000000000000),(40058444326772660983174967385190251/50000000000000000000000000000000000),(2803302577/2364910000),(4939887327868448881/12500000000000000000),(39519098622947591049/100000000000000000000),(354980076301320479/500000000000000000),false⟩
theorem valid1413 : certificate1413.Valid := by decide +kernel
theorem bound1413 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1413.a certificate1413.b certificate1413.c x ≤ (certificate1413.bound:ℝ) :=
  rat_majority_certificate_sound certificate1413 valid1413 x hx0 hx1

def certificate1414 : RatMajorityCertificate := ⟨0,(250014667532055947/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(137386216792274459/250000000000000000),false⟩
theorem valid1414 : certificate1414.Valid := by decide +kernel
theorem bound1414 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1414.a certificate1414.b certificate1414.c x ≤ (certificate1414.bound:ℝ) :=
  rat_majority_certificate_sound certificate1414 valid1414 x hx0 hx1

def certificate1415 : RatMajorityCertificate := ⟨(41380544917656653/200000000000000000),(39657190326527953866330601467234609/50000000000000000000000000000000000),1,(8639026513643777189/25000000000000000000),(34556106054575108757/100000000000000000000),(137386216792274459/250000000000000000),false⟩
theorem valid1415 : certificate1415.Valid := by decide +kernel
theorem bound1415 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1415.a certificate1415.b certificate1415.c x ≤ (certificate1415.bound:ℝ) :=
  rat_majority_certificate_sound certificate1415 valid1415 x hx0 hx1

def certificate1416 : RatMajorityCertificate := ⟨0,(200012781965038269/200000000000000000),(2804659981/2362710000),(43882100399574992941/100000000000000000000),(21941050199787496471/50000000000000000000),(88930419705759817/125000000000000000),false⟩
theorem valid1416 : certificate1416.Valid := by decide +kernel
theorem bound1416 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1416.a certificate1416.b certificate1416.c x ≤ (certificate1416.bound:ℝ) :=
  rat_majority_certificate_sound certificate1416 valid1416 x hx0 hx1

def certificate1417 : RatMajorityCertificate := ⟨(99299053207294977/500000000000000000),(80145311104033710242392120223525187/100000000000000000000000000000000000),(2804659981/2362710000),(19783030915033347469/50000000000000000000),(39566061830066694939/100000000000000000000),(88930419705759817/125000000000000000),false⟩
theorem valid1417 : certificate1417.Valid := by decide +kernel
theorem bound1417 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1417.a certificate1417.b certificate1417.c x ≤ (certificate1417.bound:ℝ) :=
  rat_majority_certificate_sound certificate1417 valid1417 x hx0 hx1

def certificate1418 : RatMajorityCertificate := ⟨0,(200012781965038269/200000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(34349430005092089/62500000000000000),false⟩
theorem valid1418 : certificate1418.Valid := by decide +kernel
theorem bound1418 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1418.a certificate1418.b certificate1418.c x ≤ (certificate1418.bound:ℝ) :=
  rat_majority_certificate_sound certificate1418 valid1418 x hx0 hx1

def certificate1419 : RatMajorityCertificate := ⟨(51808521153476331/250000000000000000),(39640829045858232895612807199288961/50000000000000000000000000000000000),1,(34547126913694513779/100000000000000000000),(1727356345684725689/5000000000000000000),(34349430005092089/62500000000000000),false⟩
theorem valid1419 : certificate1419.Valid := by decide +kernel
theorem bound1419 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1419.a certificate1419.b certificate1419.c x ≤ (certificate1419.bound:ℝ) :=
  rat_majority_certificate_sound certificate1419 valid1419 x hx0 hx1

def certificate1420 : RatMajorityCertificate := ⟨0,(62504143901537999/62500000000000000),(93578567/78733000),(10979053897586170261/25000000000000000000),(8783243118068936209/20000000000000000000),(356368283909780103/500000000000000000),false⟩
theorem valid1420 : certificate1420.Valid := by decide +kernel
theorem bound1420 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1420.a certificate1420.b certificate1420.c x ≤ (certificate1420.bound:ℝ) :=
  rat_majority_certificate_sound certificate1420 valid1420 x hx0 hx1

def certificate1421 : RatMajorityCertificate := ⟨(24749054602287243/125000000000000000),(6266099517403866748164469122553243/7812500000000000000000000000000000),(93578567/78733000),(3961726996404851699/10000000000000000000),(39617269964048516991/100000000000000000000),(356368283909780103/500000000000000000),false⟩
theorem valid1421 : certificate1421.Valid := by decide +kernel
theorem bound1421 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1421.a certificate1421.b certificate1421.c x ≤ (certificate1421.bound:ℝ) :=
  rat_majority_certificate_sound certificate1421 valid1421 x hx0 hx1

def certificate1422 : RatMajorityCertificate := ⟨0,(62504143901537999/62500000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(34346057040685269/62500000000000000),false⟩
theorem valid1422 : certificate1422.Valid := by decide +kernel
theorem bound1422 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1422.a certificate1422.b certificate1422.c x ≤ (certificate1422.bound:ℝ) :=
  rat_majority_certificate_sound certificate1422 valid1422 x hx0 hx1

def certificate1423 : RatMajorityCertificate := ⟨(41363734312187773/200000000000000000),(9915423978553630330579054817313773/12500000000000000000000000000000000),1,(17279211354512182739/50000000000000000000),(34558422709024365479/100000000000000000000),(34346057040685269/62500000000000000),false⟩
theorem valid1423 : certificate1423.Valid := by decide +kernel
theorem bound1423 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1423.a certificate1423.b certificate1423.c x ≤ (certificate1423.bound:ℝ) :=
  rat_majority_certificate_sound certificate1423 valid1423 x hx0 hx1

def certificate1424 : RatMajorityCertificate := ⟨0,(500034508908805021/500000000000000000),(2808068343/2360920000),(8787050176387538593/20000000000000000000),(21967625440968846483/50000000000000000000),(356739194600082707/500000000000000000),false⟩
theorem valid1424 : certificate1424.Valid := by decide +kernel
theorem bound1424 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1424.a certificate1424.b certificate1424.c x ≤ (certificate1424.bound:ℝ) :=
  rat_majority_certificate_sound certificate1424 valid1424 x hx0 hx1

def certificate1425 : RatMajorityCertificate := ⟨(197837920329561153/1000000000000000000),(401108721573273616664029125427050787/500000000000000000000000000000000000),(2808068343/2360920000),(19820544524974555031/50000000000000000000),(39641089049949110063/100000000000000000000),(356739194600082707/500000000000000000),false⟩
theorem valid1425 : certificate1425.Valid := by decide +kernel
theorem bound1425 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1425.a certificate1425.b certificate1425.c x ≤ (certificate1425.bound:ℝ) :=
  rat_majority_certificate_sound certificate1425 valid1425 x hx0 hx1

def certificate1426 : RatMajorityCertificate := ⟨0,(500034508908805021/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(549488452952751323/1000000000000000000),false⟩
theorem valid1426 : certificate1426.Valid := by decide +kernel
theorem bound1426 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1426.a certificate1426.b certificate1426.c x ≤ (certificate1426.bound:ℝ) :=
  rat_majority_certificate_sound certificate1426 valid1426 x hx0 hx1

def certificate1427 : RatMajorityCertificate := ⟨(206443487033479963/1000000000000000000),(396805641252597610604661810522705777/500000000000000000000000000000000000),1,(8642154782759604371/25000000000000000000),(6913723826207683497/20000000000000000000),(549488452952751323/1000000000000000000),false⟩
theorem valid1427 : certificate1427.Valid := by decide +kernel
theorem bound1427 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1427.a certificate1427.b certificate1427.c x ≤ (certificate1427.bound:ℝ) :=
  rat_majority_certificate_sound certificate1427 valid1427 x hx0 hx1

def certificate1428 : RatMajorityCertificate := ⟨0,(200014355003487453/200000000000000000),(561758423/471972000),(2813074763048797/6400000000000000),(21977146586318726563/50000000000000000000),(714221334600863469/1000000000000000000),false⟩
theorem valid1428 : certificate1428.Valid := by decide +kernel
theorem bound1428 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1428.a certificate1428.b certificate1428.c x ≤ (certificate1428.bound:ℝ) :=
  rat_majority_certificate_sound certificate1428 valid1428 x hx0 hx1

def certificate1429 : RatMajorityCertificate := ⟨(49420765721485931/250000000000000000),(40118726171310392521782801725476257/50000000000000000000000000000000000),(561758423/471972000),(7932984707835078673/20000000000000000000),(19832461769587696683/50000000000000000000),(714221334600863469/1000000000000000000),false⟩
theorem valid1429 : certificate1429.Valid := by decide +kernel
theorem bound1429 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1429.a certificate1429.b certificate1429.c x ≤ (certificate1429.bound:ℝ) :=
  rat_majority_certificate_sound certificate1429 valid1429 x hx0 hx1

def certificate1430 : RatMajorityCertificate := ⟨0,(200014355003487453/200000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(54950929808688849/100000000000000000),false⟩
theorem valid1430 : certificate1430.Valid := by decide +kernel
theorem bound1430 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1430.a certificate1430.b certificate1430.c x ≤ (certificate1430.bound:ℝ) :=
  rat_majority_certificate_sound certificate1430 valid1430 x hx0 hx1

def certificate1431 : RatMajorityCertificate := ⟨(206592614118278133/1000000000000000000),(158692866542135676485516153570234751/200000000000000000000000000000000000),1,(34564584263768163567/100000000000000000000),(2160286516485510223/6250000000000000000),(54950929808688849/100000000000000000),false⟩
theorem valid1431 : certificate1431.Valid := by decide +kernel
theorem bound1431 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1431.a certificate1431.b certificate1431.c x ≤ (certificate1431.bound:ℝ) :=
  rat_majority_certificate_sound certificate1431 valid1431 x hx0 hx1

def certificate1432 : RatMajorityCertificate := ⟨0,(40002982916104729/40000000000000000),(87798034/73713125),(43973312015047314211/100000000000000000000),(10993328003761828553/25000000000000000000),(714963917830904553/1000000000000000000),false⟩
theorem valid1432 : certificate1432.Valid := by decide +kernel
theorem bound1432 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1432.a certificate1432.b certificate1432.c x ≤ (certificate1432.bound:ℝ) :=
  rat_majority_certificate_sound certificate1432 valid1432 x hx0 hx1

def certificate1433 : RatMajorityCertificate := ⟨(197525066620987261/1000000000000000000),(32101391050562927148461217549142731/40000000000000000000000000000000000),(87798034/73713125),(39688814117204577883/100000000000000000000),(9922203529301144471/25000000000000000000),(714963917830904553/1000000000000000000),false⟩
theorem valid1433 : certificate1433.Valid := by decide +kernel
theorem bound1433 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1433.a certificate1433.b certificate1433.c x ≤ (certificate1433.bound:ℝ) :=
  rat_majority_certificate_sound certificate1433 valid1433 x hx0 hx1

def certificate1434 : RatMajorityCertificate := ⟨0,(40002982916104729/40000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(549466127395823857/1000000000000000000),false⟩
theorem valid1434 : certificate1434.Valid := by decide +kernel
theorem bound1434 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1434.a certificate1434.b certificate1434.c x ≤ (certificate1434.bound:ℝ) :=
  rat_majority_certificate_sound certificate1434 valid1434 x hx0 hx1

def certificate1435 : RatMajorityCertificate := ⟨(206257000769101897/1000000000000000000),(31752087638011345864212261075429087/40000000000000000000000000000000000),1,(17286851573899269707/50000000000000000000),(6914740629559707883/20000000000000000000),(549466127395823857/1000000000000000000),false⟩
theorem valid1435 : certificate1435.Valid := by decide +kernel
theorem bound1435 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1435.a certificate1435.b certificate1435.c x ≤ (certificate1435.bound:ℝ) :=
  rat_majority_certificate_sound certificate1435 valid1435 x hx0 hx1

def certificate1436 : RatMajorityCertificate := ⟨0,(250020162901559941/250000000000000000),(56221647/47127400),(11004028063135243171/25000000000000000000),(8803222450508194537/20000000000000000000),(358372084070335879/500000000000000000),false⟩
theorem valid1436 : certificate1436.Valid := by decide +kernel
theorem bound1436 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1436.a certificate1436.b certificate1436.c x ≤ (certificate1436.bound:ℝ) :=
  rat_majority_certificate_sound certificate1436 valid1436 x hx0 hx1

def certificate1437 : RatMajorityCertificate := ⟨(198247196468338333/1000000000000000000),(200454366545768432361119538132481647/250000000000000000000000000000000000),(56221647/47127400),(1588587663771680659/4000000000000000000),(9928672898573004119/25000000000000000000),(358372084070335879/500000000000000000),false⟩
theorem valid1437 : certificate1437.Valid := by decide +kernel
theorem bound1437 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1437.a certificate1437.b certificate1437.c x ≤ (certificate1437.bound:ℝ) :=
  rat_majority_certificate_sound certificate1437 valid1437 x hx0 hx1

def certificate1438 : RatMajorityCertificate := ⟨0,(250020162901559941/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(549542775352657273/1000000000000000000),false⟩
theorem valid1438 : certificate1438.Valid := by decide +kernel
theorem bound1438 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1438.a certificate1438.b certificate1438.c x ≤ (certificate1438.bound:ℝ) :=
  rat_majority_certificate_sound certificate1438 valid1438 x hx0 hx1

def certificate1439 : RatMajorityCertificate := ⟨(206818064873808089/1000000000000000000),(198311476630825050665944988835837251/250000000000000000000000000000000000),1,(17279251549194790883/50000000000000000000),(34558503098389581767/100000000000000000000),(549542775352657273/1000000000000000000),false⟩
theorem valid1439 : certificate1439.Valid := by decide +kernel
theorem bound1439 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1439.a certificate1439.b certificate1439.c x ≤ (certificate1439.bound:ℝ) :=
  rat_majority_certificate_sound certificate1439 valid1439 x hx0 hx1

end Cycle12.MajorityCertificates.Batch035
