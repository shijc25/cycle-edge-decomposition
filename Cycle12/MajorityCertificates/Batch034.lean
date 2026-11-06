import Cycle12.RationalMajorityCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Batch034

def certificate1360 : RatMajorityCertificate := ⟨0,(500010209110436559/500000000000000000),(696358567/596752500),(5427552711171104397/12500000000000000000),(43420421689368835177/100000000000000000000),(10832900500551719/15625000000000000),false⟩
theorem valid1360 : certificate1360.Valid := by decide +kernel
theorem bound1360 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1360.a certificate1360.b certificate1360.c x ≤ (certificate1360.bound:ℝ) :=
  rat_majority_certificate_sound certificate1360 valid1360 x hx0 hx1

def certificate1361 : RatMajorityCertificate := ⟨(395933393209019/2000000000000000),(802049679488626825585830973874379/1000000000000000000000000000000000),(696358567/596752500),(39102474312141586323/100000000000000000000),(9775618578035396581/25000000000000000000),(10832900500551719/15625000000000000),false⟩
theorem valid1361 : certificate1361.Valid := by decide +kernel
theorem bound1361 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1361.a certificate1361.b certificate1361.c x ≤ (certificate1361.bound:ℝ) :=
  rat_majority_certificate_sound certificate1361 valid1361 x hx0 hx1

def certificate1362 : RatMajorityCertificate := ⟨0,(500010209110436559/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(274803796171744919/500000000000000000),false⟩
theorem valid1362 : certificate1362.Valid := by decide +kernel
theorem bound1362 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1362.a certificate1362.b certificate1362.c x ≤ (certificate1362.bound:ℝ) :=
  rat_majority_certificate_sound certificate1362 valid1362 x hx0 hx1

def certificate1363 : RatMajorityCertificate := ⟨(207496200478312613/1000000000000000000),(396259990519654403020134883893981333/500000000000000000000000000000000000),1,(34539807052046051529/100000000000000000000),(3453980705204605153/10000000000000000000),(274803796171744919/500000000000000000),false⟩
theorem valid1363 : certificate1363.Valid := by decide +kernel
theorem bound1363 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1363.a certificate1363.b certificate1363.c x ≤ (certificate1363.bound:ℝ) :=
  rat_majority_certificate_sound certificate1363 valid1363 x hx0 hx1

def certificate1364 : RatMajorityCertificate := ⟨0,(500010995388690201/500000000000000000),(696778229/596497500),(4344823758599786431/10000000000000000000),(43448237585997864311/100000000000000000000),(694152839005740019/1000000000000000000),false⟩
theorem valid1364 : certificate1364.Valid := by decide +kernel
theorem bound1364 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1364.a certificate1364.b certificate1364.c x ≤ (certificate1364.bound:ℝ) :=
  rat_majority_certificate_sound certificate1364 valid1364 x hx0 hx1

def certificate1365 : RatMajorityCertificate := ⟨(97868859513182903/500000000000000000),(201069991831602634878161690283166497/250000000000000000000000000000000000),(696778229/596497500),(9797302262210918513/25000000000000000000),(39189209048843674053/100000000000000000000),(694152839005740019/1000000000000000000),false⟩
theorem valid1365 : certificate1365.Valid := by decide +kernel
theorem bound1365 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1365.a certificate1365.b certificate1365.c x ≤ (certificate1365.bound:ℝ) :=
  rat_majority_certificate_sound certificate1365 valid1365 x hx0 hx1

def certificate1366 : RatMajorityCertificate := ⟨0,(500010995388690201/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(549554575040182087/1000000000000000000),false⟩
theorem valid1366 : certificate1366.Valid := by decide +kernel
theorem bound1366 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1366.a certificate1366.b certificate1366.c x ≤ (certificate1366.bound:ℝ) :=
  rat_majority_certificate_sound certificate1366 valid1366 x hx0 hx1

def certificate1367 : RatMajorityCertificate := ⟨(103545447894002283/500000000000000000),(198231635224897263490343640926271117/250000000000000000000000000000000000),1,(34550830820171163459/100000000000000000000),(1727541541008558173/5000000000000000000),(549554575040182087/1000000000000000000),false⟩
theorem valid1367 : certificate1367.Valid := by decide +kernel
theorem bound1367 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1367.a certificate1367.b certificate1367.c x ≤ (certificate1367.bound:ℝ) :=
  rat_majority_certificate_sound certificate1367 valid1367 x hx0 hx1

def certificate1368 : RatMajorityCertificate := ⟨0,(125002963057367313/125000000000000000),(697140523/596165000),(543466667263399451/1250000000000000000),(43477333381071956081/100000000000000000000),(695547125636677181/1000000000000000000),false⟩
theorem valid1368 : certificate1368.Valid := by decide +kernel
theorem bound1368 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1368.a certificate1368.b certificate1368.c x ≤ (certificate1368.bound:ℝ) :=
  rat_majority_certificate_sound certificate1368 valid1368 x hx0 hx1

def certificate1369 : RatMajorityCertificate := ⟨(4958738219294427/25000000000000000),(2505217105996566193101472967135349/3125000000000000000000000000000000),(697140523/596165000),(39151619725287260197/100000000000000000000),(19575809862643630099/50000000000000000000),(695547125636677181/1000000000000000000),false⟩
theorem valid1369 : certificate1369.Valid := by decide +kernel
theorem bound1369 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1369.a certificate1369.b certificate1369.c x ≤ (certificate1369.bound:ℝ) :=
  rat_majority_certificate_sound certificate1369 valid1369 x hx0 hx1

def certificate1370 : RatMajorityCertificate := ⟨0,(125002963057367313/125000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(274751538915069507/500000000000000000),false⟩
theorem valid1370 : certificate1370.Valid := by decide +kernel
theorem bound1370 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1370.a certificate1370.b certificate1370.c x ≤ (certificate1370.bound:ℝ) :=
  rat_majority_certificate_sound certificate1370 valid1370 x hx0 hx1

def certificate1371 : RatMajorityCertificate := ⟨(206696215427969071/1000000000000000000),(99165323676127259566270896349623777/125000000000000000000000000000000000),1,(8640389492804196943/25000000000000000000),(34561557971216787773/100000000000000000000),(274751538915069507/500000000000000000),false⟩
theorem valid1371 : certificate1371.Valid := by decide +kernel
theorem bound1371 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1371.a certificate1371.b certificate1371.c x ≤ (certificate1371.bound:ℝ) :=
  rat_majority_certificate_sound certificate1371 valid1371 x hx0 hx1

def certificate1372 : RatMajorityCertificate := ⟨0,(100002741638123177/100000000000000000),(2789507573/2381720000),(21759898391186539543/50000000000000000000),(43519796782373079087/100000000000000000000),(697278804276513227/1000000000000000000),false⟩
theorem valid1372 : certificate1372.Valid := by decide +kernel
theorem bound1372 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1372.a certificate1372.b certificate1372.c x ≤ (certificate1372.bound:ℝ) :=
  rat_majority_certificate_sound certificate1372 valid1372 x hx0 hx1

def certificate1373 : RatMajorityCertificate := ⟨(49791038361021803/250000000000000000),(20021445064419650804173871103371869/25000000000000000000000000000000000),(2789507573/2381720000),(9793632047901496001/25000000000000000000),(7834905638321196801/20000000000000000000),(697278804276513227/1000000000000000000),false⟩
theorem valid1373 : certificate1373.Valid := by decide +kernel
theorem bound1373 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1373.a certificate1373.b certificate1373.c x ≤ (certificate1373.bound:ℝ) :=
  rat_majority_certificate_sound certificate1373 valid1373 x hx0 hx1

def certificate1374 : RatMajorityCertificate := ⟨0,(100002741638123177/100000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(137395584635024191/250000000000000000),false⟩
theorem valid1374 : certificate1374.Valid := by decide +kernel
theorem bound1374 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1374.a certificate1374.b certificate1374.c x ≤ (certificate1374.bound:ℝ) :=
  rat_majority_certificate_sound certificate1374 valid1374 x hx0 hx1

def certificate1375 : RatMajorityCertificate := ⟨(41456732347912171/200000000000000000),(15854761433475550918850905124512733/20000000000000000000000000000000000),1,(17272808251913348531/50000000000000000000),(34545616503826697063/100000000000000000000),(137395584635024191/250000000000000000),false⟩
theorem valid1375 : certificate1375.Valid := by decide +kernel
theorem bound1375 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1375.a certificate1375.b certificate1375.c x ≤ (certificate1375.bound:ℝ) :=
  rat_majority_certificate_sound certificate1375 valid1375 x hx0 hx1

def certificate1376 : RatMajorityCertificate := ⟨0,(500014593649192843/500000000000000000),(279190593/238076000),(21776940850567693421/50000000000000000000),(43553881701135386843/100000000000000000000),(69854888510316833/100000000000000000),false⟩
theorem valid1376 : certificate1376.Valid := by decide +kernel
theorem bound1376 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1376.a certificate1376.b certificate1376.c x ≤ (certificate1376.bound:ℝ) :=
  rat_majority_certificate_sound certificate1376 valid1376 x hx0 hx1

def certificate1377 : RatMajorityCertificate := ⟨(198628241458651713/1000000000000000000),(400697574208991347622919618490709941/500000000000000000000000000000000000),(279190593/238076000),(9805975125145613507/25000000000000000000),(39223900500582454029/100000000000000000000),(69854888510316833/100000000000000000),false⟩
theorem valid1377 : certificate1377.Valid := by decide +kernel
theorem bound1377 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1377.a certificate1377.b certificate1377.c x ≤ (certificate1377.bound:ℝ) :=
  rat_majority_certificate_sound certificate1377 valid1377 x hx0 hx1

def certificate1378 : RatMajorityCertificate := ⟨0,(500014593649192843/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(109905994822169847/200000000000000000),false⟩
theorem valid1378 : certificate1378.Valid := by decide +kernel
theorem bound1378 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1378.a certificate1378.b certificate1378.c x ≤ (certificate1378.bound:ℝ) :=
  rat_majority_certificate_sound certificate1378 valid1378 x hx0 hx1

def certificate1379 : RatMajorityCertificate := ⟨(206882434866089577/1000000000000000000),(396570357046469457597323822214702589/500000000000000000000000000000000000),1,(17278262863030784603/50000000000000000000),(34556525726061569207/100000000000000000000),(109905994822169847/200000000000000000),false⟩
theorem valid1379 : certificate1379.Valid := by decide +kernel
theorem bound1379 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1379.a certificate1379.b certificate1379.c x ≤ (certificate1379.bound:ℝ) :=
  rat_majority_certificate_sound certificate1379 valid1379 x hx0 hx1

def certificate1380 : RatMajorityCertificate := ⟨0,(1000031126275549917/1000000000000000000),(2792377277/2379490000),(4357284179127525971/10000000000000000000),(43572841791275259711/100000000000000000000),(699273815816348041/1000000000000000000),false⟩
theorem valid1380 : certificate1380.Valid := by decide +kernel
theorem bound1380 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1380.a certificate1380.b certificate1380.c x ≤ (certificate1380.bound:ℝ) :=
  rat_majority_certificate_sound certificate1380 valid1380 x hx0 hx1

def certificate1381 : RatMajorityCertificate := ⟨(198493706240969579/1000000000000000000),(801531241664784957301162496507025057/1000000000000000000000000000000000000),(2792377277/2379490000),(19623553457930422589/50000000000000000000),(39247106915860845179/100000000000000000000),(699273815816348041/1000000000000000000),false⟩
theorem valid1381 : certificate1381.Valid := by decide +kernel
theorem bound1381 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1381.a certificate1381.b certificate1381.c x ≤ (certificate1381.bound:ℝ) :=
  rat_majority_certificate_sound certificate1381 valid1381 x hx0 hx1

def certificate1382 : RatMajorityCertificate := ⟨0,(1000031126275549917/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(549501337133208301/1000000000000000000),false⟩
theorem valid1382 : certificate1382.Valid := by decide +kernel
theorem bound1382 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1382.a certificate1382.b certificate1382.c x ≤ (certificate1382.bound:ℝ) :=
  rat_majority_certificate_sound certificate1382 valid1382 x hx0 hx1

def certificate1383 : RatMajorityCertificate := ⟨(206659792200941883/1000000000000000000),(793364901524970898894742958817526289/1000000000000000000000000000000000000),1,(6912515967705658541/20000000000000000000),(17281289919264146353/50000000000000000000),(549501337133208301/1000000000000000000),false⟩
theorem valid1383 : certificate1383.Valid := by decide +kernel
theorem bound1383 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1383.a certificate1383.b certificate1383.c x ≤ (certificate1383.bound:ℝ) :=
  rat_majority_certificate_sound certificate1383 valid1383 x hx0 hx1

def certificate1384 : RatMajorityCertificate := ⟨0,(10000353144536239/10000000000000000),(174587794/148540625),(8723000533404869029/20000000000000000000),(21807501333512172573/50000000000000000000),(700989880434015863/1000000000000000000),false⟩
theorem valid1384 : certificate1384.Valid := by decide +kernel
theorem bound1384 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1384.a certificate1384.b certificate1384.c x ≤ (certificate1384.bound:ℝ) :=
  rat_majority_certificate_sound certificate1384 valid1384 x hx0 hx1

def certificate1385 : RatMajorityCertificate := ⟨(49797226807996441/250000000000000000),(2002098432435528241798546292474601/2500000000000000000000000000000000),(174587794/148540625),(39272843297379787123/100000000000000000000),(9818210824344946781/25000000000000000000),(700989880434015863/1000000000000000000),false⟩
theorem valid1385 : certificate1385.Valid := by decide +kernel
theorem bound1385 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1385.a certificate1385.b certificate1385.c x ≤ (certificate1385.bound:ℝ) :=
  rat_majority_certificate_sound certificate1385 valid1385 x hx0 hx1

def certificate1386 : RatMajorityCertificate := ⟨0,(10000353144536239/10000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(68702501983182957/125000000000000000),false⟩
theorem valid1386 : certificate1386.Valid := by decide +kernel
theorem bound1386 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1386.a certificate1386.b certificate1386.c x ≤ (certificate1386.bound:ℝ) :=
  rat_majority_certificate_sound certificate1386 valid1386 x hx0 hx1

def certificate1387 : RatMajorityCertificate := ⟨(207543450632115221/1000000000000000000),(7924845345379463869878880342006181/10000000000000000000000000000000000),1,(4317323597367823711/12500000000000000000),(34538588778942589689/100000000000000000000),(68702501983182957/125000000000000000),false⟩
theorem valid1387 : certificate1387.Valid := by decide +kernel
theorem bound1387 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1387.a certificate1387.b certificate1387.c x ≤ (certificate1387.bound:ℝ) :=
  rat_majority_certificate_sound certificate1387 valid1387 x hx0 hx1

def certificate1388 : RatMajorityCertificate := ⟨0,(500018633290663983/500000000000000000),(559177747/475152000),(43649095146744794939/100000000000000000000),(2182454757337239747/5000000000000000000),(17556648710617503/25000000000000000),false⟩
theorem valid1388 : certificate1388.Valid := by decide +kernel
theorem bound1388 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1388.a certificate1388.b certificate1388.c x ≤ (certificate1388.bound:ℝ) :=
  rat_majority_certificate_sound certificate1388 valid1388 x hx0 hx1

def certificate1389 : RatMajorityCertificate := ⟨(39727175228950951/200000000000000000),(80139398795654021071544196670702167/100000000000000000000000000000000000),(559177747/475152000),(7864534804263751553/20000000000000000000),(19661337010659378883/50000000000000000000),(17556648710617503/25000000000000000),false⟩
theorem valid1389 : certificate1389.Valid := by decide +kernel
theorem bound1389 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1389.a certificate1389.b certificate1389.c x ≤ (certificate1389.bound:ℝ) :=
  rat_majority_certificate_sound certificate1389 valid1389 x hx0 hx1

def certificate1390 : RatMajorityCertificate := ⟨0,(500018633290663983/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(549572146266252297/1000000000000000000),false⟩
theorem valid1390 : certificate1390.Valid := by decide +kernel
theorem bound1390 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1390.a certificate1390.b certificate1390.c x ≤ (certificate1390.bound:ℝ) :=
  rat_majority_certificate_sound certificate1390 valid1390 x hx0 hx1

def certificate1391 : RatMajorityCertificate := ⟨(207175874502154173/1000000000000000000),(396426835671298732996990216995748941/500000000000000000000000000000000000),1,(863714747309197917/2500000000000000000),(34548589892367916681/100000000000000000000),(549572146266252297/1000000000000000000),false⟩
theorem valid1391 : certificate1391.Valid := by decide +kernel
theorem bound1391 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1391.a certificate1391.b certificate1391.c x ≤ (certificate1391.bound:ℝ) :=
  rat_majority_certificate_sound certificate1391 valid1391 x hx0 hx1

def certificate1392 : RatMajorityCertificate := ⟨0,(1000039418435573187/1000000000000000000),(699107569/593637500),(21834033025679599883/50000000000000000000),(43668066051359199767/100000000000000000000),(140598963348997651/200000000000000000),false⟩
theorem valid1392 : certificate1392.Valid := by decide +kernel
theorem bound1392 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1392.a certificate1392.b certificate1392.c x ≤ (certificate1392.bound:ℝ) :=
  rat_majority_certificate_sound certificate1392 valid1392 x hx0 hx1

def certificate1393 : RatMajorityCertificate := ⟨(198495593247839269/1000000000000000000),(801536000801979916515277526737919697/1000000000000000000000000000000000000),(699107569/593637500),(983651187510513327/2500000000000000000),(39346047500420533081/100000000000000000000),(140598963348997651/200000000000000000),false⟩
theorem valid1393 : certificate1393.Valid := by decide +kernel
theorem bound1393 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1393.a certificate1393.b certificate1393.c x ≤ (certificate1393.bound:ℝ) :=
  rat_majority_certificate_sound certificate1393 valid1393 x hx0 hx1

def certificate1394 : RatMajorityCertificate := ⟨0,(1000039418435573187/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(549522701778864821/1000000000000000000),false⟩
theorem valid1394 : certificate1394.Valid := by decide +kernel
theorem bound1394 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1394.a certificate1394.b certificate1394.c x ≤ (certificate1394.bound:ℝ) :=
  rat_majority_certificate_sound certificate1394 valid1394 x hx0 hx1

def certificate1395 : RatMajorityCertificate := ⟨(103397703293885051/500000000000000000),(396617930148195836986861772724272463/500000000000000000000000000000000000),1,(34558934715373183467/100000000000000000000),(8639733678843295867/25000000000000000000),(549522701778864821/1000000000000000000),false⟩
theorem valid1395 : certificate1395.Valid := by decide +kernel
theorem bound1395 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1395.a certificate1395.b certificate1395.c x ≤ (certificate1395.bound:ℝ) :=
  rat_majority_certificate_sound certificate1395 valid1395 x hx0 hx1

def certificate1396 : RatMajorityCertificate := ⟨0,(31251376963915941/31250000000000000),(1398788803/1185900000),(21855196491430531629/50000000000000000000),(43710392982861063259/100000000000000000000),(352363179409208613/500000000000000000),false⟩
theorem valid1396 : certificate1396.Valid := by decide +kernel
theorem bound1396 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1396.a certificate1396.b certificate1396.c x ≤ (certificate1396.bound:ℝ) :=
  rat_majority_certificate_sound certificate1396 valid1396 x hx0 hx1

def certificate1397 : RatMajorityCertificate := ⟨(99598047078509267/500000000000000000),(12513112367837630606055047022474753/15625000000000000000000000000000000),(1398788803/1185900000),(2460740833540893823/6250000000000000000),(39371853336654301169/100000000000000000000),(352363179409208613/500000000000000000),false⟩
theorem valid1397 : certificate1397.Valid := by decide +kernel
theorem bound1397 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1397.a certificate1397.b certificate1397.c x ≤ (certificate1397.bound:ℝ) :=
  rat_majority_certificate_sound certificate1397 valid1397 x hx0 hx1

def certificate1398 : RatMajorityCertificate := ⟨0,(31251376963915941/31250000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(549589976314577083/1000000000000000000),false⟩
theorem valid1398 : certificate1398.Valid := by decide +kernel
theorem bound1398 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1398.a certificate1398.b certificate1398.c x ≤ (certificate1398.bound:ℝ) :=
  rat_majority_certificate_sound certificate1398 valid1398 x hx0 hx1

def certificate1399 : RatMajorityCertificate := ⟨(207289310503567367/1000000000000000000),(24773300580778737079265685581302653/31250000000000000000000000000000000),1,(6909107462410647579/20000000000000000000),(4318192164006654737/12500000000000000000),(549589976314577083/1000000000000000000),false⟩
theorem valid1399 : certificate1399.Valid := by decide +kernel
theorem bound1399 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate1399.a certificate1399.b certificate1399.c x ≤ (certificate1399.bound:ℝ) :=
  rat_majority_certificate_sound certificate1399 valid1399 x hx0 hx1

end Cycle12.MajorityCertificates.Batch034
