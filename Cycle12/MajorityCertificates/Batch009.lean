import Cycle12.RationalMajorityCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Batch009

def certificate360 : RatMajorityCertificate := ⟨0,(125818388862992657/125000000000000000),(1177007361/987550000),(4399068583022273253/10000000000000000000),(43990685830222732531/100000000000000000000),(143977701730210689/200000000000000000),false⟩
theorem valid360 : certificate360.Valid := by decide +kernel
theorem bound360 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate360.a certificate360.b certificate360.c x ≤ (certificate360.bound:ℝ) :=
  rat_majority_certificate_sound certificate360 valid360 x hx0 hx1

def certificate361 : RatMajorityCertificate := ⟨(204030526454865041/1000000000000000000),(100147596745573336649433319690996063/125000000000000000000000000000000000),(1177007361/987550000),(19782446393718230299/50000000000000000000),(39564892787436460599/100000000000000000000),(143977701730210689/200000000000000000),false⟩
theorem valid361 : certificate361.Valid := by decide +kernel
theorem bound361 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate361.a certificate361.b certificate361.c x ≤ (certificate361.bound:ℝ) :=
  rat_majority_certificate_sound certificate361 valid361 x hx0 hx1

def certificate362 : RatMajorityCertificate := ⟨0,(125818388862992657/125000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(543160277002147041/1000000000000000000),false⟩
theorem valid362 : certificate362.Valid := by decide +kernel
theorem bound362 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate362.a certificate362.b certificate362.c x ≤ (certificate362.bound:ℝ) :=
  rat_majority_certificate_sound certificate362 valid362 x hx0 hx1

def certificate363 : RatMajorityCertificate := ⟨(25773418084735321/200000000000000000),(21920907833684815352199866188462103/25000000000000000000000000000000000),1,(365423992498039648641353/1000000000000000000000000),(182711996249019824320677/500000000000000000000000),(543160277002147041/1000000000000000000),false⟩
theorem valid363 : certificate363.Valid := by decide +kernel
theorem bound363 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate363.a certificate363.b certificate363.c x ≤ (certificate363.bound:ℝ) :=
  rat_majority_certificate_sound certificate363 valid363 x hx0 hx1

def certificate364 : RatMajorityCertificate := ⟨0,(503296771445858017/500000000000000000),(1176002033/987115000),(21989768216770154311/50000000000000000000),(43979536433540308623/100000000000000000000),(719393837185070627/1000000000000000000),false⟩
theorem valid364 : certificate364.Valid := by decide +kernel
theorem bound364 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate364.a certificate364.b certificate364.c x ≤ (certificate364.bound:ℝ) :=
  rat_majority_certificate_sound certificate364 valid364 x hx0 hx1

def certificate365 : RatMajorityCertificate := ⟨(101626701805893173/500000000000000000),(200499994811332026016729767972382059/250000000000000000000000000000000000),(1176002033/987115000),(39573701023113236121/100000000000000000000),(19786850511556618061/50000000000000000000),(719393837185070627/1000000000000000000),false⟩
theorem valid365 : certificate365.Valid := by decide +kernel
theorem bound365 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate365.a certificate365.b certificate365.c x ≤ (certificate365.bound:ℝ) :=
  rat_majority_certificate_sound certificate365 valid365 x hx0 hx1

def certificate366 : RatMajorityCertificate := ⟨0,(503296771445858017/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(33947462427963641/62500000000000000),false⟩
theorem valid366 : certificate366.Valid := by decide +kernel
theorem bound366 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate366.a certificate366.b certificate366.c x ≤ (certificate366.bound:ℝ) :=
  rat_majority_certificate_sound certificate366 valid366 x hx0 hx1

def certificate367 : RatMajorityCertificate := ⟨(64327896920131441/500000000000000000),(219272362889124900790532777336387503/250000000000000000000000000000000000),1,(36547445429588882129/100000000000000000000),(3654744542958888213/10000000000000000000),(33947462427963641/62500000000000000),false⟩
theorem valid367 : certificate367.Valid := by decide +kernel
theorem bound367 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate367.a certificate367.b certificate367.c x ≤ (certificate367.bound:ℝ) :=
  rat_majority_certificate_sound certificate367 valid367 x hx0 hx1

def certificate368 : RatMajorityCertificate := ⟨0,(201327986135208619/200000000000000000),(293761301/246671250),(8793869453935913783/20000000000000000000),(10992336817419892229/25000000000000000000),(718960528143559193/1000000000000000000),false⟩
theorem valid368 : certificate368.Valid := by decide +kernel
theorem bound368 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate368.a certificate368.b certificate368.c x ≤ (certificate368.bound:ℝ) :=
  rat_majority_certificate_sound certificate368 valid368 x hx0 hx1

def certificate369 : RatMajorityCertificate := ⟨(50678346507417653/250000000000000000),(40129027090801475366191727881648793/50000000000000000000000000000000000),(293761301/246671250),(1583092843076549221/4000000000000000000),(19788660538456865263/50000000000000000000),(718960528143559193/1000000000000000000),false⟩
theorem valid369 : certificate369.Valid := by decide +kernel
theorem bound369 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate369.a certificate369.b certificate369.c x ≤ (certificate369.bound:ℝ) :=
  rat_majority_certificate_sound certificate369 valid369 x hx0 hx1

def certificate370 : RatMajorityCertificate := ⟨0,(201327986135208619/200000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(543159120679799839/1000000000000000000),false⟩
theorem valid370 : certificate370.Valid := by decide +kernel
theorem bound370 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate370.a certificate370.b certificate370.c x ≤ (certificate370.bound:ℝ) :=
  rat_majority_certificate_sound certificate370 valid370 x hx0 hx1

def certificate371 : RatMajorityCertificate := ⟨(4014068719052681/31250000000000000),(5483355195310056562045322013742461/6250000000000000000000000000000000),1,(36552356354830876633/100000000000000000000),(18276178177415438317/50000000000000000000),(543159120679799839/1000000000000000000),false⟩
theorem valid371 : certificate371.Valid := by decide +kernel
theorem bound371 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate371.a certificate371.b certificate371.c x ≤ (certificate371.bound:ℝ) :=
  rat_majority_certificate_sound certificate371 valid371 x hx0 hx1

def certificate372 : RatMajorityCertificate := ⟨0,(1006686271187079129/1000000000000000000),(1174176133/986260000),(43961021760554894301/100000000000000000000),(21980510880277447151/50000000000000000000),(718585875430872027/1000000000000000000),false⟩
theorem valid372 : certificate372.Valid := by decide +kernel
theorem bound372 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate372.a certificate372.b certificate372.c x ≤ (certificate372.bound:ℝ) :=
  rat_majority_certificate_sound certificate372 valid372 x hx0 hx1

def certificate373 : RatMajorityCertificate := ⟨(12625326750647147/62500000000000000),(50208148840064987180429694552905037/62500000000000000000000000000000000),(1174176133/986260000),(494840400558838491/1250000000000000000),(39587232044707079281/100000000000000000000),(718585875430872027/1000000000000000000),false⟩
theorem valid373 : certificate373.Valid := by decide +kernel
theorem bound373 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate373.a certificate373.b certificate373.c x ≤ (certificate373.bound:ℝ) :=
  rat_majority_certificate_sound certificate373 valid373 x hx0 hx1

def certificate374 : RatMajorityCertificate := ⟨0,(1006686271187079129/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(543161734877320369/1000000000000000000),false⟩
theorem valid374 : certificate374.Valid := by decide +kernel
theorem bound374 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate374.a certificate374.b certificate374.c x ≤ (certificate374.bound:ℝ) :=
  rat_majority_certificate_sound certificate374 valid374 x hx0 hx1

def certificate375 : RatMajorityCertificate := ⟨(64136113813181183/500000000000000000),(438778190330518080428746602565170393/500000000000000000000000000000000000),1,(2284788855037330009/6250000000000000000),(7311324336119456029/20000000000000000000),(543161734877320369/1000000000000000000),false⟩
theorem valid375 : certificate375.Valid := by decide +kernel
theorem bound375 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate375.a certificate375.b certificate375.c x ≤ (certificate375.bound:ℝ) :=
  rat_majority_certificate_sound certificate375 valid375 x hx0 hx1

def certificate376 : RatMajorityCertificate := ⟨0,(1006732561354449649/1000000000000000000),(2346459861/1971680000),(43950778369475086227/100000000000000000000),(10987694592368771557/25000000000000000000),(22442159997599889/31250000000000000),false⟩
theorem valid376 : certificate376.Valid := by decide +kernel
theorem bound376 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate376.a certificate376.b certificate376.c x ≤ (certificate376.bound:ℝ) :=
  rat_majority_certificate_sound certificate376 valid376 x hx0 hx1

def certificate377 : RatMajorityCertificate := ⟨(100723620252334271/500000000000000000),(401964532471699425783652795213379121/500000000000000000000000000000000000),(2346459861/1971680000),(39591229682043040333/100000000000000000000),(19795614841021520167/50000000000000000000),(22442159997599889/31250000000000000),false⟩
theorem valid377 : certificate377.Valid := by decide +kernel
theorem bound377 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate377.a certificate377.b certificate377.c x ≤ (certificate377.bound:ℝ) :=
  rat_majority_certificate_sound certificate377 valid377 x hx0 hx1

def certificate378 : RatMajorityCertificate := ⟨0,(1006732561354449649/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(135793486916568483/250000000000000000),false⟩
theorem valid378 : certificate378.Valid := by decide +kernel
theorem bound378 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate378.a certificate378.b certificate378.c x ≤ (certificate378.bound:ℝ) :=
  rat_majority_certificate_sound certificate378 valid378 x hx0 hx1

def certificate379 : RatMajorityCertificate := ⟨(16023254600789523/125000000000000000),(109710438023818900044154115449772573/125000000000000000000000000000000000),1,(2284921774346076929/6250000000000000000),(7311749677907446173/20000000000000000000),(135793486916568483/250000000000000000),false⟩
theorem valid379 : certificate379.Valid := by decide +kernel
theorem bound379 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate379.a certificate379.b certificate379.c x ≤ (certificate379.bound:ℝ) :=
  rat_majority_certificate_sound certificate379 valid379 x hx0 hx1

def certificate380 : RatMajorityCertificate := ⟨0,(50338939905374079/50000000000000000),(1172313469/985425000),(43941068594689180491/100000000000000000000),(10985267148672295123/25000000000000000000),(35887381389168721/50000000000000000),false⟩
theorem valid380 : certificate380.Valid := by decide +kernel
theorem bound380 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate380.a certificate380.b certificate380.c x ≤ (certificate380.bound:ℝ) :=
  rat_majority_certificate_sound certificate380 valid380 x hx0 hx1

def certificate381 : RatMajorityCertificate := ⟨(40206737974830103/200000000000000000),(8043823414368721346163153314899863/10000000000000000000000000000000000),(1172313469/985425000),(39592027908967706723/100000000000000000000),(9898006977241926681/25000000000000000000),(35887381389168721/50000000000000000),false⟩
theorem valid381 : certificate381.Valid := by decide +kernel
theorem bound381 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate381.a certificate381.b certificate381.c x ≤ (certificate381.bound:ℝ) :=
  rat_majority_certificate_sound certificate381 valid381 x hx0 hx1

def certificate382 : RatMajorityCertificate := ⟨0,(50338939905374079/50000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(271586206084381021/500000000000000000),false⟩
theorem valid382 : certificate382.Valid := by decide +kernel
theorem bound382 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate382.a certificate382.b certificate382.c x ≤ (certificate382.bound:ℝ) :=
  rat_majority_certificate_sound certificate382 valid382 x hx0 hx1

def certificate383 : RatMajorityCertificate := ⟨(127968566345581911/1000000000000000000),(43897137934326955366585952609315031/50000000000000000000000000000000000),1,(36563930139863656927/100000000000000000000),(1142622816870739279/3125000000000000000),(271586206084381021/500000000000000000),false⟩
theorem valid383 : certificate383.Valid := by decide +kernel
theorem bound383 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate383.a certificate383.b certificate383.c x ≤ (certificate383.bound:ℝ) :=
  rat_majority_certificate_sound certificate383 valid383 x hx0 hx1

def certificate384 : RatMajorityCertificate := ⟨0,(503412506601695323/500000000000000000),(234272457/197002000),(21965273971183421409/50000000000000000000),(43930547942366842819/100000000000000000000),(717295267440054247/1000000000000000000),false⟩
theorem valid384 : certificate384.Valid := by decide +kernel
theorem bound384 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate384.a certificate384.b certificate384.c x ≤ (certificate384.bound:ℝ) :=
  rat_majority_certificate_sound certificate384 valid384 x hx0 hx1

def certificate385 : RatMajorityCertificate := ⟨(10021165800739733/50000000000000000),(20125845135263191913386454713631241/25000000000000000000000000000000000),(234272457/197002000),(7919413501817365649/20000000000000000000),(19798533754543414123/50000000000000000000),(717295267440054247/1000000000000000000),false⟩
theorem valid385 : certificate385.Valid := by decide +kernel
theorem bound385 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate385.a certificate385.b certificate385.c x ≤ (certificate385.bound:ℝ) :=
  rat_majority_certificate_sound certificate385 valid385 x hx0 hx1

def certificate386 : RatMajorityCertificate := ⟨0,(503412506601695323/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(271595459703532359/500000000000000000),false⟩
theorem valid386 : certificate386.Valid := by decide +kernel
theorem bound386 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate386.a certificate386.b certificate386.c x ≤ (certificate386.bound:ℝ) :=
  rat_majority_certificate_sound certificate386 valid386 x hx0 hx1

def certificate387 : RatMajorityCertificate := ⟨(63971369029055029/500000000000000000),(219502266067189008988517863941070633/250000000000000000000000000000000000),1,(36564650423427551943/100000000000000000000),(4570581302928443993/12500000000000000000),(271595459703532359/500000000000000000),false⟩
theorem valid387 : certificate387.Valid := by decide +kernel
theorem bound387 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate387.a certificate387.b certificate387.c x ≤ (certificate387.bound:ℝ) :=
  rat_majority_certificate_sound certificate387 valid387 x hx0 hx1

def certificate388 : RatMajorityCertificate := ⟨0,(1006871134166732153/1000000000000000000),(146391168/123075625),(43936269792391650127/100000000000000000000),(2746016862024478133/6250000000000000000),(143569468055618217/200000000000000000),false⟩
theorem valid388 : certificate388.Valid := by decide +kernel
theorem bound388 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate388.a certificate388.b certificate388.c x ≤ (certificate388.bound:ℝ) :=
  rat_majority_certificate_sound certificate388 valid388 x hx0 hx1

def certificate389 : RatMajorityCertificate := ⟨(40709701229420267/200000000000000000),(160384803784891236069159233941255149/200000000000000000000000000000000000),(146391168/123075625),(19761059183522062193/50000000000000000000),(39522118367044124387/100000000000000000000),(143569468055618217/200000000000000000),false⟩
theorem valid389 : certificate389.Valid := by decide +kernel
theorem bound389 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate389.a certificate389.b certificate389.c x ≤ (certificate389.bound:ℝ) :=
  rat_majority_certificate_sound certificate389 valid389 x hx0 hx1

def certificate390 : RatMajorityCertificate := ⟨0,(1006871134166732153/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(27159420811396637/50000000000000000),false⟩
theorem valid390 : certificate390.Valid := by decide +kernel
theorem bound390 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate390.a certificate390.b certificate390.c x ≤ (certificate390.bound:ℝ) :=
  rat_majority_certificate_sound certificate390 valid390 x hx0 hx1

def certificate391 : RatMajorityCertificate := ⟨(127716209958237997/1000000000000000000),(878277368994604569659384340673782459/1000000000000000000000000000000000000),1,(1142813738999826531/3125000000000000000),(36570039647994448993/100000000000000000000),(27159420811396637/50000000000000000),false⟩
theorem valid391 : certificate391.Valid := by decide +kernel
theorem bound391 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate391.a certificate391.b certificate391.c x ≤ (certificate391.bound:ℝ) :=
  rat_majority_certificate_sound certificate391 valid391 x hx0 hx1

def certificate392 : RatMajorityCertificate := ⟨0,(1006917227834088743/1000000000000000000),(83539471/70300000),(43911053668329923041/100000000000000000000),(21955526834164961521/50000000000000000000),(358244793242618757/500000000000000000),false⟩
theorem valid392 : certificate392.Valid := by decide +kernel
theorem bound392 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate392.a certificate392.b certificate392.c x ≤ (certificate392.bound:ℝ) :=
  rat_majority_certificate_sound certificate392 valid392 x hx0 hx1

def certificate393 : RatMajorityCertificate := ⟨(199589410245961201/1000000000000000000),(805947212164184822231325274031139657/1000000000000000000000000000000000000),(83539471/70300000),(39598715986305131073/100000000000000000000),(19799357993152565537/50000000000000000000),(358244793242618757/500000000000000000),false⟩
theorem valid393 : certificate393.Valid := by decide +kernel
theorem bound393 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate393.a certificate393.b certificate393.c x ≤ (certificate393.bound:ℝ) :=
  rat_majority_certificate_sound certificate393 valid393 x hx0 hx1

def certificate394 : RatMajorityCertificate := ⟨0,(1006917227834088743/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(543206986209270123/1000000000000000000),false⟩
theorem valid394 : certificate394.Valid := by decide +kernel
theorem bound394 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate394.a certificate394.b certificate394.c x ≤ (certificate394.bound:ℝ) :=
  rat_majority_certificate_sound certificate394 valid394 x hx0 hx1

def certificate395 : RatMajorityCertificate := ⟨(127691424810666417/1000000000000000000),(878342532345547534360126576252156169/1000000000000000000000000000000000000),1,(36570734756910331739/100000000000000000000),(1828536737845516587/5000000000000000000),(543206986209270123/1000000000000000000),false⟩
theorem valid395 : certificate395.Valid := by decide +kernel
theorem bound395 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate395.a certificate395.b certificate395.c x ≤ (certificate395.bound:ℝ) :=
  rat_majority_certificate_sound certificate395 valid395 x hx0 hx1

def certificate396 : RatMajorityCertificate := ⟨0,(201412505479139843/200000000000000000),(467761509/391540000),(352435580563607587/800000000000000000),(5506805946306368547/12500000000000000000),(722934843658550579/1000000000000000000),false⟩
theorem valid396 : certificate396.Valid := by decide +kernel
theorem bound396 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate396.a certificate396.b certificate396.c x ≤ (certificate396.bound:ℝ) :=
  rat_majority_certificate_sound certificate396 valid396 x hx0 hx1

def certificate397 : RatMajorityCertificate := ⟨(103086674505972079/500000000000000000),(79943307345809514570368540505556403/100000000000000000000000000000000000),(467761509/391540000),(4947202194075276049/12500000000000000000),(39577617552602208393/100000000000000000000),(722934843658550579/1000000000000000000),false⟩
theorem valid397 : certificate397.Valid := by decide +kernel
theorem bound397 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate397.a certificate397.b certificate397.c x ≤ (certificate397.bound:ℝ) :=
  rat_majority_certificate_sound certificate397 valid397 x hx0 hx1

def certificate398 : RatMajorityCertificate := ⟨0,(201412505479139843/200000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(543434996254649989/1000000000000000000),false⟩
theorem valid398 : certificate398.Valid := by decide +kernel
theorem bound398 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate398.a certificate398.b certificate398.c x ≤ (certificate398.bound:ℝ) :=
  rat_majority_certificate_sound certificate398 valid398 x hx0 hx1

def certificate399 : RatMajorityCertificate := ⟨(25846885126672961/200000000000000000),(35076615203633252727589577354114877/40000000000000000000000000000000000),1,(11417242316712257719397/31250000000000000000000),(73070350826958449404141/200000000000000000000000),(543434996254649989/1000000000000000000),false⟩
theorem valid399 : certificate399.Valid := by decide +kernel
theorem bound399 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate399.a certificate399.b certificate399.c x ≤ (certificate399.bound:ℝ) :=
  rat_majority_certificate_sound certificate399 valid399 x hx0 hx1

end Cycle12.MajorityCertificates.Batch009
