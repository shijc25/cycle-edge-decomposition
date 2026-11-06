import Cycle12.RationalMajorityCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Batch013

def certificate520 : RatMajorityCertificate := ⟨0,(1008244346335177707/1000000000000000000),(380603461/324740000),(8707690530054150183/20000000000000000000),(10884613162567687729/25000000000000000000),(701209875935287391/1000000000000000000),false⟩
theorem valid520 : certificate520.Valid := by decide +kernel
theorem bound520 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate520.a certificate520.b certificate520.c x ≤ (certificate520.bound:ℝ) :=
  rat_majority_certificate_sound certificate520 valid520 x hx0 hx1

def certificate521 : RatMajorityCertificate := ⟨(92949072526874423/500000000000000000),(410406796295269326460903177021911939/500000000000000000000000000000000000),(380603461/324740000),(9891593836263693603/25000000000000000000),(39566375345054774413/100000000000000000000),(701209875935287391/1000000000000000000),false⟩
theorem valid521 : certificate521.Valid := by decide +kernel
theorem bound521 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate521.a certificate521.b certificate521.c x ≤ (certificate521.bound:ℝ) :=
  rat_majority_certificate_sound certificate521 valid521 x hx0 hx1

def certificate522 : RatMajorityCertificate := ⟨0,(1008244346335177707/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(108660794602500853/200000000000000000),false⟩
theorem valid522 : certificate522.Valid := by decide +kernel
theorem bound522 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate522.a certificate522.b certificate522.c x ≤ (certificate522.bound:ℝ) :=
  rat_majority_certificate_sound certificate522 valid522 x hx0 hx1

def certificate523 : RatMajorityCertificate := ⟨(122719576213021101/1000000000000000000),(884513027433750224178962897824204593/1000000000000000000000000000000000000),1,(18344563436736237297/50000000000000000000),(7337825374694494919/20000000000000000000),(108660794602500853/200000000000000000),false⟩
theorem valid523 : certificate523.Valid := by decide +kernel
theorem bound523 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate523.a certificate523.b certificate523.c x ≤ (certificate523.bound:ℝ) :=
  rat_majority_certificate_sound certificate523 valid523 x hx0 hx1

def certificate524 : RatMajorityCertificate := ⟨0,(252066442437751919/250000000000000000),(2282264741/1948160000),(5440787089056783163/12500000000000000000),(8705259342490853061/20000000000000000000),(175156192071340867/250000000000000000),false⟩
theorem valid524 : certificate524.Valid := by decide +kernel
theorem bound524 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate524.a certificate524.b certificate524.c x ≤ (certificate524.bound:ℝ) :=
  rat_majority_certificate_sound certificate524 valid524 x hx0 hx1

def certificate525 : RatMajorityCertificate := ⟨(184591687058681853/1000000000000000000),(205537072577287173862937527238774093/250000000000000000000000000000000000),(2282264741/1948160000),(19793369540796977561/50000000000000000000),(39586739081593955123/100000000000000000000),(175156192071340867/250000000000000000),false⟩
theorem valid525 : certificate525.Valid := by decide +kernel
theorem bound525 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate525.a certificate525.b certificate525.c x ≤ (certificate525.bound:ℝ) :=
  rat_majority_certificate_sound certificate525 valid525 x hx0 hx1

def certificate526 : RatMajorityCertificate := ⟨0,(252066442437751919/250000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(271654369132777803/500000000000000000),false⟩
theorem valid526 : certificate526.Valid := by decide +kernel
theorem bound526 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate526.a certificate526.b certificate526.c x ≤ (certificate526.bound:ℝ) :=
  rat_majority_certificate_sound certificate526 valid526 x hx0 hx1

def certificate527 : RatMajorityCertificate := ⟨(122669471834565637/1000000000000000000),(221145585076694949567648887871792597/250000000000000000000000000000000000),1,(36690333063200788241/100000000000000000000),(18345166531600394121/50000000000000000000),(271654369132777803/500000000000000000),false⟩
theorem valid527 : certificate527.Valid := by decide +kernel
theorem bound527 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate527.a certificate527.b certificate527.c x ≤ (certificate527.bound:ℝ) :=
  rat_majority_certificate_sound certificate527 valid527 x hx0 hx1

def certificate528 : RatMajorityCertificate := ⟨0,(1008287165153929489/1000000000000000000),(1140828207/973940000),(43522980116947167137/100000000000000000000),(21761490058473583569/50000000000000000000),(140117467097485699/200000000000000000),false⟩
theorem valid528 : certificate528.Valid := by decide +kernel
theorem bound528 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate528.a certificate528.b certificate528.c x ≤ (certificate528.bound:ℝ) :=
  rat_majority_certificate_sound certificate528 valid528 x hx0 hx1

def certificate529 : RatMajorityCertificate := ⟨(185467903312828019/1000000000000000000),(821282258695595038007078840890447709/1000000000000000000000000000000000000),(1140828207/973940000),(19780672815768175691/50000000000000000000),(39561345631536351383/100000000000000000000),(140117467097485699/200000000000000000),false⟩
theorem valid529 : certificate529.Valid := by decide +kernel
theorem bound529 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate529.a certificate529.b certificate529.c x ≤ (certificate529.bound:ℝ) :=
  rat_majority_certificate_sound certificate529 valid529 x hx0 hx1

def certificate530 : RatMajorityCertificate := ⟨0,(1008287165153929489/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(543323004787396899/1000000000000000000),false⟩
theorem valid530 : certificate530.Valid := by decide +kernel
theorem bound530 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate530.a certificate530.b certificate530.c x ≤ (certificate530.bound:ℝ) :=
  rat_majority_certificate_sound certificate530 valid530 x hx0 hx1

def certificate531 : RatMajorityCertificate := ⟨(122712325669263311/1000000000000000000),(884557902175422211929025400531321921/1000000000000000000000000000000000000),1,(7337879813138404413/20000000000000000000),(18344699532846011033/50000000000000000000),(543323004787396899/1000000000000000000),false⟩
theorem valid531 : certificate531.Valid := by decide +kernel
theorem bound531 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate531.a certificate531.b certificate531.c x ≤ (certificate531.bound:ℝ) :=
  rat_majority_certificate_sound certificate531 valid531 x hx0 hx1

def certificate532 : RatMajorityCertificate := ⟨0,(1008344779890064423/1000000000000000000),(1139867563/973460000),(2175677269061388643/5000000000000000000),(43513545381227772861/100000000000000000000),(10940812598656853/15625000000000000),false⟩
theorem valid532 : certificate532.Valid := by decide +kernel
theorem bound532 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate532.a certificate532.b certificate532.c x ≤ (certificate532.bound:ℝ) :=
  rat_majority_certificate_sound certificate532 valid532 x hx0 hx1

def certificate533 : RatMajorityCertificate := ⟨(185060904250709073/1000000000000000000),(821739583127126895230754514599390121/1000000000000000000000000000000000000),(1139867563/973460000),(19781016717391139027/50000000000000000000),(7912406686956455611/20000000000000000000),(10940812598656853/15625000000000000),false⟩
theorem valid533 : certificate533.Valid := by decide +kernel
theorem bound533 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate533.a certificate533.b certificate533.c x ≤ (certificate533.bound:ℝ) :=
  rat_majority_certificate_sound certificate533 valid533 x hx0 hx1

def certificate534 : RatMajorityCertificate := ⟨0,(1008344779890064423/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(271674653143205409/500000000000000000),false⟩
theorem valid534 : certificate534.Valid := by decide +kernel
theorem bound534 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate534.a certificate534.b certificate534.c x ≤ (certificate534.bound:ℝ) :=
  rat_majority_certificate_sound certificate534 valid534 x hx0 hx1

def certificate535 : RatMajorityCertificate := ⟨(122709341202063989/1000000000000000000),(884611456245214396694211358221636653/1000000000000000000000000000000000000),1,(3668960938759587661/10000000000000000000),(36689609387595876611/100000000000000000000),(271674653143205409/500000000000000000),false⟩
theorem valid535 : certificate535.Valid := by decide +kernel
theorem bound535 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate535.a certificate535.b certificate535.c x ≤ (certificate535.bound:ℝ) :=
  rat_majority_certificate_sound certificate535 valid535 x hx0 hx1

def certificate536 : RatMajorityCertificate := ⟨0,(1008351050988186007/1000000000000000000),(2278993881/1947070000),(21751342413261232713/50000000000000000000),(43502684826522465427/100000000000000000000),(87473032958300997/125000000000000000),false⟩
theorem valid536 : certificate536.Valid := by decide +kernel
theorem bound536 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate536.a certificate536.b certificate536.c x ≤ (certificate536.bound:ℝ) :=
  rat_majority_certificate_sound certificate536 valid536 x hx0 hx1

def certificate537 : RatMajorityCertificate := ⟨(184996413650107231/1000000000000000000),(821809722855055180694337690276283383/1000000000000000000000000000000000000),(2278993881/1947070000),(988810810357723507/2500000000000000000),(39552432414308940281/100000000000000000000),(87473032958300997/125000000000000000),false⟩
theorem valid537 : certificate537.Valid := by decide +kernel
theorem bound537 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate537.a certificate537.b certificate537.c x ≤ (certificate537.bound:ℝ) :=
  rat_majority_certificate_sound certificate537 valid537 x hx0 hx1

def certificate538 : RatMajorityCertificate := ⟨0,(1008351050988186007/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(67915429170024747/125000000000000000),false⟩
theorem valid538 : certificate538.Valid := by decide +kernel
theorem bound538 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate538.a certificate538.b certificate538.c x ≤ (certificate538.bound:ℝ) :=
  rat_majority_certificate_sound certificate538 valid538 x hx0 hx1

def certificate539 : RatMajorityCertificate := ⟨(30607008231281569/250000000000000000),(221225153829429671552916283837195017/250000000000000000000000000000000000),1,(36696099212422627933/100000000000000000000),(18348049606211313967/50000000000000000000),(67915429170024747/125000000000000000),false⟩
theorem valid539 : certificate539.Valid := by decide +kernel
theorem bound539 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate539.a certificate539.b certificate539.c x ≤ (certificate539.bound:ℝ) :=
  rat_majority_certificate_sound certificate539 valid539 x hx0 hx1

def certificate540 : RatMajorityCertificate := ⟨0,(126046535989451013/125000000000000000),(2277910693/1946800000),(43493592761400541967/100000000000000000000),(2718349547587533873/6250000000000000000),(349697155256122249/500000000000000000),false⟩
theorem valid540 : certificate540.Valid := by decide +kernel
theorem bound540 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate540.a certificate540.b certificate540.c x ≤ (certificate540.bound:ℝ) :=
  rat_majority_certificate_sound certificate540 valid540 x hx0 hx1

def certificate541 : RatMajorityCertificate := ⟨(46124794761509453/250000000000000000),(25697763394450110428412023320074111/31250000000000000000000000000000000),(2277910693/1946800000),(3955559930694972717/10000000000000000000),(39555599306949727171/100000000000000000000),(349697155256122249/500000000000000000),false⟩
theorem valid541 : certificate541.Valid := by decide +kernel
theorem bound541 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate541.a certificate541.b certificate541.c x ≤ (certificate541.bound:ℝ) :=
  rat_majority_certificate_sound certificate541 valid541 x hx0 hx1

def certificate542 : RatMajorityCertificate := ⟨0,(126046535989451013/125000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(21731763690415881/40000000000000000),false⟩
theorem valid542 : certificate542.Valid := by decide +kernel
theorem bound542 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate542.a certificate542.b certificate542.c x ≤ (certificate542.bound:ℝ) :=
  rat_majority_certificate_sound certificate542 valid542 x hx0 hx1

def certificate543 : RatMajorityCertificate := ⟨(3051120724410173/25000000000000000),(2766580201538748608046505497644751/3125000000000000000000000000000000),1,(36704965448390349003/100000000000000000000),(9176241362097587251/25000000000000000000),(21731763690415881/40000000000000000),false⟩
theorem valid543 : certificate543.Valid := by decide +kernel
theorem bound543 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate543.a certificate543.b certificate543.c x ≤ (certificate543.bound:ℝ) :=
  rat_majority_certificate_sound certificate543 valid543 x hx0 hx1

def certificate544 : RatMajorityCertificate := ⟨0,(7878357882430273/7812500000000000),(91018379/77834400),(21738780553415731797/50000000000000000000),(8695512221366292719/20000000000000000000),(139723640142389359/200000000000000000),false⟩
theorem valid544 : certificate544.Valid := by decide +kernel
theorem bound544 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate544.a certificate544.b certificate544.c x ≤ (certificate544.bound:ℝ) :=
  rat_majority_certificate_sound certificate544 valid544 x hx0 hx1

def certificate545 : RatMajorityCertificate := ⟨(182532063474932839/1000000000000000000),(6440304961356272939896163224564953/7812500000000000000000000000000000),(91018379/77834400),(395885615074508016421697/1000000000000000000000000),(197942807537254008210849/500000000000000000000000),(139723640142389359/200000000000000000),false⟩
theorem valid545 : certificate545.Valid := by decide +kernel
theorem bound545 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate545.a certificate545.b certificate545.c x ≤ (certificate545.bound:ℝ) :=
  rat_majority_certificate_sound certificate545 valid545 x hx0 hx1

def certificate546 : RatMajorityCertificate := ⟨0,(7878357882430273/7812500000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(543331368094990163/1000000000000000000),false⟩
theorem valid546 : certificate546.Valid := by decide +kernel
theorem bound546 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate546.a certificate546.b certificate546.c x ≤ (certificate546.bound:ℝ) :=
  rat_majority_certificate_sound certificate546 valid546 x hx0 hx1

def certificate547 : RatMajorityCertificate := ⟨(1221495384920473/10000000000000000),(69160201030162321113525927320871/78125000000000000000000000000000),1,(18351349129688445911/50000000000000000000),(36702698259376891823/100000000000000000000),(543331368094990163/1000000000000000000),false⟩
theorem valid547 : certificate547.Valid := by decide +kernel
theorem bound547 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate547.a certificate547.b certificate547.c x ≤ (certificate547.bound:ℝ) :=
  rat_majority_certificate_sound certificate547 valid547 x hx0 hx1

def certificate548 : RatMajorityCertificate := ⟨0,(504217844430377297/500000000000000000),(1137474191/973010000),(21734637290868978161/50000000000000000000),(43469274581737956323/100000000000000000000),(43650373838235571/62500000000000000),false⟩
theorem valid548 : certificate548.Valid := by decide +kernel
theorem bound548 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate548.a certificate548.b certificate548.c x ≤ (certificate548.bound:ℝ) :=
  rat_majority_certificate_sound certificate548 valid548 x hx0 hx1

def certificate549 : RatMajorityCertificate := ⟨(183714130260658087/1000000000000000000),(411585901678946727549407639075749161/500000000000000000000000000000000000),(1137474191/973010000),(9887594041168515203/25000000000000000000),(39550376164674060813/100000000000000000000),(43650373838235571/62500000000000000),false⟩
theorem valid549 : certificate549.Valid := by decide +kernel
theorem bound549 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate549.a certificate549.b certificate549.c x ≤ (certificate549.bound:ℝ) :=
  rat_majority_certificate_sound certificate549 valid549 x hx0 hx1

def certificate550 : RatMajorityCertificate := ⟨0,(504217844430377297/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(543301957736796067/1000000000000000000),false⟩
theorem valid550 : certificate550.Valid := by decide +kernel
theorem bound550 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate550.a certificate550.b certificate550.c x ≤ (certificate550.bound:ℝ) :=
  rat_majority_certificate_sound certificate550 valid550 x hx0 hx1

def certificate551 : RatMajorityCertificate := ⟨(951834216749717/7812500000000000),(3459270112587703802065496672025051/3906250000000000000000000000000000),1,(18354974447983190107/50000000000000000000),(7341989779193276043/20000000000000000000),(543301957736796067/1000000000000000000),false⟩
theorem valid551 : certificate551.Valid := by decide +kernel
theorem bound551 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate551.a certificate551.b certificate551.c x ≤ (certificate551.bound:ℝ) :=
  rat_majority_certificate_sound certificate551 valid551 x hx0 hx1

def certificate552 : RatMajorityCertificate := ⟨0,(10084567614771157/10000000000000000),(1136653447/972880000),(43453389893767481251/100000000000000000000),(10863347473441870313/25000000000000000000),(697606698000547713/1000000000000000000),false⟩
theorem valid552 : certificate552.Valid := by decide +kernel
theorem bound552 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate552.a certificate552.b certificate552.c x ≤ (certificate552.bound:ℝ) :=
  rat_majority_certificate_sound certificate552 valid552 x hx0 hx1

def certificate553 : RatMajorityCertificate := ⟨(90820647392214849/500000000000000000),(4126396847941498100063661487689707/5000000000000000000000000000000000),(1136653447/972880000),(39585934258908067981/100000000000000000000),(19792967129454033991/50000000000000000000),(697606698000547713/1000000000000000000),false⟩
theorem valid553 : certificate553.Valid := by decide +kernel
theorem bound553 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate553.a certificate553.b certificate553.c x ≤ (certificate553.bound:ℝ) :=
  rat_majority_certificate_sound certificate553 valid553 x hx0 hx1

def certificate554 : RatMajorityCertificate := ⟨0,(10084567614771157/10000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(10865041695731703/20000000000000000),false⟩
theorem valid554 : certificate554.Valid := by decide +kernel
theorem bound554 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate554.a certificate554.b certificate554.c x ≤ (certificate554.bound:ℝ) :=
  rat_majority_certificate_sound certificate554 valid554 x hx0 hx1

def certificate555 : RatMajorityCertificate := ⟨(30312496131108107/250000000000000000),(2215453486886140442635976367530201/2500000000000000000000000000000000),1,(9180858396751725377/25000000000000000000),(36723433587006901509/100000000000000000000),(10865041695731703/20000000000000000),false⟩
theorem valid555 : certificate555.Valid := by decide +kernel
theorem bound555 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate555.a certificate555.b certificate555.c x ≤ (certificate555.bound:ℝ) :=
  rat_majority_certificate_sound certificate555 valid555 x hx0 hx1

def certificate556 : RatMajorityCertificate := ⟨0,(1008477803117348361/1000000000000000000),(2272365823/1945500000),(8689163314193803409/20000000000000000000),(21722908285484508523/50000000000000000000),(69730919062826343/100000000000000000),false⟩
theorem valid556 : certificate556.Valid := by decide +kernel
theorem bound556 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate556.a certificate556.b certificate556.c x ≤ (certificate556.bound:ℝ) :=
  rat_majority_certificate_sound certificate556 valid556 x hx0 hx1

def certificate557 : RatMajorityCertificate := ⟨(2268697033216861/12500000000000000),(10318041938969468630210055804085179/12500000000000000000000000000000000),(2272365823/1945500000),(39581813987365197041/100000000000000000000),(19790906993682598521/50000000000000000000),(69730919062826343/100000000000000000),false⟩
theorem valid557 : certificate557.Valid := by decide +kernel
theorem bound557 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate557.a certificate557.b certificate557.c x ≤ (certificate557.bound:ℝ) :=
  rat_majority_certificate_sound certificate557 valid557 x hx0 hx1

def certificate558 : RatMajorityCertificate := ⟨0,(1008477803117348361/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(543250129162458233/1000000000000000000),false⟩
theorem valid558 : certificate558.Valid := by decide +kernel
theorem bound558 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate558.a certificate558.b certificate558.c x ≤ (certificate558.bound:ℝ) :=
  rat_majority_certificate_sound certificate558 valid558 x hx0 hx1

def certificate559 : RatMajorityCertificate := ⟨(121135195903283681/1000000000000000000),(886315646872615217200702902516603159/1000000000000000000000000000000000000),1,(2295382483454180583/6250000000000000000),(36726119735266889329/100000000000000000000),(543250129162458233/1000000000000000000),false⟩
theorem valid559 : certificate559.Valid := by decide +kernel
theorem bound559 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate559.a certificate559.b certificate559.c x ≤ (certificate559.bound:ℝ) :=
  rat_majority_certificate_sound certificate559 valid559 x hx0 hx1

end Cycle12.MajorityCertificates.Batch013
