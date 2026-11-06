import Cycle12.RationalMajorityCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.MajorityCertificates.Batch003

def certificate120 : RatMajorityCertificate := ⟨0,(501409865270778433/500000000000000000),(249602521/207925000),(44184218286128081513/100000000000000000000),(22092109143064040757/50000000000000000000),(45451432068627787/62500000000000000),false⟩
theorem valid120 : certificate120.Valid := by decide +kernel
theorem bound120 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate120.a certificate120.b certificate120.c x ≤ (certificate120.bound:ℝ) :=
  rat_majority_certificate_sound certificate120 valid120 x hx0 hx1

def certificate121 : RatMajorityCertificate := ⟨(13776332785009393/62500000000000000),(24430527413766684490626685673178831/31250000000000000000000000000000000),(249602521/207925000),(39316110161477997569/100000000000000000000),(3931611016147799757/10000000000000000000),(45451432068627787/62500000000000000),false⟩
theorem valid121 : certificate121.Valid := by decide +kernel
theorem bound121 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate121.a certificate121.b certificate121.c x ≤ (certificate121.bound:ℝ) :=
  rat_majority_certificate_sound certificate121 valid121 x hx0 hx1

def certificate122 : RatMajorityCertificate := ⟨0,(501409865270778433/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(541684218568856353/1000000000000000000),false⟩
theorem valid122 : certificate122.Valid := by decide +kernel
theorem bound122 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate122.a certificate122.b certificate122.c x ≤ (certificate122.bound:ℝ) :=
  rat_majority_certificate_sound certificate122 valid122 x hx0 hx1

def certificate123 : RatMajorityCertificate := ⟨(1023700949672177/7812500000000000),(3403970817175262304973551048241359/3906250000000000000000000000000000),1,(9120469543507892683/25000000000000000000),(36481878174031570733/100000000000000000000),(541684218568856353/1000000000000000000),false⟩
theorem valid123 : certificate123.Valid := by decide +kernel
theorem bound123 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate123.a certificate123.b certificate123.c x ≤ (certificate123.bound:ℝ) :=
  rat_majority_certificate_sound certificate123 valid123 x hx0 hx1

def certificate124 : RatMajorityCertificate := ⟨0,(1002885227578486383/1000000000000000000),(166213459/138460000),(8836838737793480201/20000000000000000000),(22092096844483700503/50000000000000000000),(727081996092637009/1000000000000000000),false⟩
theorem valid124 : certificate124.Valid := by decide +kernel
theorem bound124 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate124.a certificate124.b certificate124.c x ≤ (certificate124.bound:ℝ) :=
  rat_majority_certificate_sound certificate124 valid124 x hx0 hx1

def certificate125 : RatMajorityCertificate := ⟨(8748147215590313/40000000000000000),(31342021491942062287295587622792121/40000000000000000000000000000000000),(166213459/138460000),(19681314122277628699/50000000000000000000),(39362628244555257399/100000000000000000000),(727081996092637009/1000000000000000000),false⟩
theorem valid125 : certificate125.Valid := by decide +kernel
theorem bound125 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate125.a certificate125.b certificate125.c x ≤ (certificate125.bound:ℝ) :=
  rat_majority_certificate_sound certificate125 valid125 x hx0 hx1

def certificate126 : RatMajorityCertificate := ⟨0,(1002885227578486383/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(27081870160435789/50000000000000000),false⟩
theorem valid126 : certificate126.Valid := by decide +kernel
theorem bound126 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate126.a certificate126.b certificate126.c x ≤ (certificate126.bound:ℝ) :=
  rat_majority_certificate_sound certificate126 valid126 x hx0 hx1

def certificate127 : RatMajorityCertificate := ⟨(65159721509280417/500000000000000000),(436094891654457706277109411636938289/500000000000000000000000000000000000),1,(4562352352057699777/12500000000000000000),(36498818816461598217/100000000000000000000),(27081870160435789/50000000000000000),false⟩
theorem valid127 : certificate127.Valid := by decide +kernel
theorem bound127 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate127.a certificate127.b certificate127.c x ≤ (certificate127.bound:ℝ) :=
  rat_majority_certificate_sound certificate127 valid127 x hx0 hx1

def certificate128 : RatMajorityCertificate := ⟨0,(125370723982114381/125000000000000000),(177873799/148115000),(44194791930444506907/100000000000000000000),(11048697982611126727/25000000000000000000),(363810743392656071/500000000000000000),false⟩
theorem valid128 : certificate128.Valid := by decide +kernel
theorem bound128 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate128.a certificate128.b certificate128.c x ≤ (certificate128.bound:ℝ) :=
  rat_majority_certificate_sound certificate128 valid128 x hx0 hx1

def certificate129 : RatMajorityCertificate := ⟨(219379668080092349/1000000000000000000),(97866936167957254378636317239029031/125000000000000000000000000000000000),(177873799/148115000),(39355910971898047361/100000000000000000000),(19677955485949023681/50000000000000000000),(363810743392656071/500000000000000000),false⟩
theorem valid129 : certificate129.Valid := by decide +kernel
theorem bound129 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate129.a certificate129.b certificate129.c x ≤ (certificate129.bound:ℝ) :=
  rat_majority_certificate_sound certificate129 valid129 x hx0 hx1

def certificate130 : RatMajorityCertificate := ⟨0,(125370723982114381/125000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(541682961649943089/1000000000000000000),false⟩
theorem valid130 : certificate130.Valid := by decide +kernel
theorem bound130 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate130.a certificate130.b certificate130.c x ≤ (certificate130.bound:ℝ) :=
  rat_majority_certificate_sound certificate130 valid130 x hx0 hx1

def certificate131 : RatMajorityCertificate := ⟨(130400454984073273/1000000000000000000),(109022324533163999150212133628960987/125000000000000000000000000000000000),1,(2281070752313120787/6250000000000000000),(36497132037009932593/100000000000000000000),(541682961649943089/1000000000000000000),false⟩
theorem valid131 : certificate131.Valid := by decide +kernel
theorem bound131 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate131.a certificate131.b certificate131.c x ≤ (certificate131.bound:ℝ) :=
  rat_majority_certificate_sound certificate131 valid131 x hx0 hx1

def certificate132 : RatMajorityCertificate := ⟨0,(501523547660046249/500000000000000000),(2489231459/2070360000),(8845232814888421333/20000000000000000000),(22113082037221053333/50000000000000000000),(364493262323518373/500000000000000000),false⟩
theorem valid132 : certificate132.Valid := by decide +kernel
theorem bound132 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate132.a certificate132.b certificate132.c x ≤ (certificate132.bound:ℝ) :=
  rat_majority_certificate_sound certificate132 valid132 x hx0 hx1

def certificate133 : RatMajorityCertificate := ⟨(6873132559125163/31250000000000000),(12225573039786220952006504440336413/15625000000000000000000000000000000),(2489231459/2070360000),(1574961366998853539/4000000000000000000),(9843508543742834619/25000000000000000000),(364493262323518373/500000000000000000),false⟩
theorem valid133 : certificate133.Valid := by decide +kernel
theorem bound133 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate133.a certificate133.b certificate133.c x ≤ (certificate133.bound:ℝ) :=
  rat_majority_certificate_sound certificate133 valid133 x hx0 hx1

def certificate134 : RatMajorityCertificate := ⟨0,(501523547660046249/500000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(541757568598032009/1000000000000000000),false⟩
theorem valid134 : certificate134.Valid := by decide +kernel
theorem bound134 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate134.a certificate134.b certificate134.c x ≤ (certificate134.bound:ℝ) :=
  rat_majority_certificate_sound certificate134 valid134 x hx0 hx1

def certificate135 : RatMajorityCertificate := ⟨(130748949100601049/1000000000000000000),(435949870854289997659055550962084799/500000000000000000000000000000000000),1,(18244585173143626887/50000000000000000000),(1459566813851490151/4000000000000000000),(541757568598032009/1000000000000000000),false⟩
theorem valid135 : certificate135.Valid := by decide +kernel
theorem bound135 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate135.a certificate135.b certificate135.c x ≤ (certificate135.bound:ℝ) :=
  rat_majority_certificate_sound certificate135 valid135 x hx0 hx1

def certificate136 : RatMajorityCertificate := ⟨0,(6269556989220921/6250000000000000),(248460887/206715000),(11054475806918740771/25000000000000000000),(8843580645534992617/20000000000000000000),(728787372450303757/1000000000000000000),false⟩
theorem valid136 : certificate136.Valid := by decide +kernel
theorem bound136 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate136.a certificate136.b certificate136.c x ≤ (certificate136.bound:ℝ) :=
  rat_majority_certificate_sound certificate136 valid136 x hx0 hx1

def certificate137 : RatMajorityCertificate := ⟨(220807519080500757/1000000000000000000),(4885191664697235607408076019262803/6250000000000000000000000000000000),(248460887/206715000),(39342389288632172187/100000000000000000000),(9835597322158043047/25000000000000000000),(728787372450303757/1000000000000000000),false⟩
theorem valid137 : certificate137.Valid := by decide +kernel
theorem bound137 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate137.a certificate137.b certificate137.c x ≤ (certificate137.bound:ℝ) :=
  rat_majority_certificate_sound certificate137 valid137 x hx0 hx1

def certificate138 : RatMajorityCertificate := ⟨0,(6269556989220921/6250000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(541784784486835781/1000000000000000000),false⟩
theorem valid138 : certificate138.Valid := by decide +kernel
theorem bound138 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate138.a certificate138.b certificate138.c x ≤ (certificate138.bound:ℝ) :=
  rat_majority_certificate_sound certificate138 valid138 x hx0 hx1

def certificate139 : RatMajorityCertificate := ⟨(130653031123419567/1000000000000000000),(5450420364778187333846979262838793/6250000000000000000000000000000000),1,(18245819750978962721/50000000000000000000),(36491639501957925443/100000000000000000000),(541784784486835781/1000000000000000000),false⟩
theorem valid139 : certificate139.Valid := by decide +kernel
theorem bound139 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate139.a certificate139.b certificate139.c x ≤ (certificate139.bound:ℝ) :=
  rat_majority_certificate_sound certificate139 valid139 x hx0 hx1

def certificate140 : RatMajorityCertificate := ⟨0,(125401480103727083/125000000000000000),(1240527081/1031990000),(44220673193617035803/100000000000000000000),(11055168298404258951/25000000000000000000),(36440069055013571/50000000000000000),false⟩
theorem valid140 : certificate140.Valid := by decide +kernel
theorem bound140 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate140.a certificate140.b certificate140.c x ≤ (certificate140.bound:ℝ) :=
  rat_majority_certificate_sound certificate140 valid140 x hx0 hx1

def certificate141 : RatMajorityCertificate := ⟨(6856443095254121/31250000000000000),(3058988140849624752224718884940957/3906250000000000000000000000000000),(1240527081/1031990000),(39383416703792622709/100000000000000000000),(3938341670379262271/10000000000000000000),(36440069055013571/50000000000000000),false⟩
theorem valid141 : certificate141.Valid := by decide +kernel
theorem bound141 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate141.a certificate141.b certificate141.c x ≤ (certificate141.bound:ℝ) :=
  rat_majority_certificate_sound certificate141 valid141 x hx0 hx1

def certificate142 : RatMajorityCertificate := ⟨0,(125401480103727083/125000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(4233086087274491/7812500000000000),false⟩
theorem valid142 : certificate142.Valid := by decide +kernel
theorem bound142 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate142.a certificate142.b certificate142.c x ≤ (certificate142.bound:ℝ) :=
  rat_majority_certificate_sound certificate142 valid142 x hx0 hx1

def certificate143 : RatMajorityCertificate := ⟨(130768598105095651/1000000000000000000),(109002904350258647593595620685783967/125000000000000000000000000000000000),1,(7297829458229245453/20000000000000000000),(18244573645573113633/50000000000000000000),(4233086087274491/7812500000000000),false⟩
theorem valid143 : certificate143.Valid := by decide +kernel
theorem bound143 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate143.a certificate143.b certificate143.c x ≤ (certificate143.bound:ℝ) :=
  rat_majority_certificate_sound certificate143 valid143 x hx0 hx1

def certificate144 : RatMajorityCertificate := ⟨0,(100324491363581793/100000000000000000),(1239921521/1031470000),(44221096626637180559/100000000000000000000),(552763707832964757/1250000000000000000),(145754991218990743/200000000000000000),false⟩
theorem valid144 : certificate144.Valid := by decide +kernel
theorem bound144 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate144.a certificate144.b certificate144.c x ≤ (certificate144.bound:ℝ) :=
  rat_majority_certificate_sound certificate144 valid144 x hx0 hx1

def certificate145 : RatMajorityCertificate := ⟨(218799399178085457/1000000000000000000),(78373552930383073311481576236715599/100000000000000000000000000000000000),(1239921521/1031470000),(9850080309321887577/25000000000000000000),(39400321237287550309/100000000000000000000),(145754991218990743/200000000000000000),false⟩
theorem valid145 : certificate145.Valid := by decide +kernel
theorem bound145 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate145.a certificate145.b certificate145.c x ≤ (certificate145.bound:ℝ) :=
  rat_majority_certificate_sound certificate145 valid145 x hx0 hx1

def certificate146 : RatMajorityCertificate := ⟨0,(100324491363581793/100000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(270911619806694107/500000000000000000),false⟩
theorem valid146 : certificate146.Valid := by decide +kernel
theorem bound146 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate146.a certificate146.b certificate146.c x ≤ (certificate146.bound:ℝ) :=
  rat_majority_certificate_sound certificate146 valid146 x hx0 hx1

def certificate147 : RatMajorityCertificate := ⟨(26103550209344043/200000000000000000),(17446072875180198453364054492190901/20000000000000000000000000000000000),1,(18247560460148451367/50000000000000000000),(7299024184059380547/20000000000000000000),(270911619806694107/500000000000000000),false⟩
theorem valid147 : certificate147.Valid := by decide +kernel
theorem bound147 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate147.a certificate147.b certificate147.c x ≤ (certificate147.bound:ℝ) :=
  rat_majority_certificate_sound certificate147 valid147 x hx0 hx1

def certificate148 : RatMajorityCertificate := ⟨0,(200657310881579737/200000000000000000),(826353043/687130000),(44232810201545626789/100000000000000000000),(4423281020154562679/10000000000000000000),(729456765997304727/1000000000000000000),false⟩
theorem valid148 : certificate148.Valid := by decide +kernel
theorem bound148 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate148.a certificate148.b certificate148.c x ≤ (certificate148.bound:ℝ) :=
  rat_majority_certificate_sound certificate148 valid148 x hx0 hx1

def certificate149 : RatMajorityCertificate := ⟨(44126856258545293/200000000000000000),(31277085861818242058413006594472059/40000000000000000000000000000000000),(826353043/687130000),(19681698708152194401/50000000000000000000),(39363397416304388803/100000000000000000000),(729456765997304727/1000000000000000000),false⟩
theorem valid149 : certificate149.Valid := by decide +kernel
theorem bound149 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate149.a certificate149.b certificate149.c x ≤ (certificate149.bound:ℝ) :=
  rat_majority_certificate_sound certificate149 valid149 x hx0 hx1

def certificate150 : RatMajorityCertificate := ⟨0,(200657310881579737/200000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(270925933031982247/500000000000000000),false⟩
theorem valid150 : certificate150.Valid := by decide +kernel
theorem bound150 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate150.a certificate150.b certificate150.c x ≤ (certificate150.bound:ℝ) :=
  rat_majority_certificate_sound certificate150 valid150 x hx0 hx1

def certificate151 : RatMajorityCertificate := ⟨(13060708839778419/100000000000000000),(17445004374160758883401676239704197/20000000000000000000000000000000000),1,(36493135650744141619/100000000000000000000),(1824656782537207081/5000000000000000000),(270925933031982247/500000000000000000),false⟩
theorem valid151 : certificate151.Valid := by decide +kernel
theorem bound151 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate151.a certificate151.b certificate151.c x ≤ (certificate151.bound:ℝ) :=
  rat_majority_certificate_sound certificate151 valid151 x hx0 hx1

def certificate152 : RatMajorityCertificate := ⟨0,(1003379271248158287/1000000000000000000),(2469459337/2057780000),(8835117388706061659/20000000000000000000),(5521948367941288537/12500000000000000000),(45433544565925721/62500000000000000),false⟩
theorem valid152 : certificate152.Valid := by decide +kernel
theorem bound152 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate152.a certificate152.b certificate152.c x ≤ (certificate152.bound:ℝ) :=
  rat_majority_certificate_sound certificate152 valid152 x hx0 hx1

def certificate153 : RatMajorityCertificate := ⟨(109005370452745521/500000000000000000),(392315906457067816685151066061717473/500000000000000000000000000000000000),(2469459337/2057780000),(39374486049594599951/100000000000000000000),(2460905378099662497/6250000000000000000),(45433544565925721/62500000000000000),false⟩
theorem valid153 : certificate153.Valid := by decide +kernel
theorem bound153 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate153.a certificate153.b certificate153.c x ≤ (certificate153.bound:ℝ) :=
  rat_majority_certificate_sound certificate153 valid153 x hx0 hx1

def certificate154 : RatMajorityCertificate := ⟨0,(1003379271248158287/1000000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(541887411618084589/1000000000000000000),false⟩
theorem valid154 : certificate154.Valid := by decide +kernel
theorem bound154 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate154.a certificate154.b certificate154.c x ≤ (certificate154.bound:ℝ) :=
  rat_majority_certificate_sound certificate154 valid154 x hx0 hx1

def certificate155 : RatMajorityCertificate := ⟨(4079469976565487/31250000000000000),(27262346614339926757677601602759231/31250000000000000000000000000000000),1,(1824744211959213827/5000000000000000000),(36494884239184276541/100000000000000000000),(541887411618084589/1000000000000000000),false⟩
theorem valid155 : certificate155.Valid := by decide +kernel
theorem bound155 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate155.a certificate155.b certificate155.c x ≤ (certificate155.bound:ℝ) :=
  rat_majority_certificate_sound certificate155 valid155 x hx0 hx1

def certificate156 : RatMajorityCertificate := ⟨0,(200692790699323307/200000000000000000),(2466328067/2054740000),(22090613379445338837/50000000000000000000),(1767249070355627107/4000000000000000000),(181801782849014241/250000000000000000),false⟩
theorem valid156 : certificate156.Valid := by decide +kernel
theorem bound156 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate156.a certificate156.b certificate156.c x ≤ (certificate156.bound:ℝ) :=
  rat_majority_certificate_sound certificate156 valid156 x hx0 hx1

def certificate157 : RatMajorityCertificate := ⟨(217981886684020403/1000000000000000000),(156945397538803590043037217718567279/200000000000000000000000000000000000),(2466328067/2054740000),(19690773061873760867/50000000000000000000),(7876309224749504347/20000000000000000000),(181801782849014241/250000000000000000),false⟩
theorem valid157 : certificate157.Valid := by decide +kernel
theorem bound157 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate157.a certificate157.b certificate157.c x ≤ (certificate157.bound:ℝ) :=
  rat_majority_certificate_sound certificate157 valid157 x hx0 hx1

def certificate158 : RatMajorityCertificate := ⟨0,(200692790699323307/200000000000000000),1,(19618739074461745079/50000000000000000000),(39237478148923490159/100000000000000000000),(135483004571667637/250000000000000000),false⟩
theorem valid158 : certificate158.Valid := by decide +kernel
theorem bound158 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate158.a certificate158.b certificate158.c x ≤ (certificate158.bound:ℝ) :=
  rat_majority_certificate_sound certificate158 valid158 x hx0 hx1

def certificate159 : RatMajorityCertificate := ⟨(32649459506020209/250000000000000000),(43620686531743081215894251033288837/50000000000000000000000000000000000),1,(36493823586850893663/100000000000000000000),(1140431987089090427/3125000000000000000),(135483004571667637/250000000000000000),false⟩
theorem valid159 : certificate159.Valid := by decide +kernel
theorem bound159 (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    majorityCubic certificate159.a certificate159.b certificate159.c x ≤ (certificate159.bound:ℝ) :=
  rat_majority_certificate_sound certificate159 valid159 x hx0 hx1

end Cycle12.MajorityCertificates.Batch003
